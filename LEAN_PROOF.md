# The Lean proof of the B+ tree, and what it buys

`src/` is a B+ tree map over raw memory blocks. `lean/` is a Lean 4 model
of it with machine-checked proofs that the map is correct and that its
memory discipline is sound, at the level of nodes and slots. This
document says what was proved, how the proof is connected to the Rust,
what it changed in the Rust, and what it does not cover. It is the
companion to `LEAN_VERIFICATION_PLAN.md` (the plan and its phases),
`lean/README.md` (the files and how to run them), and
`PROOF_GUIDED_CLEANUP.md` (a worked example of the proofs removing dead
code).

## The one-paragraph version

Every operation the map exposes is proved correct twice over. On a
functional model of the tree, `insert`, `remove`, `get`, `first`, `last`,
`range` and `items` behave as a sorted association list and preserve the
tree invariant. On a second model where nodes live in a store under
numeric ids, are read and written through those ids, and fault on any
use of an unallocated id, every one of those operations never faults,
returns what the first model returns, keeps the store equal to the set
of reachable nodes, and keeps the leaves' doubly-linked sibling chain
intact. `clear` and `Drop` free every node exactly once. Over any
sequence of operations from the empty map, every entry ever inserted is,
at the end, in exactly one place: a leaf slot, handed back to the caller,
or dropped by `clear`. The proofs use no axioms beyond Lean's standard
three, contain no `sorry`, and build in CI on every push. The models are
tied to the Rust by a replay harness that feeds Rust-generated traces
through both models and checks shapes, return values and the store
invariant at every step, and by citations in the Rust source that name
the theorem behind each function.

## Why a proof, when there is already fuzzing and Miri

Fuzzing against `BTreeMap` and Miri find bugs by reaching them. A
rotation that drops a key only at one fill pattern, a merge that mislinks
a successor's `prev` only when the merged leaf was the last under its
parent, a root collapse that frees the wrong node when two leaves just
fit: each is a specific shape a trace has to hit. The theorems quantify
over every tree and every input, so those classes are closed rather than
sampled. What remains for testing is narrower and better defined: that
the models are faithful transcriptions of the Rust, and that the byte-level
manipulation the models abstract away is sound. The sections below say
how each of those is defended.

## Four layers and how they connect

```
  spec        sorted association list: insertSorted, eraseSorted, rangeSorted
    ▲  proved: toList of every operation equals the spec's list function
  tree model  Node = leaf (entries) | branch (child, (key, child)*)
              insertTree, removeTree, getTree, ..., WF (the invariant)
    ▲  proved: simulation; each heap operation abstracts to the tree operation
  heap model  Heap = HashMap NodeId NodeRec, leaves carry prev/next ids
              insertH, removeH, getH, rangeH, clearH; faulting primitives
    ▲  replay harness (Rust traces through both models) + citations
  Rust        src/*.rs, raw blocks, ptr::copy, carved offsets
```

**The spec** (`lean/BPlusTree/Model/Spec.lean`) is what a map is: a
sorted list of key-value pairs, with `insertSorted`, `eraseSorted` and
`rangeSorted` as the meaning of insert, remove and range.

**The tree model** (`Model/Tree.lean`, `Model/Delete.lean`,
`Model/Read.lean`) is a line-by-line port of the Rust algorithms onto an
inductive tree: the same descent through `child_for_key`, the same
split-first leaf insert, the same fused branch split arithmetic, the same
`plan_rebalance` with its four repairs, the same root collapse, the same
`resolve_front` / `resolve_back` / `make_items` for ranges. `WF` is the
invariant the Rust validator checks, height-indexed so that all leaves
sit at one depth.

**The heap model** (`Model/Heap.lean`) is the same algorithms again,
but over a store. A node is a record under a `NodeId`; a leaf record
carries its `prev` and `next` ids; reads, writes and frees go through
the store and return `none` on an unallocated id. `insertH` allocates
with `alloc`, `removeH` frees with `free`, `rangeH` walks `next` the way
`Items::next` does, `clearH` frees the subtree. The abstraction function
`absNode` maps a store and a root id back to a tree-model tree, and
`HeapInv` says the store holds exactly the nodes reachable from the root,
no id twice, with the leaves `Linked` end to end and the stored count
right.

**The Rust** is reached two ways. `examples/gen_trace.rs` drives the
Rust tree through nine configurations of inserts, removes and reads
(capacities from 4x4 to 32x256, dense and sparse key spaces, a
remove-heavy mix, each ending in a drain to empty) and records every
operation's return value plus periodic digests of the tree's shape;
`lake exe replay` runs the same operations through both models, checks
every return value and digest, checks `HeapInv` on the heap model at
every checkpoint, and checks the store is empty after the final clear.
And 39 `/// Lean:` comments in `src/*.rs` name the theorem that justifies
the function they sit on, so a reader of the Rust can find the proof and
a reader of the proof can find the code.

## What is proved, operation by operation

| Operation | Tree model | Heap model |
|---|---|---|
| `insert` | `insertTree_wf`, `insertTree_toList` (`Proofs/Tree.lean`): the tree stays well-formed at the same height or one higher, its entries become `insertSorted k v` of the old, the returned value is the one that was stored under `k` | `insertRecH_sim`, `insertH_sim` (`Proofs/Heap.lean`): no fault, same return value, `HeapInv` re-established; the new ids are exactly the ones allocated, the chain is preserved through `link_leaf_after`, nothing outside the touched subtree changes but the successor leaf's `prev` |
| `remove` | `removeRec_spec`, `removeTree_spec` (`Proofs/Delete.lean`): the removed pair was stored, entries become `eraseSorted k`, the tree stays well-formed at the same height or one lower, the underflow flag is exact below the root, each of the six repairs and the root collapse keeps the window well-formed | `fixBranchChildH_sim`, `removeRecH_sim`, `checkRootCollapseH_sim`, `removeH_sim` (`Proofs/HeapRemove.lean`): no fault, same return value, `HeapInv` re-established; ids only shrink and the dropped ids are exactly the freed ones (the absorbed sibling of a merge, the old root of a collapse), the chain survives `unlink_leaf` |
| `get`, `first`, `last` | `getTree_spec`, `firstTree_spec`, `lastTree_spec` (`Proofs/Read.lean`): `Some(v)` exactly when `(k, v)` is an entry; the first and last entries | `getH_sim`, `firstH_sim`, `lastH_sim` (`Proofs/HeapRead.lean`): no fault, same answers |
| `range`, `items` | `rangeTree_spec`, `itemsTree_spec`: exactly the entries between the bounds, inverted bounds included | `rangeH_sim`: hopping along `next` from the front leaf to the back leaf reads exactly that slice (`drainH_sim`) |
| `clear`, `Drop` | (nothing to say: the tree is gone) | `dropSubtreeH_spec`, `clearH_sim` (`Proofs/HeapLedger.lean`): exactly the subtree's nodes are freed, each once, and the store is empty afterwards |
| the validator | `checkInvariants_iff`, `Map.insert_wf`, `Map.remove_wf` (`Proofs/Check.lean`): the runtime checker accepts a tree exactly when it is well-formed, and `entry_count` is carried correctly | |
| any sequence | `ledger` (`Proofs/HeapLedger.lean`): live entries + entries handed back + entries dropped is a permutation of the starting entries + everything inserted | `runH_sim`, `runH_ledger`: from the empty map, any sequence of insert, remove and clear runs without a fault, hands back what the tree model hands back, and ends mirroring its tree |

Three things about the heap-model rows are worth spelling out, because
they are the memory-safety content.

- **No use after free, no double free.** Every primitive faults on an
  unallocated id, so "never faults" means every read, write and free hits
  a live node. In particular `remove` never touches a node it has already
  freed, and `clear` never frees a node twice.
- **No leak.** `HeapInv` says the store's domain is exactly the reachable
  set. Insert grows it by precisely the nodes it allocates; remove shrinks
  it by precisely the nodes it frees; clear empties it.
- **Chain integrity.** `Linked h none leaves none` says the leaves,
  listed in tree order, are joined by `prev` / `next` with null ends.
  Every operation preserves it, which is what makes `range` correct.

The ledger theorem is the value-token accounting. The models are
functional, so "a value dropped twice" is not a sentence they can form;
what the Rust's ownership discipline amounts to is a conservation law,
and that they can form: nothing is duplicated and nothing is lost, over
whole histories, on both models.

## What the proof changed in the Rust

Proving is a way of reading, and the reading produced changes.

- **Dead arms removed from `delete.rs`.** The proofs showed that under
  the invariant `fix_branch_child` never sees an empty branch or a
  missing child, `plan_rebalance` never measures a missing sibling, and
  root collapse never meets an empty leaf child or ends with no survivor.
  The defensive code for those cases was removed: `fix_branch_child`
  asserts its preconditions, `check_root_collapse` is a two-case
  function, and the `RootChild` machinery is gone. The models were
  simplified in step so they still mirror the code.
- **The validator now checks uniform leaf depth.** The runtime checker
  never verified that all leaves sit at one depth. The height-indexed
  invariant made the gap visible; `validate_node` now returns the height
  and rejects children at different heights, and rejects a branch with
  no keys.
- **Insert is recursive again, and splits a leaf before inserting.** Two
  earlier restructurings made insert mirror `remove_rec`, which is what
  let one induction scheme serve both proofs.
- **The fused branch split is the theorem, not a simplification.** A
  branch promotes a key when it splits, so an even-capacity branch split
  naively leaves one side below minimum fill; the arithmetic in
  `branch_insert_and_split` that picks the promotion point knowing where
  the new entry lands is what the proof verifies (`branchApplySplit_*`).

## What it does not cover

- **Bytes.** Node layout, carved offsets, alignment, `ptr::copy` and
  aliasing are below the heap model. The model faults where the Rust
  would read garbage, so "the model never faults" is the property; the
  Miri suites (`differential_fuzz`, `drop_and_clear_tests`,
  `memory_safety_audit`, `borrowing_double_free_test`) remain the gate
  for the manipulation itself. A `ptr::copy` that leaves a stale
  duplicate behind a decremented length is invisible to a functional
  model and is Miri's to catch.
- **Transcription.** The models are hand-written ports. Nothing
  mechanically ties a model function to its Rust function; the replay
  harness and the citations are the defence, and both are testing rather
  than proof. The most likely residual error is a mistranscribed repair
  in `delete.rs`, and each repair is both cited and exercised by the
  replay's remove-heavy configurations.
- **Capacities.** The remove theorems assume leaf and branch capacities
  of at least 4, the insert and read theorems at least 2 or 3. `with_caps`
  rejects anything below 4 (`MIN_NODE_CAPACITY`), so the assumptions hold
  for every tree the Rust will build, but that rejection is a Rust-side
  check, not a proved one.
- **Order lawfulness.** As for `std::collections::BTreeMap`, `K: Ord` is
  assumed to be a total order and `K::clone` to return an equal key.
- **Allocation failure and panics** are outside the model; the model's
  `alloc` always succeeds.
- **Concurrency** does not arise; the tree is single-threaded by type.

## How to check it yourself

```
cd lean && lake build          # every theorem, no sorry
./lean/replay.sh               # nine Rust traces through both models
```

The toolchain is pinned in `lean/lean-toolchain` (Lean 4.33.0, core `Std`
only, no Mathlib). To see what a theorem rests on:

```
import BPlusTree
#print axioms BPlusTree.runH_ledger
-- [propext, Classical.choice, Quot.sound]
```

Those three are Lean's standard axioms; nothing else is assumed anywhere
in `lean/`. `grep -r sorry lean/BPlusTree` is empty. CI runs `lake build`
and the replay on every push.

## Size and layout

| Part | Lines |
|---|---|
| Models (`lean/BPlusTree/Model/*.lean`) | about 1,600 |
| Tree-model proofs (`Proofs/Spec,Leaf,Branch,Tree,Delete,Read,Check`) | about 4,500 |
| Heap-model proofs (`Proofs/Heap,HeapRemove,HeapRead,HeapLedger`) | about 6,400 |
| Replay harness (`Replay/Main.lean`, `examples/gen_trace.rs`) | a few hundred |

The heap-model proofs are the larger half because the store is explicit:
every step has to say which ids change, which do not, and why the ones
that do are allocated. The recurring device is a frame: below a subtree,
only that subtree's ids and the successor leaf's `prev` change, and a
generic "window" lemma handles all six repairs of remove at once.

## Reading order

1. `Model/Spec.lean`, then `Model/Tree.lean`: what a map means and what a
   tree is.
2. `Proofs/Tree.lean` (`insertTree_wf`, `insertTree_toList`) and
   `Proofs/Delete.lean` (`removeTree_spec`): the algorithms are right.
3. `Proofs/Check.lean` (`checkInvariants_iff`): the runtime checker
   checks the invariant the proofs use.
4. `Model/Heap.lean`, then `Proofs/Heap.lean` from `HeapInv` and
   `insertH_sim` backwards: what the store is and how a simulation is
   stated.
5. `Proofs/HeapLedger.lean` (`runH_ledger`): the end-to-end statement.
6. `PROOF_GUIDED_CLEANUP.md`: a worked example of the proofs changing the
   code. It walks through the removal of the defensive arms in
   `delete.rs` and then of `child_for_key`'s `Option`, showing the exact
   proof steps that dismissed each arm, and is the best single read for
   what "the proof forces every branch to be accounted for" means in
   practice.
7. `LEAN_VERIFICATION_PLAN.md`: the plan the work followed, phase by
   phase, with the findings each phase produced and what remains out of
   scope; read it for the history and the decisions rather than the
   results.

Every function in `src/` that has a theorem carries a `/// Lean:` line
naming it; start from the Rust if that is the side you know.
