# How the proofs found dead code in `delete.rs`

Commit `85ab40d`, "Remove the defensive arms in delete.rs the Lean proofs
showed unreachable", took 152 lines out of `src/delete.rs` and replaced
them with 56. Nothing about the tree's behaviour changed; the fuzzers,
Miri and the replay harness were green before and after. What changed is
that we knew which branches of the code could run. This is the story of
how we came to know it.

## The situation

By September, `delete.rs` had been through several cleanup rounds. The
root-collapse path in particular had been restructured twice ("Flatten
`check_root_collapse` with guard clauses and helpers", then "Flatten
`drop_subtree` and `consolidate_root_children`"). Each round left the
logic tidier and just as defensive. When `remove` finished, it called
`check_root_collapse`, which:

- returned early if there was no root, or the root was a leaf, or the
  root had more than two children;
- walked the root's children with `consolidate_root_children`, skipping
  any null child slot;
- for each child, `absorb_root_child` classified it as `Freed` (an empty
  leaf, which it freed on the spot and whose slot it nulled), `Survives`
  (the first real child), or `Blocks` (a second child that could not be
  merged into the survivor);
- and finally installed the survivor as the new root, or, when no child
  survived, set `root = None` and let the next insert allocate a fresh
  leaf.

The repair path had the same texture. `fix_branch_child` began:

```rust
let len = (*parts.hdr).len as usize;
if len == 0 {
    return true;
}
let children = parts.children_ptr as *mut *mut u8;
let idx = child_idx.min(len);
let child_ptr = *children.add(idx);
let Some(_) = NonNull::new(child_ptr) else {
    return len < self.min_branch_len();
};
```

An empty branch, an index past the end, a null child: each had an
answer. `child_len` read a null slot as length 0. The comment on
`plan_rebalance` explained why: "Null siblings can occur at the root
while `check_root_collapse` is mid-repair; they can never lend, but the
merge fallback assumes the chosen neighbour is present, as it always is
below the root."

Every one of those guards was locally reasonable. Read the function on
its own and each covers a state you cannot rule out from inside the
function. Read them together and a circle appears: the only code that
ever wrote a null child slot was `consolidate_root_children`, so the null
tolerance in `child_len`, `fix_branch_child` and `plan_rebalance` was
guarding against a state the collapse itself manufactured, and the
collapse manufactured it only while handling empty leaf children, which
nothing had shown could exist.

Tests cannot settle this. A defensive arm that is never reached makes no
test fail. Coverage tooling would have shown the arms unexecuted, but
unexecuted under a fuzzer is not the same as unreachable, and the
comment on `plan_rebalance` shows that someone had convinced themselves
the states were real. The question "can this branch run?" is a question
about every tree the code can build, and only an argument over every
tree answers it.

## What the proof showed

The Lean model of `delete.rs` was written first to mirror the Rust arm
for arm, including the defensive ones. `fixBranchChild` had the
`if len = 0` early return, the `min childIdx len` clamp and a
`children[idx]? = none` arm; `checkRootCollapse` called a
`consolidateRootChildren` with the `.leaf []` case and a `some none`
result that stood for "no survivor, the tree is empty". The point of
mirroring is that a theorem about the model is a theorem about the code
as written, defensive arms included.

The theorems are stated under `WF`, the invariant the Rust validator
checks at runtime and the proofs carry through every operation. Under
`WF`:

1. **A branch being repaired has at least one separator.** A root branch
   is required to have `1 ≤ len`; a non-root branch has
   `bc / 2 ≤ len`, and `bc ≥ 4`, so `len ≥ 2`. The `len == 0` arm cannot
   run.
2. **The repaired child's index is in range.** `remove_rec` descends to
   `children[A.length]` where `A` is the prefix of separators `≤ key`, so
   the index is at most `len`. The `min` clamp is the identity.
3. **No child slot is null.** The model has no null; a branch is
   `c0 :: es` with exactly `len + 1` children, and the abstraction from
   the Rust's memory to the model (later, the heap model's `absNode`)
   never produces one. The null arm cannot run.
4. **The underfull child always has a sibling.** From (1), `len ≥ 1`, so
   `child_idx = 0` has a right neighbour and any other index has a left
   one. `planRebalance_spec` says exactly which sibling each plan reads,
   and it is always present.
5. **A collapsing root never meets an empty leaf child and never ends
   with no survivor.** The root's children are `WF` non-root nodes, and a
   non-root node has nonempty contents (`wf_toList_ne_nil`: a non-root
   leaf holds at least `lc / 2 ≥ 2` entries; a branch's first child does,
   recursively). So `absorb_root_child`'s `Freed`-because-empty case
   cannot run, the `Survives` case always fires for the first child, and
   `root = None` is unreachable. With the empty-leaf case gone, the loop
   over at most two children has exactly two behaviours: one child hands
   over; two leaf children merge if their contents fit, and otherwise, or
   for two branch children, the root stays.

## How it showed it

Nobody set out to find dead code. The proofs found it because a proof
about a function has to account for every branch of that function, and
the way it accounts for an unreachable branch is distinctive: it shows
the branch's guard contradicts the hypotheses.

The first thing `fixBranchChild_spec`'s proof does after unfolding the
model is step past the three defensive arms:

```lean
have hlenks : 1 ≤ (ks1 ++ ks2).length := by
  split at hfill <;> omega
have hidx : cs1.length ≤ (ks1 ++ ks2).length := by simp; omega
...
simp only [if_neg (by omega : ¬ (ks1 ++ ks2).length = 0), Nat.min_eq_left hidx,
  getElem?_window_fst] at hfix
```

Three rewrites, three arms. `if_neg` with `¬ len = 0` says the `if`
always takes its else branch; `Nat.min_eq_left hidx` says the clamp never
clamps; `getElem?_window_fst` says the lookup is always `some`. Everything
after that line is about the code that actually runs. When you have to
write `if_neg (by omega : ¬ len = 0)` to get at the real work, you have
just proved that the `if` is dead.

Root collapse was the same shape. In `removeTree_spec`, the one-child
case read:

```lean
have hne : c0'.toList ≠ [] := wf_toList_ne_nil lc bc (by omega) hc c0' _ _ hwc
have hcons : consolidateRootChildren lc none [c0'] = some (some c0') := by
  cases c0' with
  | leaf L =>
    cases L with
    | nil => exact absurd rfl hne
    | cons x L' => rfl
  | branch _ _ => rfl
```

The proof needs to know what `consolidateRootChildren` returns, and it
gets the answer by cases: a branch child survives, a nonempty leaf child
survives, and the empty-leaf case is dismissed by `absurd rfl hne`, that
is, by showing it contradicts the invariant. The two-child case did the
same twice over. Every path through the loop had been evaluated to a
fixed answer under `WF`; the loop was a table with two live rows.

That was the signal to act. Once the theorem was in, the model could be
rewritten to just those rows:

```lean
def checkRootCollapse (lc : Nat) (root : Node K V) : Node K V :=
  match root with
  | .branch c0 [] => c0
  | .branch (.leaf L) [(_, .leaf R)] =>
    if L.length + R.length ≤ lc then .leaf (L ++ R) else root
  | _ => root
```

and `removeTree_spec` collapsed to three `rfl` equations
(`checkRootCollapse_one`, `checkRootCollapse_leaves`,
`checkRootCollapse_branches`). The Rust then followed the model, in the
same commit, so the two stayed mirrored. The rule we kept was: the model
mirrors the code, so when a proof simplifies the model, simplify the code
in step and re-run the gate.

## The code we eliminated

Root collapse went from an enum and three functions to one function with
one branch. Before:

```rust
enum RootChild { Freed, Survives, Blocks }

unsafe fn check_root_collapse(&mut self) {
    let Some(root) = self.root else { return; };
    if self.is_leaf(root) { return; }
    let parts = layout::carve_branch::<K>(root, &self.branch_layout);
    let child_count = (*parts.hdr).len as usize + 1;
    if child_count > 2 { return; }
    let children = parts.children_ptr as *mut *mut u8;
    let Some(survivor) = self.consolidate_root_children(children, child_count) else {
        return;
    };
    self.replace_root(root, survivor);
}

unsafe fn consolidate_root_children(&mut self, children: *mut *mut u8, child_count: usize)
    -> Option<Option<NonNull<u8>>>
{
    let mut survivor: Option<NonNull<u8>> = None;
    for i in 0..child_count {
        let slot = children.add(i);
        let Some(child) = NonNull::new(*slot) else { continue; };
        match self.absorb_root_child(survivor, child) {
            RootChild::Freed => *slot = ptr::null_mut(),
            RootChild::Survives => survivor = Some(child),
            RootChild::Blocks => return None,
        }
    }
    Some(survivor)
}

unsafe fn absorb_root_child(&mut self, survivor: Option<NonNull<u8>>, child: NonNull<u8>)
    -> RootChild
{
    if self.is_leaf(child) && self.node_len(child) == 0 {
        self.free_emptied_leaf(child);
        return RootChild::Freed;
    }
    let Some(kept) = survivor else { return RootChild::Survives; };
    if self.try_merge_leaves(kept, child) { RootChild::Freed } else { RootChild::Blocks }
}
```

After:

```rust
unsafe fn check_root_collapse(&mut self, root: NonNull<u8>) {
    let parts = layout::carve_branch::<K>(root, &self.branch_layout);
    let len = (*parts.hdr).len as usize;
    debug_assert!(len <= 1, "check_root_collapse on a root with more than two children");
    let children = parts.children_ptr as *mut *mut u8;
    let first = NonNull::new_unchecked(*children);
    if len == 1 {
        let second = NonNull::new_unchecked(*children.add(1));
        if !self.try_merge_leaves(first, second) {
            return;
        }
    }
    self.replace_root(root, first);
}
```

`replace_root` now takes `survivor: NonNull<u8>` rather than an
`Option`, because there is always one. `remove` calls
`check_root_collapse` under the single guard `len <= 1` rather than a
loose `len <= 2` prefilter followed by a recheck inside.

`fix_branch_child`'s preamble became:

```rust
let len = (*parts.hdr).len as usize;
debug_assert!(len > 0, "fix_branch_child on an empty branch");
debug_assert!(child_idx <= len, "child index out of range");
let children = parts.children_ptr as *mut *mut u8;
let child = NonNull::new_unchecked(*children.add(child_idx));
```

and `child_len` reads its slot unchecked:

```rust
unsafe fn child_len(&self, children: *mut *mut u8, idx: usize) -> usize {
    self.node_len(NonNull::new_unchecked(*children.add(idx)))
}
```

The `debug_assert!`s are the theorems' hypotheses, written where a
reader of the Rust will see them. Each `new_unchecked` now rests on item
(3) above rather than on a runtime check; the doc comments name the
theorem. Across the commit: 8 files, 151 insertions, 247 deletions, of
which `delete.rs` was 56 in and 152 out and the Lean model and proofs
gave up 60 more lines than they gained.

One arm was deliberately left at the time. `child_for_key` in
`common.rs` still returned an `Option`, because the lookup paths that
share it were not yet modelled. It went in a second pass, described
next.

## The second pass: `child_for_key`

**The situation.** `child_for_key` is the one descent step every
operation shares: given a branch and a key, binary-search the separators
and return the child after the last separator `<= key`, with its index.
It read the slot through `NonNull::new` and returned an `Option`, and
each of its three callers handled the `None` in its own idiom:

```rust
// common.rs, leaf_for_key
NodeTag::Branch => {
    if let Some((child, _)) = self.child_for_key(cur, key) {
        cur = child;
    } else {
        return None;
    }
}
// delete.rs, remove_rec
let (child, idx) = self.child_for_key(node, key)?;
// insert.rs, insert_rec
let (child, child_idx) = self.child_for_key(node, &key).expect("child must exist");
```

Three callers, three different opinions about the same impossible case:
`get` would report the key absent, `remove` would report it absent, and
`insert` would panic. That disagreement is itself a sign that nobody had
a scenario in mind. When the first cleanup landed, the `Option` stayed
because `child_for_key` is shared with the lookup paths, and at that
point only insert and remove were modelled; removing a guard on the
strength of a proof that did not cover one of its callers would have been
borrowing against work not yet done.

**What the proof showed.** Two facts, one per level. On the tree model,
a branch is `c0 :: es`, so it has exactly `len + 1` children, and the
descent picks `lastChild c0 (es.takeWhile (sepLE k))`, whose index is the
length of a prefix of `es` and so at most `len`; the slot exists. That
much was already true in the insert and remove proofs. What was missing
was the same fact for lookups, and for the pointer rather than the
index. The heap model supplied both. Its descent reads the child through
`h.get`, which returns `none` for an unallocated id, and the simulation
theorems for every operation that descends (`insertRecH_sim`,
`removeRecH_sim`, and once the reads were modelled `leafForKeyH_sim`,
which `getH_sim`, `firstH_sim`, `lastH_sim` and `rangeH_sim` all go
through) conclude that the operation never faults. A descent that never
faults never reads a missing child. With `leafForKeyH_sim` in place,
every caller of `child_for_key` sat under a theorem saying its `None`
branch is unreachable.

**How it showed it.** `leafForKeyH_sim` is stated for a subtree with
the bookkeeping `Sub h d id t ids lv`, which says the walk from `id`
reaches ids `ids` and abstracts to the tree `t`. Its proof is an
induction on the height. In the branch case the picked child
`lastChild c0 (es.takeWhile (sepLE k))` has its own `Sub` at one level
down, obtained by the same splitting of the children's walk that the
insert and remove proofs use, and the induction hypothesis then produces
the leaf. Nowhere is there a case for "the child id is not in the
store": the `Sub` of the child says it is, and the proof would not go
through without it. The absence of that case is the finding. The same
pattern appears in `insertRecH_sim` and `removeRecH_sim`, where the
recursive call is on the child's `Sub` and its first line is a `match`
on `h.get id` whose `none` arm is closed by `hsub.reach`, the walk
having visited the id.

**The code we eliminated.** `child_for_key` now returns the pair:

```rust
pub(crate) unsafe fn child_for_key(&self, branch: NonNull<u8>, key: &K) -> (NonNull<u8>, usize) {
    ...
    debug_assert!(child_idx <= len, "child index out of range");
    let child_ptr = *(parts.children_ptr.add(child_idx) as *const *mut u8);
    (NonNull::new_unchecked(child_ptr), child_idx)
}
```

and the three callers lost their three idioms:

```rust
NodeTag::Branch => cur = self.child_for_key(cur, key).0,
let (child, idx) = self.child_for_key(node, key);
let (child, child_idx) = self.child_for_key(node, &key);
```

Small in lines (nine out, three in), but it removed the last place in
the tree where a null child was a possibility the code entertained, and
with it the last disagreement about what to do if one appeared. The
`debug_assert!` states the index bound the tree-model theorems give; the
doc comment names the heap-model theorems for the pointer. The full gate
(`cargo test`, the replay, and the four Miri suites) was run before the
change went to `main`, since a `new_unchecked` is exactly what Miri is
there to check.

## What to take from it

Defensive code is a claim about reachability, and reachability is a
statement about every input, which is the one kind of statement tests do
not make. The second pass adds a corollary: remove a guard only once the
proof covers every caller of it, and until then leave it and say why. A proof forces the question on every branch: either the
argument goes through the branch, or the branch is dismissed by
contradiction, and the second outcome is a finding. Here the findings
were not bugs. The code was correct with the arms in. But the arms
carried a false story about the tree's possible states, a null-tolerant
API that only guarded against itself, and about a hundred lines that
every future reader would have to reason about. Removing them made the
code say what is true.
