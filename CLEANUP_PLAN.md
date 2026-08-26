# Comprehension Cleanup Plan

Plan for making the code easier to read, organized around restoring broken
symmetries. Every operation in a B+ tree has an inverse (alloc/free,
link/unlink, split/merge, grow-root/collapse-root, borrow-left/borrow-right);
today most pairs live in different files, at different abstraction levels, or
as four hand-rolled variants of one idea. The plan is ordered so each step is
small, behavior-preserving, and independently landable.

## Correctness gate (every step)

Same as PERFORMANCE_TUNING_PLAN.md: `cargo test`, the extended differential
fuzz, and Miri on the differential-fuzz + drop/clear + borrowing suites — all
enforced by CI on every push. These refactorings are exactly what the
drop-tracking fuzzer exists for: every step below moves code that manipulates
raw slots, and the net catches any double-drop, leak, or ordering mistake.
One step per commit. After the delete.rs steps, re-run `perf_probe` and
`bench_delete` to confirm no perf regression (delete currently beats std).

## Phase 1 — truthful names and dead weight (mechanical) — DONE

1. ~~**Fix the inverted free names.**~~ — DONE. `free_tree_no_drop` →
   `drop_subtree` (its doc comment lied too: it said "without dropping K,V"
   while dropping every key and value). `free_leaf_node` →
   `free_emptied_leaf`, `free_branch_node` → `free_emptied_branch`, both
   with the precondition as a `debug_assert_eq!(len, 0)` instead of an
   8-line comment. `free_emptied_branch`'s conditional key-dropping moved
   into a new `empty_branch`, called by the one path that needs it (root
   collapse, where separators are still owned because nothing moved them);
   the two merge paths always pass emptied nodes, so both free functions
   now share one contract: *contents already gone, node is just memory*.
   Both new asserts were verified to sit on live paths (inverting them
   fails the fuzz suite), so they are real checks, not decoration.

2. ~~**Delete or repair the lying stubs.**~~ — DONE. `validate()` and
   `NULL_NODE` were dead everywhere (no caller in `src/` or `tests/`) and
   are deleted. `validate_for_operation` — also an unconditional `Ok(())`,
   but genuinely called by two test files — now runs
   `check_invariants_detailed()` and names the operation in the error, so
   those assertions test something. The remaining compat surface
   (`NodeRef`, `BTreeResultExt`, `try_*`, `get_many`, ...) is all
   test-called and stays; `NodeRef` now carries a doc comment saying it is
   an arena-era vestige no implementation code produces or consumes. The
   module comment no longer promises removal "as the implementation
   matures" — it says what the section is.

   Note for later: `NodeRef` and its test (tests/bplus_tree.rs:13-17)
   only exercise each other. Deleting both is a defensible follow-up, but
   it removes a test, so it is left as an explicit call for the author.

## Phase 2 — pair the inverses across files — DONE

3. ~~**Alloc beside free.**~~ — DONE. `free_leaf_block` /
   `free_branch_block` now sit directly beside `alloc_leaf_block` /
   `alloc_branch_block` in node_alloc.rs, under a header stating the
   shared contract: node blocks are raw memory, allocating constructs
   nothing and freeing drops nothing. `drop_subtree`, `free_emptied_leaf`,
   and `free_emptied_branch` call them instead of reaching for
   `dealloc_raw`, so every node allocation's lifecycle is auditable in one
   file.

4. ~~**Link beside unlink.**~~ — DONE. `link_leaf_after` / `unlink_leaf`
   are adjacent inverses in common.rs and are now the only code that edits
   leaf next/prev pointers — previously open-coded in `leaf_insert_or_split`
   and `free_emptied_leaf`. The link side also gave up its raw `prev_off`
   arithmetic for `carve_leaf`, matching the unlink side. Verified by the
   `adversarial_linked_list` and `linked_list_corruption_detection` suites
   under Miri, which exist to hunt exactly this kind of chain corruption.

   Also done alongside: `NodeRef` and its self-referential test deleted
   (the Phase 1 follow-up left for the author's call).

## Phase 3 — delete.rs: eight functions are really three ideas

Biggest win: ~200 of delete.rs's 708 lines are near-mirror duplicates.

5. **Make separator ownership flow through return values.**
   `remove_branch_entry` and `collapse_branch_entry` are the same 25-line
   operation, split in two because one caller pre-reads the separator key.
   Change `remove_branch_entry` to *return* the separator `K`; branch merges
   consume it, leaf merges drop it. `collapse_branch_entry` and both
   "must not drop" comments disappear — the ownership subtlety becomes
   type-checked instead of commented.

6. **Two merges per kind → one.** `merge_leaf_with_left(b, i)` is
   `merge_leaf_with_right(b, i-1)`: both merge `children[j+1]` into
   `children[j]` and remove separator `j`. Replace each with-left/with-right
   pair with one `merge_leaf_pair(branch, left_idx)` /
   `merge_branch_pair(branch, left_idx)`; the rebalancer picks `left_idx`.
   (The two branch merges today are the same code with variables renamed.)

7. **Borrows are rotations.** `borrow_from_left_*` rotates an entry right
   through the parent separator; `borrow_from_right_*` rotates left. Rewrite
   as one rotation per node kind with a direction, which also surfaces the
   real leaf/branch difference in one visible place: leaves *re-derive* the
   separator (clone of the new first key), branches *pass it through*.

8. **Make the two rebalancers textually parallel.** After 6–7,
   `rebalance_leaf_child` and `rebalance_branch_child` are the same
   skeleton (under min? → try borrow left → try borrow right → merge).
   Lay them out identically so a reader can diff them by eye. Only abstract
   the skeleton if that stays *more* readable than the parallel pair —
   generics here can cost more than duplication.

9. **Branch shifts mirror leaf shifts.** common.rs gives leaves
   `shift_right` / `shift_left_kv`; branch code hand-rolls `ptr::copy` in
   both directions. Add the branch pair (keys + children together) and use
   it in `branch_apply_split` and `remove_branch_entry`, which then read as
   the mirrors they are.

10. **One bulk-move helper for split and merge.** Splits move slots with
    `copy_nonoverlapping`; `merge_leaf_into` moves them one read/write pair
    at a time. Use the same bulk helper in both directions — the inverse
    relationship becomes visible, and the merge loop gets faster for free.

11. **Turn "should not happen" into stated invariants.** The merge-overflow
    panics and similar defensive checks blur which states are possible.
    Where the invariant checker (run by the fuzzer after every mutation)
    already forbids the state, use `debug_assert!` with the invariant named.
    Exception: `check_root_collapse`'s null-tolerant loop nulls slots
    itself mid-pass — that tolerance is load-bearing; document it rather
    than "simplify" it away.

## Phase 4 — insert.rs and layout.rs (riskiest last)

12. **Collapse `branch_insert_and_split`'s three-way case analysis.** The
    leaf split absorbs insert-position-vs-split-point into one `left_keep`
    adjustment; the branch split hand-rolls three arms of distinct index
    arithmetic (~120 lines). Reshape it the same way: split at a fixed
    midpoint, then insert into whichever half using the existing
    `branch_apply_split` insertion. Any balanced split point satisfies the
    min-fill invariant, so the fuzzer fully checks the rewrite. Do this
    step last, with the extended fuzz.

13. **Derive `compute` from `compute_for_cap`.** In layout.rs each node
    kind states the same layout arithmetic twice; `compute` is "the largest
    cap whose `compute_for_cap` fits the byte budget" — write it that way
    and half the file goes away.

## Order and expected shape

Phases 1–2 are renames and moves: an afternoon, near-zero risk, and they
make Phase 3 reviewable. Phase 3 is the payoff: delete.rs drops from ~708
lines of eight look-alike functions to roughly 500 lines of paired,
named inverses. Phase 4 item 12 is the only genuinely delicate rewrite —
it goes last, alone in its commit, behind the extended fuzz.
