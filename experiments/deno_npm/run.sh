#!/usr/bin/env bash
# Reproduce the deno_npm substitution experiment.
#
# Clones Deno at the pinned commit, applies bplustree.patch (which swaps the
# std BTreeMap/BTreeSet in libs/npm for bplustree_compat), runs deno_npm's
# test suite on the B+ tree, then builds the divan benchmark binary for
# both the std baseline and the B+ tree and runs them interleaved.
#
# Usage: experiments/deno_npm/run.sh [work-dir] [rounds]
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
WORK="${1:-$HERE/work}"
ROUNDS="${2:-5}"
DENO_COMMIT="$(cat "$HERE/DENO_COMMIT")"

mkdir -p "$WORK"
if [ ! -d "$WORK/deno/.git" ]; then
  git clone --depth 1 https://github.com/denoland/deno "$WORK/deno"
  git -C "$WORK/deno" fetch --depth 1 origin "$DENO_COMMIT"
  git -C "$WORK/deno" checkout -q "$DENO_COMMIT"
fi
cd "$WORK/deno"
git checkout -q -B baseline "$DENO_COMMIT"

# The patch names the compat crate by absolute path; point it at this checkout.
git checkout -q -B bplustree baseline
sed "s|/home/user/BPlusTree5/compat|$REPO_ROOT/compat|" "$HERE/bplustree.patch" | git apply -
git commit -qam "Use bplustree_compat::BTreeMap in deno_npm"

echo "== deno_npm tests on the B+ tree"
cargo test -p deno_npm 2>&1 | grep -E "^test result"

for br in baseline bplustree; do
  git checkout -q "$br"
  bin=$(cargo bench -p deno_npm --bench bench --no-run 2>&1 \
    | grep -oE "target/release/deps/bench-[0-9a-f]+" | tail -1)
  cp "$bin" "$WORK/bench_$br"
done
git checkout -q bplustree

echo "== interleaved benchmark rounds ($ROUNDS)"
for i in $(seq 1 "$ROUNDS"); do
  for br in baseline bplustree; do
    echo "--- round $i: $br"
    "$WORK/bench_$br" resolution::test 2>&1 | grep -E "test|resolution"
  done
done
