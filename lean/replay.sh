#!/usr/bin/env bash
# Generate insert traces from the Rust tree and replay them through the
# Lean model, comparing shapes at every dump. Run from anywhere; traces go
# to target/replay (or $1).
set -euo pipefail
cd "$(dirname "$0")/.."
out=$(realpath -m "${1:-target/replay}")
mkdir -p "$out"

cargo build --release --example gen_trace
gen=target/release/examples/gen_trace

# seed leaf_cap branch_cap ops key_space dump_every
configs=(
  "1 4 4 3000 200 1"
  "2 4 8 3000 500 1"
  "3 8 4 3000 500 1"
  "4 5 5 3000 300 1"
  "5 6 7 4000 1000 1"
  "6 4 4 3000 20 1"
  "7 16 16 20000 50000 200"
  "8 32 256 60000 1000000 2000"
)
traces=()
for c in "${configs[@]}"; do
  # shellcheck disable=SC2086
  set -- $c
  f="$out/trace_$1_${2}x$3.txt"
  "$gen" "$@" "$f"
  traces+=("$f")
done

cd lean
lake exe replay "${traces[@]}"
