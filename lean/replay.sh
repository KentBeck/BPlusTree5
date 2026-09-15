#!/usr/bin/env bash
# Generate insert traces from the Rust tree and replay them through the
# Lean model, comparing a digest of the tree shape at every check line and
# the full shape at the end. On a digest mismatch, rerun the generator to
# print the Rust shape at the failing operation next to the Lean one.
# Run from anywhere; traces go to target/replay (or $1).
set -euo pipefail
cd "$(dirname "$0")/.."
out=$(realpath -m "${1:-target/replay}")
mkdir -p "$out"

cargo build --release --example gen_trace
gen=$(realpath target/release/examples/gen_trace)

# seed leaf_cap branch_cap ops key_space check_every remove_pct drain
# remove_pct 43 is the differential fuzz's 30 removes per 40 inserts;
# drain 1 removes every remaining key afterwards, down to the empty tree.
configs=(
  "1 4 4 3000 200 1 0 1"
  "2 4 8 3000 500 1 43 1"
  "3 8 4 3000 500 1 43 1"
  "4 5 5 3000 300 1 43 1"
  "5 6 7 4000 1000 1 43 1"
  "6 4 4 3000 20 1 43 1"
  "7 4 4 6000 60 1 60 1"
  "8 16 16 20000 50000 10 43 1"
  "9 32 256 60000 1000000 100 43 1"
)
declare -A args_of
traces=()
for c in "${configs[@]}"; do
  # shellcheck disable=SC2086
  set -- $c
  f="$out/trace_$1_${2}x$3.txt"
  "$gen" "$@" "$f"
  args_of["$f"]="$c"
  traces+=("$f")
done

status=0
log=$(mktemp)
(cd lean && lake exe replay "${traces[@]}") 2>&1 | tee "$log" || status=$?

# Fallback: for each digest mismatch, show both shapes token by token.
while IFS= read -r line; do
  f=${line%%:*}
  n=$(sed -n 's/.*after \([0-9]*\) ops.*/\1/p' <<<"$line")
  [[ -n "$n" && -n "${args_of[$f]:-}" ]] || continue
  echo
  echo "== $f: shapes after op $n =="
  # shellcheck disable=SC2086
  set -- ${args_of[$f]}
  rust=$("$gen" "$@" /dev/null "$n")
  lean=$(awk -v f="$f" 'found && /^  lean shape: / { sub(/^  lean shape: /, ""); print; exit }
                        index($0, f ":") == 1 && /digest mismatch/ { found = 1 }' "$log")
  echo "rust: $rust"
  echo "lean: $lean"
  echo "-- token diff (rust <, lean >) --"
  diff <(tr ' ' '\n' <<<"$rust") <(tr ' ' '\n' <<<"$lean") || true
done < <(grep "shape digest mismatch" "$log" || true)
rm -f "$log"
exit $status
