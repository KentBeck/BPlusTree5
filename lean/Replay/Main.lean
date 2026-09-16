import BPlusTree

/-!
# Replay harness

Reads traces written by `examples/gen_trace.rs`, replays every operation
through the Lean model, and compares the model's shape with the Rust
tree's shape at every dump line. Equal shapes at every dump across the
fuzz configurations is the evidence that the model is the code: same
splits, same separators, same leaf contents, not just the same map.

Trace format (one op or check per line):

    CAPS <leaf_cap> <branch_cap>
    I <key> <value> <old value or ->
    R <key> <removed value or ->
    G <key> <value or ->
    F <key:value or ->
    L <key:value or ->
    N <start> <end> <count> <fnv1a-64 of the items rendered as a leaf>
    # <fnv1a-64 of the shape, 16 hex digits>
    = <shape>

The value fields are what the Rust call returned; the model's return
value must agree. A range bound is `u` (unbounded), `i<k>` (included)
or `e<k>` (excluded).

Every operation and query is also run through the heap model
(`Model/Heap.lean`): it must not fault, its return value must match, at
every digest or shape line its store must abstract to the same tree as
the tree model and pass `heapInvOK` (store = reachable nodes, no id
twice, leaves chained in tree order), and its range answers, which walk
the sibling chain, must match the Rust. At the end of a trace the tree
is dropped and the store must be empty.

Shapes: a leaf is `(k:v k:v ...)`, a branch is `[child sep child ...]`.
Digest lines are the cheap, frequent check; a full shape line normally
appears only at the end of a trace. On a digest mismatch this tool prints
the model's shape, and `lean/replay.sh` reruns the generator to print the
Rust shape at the same operation.
-/

open BPlusTree

/-- 64-bit FNV-1a over the UTF-8 bytes, matching `ShapeHasher` in
`src/common.rs`. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x0000_0100_0000_01b3) 0xcbf2_9ce4_8422_2325

/-- Sixteen lowercase hex digits, as Rust's `{:016x}` prints. -/
def hex16 (x : UInt64) : String :=
  let digits := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - digits.length) ++ digits

/-- The same rendering as the Rust `dump_shape`. -/
partial def shape : Node Int Int → String
  | .leaf kvs => "(" ++ " ".intercalate (kvs.map fun (k, v) => s!"{k}:{v}") ++ ")"
  | .branch c0 entries =>
    "[" ++ shape c0 ++ String.join (entries.map fun (s, c) => s!" {s} " ++ shape c) ++ "]"

def optStr : Option Int → String
  | some v => toString v
  | none => "-"

def pairStr : Option (Int × Int) → String
  | some (k, v) => s!"{k}:{v}"
  | none => "-"

def parseBound (s : String) : Bound Int :=
  if s == "u" then .unbounded
  else if s.startsWith "i" then .included (s.drop 1).toInt!
  else .excluded (s.drop 1).toInt!

structure Outcome where
  ok : Bool
  ops : Nat
  checks : Nat
  queries : Nat

/-- Descent fuel for the heap model: far more than any replayed height. -/
def fuel : Nat := 64

/-- The heap model's tree, rendered like the tree model's. -/
def heapShape (m : HeapMap Int Int) : String :=
  match m.root with
  | none => "()"
  | some root =>
    match absNode fuel m.heap root with
    | some n => shape n
    | none => "<unreadable>"

def replayFile (path : System.FilePath) : IO Outcome := do
  let content ← IO.FS.readFile path
  let mut root : Node Int Int := .leaf []
  let mut hm : HeapMap Int Int := HeapMap.new
  let mut lc := 0
  let mut bc := 0
  let mut ops := 0
  let mut checks := 0
  let mut queries := 0
  let mut lineNo := 0
  for line in content.splitOn "\n" do
    lineNo := lineNo + 1
    match line.splitOn " " with
    | ["CAPS", l, b] =>
      lc := l.toNat!
      bc := b.toNat!
    | ["I", k, v, old] =>
      let (root', got) := insertTree lc bc root k.toInt! v.toInt!
      root := root'
      ops := ops + 1
      if optStr got != old then
        IO.eprintln s!"{path}:{lineNo}: insert {k} returned {optStr got} in the model, {old} in Rust"
        return { ok := false, ops, checks, queries }
      match insertH lc bc fuel hm k.toInt! v.toInt! with
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted on insert {k}"
        return { ok := false, ops, checks, queries }
      | some (gotH, hm') =>
        hm := hm'
        if optStr gotH != old then
          IO.eprintln s!"{path}:{lineNo}: heap insert {k} returned {optStr gotH}, Rust {old}"
          return { ok := false, ops, checks, queries }
    | ["R", k, res] =>
      let got := removeTree lc bc root k.toInt!
      ops := ops + 1
      match got with
      | some (v, root') =>
        root := root'
        if toString v != res then
          IO.eprintln s!"{path}:{lineNo}: remove {k} returned {v} in the model, {res} in Rust"
          return { ok := false, ops, checks, queries }
      | none =>
        if res != "-" then
          IO.eprintln s!"{path}:{lineNo}: remove {k} found nothing in the model, {res} in Rust"
          return { ok := false, ops, checks, queries }
      match removeH lc bc fuel hm k.toInt! with
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted on remove {k}"
        return { ok := false, ops, checks, queries }
      | some (gotH, hm') =>
        hm := hm'
        if optStr gotH != res then
          IO.eprintln s!"{path}:{lineNo}: heap remove {k} returned {optStr gotH}, Rust {res}"
          return { ok := false, ops, checks, queries }
    | ["G", k, res] =>
      let got := getTree root k.toInt!
      queries := queries + 1
      if optStr got != res then
        IO.eprintln s!"{path}:{lineNo}: get {k} returned {optStr got} in the model, {res} in Rust"
        return { ok := false, ops, checks, queries }
      match getH fuel hm k.toInt! with
      | some gotH =>
        if optStr gotH != res then
          IO.eprintln s!"{path}:{lineNo}: heap get {k} returned {optStr gotH}, Rust {res}"
          return { ok := false, ops, checks, queries }
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted on get {k}"
        return { ok := false, ops, checks, queries }
    | ["F", res] =>
      let got := firstTree root
      queries := queries + 1
      if pairStr got != res then
        IO.eprintln s!"{path}:{lineNo}: first returned {pairStr got} in the model, {res} in Rust"
        return { ok := false, ops, checks, queries }
      match firstH fuel hm with
      | some gotH =>
        if pairStr gotH != res then
          IO.eprintln s!"{path}:{lineNo}: heap first returned {pairStr gotH}, Rust {res}"
          return { ok := false, ops, checks, queries }
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted on first"
        return { ok := false, ops, checks, queries }
    | ["L", res] =>
      let got := lastTree root
      queries := queries + 1
      if pairStr got != res then
        IO.eprintln s!"{path}:{lineNo}: last returned {pairStr got} in the model, {res} in Rust"
        return { ok := false, ops, checks, queries }
      match lastH fuel hm with
      | some gotH =>
        if pairStr gotH != res then
          IO.eprintln s!"{path}:{lineNo}: heap last returned {pairStr gotH}, Rust {res}"
          return { ok := false, ops, checks, queries }
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted on last"
        return { ok := false, ops, checks, queries }
    | ["N", sb, eb, n, expected] =>
      let items := rangeTree root (parseBound sb) (parseBound eb)
      let got := hex16 (fnv1a (shape (.leaf items)))
      queries := queries + 1
      if got != expected || toString items.length != n then
        IO.eprintln s!"{path}:{lineNo}: range {sb} {eb} differs: model has {items.length} items, digest {got}; Rust has {n} items, digest {expected}"
        IO.eprintln s!"  model items: {shape (.leaf items)}"
        return { ok := false, ops, checks, queries }
      match rangeH fuel (hm.heap.fresh + 1) hm (parseBound sb) (parseBound eb) with
      | some itemsH =>
        let gotH := hex16 (fnv1a (shape (.leaf itemsH)))
        if gotH != expected || toString itemsH.length != n then
          IO.eprintln s!"{path}:{lineNo}: heap range {sb} {eb} differs: {itemsH.length} items, digest {gotH}; Rust {n} items, digest {expected}"
          IO.eprintln s!"  heap items: {shape (.leaf itemsH)}"
          return { ok := false, ops, checks, queries }
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted on range {sb} {eb}"
        return { ok := false, ops, checks, queries }
    | ["#", expected] =>
      let got := hex16 (fnv1a (shape root))
      if got == expected then
        checks := checks + 1
      else
        IO.eprintln s!"{path}:{lineNo}: shape digest mismatch after {ops} ops (rust {expected}, lean {got})"
        IO.eprintln s!"  lean shape: {shape root}"
        return { ok := false, ops, checks, queries }
      let gotH := hex16 (fnv1a (heapShape hm))
      if gotH != expected then
        IO.eprintln s!"{path}:{lineNo}: heap model shape digest mismatch after {ops} ops (rust {expected}, heap {gotH})"
        IO.eprintln s!"  heap shape: {heapShape hm}"
        return { ok := false, ops, checks, queries }
      if !heapInvOK fuel hm then
        IO.eprintln s!"{path}:{lineNo}: heap invariant broken after {ops} ops (count {hm.count}, nodes {hm.heap.nodes.size}, fresh {hm.heap.fresh})"
        return { ok := false, ops, checks, queries }
      if hm.count != root.toList.length then
        IO.eprintln s!"{path}:{lineNo}: heap model count {hm.count} differs from {root.toList.length} entries"
        return { ok := false, ops, checks, queries }
    | "=" :: rest =>
      let expected := " ".intercalate rest
      let got := shape root
      if got == expected then
        checks := checks + 1
      else
        IO.eprintln s!"{path}:{lineNo}: shape mismatch after {ops} ops"
        IO.eprintln s!"  rust: {expected}"
        IO.eprintln s!"  lean: {got}"
        return { ok := false, ops, checks, queries }
      if heapShape hm != expected || !heapInvOK fuel hm then
        IO.eprintln s!"{path}:{lineNo}: heap model shape or invariant mismatch at the final shape"
        IO.eprintln s!"  heap: {heapShape hm}"
        return { ok := false, ops, checks, queries }
      -- Drop the tree: every node must be freed, none twice.
      match clearH fuel hm with
      | none =>
        IO.eprintln s!"{path}:{lineNo}: heap model faulted while dropping the tree"
        return { ok := false, ops, checks, queries }
      | some hm' =>
        if !hm'.heap.nodes.isEmpty then
          IO.eprintln s!"{path}:{lineNo}: {hm'.heap.nodes.size} nodes leaked after drop"
          return { ok := false, ops, checks, queries }
        hm := hm'
        root := .leaf []
    | [""] => pure ()
    | _ =>
      IO.eprintln s!"{path}:{lineNo}: unparsed line: {line}"
      return { ok := false, ops, checks, queries }
  return { ok := true, ops, checks, queries }

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: replay <trace>..."
    return 2
  let mut failed := false
  for path in args do
    let r ← replayFile path
    if r.ok then
      IO.println s!"{path}: OK ({r.ops} ops, {r.checks} checks, {r.queries} queries)"
    else
      failed := true
  return if failed then 1 else 0
