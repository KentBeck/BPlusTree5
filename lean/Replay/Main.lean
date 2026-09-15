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
    # <fnv1a-64 of the shape, 16 hex digits>
    = <shape>

The value fields are what the Rust call returned; the model's return
value must agree.

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

structure Outcome where
  ok : Bool
  ops : Nat
  checks : Nat

def replayFile (path : System.FilePath) : IO Outcome := do
  let content ← IO.FS.readFile path
  let mut root : Node Int Int := .leaf []
  let mut lc := 0
  let mut bc := 0
  let mut ops := 0
  let mut checks := 0
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
        return { ok := false, ops, checks }
    | ["R", k, res] =>
      let got := removeTree lc bc root k.toInt!
      ops := ops + 1
      match got with
      | some (v, root') =>
        root := root'
        if toString v != res then
          IO.eprintln s!"{path}:{lineNo}: remove {k} returned {v} in the model, {res} in Rust"
          return { ok := false, ops, checks }
      | none =>
        if res != "-" then
          IO.eprintln s!"{path}:{lineNo}: remove {k} found nothing in the model, {res} in Rust"
          return { ok := false, ops, checks }
    | ["#", expected] =>
      let got := hex16 (fnv1a (shape root))
      if got == expected then
        checks := checks + 1
      else
        IO.eprintln s!"{path}:{lineNo}: shape digest mismatch after {ops} ops (rust {expected}, lean {got})"
        IO.eprintln s!"  lean shape: {shape root}"
        return { ok := false, ops, checks }
    | "=" :: rest =>
      let expected := " ".intercalate rest
      let got := shape root
      if got == expected then
        checks := checks + 1
      else
        IO.eprintln s!"{path}:{lineNo}: shape mismatch after {ops} ops"
        IO.eprintln s!"  rust: {expected}"
        IO.eprintln s!"  lean: {got}"
        return { ok := false, ops, checks }
    | [""] => pure ()
    | _ =>
      IO.eprintln s!"{path}:{lineNo}: unparsed line: {line}"
      return { ok := false, ops, checks }
  return { ok := true, ops, checks }

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: replay <trace>..."
    return 2
  let mut failed := false
  for path in args do
    let r ← replayFile path
    if r.ok then
      IO.println s!"{path}: OK ({r.ops} ops, {r.checks} checks)"
    else
      failed := true
  return if failed then 1 else 0
