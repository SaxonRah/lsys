/-
Command-line front end for the verified search `LSys.infer`.

  lake exe lsys WORD N [--max-axiom A] [--max-rule R] [--empty] [--hidden H] [--json]

The alphabet is the sorted set of characters of WORD, plus H hidden symbols drawn from
`XYZUVW` (the same convention as `lsys/lsys_infer.py`). Solutions are printed in canonical
form (`canon`: rules of symbols never rewritten are dropped), one per line, sorted, so the
output is directly comparable with the Python search.
-/
import LSys
open LSys

structure Opts where
  word     : String := ""
  n        : Nat := 0
  maxAxiom : Nat := 3
  maxRule  : Nat := 4
  empty    : Bool := false
  hidden   : Nat := 0
  json     : Bool := false

def usage : String :=
  "usage: lsys WORD N [--max-axiom A] [--max-rule R] [--empty] [--hidden H] [--json]"

def num (v : String) : Except String Nat :=
  match v.toNat? with | some k => pure k | none => throw s!"not a number: {v}"

def parse (o : Opts) : List String → Except String Opts
  | [] => pure o
  | "--max-axiom" :: v :: r => do parse { o with maxAxiom := ← num v } r
  | "--max-rule" :: v :: r => do parse { o with maxRule := ← num v } r
  | "--hidden" :: v :: r => do parse { o with hidden := ← num v } r
  | "--empty" :: r => parse { o with empty := true } r
  | "--json" :: r => parse { o with json := true } r
  | s :: r =>
    if s.startsWith "--" then throw s!"unknown option {s}"
    else if o.word.isEmpty then parse { o with word := s } r
    else do parse { o with n := ← num s } r

def insertSorted (c : Char) : List Char → List Char
  | [] => [c]
  | d :: ds => if c < d then c :: d :: ds else if c = d then d :: ds else d :: insertSorted c ds

/-- Sorted set of characters of `w`. -/
def charsOf (w : String) : List Char := w.toList.foldl (fun acc c => insertSorted c acc) []

def alphabet (o : Opts) : List Char :=
  let base := charsOf o.word
  let hid := ("XYZUVW".toList.filter (· ∉ base)).take o.hidden
  base ++ hid

def encode (sigma : List Char) (s : String) : List Nat :=
  s.toList.map fun c => (sigma.findIdx? (· = c)).getD 0

def decode (sigma : List Char) (l : List Nat) : String :=
  String.mk (l.map fun i => sigma.getD i '?')

def showRules (sigma : List Char) (rs : List (Nat × List Nat)) : String :=
  ", ".intercalate (rs.map fun (a, b) =>
    s!"{decode sigma [a]}->{if b.isEmpty then "ε" else decode sigma b}")

def showJson (sigma : List Char) (P : Presented Nat) : String :=
  let rules := ", ".intercalate (P.2.map fun (a, b) =>
    s!"\"{decode sigma [a]}\": \"{decode sigma b}\"")
  "{\"axiom\": \"" ++ decode sigma P.1 ++ "\", \"rules\": {" ++ rules ++ "}}"

def showPlain (sigma : List Char) (P : Presented Nat) : String :=
  let size := P.1.length + (P.2.map fun r => r.2.length).sum
  s!"axiom={decode sigma P.1}  rules=[{showRules sigma P.2}]  size={size}"

def main (args : List String) : IO UInt32 := do
  match parse {} args with
  | .error e => IO.eprintln s!"{e}\n{usage}"; return 2
  | .ok o =>
    if o.word.isEmpty then IO.eprintln usage; return 2
    let sigma := alphabet o
    let sigmaN := List.range sigma.length
    let w := encode sigma o.word
    let B : Bounds := ⟨o.maxAxiom, o.maxRule, o.empty⟩
    let sols := infer sigmaN B w o.n
    -- canonical, sorted, duplicates dropped
    let cs := (sols.map (canon sigmaN o.n)).eraseDups
    let lines := cs.map (if o.json then showJson sigma else showPlain sigma)
    let lines := lines.mergeSort (· ≤ ·)
    if !o.json then IO.println s!"{lines.length} solutions"
    for l in lines do IO.println l
    return 0
