# lsys — inverse inference of D0L systems, formally

Given a word `w` and a step count `n`, find an L-system (axiom + context-free rewrite rules)
that derives `w` in exactly `n` steps. This repository contains an exact search for that
problem, the theorems around it, and a Lean 4 formalization of all of them, together with a
short paper whose statements are machine-aligned to the formalization.

Everything is checked in **Lean 4.15, core library only** (no Mathlib), with **no `sorry`**.

## What is proved

| Result | Lean name |
|---|---|
| The pruned search finds every bounded solution | `infer_complete` |
| Everything the search emits is a bounded solution (no side conditions) | `infer_sound` |
| Any word has a system (identity rules); one hidden symbol gives a 1-letter axiom | `exists_trivial`, `exists_hidden` |
| `n` distinct letters of `w` give a 1-letter axiom over `Σ(w)` alone | `chain_exists` |
| One-letter alphabet: `a^L` solvable at step `n` ⇔ `∃ m ≥ 2, m^n ∣ L` | `unary_iff` |
| Pigeonhole: fewer bounded systems than words ⇒ some word is underivable | `exists_underivable` |
| Incompressibility by total description size, via an encode/decode injection | `exists_incompressible` |
| Binary, non-erasing, short axiom: `|w| < T(n)` ⇒ an *insertion system* | `sharp_implies_insertion` |
| Insertion words are exactly those meeting a run-length criterion | `crit_of_insertion`, `insertion_of_crit` |
| `T(n) = min(F_{n+1}, D(n))` is attained for every `n ≥ 2` | `sharp_witness` |

Here an *insertion system* fixes one letter `x` and sends the other to `x^p (!x) x^q`;
`D(n) = 2·2^(n/2)` for even `n`, `3·2^(n/2)` for odd `n`; the Fibonacci iterate is the shortest
exception for `n ≤ 7` and `a^(2^k) b^(2^k)` for `n ≥ 8`.

What is *not* known: any structural description of the binary case for `|w| ≥ T(n)`, anything
for `|Σ| ≥ 3` with `n > |Σ|`, and the complexity of minimum-size inference. Two conjectures
(density of solvable words; bounded axiom length for non-insertion solutions) are stated in
`lsys/SUMMARY.md` and in the paper.

## Layout

```
lsys/
  LSys_*.lean        the formalization, one file per version (see below)
  lsys_infer.py      the search, mutable prototype
  lsys_pure.py       the same search as pure functions (what the Lean `search` transcribes)
  brute_check.py     property test: search == brute-force enumeration (random bounds, degenerate inputs)
  explore.py         data: which binary words are solvable for n = 3..6
  conj.py            tests the run-length criterion against exhaustive search
  rand_check.lean    in-Lean randomized check of `infer` against `sol`
  SUMMARY.md         results, open problems, conjectures
paper/
  paper.tex, paper.pdf       the paper (4 pages), tagged with PFA macros
  Paper.lean                 LSys.lean plus paper-facing statements (namespace Paper)
  align.sty                  the tag macros
  checker_output.txt, pfa.json, ALIGNMENT_REPORT.md   the alignment check and its report
```

Versions of the Lean file, in order: `LSys_1` … `LSys_5` (definitions, search, completeness),
`LSys_Alpha` (soundness), `LSys_Beta` (unary, chain, counting), `LSys_Gamma` (weak bound),
`LSys_Delta` (sharp bound), `LSys_Epsilon` (run criterion, sharpness for n ≤ 9),
`LSys_Zeta` (soundness without side conditions, sharpness for all n). The newest is the one
to read; older ones are kept as history.

## Building

Lean (any file is self-contained; no project needed):

```sh
lean lsys/LSys_Zeta.lean          # prints a few #eval sanity checks; no errors, no sorry
lean -o LSys.olean lsys/LSys_Zeta.lean && LEAN_PATH=. lean --run lsys/rand_check.lean
```

The last command compiles the file as module `LSys` and runs 150 random comparisons of the
search against the brute-force specification inside Lean (rename the `.olean` or adjust the
import if you keep the versioned filename).

Python (no dependencies):

```sh
python3 lsys/lsys_infer.py abaababaabaab 5     # finds a->ab, b->a, axiom a
python3 lsys/brute_check.py                     # ~600 random instances, expects 0 mismatches
```

Paper and alignment check (needs `pdflatex`, Lean, and
[PFA](https://github.com/SaxonRah/paper-formal-alignment)):

```sh
cd paper
python3 <pfa>/pfa/scripts/check_alignment.py paper.tex --lean Paper.lean --namespace LSys
pdflatex paper.tex
```

The checker asks Lean for the signature of every tagged statement and compares binder by
binder with the paper; the current files pass. Note `Paper.lean` is `LSys.lean` plus an
appended `namespace Paper` of statements with concrete alphabets and named hypotheses —
those are what the paper tags, so there are no implicit or instance binders to explain away.

## How the search works, in one paragraph

Build the derivation tree of `w` depth-first, leftmost-first. Rule bodies are invented one
symbol at a time and shared across all occurrences of the symbol, so a guess made anywhere
constrains the whole tree; leaves are matched against `w` as they are produced; a branch is
pruned when a lower bound on the leaves still owed exceeds what is left of `w`. Completeness
is proved by showing the search stays on the path of any given solution while a measure
decreases; soundness by inducting backwards from the emitted key and reading a system off the
final rule table. Both are up to `canon`, which forgets rules of symbols never rewritten.

## License

MIT.
