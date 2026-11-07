# lsys — inverse inference of D0L systems, formally

Given a word `w` and a step count `n`, find an L-system (axiom + context-free rewrite rules)
that derives `w` in exactly `n` steps. This repository contains an exact search for that
problem, the theorems around it, and a Lean 4 formalization of all of them, together with a
short paper whose statements are machine-aligned to the formalization.

Everything is checked in **Lean 4.36.0-rc2, core library only** (no Mathlib), with **no `sorry`**,
no deprecation warnings, and no axioms beyond `propext`/`Quot.sound`/`Classical.choice`
(`test/Axioms.lean` guards this). CI builds the project, runs the randomized and cross-language
checks, and re-runs the paper alignment on every push.

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
| Completeness with an explicit fuel bound (so a decided `infer … = []` is a refutation) | `infer_complete_fuel` |
| Exact optimum over insertion systems: max `p+q`, min axiom length and description size | `insertion_min_axiom`, `insertion_min_dsize`, `insP_pos_iff_crit` |
| Identity-free binary morphisms at least double every two steps | `identity_free_expansion` |
| Direct count of binary descriptions, `A(s)+1 = 2^s(s²+s+2)`; some word of length `L` needs size `> L − 2⌈log₂L⌉` | `descCount_closed`, `exists_incompressible_log` |
| The bounded-axiom conjecture (former Conjecture C) is **false**: `a^5 b^16` at `n=4` needs an axiom of length 6 > ⌊21/4⌋ | `conjC_false` |

Here an *insertion system* fixes one letter `x` and sends the other to `x^p (!x) x^q`;
`D(n) = 2·2^(n/2)` for even `n`, `3·2^(n/2)` for odd `n`; the Fibonacci iterate is the shortest
exception for `n ≤ 7` and `a^(2^k) b^(2^k)` for `n ≥ 8`.

What is *not* known: any structural description of the binary case for `|w| ≥ T(n)`, anything
for `|Σ| ≥ 3` with `n > |Σ|`, and the complexity of minimum-size inference. One conjecture
(density of solvable words) is stated in `lsys/SUMMARY.md` and in the paper; a second
(bounded axiom length for non-insertion solutions) is refuted there.

## Layout

```
lakefile.toml, lean-toolchain   Lake project, pinned to leanprover/lean4:v4.36.0-rc2
LSys.lean            the formalization: definitions, search, completeness, soundness, all theorems
LSys/Bounds.lean     further bounds: explicit-fuel completeness, insertion optimizer,
                     identity-free expansion, direct counting, refutation of the axiom conjecture
Main.lean            `lake exe lsys` — command-line front end for the verified search
paper/
  paper.tex, paper.pdf       the paper (6 pages), tagged with PFA macros
  Paper.lean                 `import LSys` + paper-facing statements (namespace Paper)
  align.sty                  the tag macros
  checker_output.txt, pfa.json, ALIGNMENT_REPORT.md   the alignment check and its report
test/
  RandCheck.lean     in-Lean randomized check of `infer` against `sol`
  Axioms.lean        `#print axioms` guards for the headline theorems
  instances.json     the fixed instance set for the Python-vs-Lean cross-check
lsys/
  lsys_infer.py      the search, mutable prototype
  lsys_pure.py       the same search as pure functions (what the Lean `search` transcribes)
  brute_check.py     property test: search == brute-force enumeration
  crosscheck.py      Python search == Lean search on test/instances.json
  explore.py, conj.py   data: solvable binary words for n = 3..6; the run-length criterion vs search
  SUMMARY.md         results, open problems, conjectures
  history/           LSys_1 … LSys_Epsilon, the earlier versions (Lean 4.15; not built)
.github/workflows/ci.yml
```

The earlier Lean files, in order: `LSys_1` … `LSys_5` (definitions, search, completeness),
`LSys_Alpha` (soundness), `LSys_Beta` (unary, chain, counting), `LSys_Gamma` (weak bound),
`LSys_Delta` (sharp bound), `LSys_Epsilon` (run criterion, sharpness for n ≤ 9). `LSys.lean`
is the former `LSys_Zeta` (soundness without side conditions, sharpness for all n), ported to
4.36.

## Building

With [elan](https://github.com/leanprover/elan) installed, the toolchain is picked up from
`lean-toolchain`:

```sh
lake build                                       # LSys, LSys.Bounds, Paper, and the lsys exe
lake env lean test/Axioms.lean                   # headline theorems use only the standard axioms
lake env lean --run test/RandCheck.lean          # 150 random comparisons of infer vs sol, in Lean
lake exe lsys abaababaabaab 5                    # finds a->ab, b->a, axiom a
lake exe lsys aaaaabbbbbbbbbbbbbbbb 4 --max-axiom 6 --max-rule 21   # the Conjecture C witness
```

Python (no dependencies):

```sh
python3 lsys/lsys_infer.py abaababaabaab 5     # same search, in Python
python3 lsys/brute_check.py                     # ~600 random instances vs brute force, expects 0 mismatches
python3 lsys/crosscheck.py                      # 200 fixed instances, Python vs `lake exe lsys`, expects 0 mismatches
```

Paper and alignment check (needs `pdflatex` and
[PFA](https://github.com/SaxonRah/paper-formal-alignment)):

```sh
cd paper
python3 <pfa>/pfa/scripts/check_alignment.py paper.tex --lean Paper.lean --namespace LSys --lake-project .. --json pfa.json
pdflatex paper.tex && pdflatex paper.tex
```

The checker asks Lean for the signature of every tagged statement and compares binder by
binder with the paper; the current files pass (30 tagged statements). `Paper.lean` imports
`LSys` and appends a `namespace Paper` of statements with concrete alphabets and named
hypotheses — those are what the paper tags, so there are no implicit or instance binders to
explain away.

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
