# Alignment report: Inverse Inference of D0L Systems

**Verdict:** ALIGNED
The PFA checker returns `Result: PASS` on the final `paper.tex` against `Paper.lean`; every
definition, theorem, proposition and example in the paper is tagged; no dependency on `sorry`
or non-standard axioms.

## Substantive mismatches
None.

## Coverage
Paper items not formalized: the two conjectures in §6 (stated as `conjecture*`, untagged by
design: they are open problems, not theorems).

Formal declarations with no paper counterpart: everything in the `LSys` namespace other than
the tagged definitions (`DOL`, `DOL.derive`, `sol`, `infer`, `canon`, `sharpT`, `Crit`). These are
the general-alphabet versions of the paper's theorems and the auxiliary lemmas; each paper-facing
theorem in `Paper` is proved by direct appeal to its `LSys` counterpart, so the paper statements
are instances of the general ones (alphabet `Nat`, `Unit` or `Bool`).

## Readings that needed judgment
- "alphabet": a `List` of symbols, possibly with repetitions except where `List.Nodup` is stated.
- "$w$ containing both letters" (binary section): read as `forall c, c ∈ w` over `Bool`.
- "non-erasing": `forall a, S.rule a ≠ []`.
- "axiom shorter than $w$": `S.start.length < w.length`.
- Standing assumptions of §5 (binary, non-erasing, short axiom, both letters) are restated as
  explicit hypotheses in each theorem rather than as untagged standing text.
- The soundness theorem's three side hypotheses (`w ⊆ Σ`, `w ≠ []`, `maxRule ≥ 1`) are stated in
  the paper; they are not artifacts of the formalization but genuine conditions.

## Equivalence lemmas added
None needed: every difference between a reading and the formal text (implicit binder types,
`List.Nodup l` vs `l.Nodup`, `∉` vs `¬ ∈`, `∃ x p q` vs nested `∃`) was closed by the checker's
built-in tactics (`Iff.rfl`).

## Definition tests and non-vacuity
- `Paper.fib_word`: five steps of the Fibonacci system over `Nat` (tests `DOL.derive`).
- `Paper.sharpT_values`: `T(0..9) = 1,1,2,3,5,8,13,21,32,48` (tests `sharpT`).
- `Paper.sharp_implies_insertion_nonvacuous`: the hypotheses of the sharp bound hold for
  `b ↦ ab, a ↦ a`, axiom `b`, `n = 5`, `w = a⁵b`.
- `Paper.sharp_witness_fib`, `Paper.sharp_witness_dbl`: decided in Lean; they also test `Crit`.

## Independence
The paper and the formalization were written by the same author in the same session, with
the formal statements in context. The readings therefore cannot claim independence from the
formal text; what the check certifies is that the paper's displayed statements and the formal
signatures agree binder by binder.

## For the human reviewer
Definitions to read once: `LSys.DOL`, `LSys.DOL.derive`, `LSys.Bounds`, `LSys.Presented`,
`LSys.allSystems`, `LSys.sol`, `LSys.infer`, `LSys.canon`, `LSys.dsize`, `LSys.sharpT`,
`LSys.runs`, `LSys.Crit`, `LSys.fibS`, `LSys.dblS`, `Paper.fibN`.
The checker's review table is in `checker_output.txt`.
