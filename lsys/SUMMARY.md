# Inverse L-system inference — results

All theorems are machine-checked in `LSys.lean` and `LSys/Bounds.lean` (Lean 4.36.0-rc2, core library only, no `sorry`).
Python prototypes: `lsys_infer.py` (mutable search), `lsys_pure.py` (pure transcription),
`brute_check.py` (property test against brute force), `crosscheck.py` (Python vs the Lean exe),
`explore.py` / `conj.py` (data: solvable words; the run-length criterion vs search).

## The problem
Given a word `w` and a step count `n`, find a D0L system (axiom + context-free rewrite rules)
with `derive n = w`.  The set of solutions under size bounds `B` is `sol sigma B w n`
(a filter of a finite enumeration); `infer` is the pruned search.

## Master theorem (proved, both directions)
* `infer_complete` — every bounded solution is emitted by the search.
* `infer_sound`    — every emitted key is a bounded solution, with no side conditions.
  (An earlier version needed `w ⊆ sigma`, `w ≠ []`, `maxRule ≥ 1`; the search was tightened instead.)
* `infer_complete_fuel` — completeness with the fuel made explicit: any fuel above the initial
  measure, which is bounded by `3n|w| + |w| + dsize + 2` (`measure_init_le`). So a kernel-decided
  `infer sigma B w n 10^6 = []` refutes the existence of any bounded solution.
Both up to `canon` (rules of never-rewritten symbols are irrelevant).

## Existence
* `exists_trivial`  — identity system, any `n`.
* `exists_hidden`   — one hidden symbol gives a length-1 axiom, any `n ≥ 1`.
* `chain_exists`    — `n ≤ |Σ(w)|` ⇒ a length-1 axiom over `Σ(w)` alone.

## Impossibility / counting
* `impossible_singleton`  — one-letter alphabet, growing rule, nonempty axiom: never `[a]`.
* `unary_iff`             — `a^L` has a shorter-axiom system at step `n` ⇔ `∃ m ≥ 2, m^n ∣ L`.
* `exists_underivable`    — fewer bounded systems than `|Σ|^L` words ⇒ some word of length `L`
  has no bounded system at any step (`underivable_binary_8`: 216 < 256, decided in Lean).
* `exists_incompressible` — same by total description size: `(k+1)^(s+k+1) < k^L` ⇒ some word
  of length `L` needs size `> s` (encode/decode injection into words over `Σ ∪ {#}`).
* `descCount_closed`, `exists_incompressible_binary`, `exists_incompressible_log` — binary
  descriptions of size `≤ s` counted directly: `A(s) = Σ_{t≤s} 2^t·C(t+2,2) = 2^s(s²+s+2) − 1`;
  `A(s) < 2^L` ⇒ some word of length `L` needs size `> s`. With `L ≤ 2^k`, `k ≥ 1`, this holds for
  every `s ≤ L − 2k`, i.e. the worst-case minimum size is `≥ L − 2⌈log₂L⌉` against the trivial
  `L + 2` (vs. `≈ 0.63 L` from `exists_incompressible`). Instance: length 64 needs size > 52.

## The regime `n > |Σ| = 2` (binary, non-erasing, axiom shorter than `w`, `w` uses both letters)
Let `T(n) = min(F_{n+1}, D(n))`, `D(n) = 2·2^(n/2)` (n even), `3·2^(n/2)` (n odd):
`T = 2,3,5,8,13,21,32,48` for `n = 2..9`.
* `small_implies_insertion`, `sharp_implies_insertion` — `|w| < T(n)` ⇒ the system is an
  *insertion system*: one letter fixed, the other ↦ `x^p (!x) x^q`, `p+q ≥ 1`.
* `crit_of_insertion`, `insertion_of_crit` — insertion words are exactly the words whose
  inner `x`-runs all have length ≥ n and whose leading or trailing `x`-run has length ≥ n.
* `sharp_witness` — `T(n)` is attained for every `n ≥ 2`: the Fibonacci word `f^n(b)` (`a→ab, b→a`)
  for `n ≤ 7` and `a^(2^k) b^(2^k)` (`a→b, b→aa`, axiom `ab`) for `n ≥ 8` are solvable and fail the criterion.

* `insertion_pq_le`, `optSys_derive`, `insertion_min_axiom`, `insertion_min_dsize`,
  `insP_pos_iff_crit` — **exact optimizer** over insertion systems fixing `x`: with runs
  `r₀,…,rₘ` and `insP = min(⌊r₀/n⌋+⌊rₘ/n⌋, min_inner ⌊rᵢ/n⌋)`, the maximum `p+q` is exactly
  `insP`, attained by `optSys`; minimum axiom length `|w| − n·m·insP`, minimum description size
  `|w| + 2 − (nm−1)·insP`; and `insP ≥ 1 ↔ Crit`. Below `T(n)` this is the global optimum over
  both orientations.

So below `T(n)` the binary problem is completely characterized, including its optimum.

## Open region: `|w| ≥ T(n)`, `n ≥ 3`
Solvability is decidable (`infer`), but no structural characterization is known.  Observed
families: insertion; Fibonacci-type (`a→ab,b→a` and relatives, growth `φ^n`); doubling
(`a→b, b→aa`, growth `√2^n`); and mixtures with longer axioms (e.g. `aaaabbbbaaaa` at `n=4`
from `a→bb, b→a`, axiom `aba`).

* `identity_free_expansion` — if neither letter is fixed and some rule has length ≥ 2, then
  `2^⌊n/2⌋·|ω| ≤ |f^n(ω)|` (so `|ω| ≤ ⌊|w| / 2^⌊n/2⌋⌋`). The long-rule hypothesis is needed
  (`a→b, b→a` only swaps); the exponent is `⌊n/2⌋`, not `n/2`, for odd `n` (`a→b, b→aa`).

**Conjecture B (asymptotic density).** For fixed `n ≥ 3`, let `N_n(L)` be the number of binary
words of length `L` with a non-erasing shorter-axiom system at step `n`.  Then
`N_n(L)^(1/L) → ρ_n`, the dominant root of `x^(n+1) = x^n + 1` (the growth rate of the insertion
family, i.e. of compositions with inner parts ≥ n).  Equivalently: the non-insertion solvable
words have exponentially smaller density. What is proved: every identity-free family expands its
axiom by `≥ 2^⌊n/2⌋` (`identity_free_expansion`) and so has growth rate at most
`2^(2^(−⌊n/2⌋))`. What is not: the fixed-letter non-insertion families (see below) and the union
over rule pairs, which vary with `L`, need a separate counting argument.

**Conjecture C (bounded axiom for non-insertion solutions) — FALSE.** It claimed every
non-insertion solution has an equivalent solution with axiom length `≤ L / 2^(n/2)`.
Counterexample (`conjC_false`, `conjC_witness`, kernel-checked): `n = 4`, `w = a^5 b^16`,
`L = 21`, system `a→a, b→bb`, axiom `a^5 b` of length 6 — non-insertion, `w` fails `Crit` in both
orientations — while `L / 2^(n/2) = 5.25`. No non-erasing solution has an axiom of length ≤ 5:
rules of never-rewritten letters can be made identities, rewritten letters have rules no longer
than `w`, so any such solution would be in `sol [a,b] ⟨5, 21, false⟩`; by `infer_complete_fuel`
the search would emit it, and `decide` evaluates the search to `[]`. A smaller odd-step instance:
`n = 3`, `a^3 b^8`, axiom `aaab` (length 4 > ⌊11/2^1.5⌋ = 3). The family `a^k b^(2^n)` with axiom
`a^k b` violates the bound exactly when `k > 2^(n/2)`: a fixed letter is carried through
unexpanded, which is precisely the case `identity_free_expansion` excludes.

Note: the earlier "evidence" for C (`conj.py`, `n = 3..6`, `L ≤ 15`) tested the run-length
criterion against solvability, not C; the `n = 3` counterexample has `L = 11`, inside that range.
