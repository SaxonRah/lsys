/-
Paper-facing statements for paper/paper.tex: concrete alphabets (`Nat`, `Unit`, `Bool`), every
hypothesis a named explicit binder. Each is proved by appeal to the corresponding `LSys`
theorem. These are the statements that the PFA tags in paper.tex refer to.
-/
import LSys
import LSys.Bounds

namespace Paper
open LSys

/-- The Fibonacci system `0 ↦ 01, 1 ↦ 0` over `Nat`, axiom `0`. -/
def fibN : DOL Nat := ⟨[0], fun a => if a = 0 then [0, 1] else [0]⟩

/-- Definition test (§1): five steps of `fibN`. -/
theorem fib_word : fibN.derive 5 = [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] := by decide

/-- Theorem 1 (trivial existence). -/
theorem exists_trivial (w : List Nat) (n : Nat) : ∃ S : DOL Nat, S.derive n = w :=
  LSys.exists_trivial w n

/-- Theorem 2 (one hidden symbol). -/
theorem exists_hidden (w : List Nat) (n : Nat) (h_pos : 1 ≤ n) :
    ∃ S : DOL (Option Nat), S.start.length = 1 ∧ S.derive n = w.map some :=
  LSys.exists_hidden w n h_pos

/-- Theorem 3 (chain). -/
theorem chain_exists (w cs : List Nat) (n : Nat) (h_pos : 1 ≤ n) (h_len : cs.length = n)
    (h_nodup : cs.Nodup) (h_sub : ∀ c ∈ cs, c ∈ w) :
    ∃ S : DOL Nat, S.start.length = 1 ∧ S.derive n = w ∧
      (∀ a ∈ S.start, a ∈ w) ∧ (∀ a, a ∉ w → S.rule a = [a]) :=
  LSys.chain_exists w n h_pos cs h_len h_nodup h_sub

/-- Theorem 4 (completeness of the search). -/
theorem infer_complete (sigma : List Nat) (B : Bounds) (w : List Nat) (n : Nat)
    (P : Presented Nat) (h_sol : P ∈ sol sigma B w n) :
    ∃ fuel, ∃ Q ∈ infer sigma B w n fuel, canon sigma n Q = canon sigma n P :=
  LSys.infer_complete sigma B w n P h_sol

/-- Theorem 5 (soundness of the search). -/
theorem infer_sound (sigma : List Nat) (B : Bounds) (w : List Nat) (n : Nat)
    (fuel : Nat) (Q : Presented Nat) (h_inf : Q ∈ infer sigma B w n fuel) :
    ∃ P ∈ sol sigma B w n, canon sigma n Q = canon sigma n P :=
  LSys.infer_sound sigma B w n fuel Q h_inf

/-- Theorem 6 (unary characterization). -/
theorem unary_iff (L n : Nat) (h_L : 1 ≤ L) (h_n : 1 ≤ n) :
    (∃ S : DOL Unit, S.start.length < L ∧ S.derive n = List.replicate L ())
      ↔ ∃ m, 2 ≤ m ∧ m ^ n ∣ L :=
  LSys.unary_iff L n h_L h_n

/-- Theorem 7 (counting, per-rule caps). -/
theorem exists_underivable (sigma : List Nat) (h_nodup : sigma.Nodup) (B : Bounds) (n L : Nat)
    (h_count : (allSystems sigma B).length < sigma.length ^ L) :
    ∃ w ∈ words sigma L, sol sigma B w n = [] :=
  LSys.exists_underivable sigma h_nodup B n L h_count

/-- Theorem 8 (incompressibility by description size). -/
theorem exists_incompressible (sigma : List Nat) (h_nodup : sigma.Nodup) (n L s : Nat)
    (h_count : (sigma.length + 1) ^ (s + sigma.length + 1) < sigma.length ^ L) :
    ∃ w ∈ words sigma L, ∀ S : DOL Nat,
      (∀ x ∈ S.start, x ∈ sigma) → (∀ a ∈ sigma, ∀ x ∈ S.rule a, x ∈ sigma) →
      (∀ a, a ∉ sigma → S.rule a = [a]) → dsize sigma S ≤ s → S.derive n ≠ w :=
  LSys.exists_incompressible sigma h_nodup n L s h_count

/-- Definition test (§4): the threshold `T(n)` for `n = 0..9`. -/
theorem sharpT_values : (List.range 10).map sharpT = [1, 1, 2, 3, 5, 8, 13, 21, 32, 48] := by
  decide

/-- Theorem 9 (sharp bound). -/
theorem sharp_implies_insertion (S : DOL Bool) (n : Nat) (w : List Bool)
    (h_ne : ∀ a, S.rule a ≠ []) (h_der : S.derive n = w) (h_short : S.start.length < w.length)
    (h_both : ∀ c, c ∈ w) (h_small : w.length < sharpT n) :
    ∃ x p q, S.rule x = [x] ∧ S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x ∧
      1 ≤ p + q :=
  LSys.sharp_implies_insertion S n w h_ne h_der h_short h_both h_small

/-- Theorem 9, non-vacuity: the hypotheses can all hold. -/
theorem sharp_implies_insertion_nonvacuous :
    ∃ (S : DOL Bool) (n : Nat) (w : List Bool), (∀ a, S.rule a ≠ []) ∧ S.derive n = w ∧
      S.start.length < w.length ∧ (∀ c, c ∈ w) ∧ w.length < sharpT n :=
  ⟨⟨[true], fun c => if c then [false, true] else [false]⟩, 5,
   [false, false, false, false, false, true], by decide, by decide, by decide, by decide, by decide⟩

/-- Theorem 10 (insertion words meet the run-length criterion). -/
theorem crit_of_insertion (S : DOL Bool) (x : Bool) (p q n : Nat) (w : List Bool)
    (h_fix : S.rule x = [x])
    (h_ins : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x)
    (h_pq : 1 ≤ p + q) (h_der : S.derive n = w) (h_mem : (!x) ∈ w) : Crit n x w :=
  LSys.crit_of_insertion S x p q n h_fix h_ins h_pq w h_der h_mem

/-- Theorem 11 (words meeting the criterion are insertion words). -/
theorem insertion_of_crit (n : Nat) (x : Bool) (w : List Bool) (h_n : 1 ≤ n)
    (h_crit : Crit n x w) (h_head : n ≤ (runs x w).headD 0) :
    ∃ S : DOL Bool, S.rule x = [x] ∧ S.start.length < w.length ∧ S.derive n = w :=
  LSys.insertion_of_crit n h_n x w h_crit h_head

/-- Theorem 12 (sharpness for every n). -/
theorem sharp_witness (n : Nat) (h_n : 2 ≤ n) :
    ∃ (S : DOL Bool) (w : List Bool), (∀ a, S.rule a ≠ []) ∧ S.derive n = w ∧
      S.start.length < w.length ∧ (∀ c, c ∈ w) ∧ w.length = sharpT n ∧
      ¬ Crit n false w ∧ ¬ Crit n true w :=
  LSys.sharp_witness n h_n


/-! ### Further bounds (paper §6) -/

/-- Theorem 23 (direct description count): `A(s) + 1 = 2^s (s² + s + 2)`. -/
theorem descCount_closed (s : Nat) : descCount s + 1 = 2 ^ s * (s * s + s + 1 + 1) :=
  LSys.descCount_closed s

/-- Theorem 24 (incompressibility on the `L − 2 log₂ L` scale). -/
theorem exists_incompressible_log (n L k s : Nat) (h_k : 1 ≤ k) (h_L : L ≤ 2 ^ k)
    (h_s : s + 2 * k ≤ L) :
    ∃ w ∈ words [false, true] L, ∀ S : DOL Bool, dsize [false, true] S ≤ s → S.derive n ≠ w :=
  LSys.exists_incompressible_log n L k s h_k h_L h_s

/-- Theorem 25 (exact insertion optimum). -/
theorem insertion_optimum (n : Nat) (x : Bool) (w : List Bool) (h_n : 1 ≤ n) (h_mem : (!x) ∈ w) :
    (optSys n x w).rule x = [x] ∧
    (optSys n x w).rule (!x) = List.replicate (optP n x w) x ++ (!x) :: List.replicate (optQ n x w) x ∧
    optP n x w + optQ n x w = insP n x w ∧
    (optSys n x w).derive n = w ∧
    (optSys n x w).start.length + n * w.count (!x) * insP n x w = w.length ∧
    ∀ (S : DOL Bool) (p q : Nat), S.rule x = [x] →
      S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x → S.derive n = w →
      p + q ≤ insP n x w ∧ (optSys n x w).start.length ≤ S.start.length :=
  ⟨optSys_rule_x n x w, optSys_rule_y n x w, optP_add_optQ n x w, optSys_derive n h_n x w h_mem,
   (insertion_min_axiom n h_n x w h_mem).1,
   fun S p q hx hy hw => ⟨insertion_pq_le S x p q n h_n hx hy w hw h_mem,
     (insertion_min_axiom n h_n x w h_mem).2 S p q hx hy hw⟩⟩

/-- Theorem 26, description size: `optSys` minimizes `|ω| + |f(x)| + |f(x̄)|` too. -/
theorem insertion_optimum_dsize (n : Nat) (x : Bool) (w : List Bool) (h_n : 1 ≤ n)
    (h_mem : (!x) ∈ w) :
    dsize [x, !x] (optSys n x w) + (n * w.count (!x) - 1) * insP n x w = w.length + 2 ∧
    ∀ (S : DOL Bool) (p q : Nat), S.rule x = [x] →
      S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x → S.derive n = w →
      dsize [x, !x] (optSys n x w) ≤ dsize [x, !x] S :=
  insertion_min_dsize n h_n x w h_mem

/-- Theorem 27, solvability: `insP ≥ 1` is the run-length criterion. -/
theorem insP_pos_iff_crit (n : Nat) (x : Bool) (w : List Bool) (h_n : 1 ≤ n) (h_mem : (!x) ∈ w) :
    1 ≤ insP n x w ↔ Crit n x w :=
  LSys.insP_pos_iff_crit n h_n x w h_mem

/-- Theorem 28 (identity-free expansion). -/
theorem identity_free_expansion (S : DOL Bool) (n : Nat) (h_ne : ∀ a, S.rule a ≠ [])
    (h_id : ∀ a, S.rule a ≠ [a]) (h_big : ∃ a, 2 ≤ (S.rule a).length) :
    2 ^ (n / 2) * S.start.length ≤ (S.derive n).length :=
  LSys.identity_free_expansion S h_ne h_id h_big n

/-- Proposition 29 (the bounded-axiom conjecture fails): the witness. -/
theorem conjC_witness :
    ∃ S : DOL Bool, (∀ a, S.rule a ≠ []) ∧ S.derive 4 = cexW ∧ S.start.length = 6 ∧
      cexW.length = 21 ∧ ¬ Crit 4 false cexW ∧ ¬ Crit 4 true cexW :=
  ⟨cexS, cexS_nonerasing, cexS_derive, by decide, cexW_length, cexW_not_crit.1, cexW_not_crit.2⟩

/-- Proposition 30: no solution has an axiom of length `≤ 5 = ⌊21 / 2^(4/2)⌋`. -/
theorem conjC_false (S : DOL Bool) (h_ne : ∀ a, S.rule a ≠ []) (h_der : S.derive 4 = cexW) :
    6 ≤ S.start.length :=
  LSys.conjC_false S h_ne h_der

end Paper
