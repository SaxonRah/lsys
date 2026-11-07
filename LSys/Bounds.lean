/-
Further bounds on top of `LSys`:

* `infer_complete_fuel` — completeness with an explicit fuel bound, so that a decided
  `infer … = []` refutes the existence of any bounded solution;
* `identity_free_expansion` — if neither letter is fixed and some rule is long, every
  two steps at least double the length (the sound form of the expansion heuristic);
* `conjC_false` — Conjecture C of `SUMMARY.md` is false: `a^5 b^16` at `n = 4` has a
  non-erasing shorter-axiom solution (axiom `a^5 b`) but none with axiom length ≤ 5;
* `insertion_max`, `insertion_optimal_*` — exact optimizer for insertion systems;
* `descCount`, `exists_incompressible'` — incompressibility by direct description counting.

Lean 4.36.0-rc2, core only, no `sorry`.
-/
import LSys

namespace LSys
variable {α : Type}

/-! ### Completeness with explicit fuel -/

theorem length_derive_le_of_le (S : DOL α) (hne : ∀ a, S.rule a ≠ []) {k j : Nat} (hkj : k ≤ j) :
    (S.derive k).length ≤ (S.derive j).length := by
  induction j with
  | zero => have : k = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hkj with h | rfl
    · exact Nat.le_trans (ih (by omega)) (length_derive_mono S hne j)
    · exact Nat.le_refl _

theorem length_stackPend_init (S : DOL α) (hne : ∀ a, S.rule a ≠ []) (n : Nat) :
    (stackPend (lift S) n [(none, 0, 0)]).length ≤ n * (S.derive n).length := by
  simp only [stackPend, framePend, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.sub_zero, List.drop_zero]
  show ((List.range n).flatMap fun j => (lift S).iter j (S.start.map some)).length ≤ _
  have h : ∀ j ∈ List.range n, ((lift S).iter j (S.start.map some)).length ≤ (S.derive n).length := by
    intro j hj
    rw [iter_lift_map, List.length_map, ← derive_eq_iter]
    exact length_derive_le_of_le S hne (Nat.le_of_lt (List.mem_range.mp hj))
  have key : ∀ (l : List Nat) (f : Nat → List (Option α)) (c : Nat),
      (∀ j ∈ l, (f j).length ≤ c) → (l.flatMap f).length ≤ l.length * c := by
    intro l f c hc
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := hc a List.mem_cons_self
      have := ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
      rw [Nat.succ_mul]; omega
  have := key (List.range n) _ _ h
  simpa using this

theorem length_stackLeaves_init (S : DOL α) (n : Nat) :
    (stackLeaves (lift S) n [(none, 0, 0)]).length = (S.derive n).length := by
  simp only [stackLeaves, frameLeaves, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.sub_zero, List.drop_zero]
  show ((lift S).iter n (S.start.map some)).length = _
  rw [iter_lift_map, List.length_map, ← derive_eq_iter]

theorem slack_init [DecidableEq α] (sigma : List α) (S : DOL α) :
    slack sigma (lift S) [] = dsize sigma S := by
  simp only [slack, allSyms, dsize, List.map_cons, List.sum_cons, List.map_map]
  have : ∀ x : Option α, (lookupR ([] : Rules α) x).1.length = 0 := fun x => rfl
  simp only [this, Nat.sub_zero]
  show (S.start.map some).length + _ = _
  rw [List.length_map]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  show ((S.rule a).map some).length = (S.rule a).length
  exact List.length_map _

/-- The measure of the initial search state, bounded by the data of the instance. -/
theorem measure_init_le [DecidableEq α] (sigma : List α) (S : DOL α) (hne : ∀ a, S.rule a ≠ [])
    (n : Nat) :
    measure sigma n (lift S) ⟨[], [(none, 0, 0)], 0⟩ ≤
      3 * (n * (S.derive n).length) + 2 + (S.derive n).length + dsize sigma S := by
  simp only [measure, List.length_cons, List.length_nil]
  have h1 := length_stackPend_init S hne n
  have h2 := length_stackLeaves_init S n
  have h3 := slack_init sigma S
  omega

/-- `infer_complete` with the fuel made explicit: any fuel above the initial measure works. -/
theorem infer_complete_fuel [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat)
    (P : Presented α) (hP : P ∈ sol sigma B w n) (fuel : Nat)
    (hfuel : measure sigma n (lift P.toDOL) ⟨[], [(none, 0, 0)], 0⟩ < fuel) :
    ∃ Q ∈ infer sigma B w n fuel, canon sigma n Q = canon sigma n P := by
  have hA : P ∈ allSystems sigma B := (List.mem_filter.mp hP).1
  have hw : P.toDOL.derive n = w := sol_sound sigma B w n P hP
  have hB := bounded_of_mem_allSystems sigma B P hA
  have hT := tok_of_bounded sigma B P.toDOL hB
  have h0 := initial_onPath w n P.toDOL hw
  refine ⟨expectedKey sigma B n (lift P.toDOL), ?_, canon_expectedKey sigma B n P hB⟩
  have hguard : (if B.allowEmpty then 0 else 1) ≤ B.maxRule := by
    cases hs : sigma with
    | nil =>
      exfalso
      have := hB.start_len_lo
      have hm := hB.start_mem
      rw [hs] at hm
      cases hst : P.toDOL.start with
      | nil => rw [hst] at this; simp at this
      | cons c _ => exact absurd (hm c (by rw [hst]; exact List.mem_cons_self)) (by simp)
    | cons a rest =>
      have h1 := hB.rule_len_lo a (by rw [hs]; exact List.mem_cons_self)
      have h2 := hB.rule_len_hi a (by rw [hs]; exact List.mem_cons_self)
      omega
  unfold infer
  rw [ite_eq_left hguard]
  exact search_complete w n sigma B (lift P.toDOL) hT _ _ h0 hfuel

/-! ### Membership in `sol` from a plain system

Any non-erasing system over a nodup alphabet deriving `w` can be trimmed (identity rules on
never-rewritten symbols) to a bounded presentation in `sol`, with `maxRule = |w|`. -/

theorem length_rule_le_step (S : DOL α) (s : List α) (a : α) (ha : a ∈ s) :
    (S.rule a).length ≤ (S.step s).length := by
  induction s with
  | nil => simp at ha
  | cons c s ih =>
    rw [step_cons, List.length_append]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

theorem length_rule_le_of_used [DecidableEq α] (S : DOL α) (hne : ∀ a, S.rule a ≠ []) (n : Nat) (a : α)
    (ha : a ∈ usedSymbols S n) : (S.rule a).length ≤ (S.derive n).length := by
  induction n with
  | zero => simp [usedSymbols] at ha
  | succ n ih =>
    simp only [usedSymbols, List.mem_append] at ha
    rcases ha with h | h
    · exact Nat.le_trans (length_rule_le_step S _ a h) (Nat.le_refl _)
    · exact Nat.le_trans (ih h) (length_derive_mono S hne n)

/-- The trimmed system: identity on symbols never rewritten. -/
def trim [DecidableEq α] (S : DOL α) (n : Nat) : DOL α :=
  ⟨S.start, fun a => if a ∈ usedSymbols S n then S.rule a else [a]⟩

theorem trim_derive [DecidableEq α] (S : DOL α) (n : Nat) : (trim S n).derive n = S.derive n :=
  derive_eq_of_agree S (trim S n) n rfl
    (fun a ha => by simp [trim, ha]) n (Nat.le_refl _)

/-- A presentation listing every symbol of a covering alphabet is the system it names. -/
theorem toDOL_map_pair [DecidableEq α] (sigma : List α) (hmem : ∀ a, a ∈ sigma) (ax : List α)
    (f : α → List α) : Presented.toDOL (ax, sigma.map fun a => (a, f a)) = ⟨ax, f⟩ := by
  refine DOL.ext' _ _ rfl ?_
  intro a
  show (match (sigma.map fun a => (a, f a)).lookup a with | some r => r | none => [a]) = f a
  rw [lookup_map_pair, ite_eq_left (hmem a)]

/-- Every non-erasing system deriving `w` over `sigma` yields a member of `sol` with
`maxAxiom = |start|`, `maxRule = |w|`. -/
theorem mem_sol_of_system [DecidableEq α] (sigma : List α) (S : DOL α) (n : Nat) (w : List α)
    (hne : ∀ a, S.rule a ≠ []) (hw : S.derive n = w) (hstart : 1 ≤ S.start.length)
    (hmem : ∀ a, a ∈ sigma) (hwne : 1 ≤ w.length) :
    (S.start, sigma.map fun a => (a, (trim S n).rule a)) ∈
      sol sigma ⟨S.start.length, w.length, false⟩ w n := by
  have hT : ∀ a, (trim S n).rule a ≠ [] := by
    intro a; simp only [trim]; split
    · exact hne a
    · simp
  have hTlen : ∀ a, ((trim S n).rule a).length ≤ w.length := by
    intro a; simp only [trim]; split
    · rename_i ha; rw [← hw]; exact length_rule_le_of_used S hne n a ha
    · simp; exact hwne
  have hPD : Presented.toDOL (S.start, sigma.map fun a => (a, (trim S n).rule a)) = trim S n :=
    toDOL_map_pair sigma hmem _ _
  unfold sol
  rw [List.mem_filter]
  refine ⟨?_, decide_eq_true (by rw [hPD, trim_derive]; exact hw)⟩
  simp only [allSystems, List.mem_flatMap, List.mem_map]
  refine ⟨S.start, ?_, sigma.map fun a => (a, (trim S n).rule a), ?_, rfl⟩
  · exact mem_wordsUpTo_of sigma 1 _ _ hstart (Nat.le_refl _) (fun x _ => hmem x)
  · apply mem_ruleTables_of
    intro a _
    exact mem_wordsUpTo_of sigma _ _ _ (List.length_pos_iff.mpr (hT a)) (hTlen a)
      (fun x _ => hmem x)

/-! ### Identity-free expansion (the sound form of Conjecture C's heuristic) -/

/-- If neither letter is fixed and at least one rule has length ≥ 2, every letter at least
doubles over two steps, hence `2^(n/2) |ω| ≤ |f^n ω|`. -/
theorem identity_free_expansion (S : DOL Bool) (hne : ∀ a, S.rule a ≠ [])
    (hid : ∀ a, S.rule a ≠ [a]) (hbig : ∃ a, 2 ≤ (S.rule a).length) (n : Nat) :
    2 ^ (n / 2) * S.start.length ≤ (S.derive n).length := by
  by_cases hall : ∀ a, 2 ≤ (S.rule a).length
  · have h := length_derive_pow S hall n
    have : 2 ^ (n / 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.div_le_self n 2)
    exact Nat.le_trans (Nat.mul_le_mul_right _ this) h
  · obtain ⟨x, hx⟩ := Classical.not_forall.mp hall
    have h1 : (S.rule x).length = 1 := by
      have := List.length_pos_iff.mpr (hne x); have := Nat.lt_of_not_le hx; omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp h1
    have hcx : c = !x := by
      cases x <;> cases c <;> simp_all
    subst hcx
    have hy : 2 ≤ (S.rule (!x)).length := by
      obtain ⟨a, ha⟩ := hbig
      rcases (show a = x ∨ a = !x by cases a <;> cases x <;> simp) with rfl | rfl
      · omega
      · exact ha
    exact length_derive_two_pow S hne x hc hy n

theorem identity_free_axiom_bound (S : DOL Bool) (hne : ∀ a, S.rule a ≠ [])
    (hid : ∀ a, S.rule a ≠ [a]) (hbig : ∃ a, 2 ≤ (S.rule a).length) (n : Nat) :
    S.start.length ≤ (S.derive n).length / 2 ^ (n / 2) := by
  have := identity_free_expansion S hne hid hbig n
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
  rw [Nat.mul_comm]; exact this

/-! ### Conjecture C is false -/

/-- `a^5 b^16` with `a = false`, `b = true`. -/
def cexW : List Bool := List.replicate 5 false ++ List.replicate 16 true

/-- The witness: axiom `a^5 b`, `a ↦ a`, `b ↦ bb`. -/
def cexS : DOL Bool := ⟨List.replicate 5 false ++ [true], fun c => if c then [true, true] else [false]⟩

theorem cexS_derive : cexS.derive 4 = cexW := by decide
theorem cexS_short : cexS.start.length < cexW.length := by decide
theorem cexS_nonerasing : ∀ a, cexS.rule a ≠ [] := by decide
theorem cexW_not_crit : ¬ Crit 4 false cexW ∧ ¬ Crit 4 true cexW := by decide

set_option maxRecDepth 100000 in
theorem cex_search_empty : infer [false, true] ⟨5, 21, false⟩ cexW 4 1000000 = [] := by decide

theorem cexW_length : cexW.length = 21 := by decide

/-- **Conjecture C fails.** Every non-erasing system deriving `a^5 b^16` in 4 steps has an
axiom of length at least 6, whereas `21 / 2^(4/2) = 5`. -/
theorem conjC_false (S : DOL Bool) (hne : ∀ a, S.rule a ≠ []) (hw : S.derive 4 = cexW) :
    6 ≤ S.start.length := by
  apply Classical.byContradiction
  intro hlt
  have hlt : S.start.length < 6 := Nat.lt_of_not_le hlt
  have hstart : 1 ≤ S.start.length := by
    apply Nat.lt_of_not_le; intro h0
    have : S.start = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h := hw
    rw [derive_eq_iter, this, iter_nil] at h
    exact absurd h (by decide)
  -- a member of `sol` with the system's own axiom bound, then widen it to 5
  have hmem := mem_sol_of_system [false, true] S 4 cexW hne hw hstart
    (fun a => by cases a <;> simp) (by rw [cexW_length]; omega)
  rw [cexW_length] at hmem
  -- widen `maxAxiom` from `|start|` to 5: `sol` is monotone in the axiom bound
  have hmem5 : (S.start, [false, true].map fun a => (a, (trim S 4).rule a)) ∈
      sol [false, true] ⟨5, 21, false⟩ cexW 4 := by
    unfold sol at hmem ⊢
    rw [List.mem_filter] at hmem ⊢
    refine ⟨?_, hmem.2⟩
    have hA := hmem.1
    simp only [allSystems, List.mem_flatMap, List.mem_map] at hA ⊢
    obtain ⟨ax, hax, t, ht, he⟩ := hA
    refine ⟨ax, ?_, t, ht, he⟩
    obtain ⟨h1, h2, h3⟩ := mem_wordsUpTo _ _ _ _ hax
    exact mem_wordsUpTo_of _ _ _ _ h1 (by omega) h3
  -- the search with fuel 10^6 is complete for this instance …
  have hμ : measure [false, true] 4 (lift (Presented.toDOL (S.start, [false, true].map fun a => (a, (trim S 4).rule a))))
      ⟨[], [(none, 0, 0)], 0⟩ < 1000000 := by
    have hPD : Presented.toDOL (S.start, [false, true].map fun a => (a, (trim S 4).rule a)) = trim S 4 :=
      toDOL_map_pair [false, true] (fun a => by cases a <;> simp) _ _
    rw [hPD]
    have hTne : ∀ a, (trim S 4).rule a ≠ [] := by
      intro a; simp only [trim]; split
      · exact hne a
      · simp
    have hb := measure_init_le [false, true] (trim S 4) hTne 4
    rw [trim_derive, hw, cexW_length] at hb
    have hd : dsize [false, true] (trim S 4) ≤ 5 + 21 + 21 := by
      simp only [dsize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hl : ∀ a, ((trim S 4).rule a).length ≤ 21 := by
        intro a; simp only [trim]; split
        · rename_i ha
          have := length_rule_le_of_used S hne 4 a ha
          rw [hw, cexW_length] at this; exact this
        · simp
      have := hl false; have := hl true
      show S.start.length + _ ≤ _
      omega
    omega
  -- … so it must emit something, but it emits nothing
  obtain ⟨Q, hQ, -⟩ := infer_complete_fuel [false, true] ⟨5, 21, false⟩ cexW 4 _ hmem5 1000000 hμ
  rw [cex_search_empty] at hQ
  exact absurd hQ (List.not_mem_nil)

/-- The number Conjecture C would allow. -/
theorem conjC_bound : cexW.length / 2 ^ (4 / 2) = 5 := by decide


/-! ### Exact optimizer for insertion systems

For `w` with `m ≥ 1` copies of `!x` and `x`-runs `r₀, r₁, …, rₘ`, the largest `p + q` an
insertion system `x ↦ x, !x ↦ x^p (!x) x^q` deriving `w` at step `n` can have is

  `insP n x w = min (⌊r₀/n⌋ + ⌊rₘ/n⌋) (min_{0<i<m} ⌊rᵢ/n⌋)`,

and it is attained. Since `|ω| = |w| − n·m·(p+q)`, this gives the minimum axiom length and
(for `n·m ≥ 1`) the minimum description size over the whole insertion family. -/

/-- The bound `min (E, inner)`; the inner minimum is `+∞` (i.e. `E`) when `m = 1`. -/
def insP (n : Nat) (x : Bool) (w : List Bool) : Nat :=
  (((runs x w).drop 1).dropLast.map (· / n)).foldr min
    ((runs x w).headD 0 / n + (runs x w).getLastD 0 / n)

theorem foldr_min_le_init (l : List Nat) (e : Nat) : l.foldr min e ≤ e := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.le_trans (Nat.min_le_right _ _) ih

theorem foldr_min_le_mem (l : List Nat) (e : Nat) (r : Nat) (hr : r ∈ l) : l.foldr min e ≤ r := by
  induction l with
  | nil => simp at hr
  | cons a l ih =>
    rcases List.mem_cons.mp hr with rfl | h
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih h)

theorem le_foldr_min (l : List Nat) (e k : Nat) (he : k ≤ e) (hl : ∀ r ∈ l, k ≤ r) :
    k ≤ l.foldr min e := by
  induction l with
  | nil => exact he
  | cons a l ih =>
    exact Nat.le_min.mpr ⟨hl a List.mem_cons_self, ih (fun r hr => hl r (List.mem_cons_of_mem _ hr))⟩

theorem insP_le_ends (n : Nat) (x : Bool) (w : List Bool) :
    insP n x w ≤ (runs x w).headD 0 / n + (runs x w).getLastD 0 / n :=
  foldr_min_le_init _ _

theorem insP_le_inner (n : Nat) (x : Bool) (w : List Bool) (r : Nat)
    (hr : r ∈ ((runs x w).drop 1).dropLast) : insP n x w ≤ r / n :=
  foldr_min_le_mem _ _ _ (List.mem_map_of_mem hr)

theorem le_insP (n : Nat) (x : Bool) (w : List Bool) (k : Nat)
    (he : k ≤ (runs x w).headD 0 / n + (runs x w).getLastD 0 / n)
    (hi : ∀ r ∈ ((runs x w).drop 1).dropLast, k ≤ r / n) : k ≤ insP n x w := by
  apply le_foldr_min _ _ _ he
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  exact hi r' hr'

/-! #### Lengths and counts under insertion -/

theorem length_ins (x : Bool) (a b : Nat) (ω : List Bool) :
    (ins x a b ω).length = ω.length + (a + b) * ω.count (!x) := by
  induction ω with
  | nil => simp [ins]
  | cons c t ih =>
    have hne : x ≠ !x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with rfl | rfl
    · simp only [ins, List.flatMap_cons, ite_true, List.singleton_append, List.length_cons,
        List.count_cons_of_ne hne]
      simp only [ins] at ih; omega
    · have : (!x) = x ↔ False := by cases x <;> simp
      simp only [ins, List.flatMap_cons, this, ite_false, List.length_append,
        List.length_replicate, List.length_cons, List.count_cons_self]
      simp only [ins] at ih
      rw [Nat.mul_succ]; omega

theorem count_ins (x : Bool) (a b : Nat) (ω : List Bool) :
    (ins x a b ω).count (!x) = ω.count (!x) := by
  induction ω with
  | nil => simp [ins]
  | cons c t ih =>
    have hne : x ≠ !x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with rfl | rfl
    · simp only [ins, List.flatMap_cons, ite_true, List.singleton_append, List.count_cons_of_ne hne]
      simpa [ins] using ih
    · have : (!x) = x ↔ False := by cases x <;> simp
      simp only [ins, List.flatMap_cons, this, ite_false, List.count_append,
        List.count_replicate, List.count_cons_self]
      simp only [ins] at ih
      rw [ih]
      have : ((!x) == x) = false := by cases x <;> decide
      simp; omega

theorem mem_not_of_mem_ins (x : Bool) (a b : Nat) (ω : List Bool) (h : (!x) ∈ ins x a b ω) :
    (!x) ∈ ω := by
  have := count_ins x a b ω
  have h1 := List.count_pos_iff.mpr h
  exact List.count_pos_iff.mp (by omega)

/-- The derived word of an insertion system, as `ins`. -/
theorem derive_insertion' (S : DOL Bool) (x : Bool) (p q : Nat) (hx : S.rule x = [x])
    (hy : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x) (n : Nat) :
    S.derive n = ins x (n * p) (n * q) S.start := by
  rw [derive_insertion S x p q hx hy n]; rfl

/-- **Axiom length of any insertion solution.** -/
theorem insertion_axiom_length (S : DOL Bool) (x : Bool) (p q n : Nat) (hx : S.rule x = [x])
    (hy : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x) (w : List Bool)
    (hw : S.derive n = w) :
    S.start.length + n * w.count (!x) * (p + q) = w.length := by
  rw [← hw, derive_insertion' S x p q hx hy n, length_ins, count_ins]
  rw [Nat.mul_assoc, Nat.mul_comm (S.start.count (!x)), ← Nat.mul_assoc, Nat.mul_add]

/-- **Description size of any insertion solution** over `[x, !x]`. -/
theorem insertion_dsize (S : DOL Bool) (x : Bool) (p q : Nat) (hx : S.rule x = [x])
    (hy : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x) :
    dsize [x, !x] S = S.start.length + (p + q) + 2 := by
  simp [dsize, hx, hy]; omega

/-- **Upper bound.** Any insertion solution has `p + q ≤ insP`. -/
theorem insertion_pq_le (S : DOL Bool) (x : Bool) (p q n : Nat) (hn : 1 ≤ n)
    (hx : S.rule x = [x]) (hy : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x)
    (w : List Bool) (hw : S.derive n = w) (hmem : (!x) ∈ w) : p + q ≤ insP n x w := by
  have hform : w = ins x (n * p) (n * q) S.start := by rw [← hw, derive_insertion' S x p q hx hy n]
  have hmem0 : (!x) ∈ S.start := mem_not_of_mem_ins x _ _ _ (hform ▸ hmem)
  have h2 := runs_length_pos_of_mem x S.start hmem0
  have hr : runs x w = adjust (n * p) (n * q) (runs x S.start) := by rw [hform, runs_ins]
  obtain ⟨hh, hl, hi⟩ := adjust_spec (n * p) (n * q) (runs x S.start) h2
  rw [← hr] at hh hl hi
  have hp : p ≤ (runs x w).headD 0 / n := (Nat.le_div_iff_mul_le hn).mpr (by rw [Nat.mul_comm]; exact hh)
  have hq : q ≤ (runs x w).getLastD 0 / n := (Nat.le_div_iff_mul_le hn).mpr (by rw [Nat.mul_comm]; exact hl)
  apply le_insP _ _ _ _ (by omega)
  intro r hr'
  have := hi r hr'
  exact (Nat.le_div_iff_mul_le hn).mpr (by rw [Nat.mul_comm, Nat.mul_add]; exact this)

/-! #### Attainability -/

/-- Shrink the tail of a run list: inner runs by `c`, the last run by `b`. -/
def shrinkTail (b c : Nat) : List Nat → List Nat
  | [] => []
  | [r] => [r - b]
  | r :: rs => (r - c) :: shrinkTail b c rs

theorem adjust_shrinkTail (a b : Nat) : ∀ (rest : List Nat) (t : Nat), rest ≠ [] → a ≤ t →
    (∀ r ∈ rest.dropLast, a + b ≤ r) → b ≤ rest.getLastD 0 →
    adjust a b ((t - a) :: shrinkTail b (a + b) rest) = t :: rest := by
  intro rest
  induction rest with
  | nil => intro t h; exact absurd rfl h
  | cons r' rs' ih =>
    intro t _ ht hinner hlast
    cases rs' with
    | nil =>
      have hl' : b ≤ r' := by simpa using hlast
      show (t - a + a) :: (match adjust a b [r' - b] with | s :: ss => (s + b) :: ss | [] => []) = [t, r']
      simp only [adjust]
      simp only [List.cons.injEq]
      exact ⟨by omega, by omega, trivial⟩
    | cons r'' rs'' =>
      have hr' : a + b ≤ r' := hinner r' (by simp)
      have hrest : (r'' :: rs'').getLastD 0 = (r' :: r'' :: rs'').getLastD 0 := by simp
      have := ih (r' - b) (by simp) (by omega)
        (fun q hq => hinner q (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact Or.inr hq))
        (by rw [hrest]; exact hlast)
      have e : r' - b - a = r' - (a + b) := by omega
      rw [e] at this
      show (t - a + a) :: (match adjust a b ((r' - (a + b)) :: shrinkTail b (a + b) (r'' :: rs'')) with
        | s :: ss => (s + b) :: ss | [] => []) = t :: r' :: r'' :: rs''
      rw [show (r' - (a + b)) :: shrinkTail b (a + b) (r'' :: rs'') = shrinkTail b (a + b) (r' :: r'' :: rs'') from rfl]
      rw [show shrinkTail b (a + b) (r' :: r'' :: rs'') = (r' - (a+b)) :: shrinkTail b (a + b) (r'' :: rs'') from rfl]
      rw [this]
      simp only [List.cons.injEq, and_true]
      omega

theorem runs_fromRuns (x : Bool) (rs : List Nat) (h : rs ≠ []) : runs x (fromRuns x rs) = rs := by
  induction rs with
  | nil => exact absurd rfl h
  | cons r rs ih =>
    cases rs with
    | nil => simp only [fromRuns]; rw [← List.append_nil (List.replicate r x), runs_replicate_append]; simp [runs]
    | cons r' rs' =>
      simp only [fromRuns]
      rw [runs_replicate_append, runs_notx_cons, ih (by simp)]
      simp

theorem getLastD_cons_of_ne_nil (b a : Nat) (l : List Nat) (h : l ≠ []) :
    (b :: l).getLastD a = l.getLastD a := by
  cases l with
  | nil => exact absurd rfl h
  | cons c cs => simp [List.getLastD_cons]

/-- The optimal insertion system for `(w, n, x)`: `p` takes as much of `insP` as the leading
run allows, `q` the rest. -/
def optP (n : Nat) (x : Bool) (w : List Bool) : Nat := min (insP n x w) ((runs x w).headD 0 / n)
def optQ (n : Nat) (x : Bool) (w : List Bool) : Nat := insP n x w - optP n x w

def optSys (n : Nat) (x : Bool) (w : List Bool) : DOL Bool :=
  ⟨fromRuns x (((runs x w).headD 0 - n * optP n x w) ::
      shrinkTail (n * optQ n x w) (n * optP n x w + n * optQ n x w) ((runs x w).drop 1)),
   fun c => if c = x then [x] else
     List.replicate (optP n x w) x ++ (!x) :: List.replicate (optQ n x w) x⟩

theorem optSys_rule_x (n : Nat) (x : Bool) (w : List Bool) : (optSys n x w).rule x = [x] := by
  simp [optSys]

theorem optSys_rule_y (n : Nat) (x : Bool) (w : List Bool) :
    (optSys n x w).rule (!x) = List.replicate (optP n x w) x ++ (!x) :: List.replicate (optQ n x w) x := by
  have : (!x) = x ↔ False := by cases x <;> simp
  simp [optSys, this]

theorem optP_add_optQ (n : Nat) (x : Bool) (w : List Bool) : optP n x w + optQ n x w = insP n x w := by
  unfold optQ; have := Nat.min_le_left (insP n x w) ((runs x w).headD 0 / n); unfold optP; omega

/-- **Attainability.** The optimal system derives `w` with `p + q = insP`. -/
theorem optSys_derive (n : Nat) (hn : 1 ≤ n) (x : Bool) (w : List Bool) (hmem : (!x) ∈ w) :
    (optSys n x w).derive n = w := by
  rw [derive_insertion' _ x _ _ (optSys_rule_x n x w) (optSys_rule_y n x w) n]
  apply ins_eq_of_runs
  rw [runs_ins]
  obtain ⟨r0, rest, hrs⟩ : ∃ r0 rest, runs x w = r0 :: rest := by
    cases h : runs x w with
    | nil => exact absurd h (runs_ne_nil x w)
    | cons r0 rest => exact ⟨r0, rest, rfl⟩
  have h2 := runs_length_pos_of_mem x w hmem
  have hrest : rest ≠ [] := by rw [hrs] at h2; cases rest <;> simp_all
  simp only [optSys]
  rw [runs_fromRuns _ _ (by simp), hrs]
  simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
  -- the three constraints
  have hP := insP_le_ends n x w
  have hhead : n * optP n x w ≤ r0 := by
    have : optP n x w ≤ r0 / n := by
      have := Nat.min_le_right (insP n x w) ((runs x w).headD 0 / n); rw [hrs] at this
      show min (insP n x w) ((runs x w).headD 0 / n) ≤ r0 / n
      rw [hrs]; exact this
    have := (Nat.le_div_iff_mul_le hn).mp this; rw [Nat.mul_comm]; exact this
  have hlast : n * optQ n x w ≤ rest.getLastD 0 := by
    have hq : optQ n x w ≤ (runs x w).getLastD 0 / n := by
      have h2 : optQ n x w = insP n x w - optP n x w := rfl
      rw [h2]
      rcases Nat.le_total (insP n x w) ((runs x w).headD 0 / n) with h | h
      · rw [show optP n x w = insP n x w from Nat.min_eq_left h]
        generalize (runs x w).getLastD 0 / n = v at *
        omega
      · rw [show optP n x w = (runs x w).headD 0 / n from Nat.min_eq_right h]
        generalize (runs x w).headD 0 / n = u at *
        generalize (runs x w).getLastD 0 / n = v at *
        omega
    rw [hrs, getLastD_cons_of_ne_nil _ _ _ hrest] at hq
    have := (Nat.le_div_iff_mul_le hn).mp hq
    rw [Nat.mul_comm]
    exact this
  have hinner : ∀ r ∈ rest.dropLast, n * optP n x w + n * optQ n x w ≤ r := by
    intro r hr
    have := insP_le_inner n x w r (by rw [hrs]; simpa using hr)
    have := (Nat.le_div_iff_mul_le hn).mp this
    rw [← Nat.mul_add, optP_add_optQ, Nat.mul_comm]; exact this
  exact adjust_shrinkTail _ _ rest r0 hrest hhead hinner hlast

/-- **Exact minimum axiom length over the insertion family.** Every insertion solution has
`|ω| ≥ |w| − n·m·insP`, and `optSys` attains it (`m = count of !x in w`). -/
theorem insertion_min_axiom (n : Nat) (hn : 1 ≤ n) (x : Bool) (w : List Bool) (hmem : (!x) ∈ w) :
    (optSys n x w).start.length + n * w.count (!x) * insP n x w = w.length ∧
    ∀ (S : DOL Bool) (p q : Nat), S.rule x = [x] →
      S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x → S.derive n = w →
      (optSys n x w).start.length ≤ S.start.length := by
  have hopt := insertion_axiom_length (optSys n x w) x _ _ n (optSys_rule_x n x w)
    (optSys_rule_y n x w) w (optSys_derive n hn x w hmem)
  rw [optP_add_optQ] at hopt
  refine ⟨hopt, ?_⟩
  intro S p q hx hy hw
  have hS := insertion_axiom_length S x p q n hx hy w hw
  have hle := insertion_pq_le S x p q n hn hx hy w hw hmem
  have := Nat.mul_le_mul_left (n * w.count (!x)) hle
  omega

/-- **Exact minimum description size over the insertion family** (when `n·m ≥ 1`). -/
theorem insertion_min_dsize (n : Nat) (hn : 1 ≤ n) (x : Bool) (w : List Bool) (hmem : (!x) ∈ w) :
    dsize [x, !x] (optSys n x w) + (n * w.count (!x) - 1) * insP n x w = w.length + 2 ∧
    ∀ (S : DOL Bool) (p q : Nat), S.rule x = [x] →
      S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x → S.derive n = w →
      dsize [x, !x] (optSys n x w) ≤ dsize [x, !x] S := by
  have hm : 1 ≤ w.count (!x) := List.count_pos_iff.mpr hmem
  have hnm : 1 ≤ n * w.count (!x) := Nat.mul_le_mul hn hm
  obtain ⟨hopt, hmin⟩ := insertion_min_axiom n hn x w hmem
  have hd := insertion_dsize (optSys n x w) x _ _ (optSys_rule_x n x w) (optSys_rule_y n x w)
  rw [optP_add_optQ] at hd
  refine ⟨?_, ?_⟩
  · rw [hd]
    have e : (n * w.count (!x) - 1) * insP n x w + insP n x w = n * w.count (!x) * insP n x w := by
      have := Nat.le_mul_of_pos_left (insP n x w) hnm
      rw [Nat.sub_one_mul]; omega
    omega
  · intro S p q hx hy hw
    have hS := insertion_axiom_length S x p q n hx hy w hw
    have hdS := insertion_dsize S x p q hx hy
    have hle := insertion_pq_le S x p q n hn hx hy w hw hmem
    -- dsize = |w| + 2 − (nm − 1)(p+q), decreasing in p + q since nm ≥ 1
    have h1 := Nat.mul_le_mul_left (n * w.count (!x) - 1) hle
    have e1 : (n * w.count (!x) - 1) * (p + q) + (p + q) = n * w.count (!x) * (p + q) := by
      have := Nat.le_mul_of_pos_left (p + q) hnm
      rw [Nat.sub_one_mul]; omega
    have e2 : (n * w.count (!x) - 1) * insP n x w + insP n x w = n * w.count (!x) * insP n x w := by
      have := Nat.le_mul_of_pos_left (insP n x w) hnm
      rw [Nat.sub_one_mul]; omega
    omega

/-- `insP ≥ 1` is exactly the run-length criterion `Crit` (for `n ≥ 1`, `!x ∈ w`). -/
theorem insP_pos_iff_crit (n : Nat) (hn : 1 ≤ n) (x : Bool) (w : List Bool) (hmem : (!x) ∈ w) :
    1 ≤ insP n x w ↔ Crit n x w := by
  have h2 := runs_length_pos_of_mem x w hmem
  constructor
  · intro h
    refine ⟨h2, ?_, ?_⟩
    · intro r hr
      have := Nat.le_trans h (insP_le_inner n x w r hr)
      have h' := (Nat.le_div_iff_mul_le hn).mp this
      simpa using h'
    · have := Nat.le_trans h (insP_le_ends n x w)
      rcases (show 1 ≤ (runs x w).headD 0 / n ∨ 1 ≤ (runs x w).getLastD 0 / n by omega) with h' | h'
      · have h'' := (Nat.le_div_iff_mul_le hn).mp h'; exact Or.inl (by simpa using h'')
      · have h'' := (Nat.le_div_iff_mul_le hn).mp h'; exact Or.inr (by simpa using h'')
  · rintro ⟨-, hinner, hends⟩
    apply le_insP
    · rcases hends with h | h
      · have := (Nat.le_div_iff_mul_le hn).mpr (by rw [Nat.one_mul]; exact h : 1 * n ≤ (runs x w).headD 0)
        generalize (runs x w).headD 0 / n = u at *
        generalize (runs x w).getLastD 0 / n = v at *
        omega
      · have := (Nat.le_div_iff_mul_le hn).mpr (by rw [Nat.one_mul]; exact h : 1 * n ≤ (runs x w).getLastD 0)
        generalize (runs x w).headD 0 / n = u at *
        generalize (runs x w).getLastD 0 / n = v at *
        omega
    · intro r hr
      exact (Nat.le_div_iff_mul_le hn).mpr (by simpa using hinner r hr)


/-! ### Incompressibility by direct description counting (binary alphabet)

A binary description is a triple `(axiom, rule a, rule b)`; those of total size `t` are in
bijection with (binary word of length `t`) × (two cut positions `i ≤ j ≤ t`), so there are
`2^t · (t+1)(t+2)/2` of them and `A(s) = Σ_{t ≤ s} 2^t (t+1)(t+2)/2 = 2^s (s² + s + 2) − 1`
of size at most `s`. Pigeonhole then gives a word of length `L` needing size `> s` whenever
`A(s) < 2^L` — on the scale `s ≈ L − 2 log₂ L`, far above the `0.63 L` that
`exists_incompressible` yields for the binary alphabet. -/

/-- Binary systems `(v.take i, a ↦ v[i..j), b ↦ v[j..])` for all words `v` of length `t`,
`i ≤ j ≤ t`; `a = false`, `b = true`. -/
def descsExact (t : Nat) : List (DOL Bool) :=
  (List.range (t + 1)).flatMap fun j => (List.range (j + 1)).flatMap fun i =>
    (words [false, true] t).map fun v =>
      ⟨v.take i, fun c => if c then v.drop j else (v.drop i).take (j - i)⟩

/-- All binary descriptions of total size at most `s`. -/
def descs (s : Nat) : List (DOL Bool) := (List.range (s + 1)).flatMap descsExact

/-- `1 + 2 + ⋯ + (t+1)`. -/
def tri (t : Nat) : Nat := ((List.range (t + 1)).map (· + 1)).sum

/-- `A(s) = Σ_{t ≤ s} 2^t · tri t`. -/
def descCount (s : Nat) : Nat := ((List.range (s + 1)).map fun t => 2 ^ t * tri t).sum

theorem tri_succ (t : Nat) : tri (t + 1) = tri t + (t + 1 + 1) := by
  simp [tri, List.range_succ]; omega

theorem two_tri (t : Nat) : tri t + tri t = (t + 1) * (t + 1 + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [tri_succ]
    have : (t + 1) * (t + 1 + 1) + (t + 1 + 1) + (t + 1 + 1) = (t + 1 + 1) * (t + 1 + 1 + 1) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega
    omega

theorem length_descsExact (t : Nat) : (descsExact t).length = 2 ^ t * tri t := by
  simp only [descsExact, List.length_flatMap, List.length_map, length_words, List.length_cons,
    List.length_nil, List.length_range, tri]
  -- Σ_{j ≤ t} Σ_{i ≤ j} 2^t = 2^t · Σ_{j ≤ t} (j + 1)
  have h1 : ∀ j, ((List.range (j + 1)).map fun _ => 2 ^ t).sum = 2 ^ t * (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [Nat.mul_succ]
  have h2 : ∀ k, ((List.range k).map fun j => 2 ^ t * (j + 1)).sum
      = 2 ^ t * ((List.range k).map (· + 1)).sum := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_append, List.sum_append,
        Nat.mul_add]
      simp
  rw [show ((List.range (t + 1)).map fun j => ((List.range (j + 1)).map fun _ => 2 ^ t).sum).sum
      = ((List.range (t + 1)).map fun j => 2 ^ t * (j + 1)).sum from by
    congr 1; apply List.map_congr_left; intro j _; exact h1 j]
  exact h2 (t + 1)

theorem length_descs (s : Nat) : (descs s).length = descCount s := by
  simp only [descs, descCount, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro t _
  exact length_descsExact t

/-- The closed form `A(s) + 1 = 2^s (s² + s + 2)`. -/
theorem descCount_closed (s : Nat) : descCount s + 1 = 2 ^ s * (s * s + s + 1 + 1) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hstep : descCount (s + 1) = descCount s + 2 ^ (s + 1) * tri (s + 1) := by
      simp [descCount, List.range_succ]; omega
    rw [hstep]
    have h2 : 2 ^ (s + 1) * tri (s + 1) = 2 ^ s * ((s + 1 + 1) * (s + 1 + 1 + 1)) := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, Nat.mul_comm (tri (s + 1)) 2, Nat.two_mul,
        two_tri]
    rw [h2]
    have key : ∀ u : Nat, u * (s * s + s + 1 + 1) + u * ((s + 1 + 1) * (s + 1 + 1 + 1))
        = u * ((s + 1) * (s + 1) + (s + 1) + 1 + 1) + u * ((s + 1) * (s + 1) + (s + 1) + 1 + 1) := by
      intro u
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      simp only [← Nat.mul_assoc]
      omega
    have := key (2 ^ s)
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, Nat.mul_assoc, Nat.two_mul]
    omega

/-- Every binary system of description size `≤ s` is listed in `descs s`. -/
theorem mem_descs (S : DOL Bool) (s : Nat) (h : dsize [false, true] S ≤ s) : S ∈ descs s := by
  simp only [dsize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  have hmem : S ∈ descsExact (S.start.length + (S.rule false).length + (S.rule true).length) := by
    simp only [descsExact, List.mem_flatMap, List.mem_map, List.mem_range]
    refine ⟨S.start.length + (S.rule false).length, by omega, S.start.length, by omega,
      S.start ++ S.rule false ++ S.rule true, ?_, ?_⟩
    · have := mem_words_of [false, true] (S.start ++ S.rule false ++ S.rule true)
        (fun x _ => by cases x <;> simp)
      rw [List.length_append, List.length_append] at this
      exact this
    · refine DOL.ext' _ _ ?_ ?_
      · simp [List.take_left']
      · intro c
        cases c
        · simp only [Bool.false_eq_true, ite_false]
          rw [List.append_assoc, List.drop_left, List.take_left']
          simp
        · simp only [ite_true]
          rw [List.drop_left']
          simp
  simp only [descs, List.mem_flatMap, List.mem_range]
  exact ⟨_, by omega, hmem⟩

/-- **Incompressibility by direct counting.** If `A(s) < 2^L` then some binary word of
length `L` has no system of description size `≤ s` at step `n`. -/
theorem exists_incompressible_binary (n L s : Nat) (hcount : descCount s < 2 ^ L) :
    ∃ w ∈ words [false, true] L, ∀ S : DOL Bool, dsize [false, true] S ≤ s → S.derive n ≠ w := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ w ∈ words [false, true] L, ∃ S : DOL Bool, dsize [false, true] S ≤ s ∧ S.derive n = w := by
    intro w hw
    apply Classical.byContradiction
    intro hne
    exact hno ⟨w, hw, fun S hS hd => hne ⟨S, hS, hd⟩⟩
  have hsub : words [false, true] L ⊆ (descs s).map fun S => S.derive n := by
    intro w hw
    obtain ⟨S, hS, hd⟩ := hall w hw
    exact List.mem_map.mpr ⟨S, mem_descs S s hS, hd⟩
  have := nodup_subset_length_le _ _ (words_nodup [false, true] (by decide) L) hsub
  rw [List.length_map, length_words, length_descs] at this
  simp at this
  omega

/-- The sufficient condition in closed form: `s ≤ L` and `s² + s + 2 ≤ 2^(L−s)`. -/
theorem exists_incompressible_binary_of (n L s : Nat) (hs : s ≤ L)
    (h : s * s + s + 1 + 1 ≤ 2 ^ (L - s)) :
    ∃ w ∈ words [false, true] L, ∀ S : DOL Bool, dsize [false, true] S ≤ s → S.derive n ≠ w := by
  apply exists_incompressible_binary n L s
  have h1 := descCount_closed s
  have h2 : 2 ^ s * (s * s + s + 1 + 1) ≤ 2 ^ s * 2 ^ (L - s) := Nat.mul_le_mul_left _ h
  rw [← Nat.pow_add, Nat.add_sub_cancel' hs] at h2
  omega

/-- **Worst case on the `L − 2 log₂ L` scale.** If `L ≤ 2^k` with `k ≥ 1` and
`s + 2k ≤ L`, some binary word of length `L` needs description size `> s` at every step. -/
theorem exists_incompressible_log (n L k s : Nat) (hk : 1 ≤ k) (hL : L ≤ 2 ^ k)
    (hs : s + 2 * k ≤ L) :
    ∃ w ∈ words [false, true] L, ∀ S : DOL Bool, dsize [false, true] S ≤ s → S.derive n ≠ w := by
  apply exists_incompressible_binary_of n L s (by omega)
  -- s² + s + 2 ≤ (s+2)² ≤ L² ≤ 2^(2k) ≤ 2^(L−s)
  have h1 : (s + 1 + 1) * (s + 1 + 1) ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
  have h2 : L * L ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hL hL
  have h3 : 2 ^ k * 2 ^ k ≤ 2 ^ (L - s) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have : s * s + s + 1 + 1 ≤ (s + 1 + 1) * (s + 1 + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega
  omega

/-- Instance: some binary word of length 64 needs size `> 52` (`A(52) < 2^64`),
whereas `exists_incompressible` only reaches size `> 37` (`3^(37+3) < 2^64`, `3^41 > 2^64`). -/
theorem incompressible_64 (n : Nat) :
    ∃ w ∈ words [false, true] 64, ∀ S : DOL Bool, dsize [false, true] S ≤ 52 → S.derive n ≠ w :=
  exists_incompressible_log n 64 6 52 (by decide) (by decide) (by decide)

end LSys
