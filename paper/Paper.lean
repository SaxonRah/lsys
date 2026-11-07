/-
Inverse L-system inference, formalized (Lean 4.15 core, no Mathlib). No `sorry`.

Master theorem, in two halves (both proved):
  infer_complete : every bounded solution in `sol` is emitted by the pruned search `infer`
  infer_sound    : every key emitted by `infer` is a bounded solution in `sol`
both up to `canon` (rules of symbols that are never rewritten are irrelevant), with no
side conditions: `infer` filters leaf candidates by `sigma`, never closes an empty axiom,
and returns nothing when no legal rule body exists (earlier versions needed w ⊆ sigma,
w ≠ [] and 1 ≤ maxRule as hypotheses; each was a genuine discrepancy).

Also proved: existence (identity; one hidden symbol gives a length-1 axiom),
impossibility over a one-letter alphabet, and the growth/length lemmas.

Problem A (non-trivial systems over Σ(w), axiom shorter than w):
  unary_iff    : a^L at step n  ⟺  ∃ m ≥ 2, m^n ∣ L
  chain_exists : n ≤ |Σ(w)|  ⟹  a length-1 axiom works
Problem B (counting):
  exists_underivable : fewer bounded systems than |sigma|^L words ⟹ some word of
                       length L has no bounded system at any step
  underivable_binary_8 : concrete instance, decided inside Lean
  exists_incompressible : total-description-size version via an encode/decode injection
Problem A, the regime n > |Σ| = 2 (non-erasing, axiom shorter than w, w uses both letters):
  small_implies_insertion : |w| < 2^(n/2)  ⟹  one letter fixed, other ↦ x^p (!x) x^q
  sharp_implies_insertion : |w| < T(n) = min(F_{n+1}, D(n))  ⟹  same conclusion,
                            where D(n) = 2·2^(n/2) (n even), 3·2^(n/2) (n odd)
  derive_insertion        : the converse formula  w = ω[!x ↦ x^(np) (!x) x^(nq)]
  crit_of_insertion / insertion_of_crit : insertion words are exactly those meeting the
                            run-length criterion `Crit n x w` (inner x-runs ≥ n; leading
                            or trailing x-run ≥ n)
  sharp_witness           : T(n) is attained for every n ≥ 2 (Fibonacci iterate for n ≤ 7,
                            a^(2^k) b^(2^k) for n ≥ 8), by words that are solvable, non-erasing,
                            use both letters and fail `Crit` for both letters
-/
namespace LSys

/-- A deterministic context-free (D0L) L-system. -/
structure DOL (α : Type) where
  start : List α
  rule  : α → List α

variable {α : Type}

def DOL.step (S : DOL α) (s : List α) : List α := s.flatMap S.rule

def DOL.derive (S : DOL α) : Nat → List α
  | 0     => S.start
  | n + 1 => S.step (S.derive n)

/-! ### Basic lemmas about step -/

@[simp] theorem step_nil (S : DOL α) : S.step [] = [] := rfl

@[simp] theorem step_cons (S : DOL α) (a : α) (s : List α) :
    S.step (a :: s) = S.rule a ++ S.step s := rfl

theorem step_append (S : DOL α) (s t : List α) :
    S.step (s ++ t) = S.step s ++ S.step t := by
  simp [DOL.step, List.flatMap_append]

/-- Length of one step is the sum of rule lengths (the "growth" lemma). -/
theorem length_step (S : DOL α) (s : List α) :
    (S.step s).length = (s.map fun a => (S.rule a).length).sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [ih, List.length_append]

/-! ### Theorem 1: trivial existence -/

def DOL.identity (w : List α) : DOL α := ⟨w, fun a => [a]⟩

theorem step_identity (w s : List α) : (DOL.identity w).step s = s := by
  induction s with
  | nil => rfl
  | cons a s ih => rw [step_cons, ih]; rfl

theorem derive_identity (w : List α) (n : Nat) : (DOL.identity w).derive n = w := by
  induction n with
  | zero => rfl
  | succ n ih => simp [DOL.derive, ih, step_identity]

theorem exists_trivial (w : List α) (n : Nat) : ∃ S : DOL α, S.derive n = w :=
  ⟨DOL.identity w, derive_identity w n⟩

/-! ### Theorem 2: one hidden symbol suffices for a length-1 start -/

/-- Hidden symbol `none`, start `[none]`, rule `none ↦ w`, identity elsewhere. -/
def DOL.hidden (w : List α) : DOL (Option α) :=
  ⟨[none], fun o => match o with
    | none   => w.map some
    | some a => [some a]⟩

theorem step_hidden_map (w s : List α) :
    (DOL.hidden w).step (s.map some) = s.map some := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.map_cons, step_cons, ih]; rfl

theorem derive_hidden (w : List α) (n : Nat) (h : 1 ≤ n) :
    (DOL.hidden w).derive n = w.map some := by
  induction n with
  | zero => exact absurd h (by decide)
  | succ n ih =>
    cases n with
    | zero => simp [DOL.derive, DOL.hidden, DOL.step]
    | succ m =>
      have := ih (by omega)
      simp [DOL.derive] at this ⊢
      rw [this, step_hidden_map]

theorem exists_hidden (w : List α) (n : Nat) (h : 1 ≤ n) :
    ∃ S : DOL (Option α), S.start.length = 1 ∧ S.derive n = w.map some :=
  ⟨DOL.hidden w, rfl, derive_hidden w n h⟩

/-! ### Theorem 3: impossibility without hidden symbols

Over a one-letter alphabet, any non-identity, non-erasing rule has length ≥ 2,
and then a nonempty start can never derive the single-letter word `[()]`. -/

theorem length_step_ge (S : DOL α) (k : Nat) (hk : ∀ a, k ≤ (S.rule a).length)
    (s : List α) : k * s.length ≤ (S.step s).length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [step_cons, List.length_append, List.length_cons]
    have := hk a
    rw [Nat.mul_succ]
    omega

theorem length_derive_ge (S : DOL α) (hk : ∀ a, 2 ≤ (S.rule a).length)
    (n : Nat) : S.start.length ≤ (S.derive n).length := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h := length_step_ge S 2 hk (S.derive n)
    simp only [DOL.derive]
    omega

theorem impossible_singleton (S : DOL Unit) (hax : S.start ≠ [])
    (hr : 2 ≤ (S.rule ()).length) (n : Nat) (hn : 1 ≤ n) :
    S.derive n ≠ [()] := by
  intro h
  have hk : ∀ a : Unit, 2 ≤ (S.rule a).length := fun a => by cases a; exact hr
  cases n with
  | zero => exact absurd hn (by decide)
  | succ m =>
    have h1 : 1 ≤ S.start.length := by
      cases hs : S.start with
      | nil => exact absurd hs hax
      | cons _ _ => simp
    have h2 := length_derive_ge S hk m
    have h3 := length_step_ge S 2 hk (S.derive m)
    have h4 : (S.derive (m + 1)).length = 1 := by rw [h]; rfl
    simp only [DOL.derive] at h4
    omega

/-! ### Sol: the brute-force solution set (the specification)

Alphabet given as a list; rules as an association list, so systems are
enumerable. `sol` is the set the efficient search must agree with. -/

/-- All words over `sigma` of length exactly `k`. -/
def words (sigma : List α) : Nat → List (List α)
  | 0     => [[]]
  | k + 1 => (words sigma k).flatMap fun w => sigma.map fun a => a :: w

/-- All words over `sigma` of length in `[lo, hi]`. -/
def wordsUpTo (sigma : List α) (lo hi : Nat) : List (List α) :=
  ((List.range (hi + 1)).filter (lo ≤ ·)).flatMap (words sigma)

/-- Bounds on a system. -/
structure Bounds where
  maxAxiom   : Nat
  maxRule    : Nat
  allowEmpty : Bool

/-- A system presented as (start, association list of rules). -/
abbrev Presented (α : Type) := List α × List (α × List α)

def Presented.toDOL [DecidableEq α] (P : Presented α) : DOL α :=
  ⟨P.1, fun a => match P.2.lookup a with | some r => r | none => [a]⟩

/-- All rule tables over `sigma`, one body per symbol. -/
def ruleTables (sigma : List α) (bodies : List (List α)) : List (List (α × List α)) :=
  sigma.foldr (fun a acc => bodies.flatMap fun b => acc.map fun t => (a, b) :: t) [[]]

def allSystems (sigma : List α) (B : Bounds) : List (Presented α) :=
  let bodies := wordsUpTo sigma (if B.allowEmpty then 0 else 1) B.maxRule
  (wordsUpTo sigma 1 B.maxAxiom).flatMap fun ax =>
    (ruleTables sigma bodies).map fun t => (ax, t)

/-- **The specification.** Every bounded system that derives `w` in `n` steps. -/
def sol [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
    List (Presented α) :=
  (allSystems sigma B).filter fun P => decide (P.toDOL.derive n = w)

theorem sol_sound [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α)
    (n : Nat) (P : Presented α) (h : P ∈ sol sigma B w n) : P.toDOL.derive n = w := by
  unfold sol at h
  have := (List.mem_filter.mp h).2
  exact of_decide_eq_true this

/-! ### The search (transcription of `lsys_pure.py`)

Symbols are `Option α`: `none` is the pseudo-symbol whose "rule" is the axiom.
Rules under construction: association list `sym ↦ (body, closed)`; `lookup`
takes the most recent binding, so updating is a `cons`.
A frame `(sym, d, i)` means "node `sym` at depth `d`, about to expand child `i`".
Leaves live at depth `n+1`. -/

abbrev Rules (α : Type) := List (Option α × (List (Option α) × Bool))

structure St (α : Type) where
  rules : Rules α
  stack : List (Option α × Nat × Nat)   -- top of stack at the head
  pos   : Nat

def lookupR [DecidableEq α] (R : Rules α) (s : Option α) : List (Option α) × Bool :=
  match R.lookup s with | some r => r | none => ([], false)

/-- Lower bound on leaves produced by `sym` with `k` levels still to expand. -/
def minexp [DecidableEq α] (R : Rules α) (allowEmpty : Bool) :
    Nat → Option α → Nat
  | 0,     _   => 1
  | k + 1, sym =>
    let (body, closed) := lookupR R sym
    if body.isEmpty && !closed then (if allowEmpty then 0 else 1)
    else (body.map (minexp R allowEmpty k)).sum

/-- Lower bound on leaves still to be produced by one frame `(sym, d, i)`:
children `i..` of `sym`, each with `n - d` levels left to expand. -/
def frameNeed [DecidableEq α] (R : Rules α) (allowEmpty : Bool) (n : Nat) :
    Option α × Nat × Nat → Nat
  | (sym, d, i) =>
    let (body, closed) := lookupR R sym
    (if i = 0 && body.isEmpty && !closed && !allowEmpty then 1 else 0)
      + ((body.drop i).map (minexp R allowEmpty (n - d))).sum

/-- Lower bound on leaves still to be produced by the whole stack. -/
def need [DecidableEq α] (R : Rules α) (allowEmpty : Bool) (n : Nat)
    (stack : List (Option α × Nat × Nat)) : Nat :=
  (stack.map (frameNeed R allowEmpty n)).sum

/-- The rule body given to a symbol of `sigma` that the search never rewrote: the shortest
legal body (`[a]`, or `[]` when rules of length 1 are not allowed). -/
def defaultBody (B : Bounds) (a : α) : List α := if B.maxRule = 0 then [] else [a]

/-- Extract the finished system: axiom from `none`; for every symbol of `sigma`, its closed
body if it was rewritten, else the default body. -/
def toKey [DecidableEq α] (sigma : List α) (B : Bounds) (R : Rules α) : Presented α :=
  ((lookupR R none).1.filterMap id,
   sigma.map fun a =>
     (a, let (body, closed) := lookupR R (some a)
         if closed then body.filterMap id else defaultBody B a))

def search [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds) :
    Nat → St α → List (Presented α)
  | 0, _ => []
  | fuel + 1, st =>
    match st.stack with
    | [] => if st.pos = w.length then [toKey sigma B st.rules] else []
    | (sym, d, i) :: rest =>
      if w.length < st.pos + need st.rules B.allowEmpty n st.stack then [] else
      let (body, closed) := lookupR st.rules sym
      if h : i < body.length then
        let child := body[i]
        let nxt := (sym, d, i + 1) :: rest
        if d = n then
          match w[st.pos]? with
          | some c => if child = some c then search w n sigma B fuel ⟨st.rules, nxt, st.pos + 1⟩ else []
          | none   => []
        else search w n sigma B fuel ⟨st.rules, (child, d + 1, 0) :: nxt, st.pos⟩
      else if closed then search w n sigma B fuel ⟨st.rules, rest, st.pos⟩
      else
        let closeBr :=
          if 1 ≤ body.length || (B.allowEmpty && sym.isSome) then
            search w n sigma B fuel ⟨(sym, (body, true)) :: st.rules, rest, st.pos⟩
          else []
        let maxlen := if sym = none then B.maxAxiom else B.maxRule
        let extBr :=
          if body.length < maxlen then
            let cands : List (Option α) :=
              if d = n then
                (match w[st.pos]? with | some c => if c ∈ sigma then [some c] else [] | none => [])
              else sigma.map some
            cands.flatMap fun c =>
              search w n sigma B fuel ⟨(sym, (body ++ [c], false)) :: st.rules, st.stack, st.pos⟩
          else []
        closeBr ++ extBr

def infer [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat)
    (fuel : Nat := 1000000) : List (Presented α) :=
  if (if B.allowEmpty then 0 else 1) ≤ B.maxRule then
    search w n sigma B fuel ⟨[], [(none, 0, 0)], 0⟩
  else []

/-! ### Iteration from an arbitrary string, and the key lower-bound lemma -/

/-- Apply `step` k times. `derive n = iter n start`. -/
def DOL.iter (S : DOL α) : Nat → List α → List α
  | 0,     s => s
  | k + 1, s => S.iter k (S.step s)

theorem iter_append (S : DOL α) (k : Nat) (s t : List α) :
    S.iter k (s ++ t) = S.iter k s ++ S.iter k t := by
  induction k generalizing s t with
  | zero => rfl
  | succ k ih => simp only [DOL.iter, step_append, ih]

theorem iter_nil (S : DOL α) (k : Nat) : S.iter k [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [DOL.iter, step_nil, ih]

theorem iter_cons (S : DOL α) (k : Nat) (a : α) (s : List α) :
    S.iter k (a :: s) = S.iter k [a] ++ S.iter k s := by
  have := iter_append S k [a] s
  simpa using this

/-- Length of an iterated string is the sum of the lengths of its symbols' expansions. -/
theorem length_iter (S : DOL α) (k : Nat) (s : List α) :
    (S.iter k s).length = (s.map fun c => (S.iter k [c]).length).sum := by
  induction s with
  | nil => simp [iter_nil]
  | cons a s ih => rw [iter_cons, List.length_append, ih]; simp

/-- Non-erasing systems never produce the empty string from a nonempty one. -/
theorem step_ne_nil (S : DOL α) (hne : ∀ a, S.rule a ≠ []) (s : List α) (hs : s ≠ []) :
    S.step s ≠ [] := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a s =>
    rw [step_cons]
    intro h
    exact hne a (List.append_eq_nil.mp h).1

theorem iter_ne_nil (S : DOL α) (hne : ∀ a, S.rule a ≠ []) (k : Nat) (s : List α)
    (hs : s ≠ []) : S.iter k s ≠ [] := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih _ (step_ne_nil S hne s hs)

theorem sum_map_le {β : Type} (l : List β) (f g : β → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (List.mem_cons_self a l)
    have := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    omega

/-- The partial rule table `R` agrees with the real system `T` on every symbol,
so far as it goes: each recorded body is a prefix of the true rule. -/
def Consistent [DecidableEq α] (R : Rules α) (T : DOL (Option α)) : Prop :=
  ∀ sym, (lookupR R sym).1 <+: T.rule sym

/-- **Key lemma.** `minexp` is a genuine lower bound on expansion length. -/
theorem minexp_le [DecidableEq α] (R : Rules α) (allowEmpty : Bool)
    (T : DOL (Option α)) (hc : Consistent R T)
    (hne : allowEmpty = false → ∀ a, T.rule a ≠ []) (k : Nat) (sym : Option α) :
    minexp R allowEmpty k sym ≤ (T.iter k [sym]).length := by
  induction k generalizing sym with
  | zero => simp [minexp, DOL.iter]
  | succ k ih =>
    have hp := hc sym
    obtain ⟨rest, hrest⟩ := hp
    rcases hb : lookupR R sym with ⟨body, closed⟩
    rw [hb] at hrest
    simp only at hrest
    -- the true expansion
    have hiter : T.iter (k + 1) [sym] = T.iter k body ++ T.iter k rest := by
      simp only [DOL.iter, step_cons, step_nil, List.append_nil]
      rw [← hrest, iter_append]
    simp only [minexp, hb]
    split
    · -- empty open body: bound is 0 or 1
      split
      · exact Nat.zero_le _
      · rename_i hae
        have hne' := hne (by cases allowEmpty <;> simp_all)
        have := iter_ne_nil T hne' (k + 1) [sym] (by simp)
        exact List.length_pos.mpr this
    · rw [hiter, List.length_append, length_iter]
      have := sum_map_le body (minexp R allowEmpty k) (fun c => (T.iter k [c]).length)
        (fun c _ => ih c)
      omega

/-! ### `need` is a lower bound, so pruning is safe -/

/-- The true number of leaves still owed by one frame, w.r.t. the real system `T`. -/
def frameRem (T : DOL (Option α)) (n : Nat) : Option α × Nat × Nat → Nat
  | (sym, d, i) => (T.iter (n - d) ((T.rule sym).drop i)).length

/-- The true number of leaves still owed by the whole stack. -/
def stackRem (T : DOL (Option α)) (n : Nat) (stack : List (Option α × Nat × Nat)) : Nat :=
  (stack.map (frameRem T n)).sum

theorem frameNeed_le [DecidableEq α] (R : Rules α) (ae : Bool) (T : DOL (Option α))
    (hc : Consistent R T) (hne : ae = false → ∀ a, T.rule a ≠ []) (n : Nat)
    (f : Option α × Nat × Nat) : frameNeed R ae n f ≤ frameRem T n f := by
  rcases f with ⟨sym, d, i⟩
  obtain ⟨rest, hrest⟩ := hc sym
  rcases hb : lookupR R sym with ⟨body, closed⟩
  rw [hb] at hrest
  simp only at hrest
  have hdrop : (T.rule sym).drop i = body.drop i ++ rest.drop (i - body.length) := by
    rw [← hrest, List.drop_append_eq_append_drop]
  have hsum : ((body.drop i).map (minexp R ae (n - d))).sum
      ≤ (T.iter (n - d) (body.drop i)).length := by
    rw [length_iter]
    exact sum_map_le _ _ _ (fun c _ => minexp_le R ae T hc hne (n - d) c)
  simp only [frameNeed, frameRem, hb]
  rw [hdrop, iter_append, List.length_append]
  split
  · rename_i h
    simp at h
    obtain ⟨⟨⟨hi, hbody⟩, -⟩, hae⟩ := h
    subst hi; subst hbody
    have hne' := hne hae
    have hrest_ne : rest ≠ [] := by
      intro h0; apply hne' sym; rw [← hrest, h0]; rfl
    have := List.length_pos.mpr (iter_ne_nil T hne' (n - d) (rest.drop 0) (by simpa using hrest_ne))
    simp [iter_nil]
    simpa using this
  · omega

theorem need_le [DecidableEq α] (R : Rules α) (ae : Bool) (T : DOL (Option α))
    (hc : Consistent R T) (hne : ae = false → ∀ a, T.rule a ≠ []) (n : Nat)
    (stack : List (Option α × Nat × Nat)) : need R ae n stack ≤ stackRem T n stack := by
  unfold need stackRem
  exact sum_map_le stack _ _ (fun f _ => frameNeed_le R ae T hc hne n f)

/-- **Pruning never cuts a live branch.** If the state is on the path of a real
system `T` (what's owed by the stack is exactly what's left of `w`), then the
`need`-based test in `search` does not fire. -/
theorem prune_safe [DecidableEq α] (w : List α) (n : Nat) (ae : Bool)
    (T : DOL (Option α)) (st : St α) (hc : Consistent st.rules T)
    (hne : ae = false → ∀ a, T.rule a ≠ [])
    (hinv : st.pos + stackRem T n st.stack = w.length) :
    ¬ (w.length < st.pos + need st.rules ae n st.stack) := by
  have := need_le st.rules ae T hc hne n st.stack
  omega

/-! ### Lifting a candidate system to `Option α` -/

/-- `none` is the pseudo-symbol whose rule is the axiom. -/
def lift (S : DOL α) : DOL (Option α) :=
  ⟨[none], fun o => match o with
    | none   => S.start.map some
    | some a => (S.rule a).map some⟩

theorem step_lift_map (S : DOL α) (s : List α) :
    (lift S).step (s.map some) = (S.step s).map some := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.map_cons, step_cons, ih, List.map_append]; rfl

theorem iter_lift_map (S : DOL α) (k : Nat) (s : List α) :
    (lift S).iter k (s.map some) = (S.iter k s).map some := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp only [DOL.iter, step_lift_map, ih]

theorem derive_eq_iter (S : DOL α) (n : Nat) : S.derive n = S.iter n S.start := by
  suffices h : ∀ n s, S.iter n (S.step s) = S.step (S.iter n s) by
    induction n with
    | zero => rfl
    | succ n ih => simp only [DOL.derive, DOL.iter, ih, h]
  intro n; induction n with
  | zero => intro s; rfl
  | succ n ih => intro s; simp only [DOL.iter, ih]

theorem iter_lift_none (S : DOL α) (j : Nat) :
    (lift S).iter (j + 1) [none] = (S.derive j).map some := by
  simp only [DOL.iter, step_cons, step_nil, List.append_nil]
  show (lift S).iter j (S.start.map some) = _
  rw [iter_lift_map, derive_eq_iter]

/-- Symbols of `T` at levels `0..n` (everything that gets rewritten). -/
def usedT (T : DOL (Option α)) (n : Nat) : List (Option α) :=
  (List.range (n + 1)).flatMap fun j => T.iter j [none]

theorem mem_rule_mem_step (S : DOL α) (s : List α) (a : α) (ha : a ∈ s) (x : α)
    (hx : x ∈ S.rule a) : x ∈ S.step s := by
  induction s with
  | nil => exact absurd ha (List.not_mem_nil a)
  | cons b s ih =>
    rw [step_cons, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h
    · exact Or.inl hx
    · exact Or.inr (ih h)

/-! ### Enumeration soundness: what `allSystems` produces is bounded -/

theorem mem_words (sigma : List α) (k : Nat) (v : List α) (h : v ∈ words sigma k) :
    v.length = k ∧ ∀ x ∈ v, x ∈ sigma := by
  induction k generalizing v with
  | zero => simp [words] at h; subst h; simp
  | succ k ih =>
    simp only [words, List.mem_flatMap, List.mem_map] at h
    obtain ⟨u, hu, a, ha, rfl⟩ := h
    obtain ⟨hl, hs⟩ := ih u hu
    refine ⟨by simp [hl], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hs x hx

theorem mem_wordsUpTo (sigma : List α) (lo hi : Nat) (v : List α)
    (h : v ∈ wordsUpTo sigma lo hi) :
    lo ≤ v.length ∧ v.length ≤ hi ∧ ∀ x ∈ v, x ∈ sigma := by
  simp only [wordsUpTo, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨k, ⟨hk, hlo⟩, hv⟩ := h
  obtain ⟨hl, hs⟩ := mem_words sigma k v hv
  subst hl
  exact ⟨by simpa using hlo, by omega, hs⟩

theorem mem_ruleTables [DecidableEq α] (sigma : List α) (bodies : List (List α))
    (t : List (α × List α)) (h : t ∈ ruleTables sigma bodies) :
    ∀ a ∈ sigma, ∃ b ∈ bodies, t.lookup a = some b := by
  induction sigma generalizing t with
  | nil => intro a ha; exact absurd ha (List.not_mem_nil a)
  | cons c sigma ih =>
    simp only [ruleTables, List.foldr_cons, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, hb, t', ht', rfl⟩ := h
    intro a ha
    by_cases hac : a = c
    · subst hac; exact ⟨b, hb, by simp [List.lookup]⟩
    · rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd rfl hac
      · obtain ⟨b', hb', hl⟩ := ih t' ht' a ha'
        refine ⟨b', hb', ?_⟩
        have : (a == c) = false := beq_false_of_ne hac
        simp [List.lookup, hl, this]

/-- Everything we need to know about a candidate drawn from `allSystems`. -/
structure Bounded [DecidableEq α] (sigma : List α) (B : Bounds) (S : DOL α) : Prop where
  start_len_lo : 1 ≤ S.start.length
  start_len_hi : S.start.length ≤ B.maxAxiom
  start_mem    : ∀ x ∈ S.start, x ∈ sigma
  rule_len_lo  : ∀ a ∈ sigma, (if B.allowEmpty then 0 else 1) ≤ (S.rule a).length
  rule_len_hi  : ∀ a ∈ sigma, (S.rule a).length ≤ B.maxRule
  rule_mem     : ∀ a ∈ sigma, ∀ x ∈ S.rule a, x ∈ sigma
  rule_default : ∀ a, a ∉ sigma → S.rule a = [a]

theorem lookup_ruleTables_none [DecidableEq α] (sigma : List α) (bodies : List (List α))
    (t : List (α × List α)) (h : t ∈ ruleTables sigma bodies) :
    ∀ a, a ∉ sigma → t.lookup a = none := by
  induction sigma generalizing t with
  | nil =>
    simp [ruleTables] at h; subst h; intro a _; rfl
  | cons c sigma ih =>
    simp only [ruleTables, List.foldr_cons, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, hb, t', ht', rfl⟩ := h
    intro a ha
    have hac : a ≠ c := fun h => ha (h ▸ List.mem_cons_self _ _)
    have : (a == c) = false := beq_false_of_ne hac
    simp only [List.lookup, this]
    exact ih t' ht' a (fun h => ha (List.mem_cons_of_mem _ h))

theorem bounded_of_mem_allSystems [DecidableEq α] (sigma : List α) (B : Bounds)
    (P : Presented α) (h : P ∈ allSystems sigma B) : Bounded sigma B P.toDOL := by
  simp only [allSystems, List.mem_flatMap, List.mem_map] at h
  obtain ⟨ax, hax, t, ht, rfl⟩ := h
  obtain ⟨h1, h2, h3⟩ := mem_wordsUpTo _ _ _ _ hax
  have hr := mem_ruleTables sigma _ t ht
  have hd := lookup_ruleTables_none sigma _ t ht
  have key : ∀ a ∈ sigma, (if B.allowEmpty then 0 else 1) ≤ ((Presented.toDOL (ax, t)).rule a).length
      ∧ ((Presented.toDOL (ax, t)).rule a).length ≤ B.maxRule
      ∧ ∀ x ∈ (Presented.toDOL (ax, t)).rule a, x ∈ sigma := by
    intro a ha
    obtain ⟨b, hb, hl⟩ := hr a ha
    obtain ⟨b1, b2, b3⟩ := mem_wordsUpTo _ _ _ _ hb
    simp only [Presented.toDOL, hl]
    exact ⟨b1, b2, b3⟩
  refine ⟨h1, h2, h3, fun a ha => (key a ha).1, fun a ha => (key a ha).2.1,
    fun a ha => (key a ha).2.2, ?_⟩
  intro a ha
  simp only [Presented.toDOL, hd a ha]

/-! ### Completeness: stack semantics, invariant, measure -/

abbrev Frame (α : Type) := Option α × Nat × Nat

theorem iter_step_comm (S : DOL α) (k : Nat) (s : List α) :
    S.iter (k + 1) s = S.step (S.iter k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp only [DOL.iter] at ih ⊢; rw [ih]

/-- Leaves still owed by one frame, in order. -/
def frameLeaves (T : DOL (Option α)) (n : Nat) : Frame α → List (Option α)
  | (sym, d, i) => T.iter (n - d) ((T.rule sym).drop i)

def stackLeaves (T : DOL (Option α)) (n : Nat) (stack : List (Frame α)) : List (Option α) :=
  stack.flatMap (frameLeaves T n)

/-- Interior nodes (depths `d+1 .. n`) not yet visited below one frame. -/
def framePend (T : DOL (Option α)) (n : Nat) : Frame α → List (Option α)
  | (sym, d, i) => (List.range (n - d)).flatMap fun j => T.iter j ((T.rule sym).drop i)

def stackPend (T : DOL (Option α)) (n : Nat) (stack : List (Frame α)) : List (Option α) :=
  stack.flatMap (framePend T n)

/-- Nodes not yet *finished*: the frame's own symbol plus its pending subtree. -/
def stackNodes (T : DOL (Option α)) (n : Nat) (stack : List (Frame α)) : List (Option α) :=
  stack.flatMap fun f => f.1 :: framePend T n f

def allSyms (sigma : List α) : List (Option α) := none :: sigma.map some

/-- How much of each rule is still unwritten. -/
def slack [DecidableEq α] (sigma : List α) (T : DOL (Option α)) (R : Rules α) : Nat :=
  ((allSyms sigma).map fun x => (T.rule x).length - (lookupR R x).1.length).sum

def measure [DecidableEq α] (sigma : List α) (n : Nat) (T : DOL (Option α)) (st : St α) : Nat :=
  3 * (stackPend T n st.stack).length + 2 * st.stack.length
    + (stackLeaves T n st.stack).length + slack sigma T st.rules

/-- The key the search must emit for the lifted system `T`. -/
def expectedKey [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (T : DOL (Option α)) :
    Presented α :=
  ((T.rule none).filterMap id,
   sigma.map fun a =>
     (a, if some a ∈ usedT T n then (T.rule (some a)).filterMap id else defaultBody B a))

/-- What we know about a lifted bounded candidate. -/
structure TOk [DecidableEq α] (sigma : List α) (B : Bounds) (T : DOL (Option α)) : Prop where
  mem : ∀ x ∈ allSyms sigma, ∀ y ∈ T.rule x, y ∈ sigma.map some
  len : ∀ x ∈ allSyms sigma, (T.rule x).length ≤ (if x = none then B.maxAxiom else B.maxRule)
  ne  : B.allowEmpty = false → ∀ x, T.rule x ≠ []
  ne' : T.rule none ≠ []

/-- The search-state invariant along the path of `T`. -/
structure OnPath [DecidableEq α] (w : List α) (n : Nat) (T : DOL (Option α)) (st : St α) : Prop where
  leaves      : stackLeaves T n st.stack = (w.map some).drop st.pos
  closed_eq   : ∀ x, (lookupR st.rules x).2 = true → (lookupR st.rules x).1 = T.rule x
  open_prefix : ∀ x, (lookupR st.rules x).1 <+: T.rule x
  idx         : ∀ f ∈ st.stack, f.2.2 ≤ (lookupR st.rules f.1).1.length
  level       : ∀ f ∈ st.stack, f.2.1 ≤ n ∧ f.1 ∈ T.iter f.2.1 [none]
  closed_used : ∀ x, (lookupR st.rules x).2 = true → x ∈ usedT T n
  used        : ∀ x ∈ usedT T n, (lookupR st.rules x).2 = true ∨ x ∈ stackNodes T n st.stack
  pos_le      : st.pos ≤ w.length

/-! #### small lemmas -/

theorem lookupR_cons_self [DecidableEq α] (R : Rules α) (x : Option α) (v) :
    lookupR ((x, v) :: R) x = v := by
  simp [lookupR, List.lookup]

theorem lookupR_cons_ne [DecidableEq α] (R : Rules α) (x y : Option α) (v) (h : y ≠ x) :
    lookupR ((x, v) :: R) y = lookupR R y := by
  have : (y == x) = false := beq_false_of_ne h
  simp [lookupR, List.lookup, this]

theorem mem_usedT_of_level (T : DOL (Option α)) (n d : Nat) (hd : d ≤ n) (x : Option α)
    (hx : x ∈ T.iter d [none]) : x ∈ usedT T n := by
  simp only [usedT, List.mem_flatMap, List.mem_range]
  exact ⟨d, by omega, hx⟩

theorem none_mem_usedT (T : DOL (Option α)) (n : Nat) : none ∈ usedT T n :=
  mem_usedT_of_level T n 0 (Nat.zero_le _) none (by simp [DOL.iter])

theorem mem_iter_syms [DecidableEq α] (sigma : List α) (B : Bounds) (T : DOL (Option α))
    (hT : TOk sigma B T) (d : Nat) (x : Option α) (hx : x ∈ T.iter d [none]) :
    x ∈ allSyms sigma := by
  induction d generalizing x with
  | zero => simp [DOL.iter] at hx; subst hx; simp [allSyms]
  | succ d ih =>
    rw [iter_step_comm] at hx
    -- x ∈ step (iter d [none]) : pick the parent
    have : ∀ s : List (Option α), (∀ y ∈ s, y ∈ allSyms sigma) → x ∈ T.step s → x ∈ allSyms sigma := by
      intro s hs hxs
      induction s with
      | nil => simp at hxs
      | cons a s ihs =>
        rw [step_cons, List.mem_append] at hxs
        rcases hxs with h | h
        · exact List.mem_cons_of_mem _ (hT.mem a (hs a (List.mem_cons_self _ _)) x h)
        · exact ihs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) h
    exact this _ (fun y hy => ih y hy) hx

theorem mem_rule_mem_level (T : DOL (Option α)) (d : Nat) (sym : Option α)
    (hs : sym ∈ T.iter d [none]) (c : Option α) (hc : c ∈ T.rule sym) :
    c ∈ T.iter (d + 1) [none] := by
  rw [iter_step_comm]; exact mem_rule_mem_step T _ sym hs c hc

theorem flatMap_range_succ {β : Type} (m : Nat) (f : Nat → List β) :
    (List.range (m + 1)).flatMap f = f 0 ++ (List.range m).flatMap fun j => f (j + 1) := by
  rw [List.range_succ_eq_map]
  simp [List.flatMap_cons, List.flatMap_map, Function.comp]

theorem length_flatMap_append {β γ : Type} (l : List β) (f g : β → List γ) :
    (l.flatMap fun j => f j ++ g j).length = (l.flatMap f).length + (l.flatMap g).length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.length_append, ih]; omega

theorem sum_map_lt {β : Type} (l : List β) (f g : β → Nat) (h : ∀ x ∈ l, g x ≤ f x)
    (x₀ : β) (hx₀ : x₀ ∈ l) (hlt : g x₀ < f x₀) : (l.map g).sum < (l.map f).sum := by
  induction l with
  | nil => exact absurd hx₀ (List.not_mem_nil _)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hle := sum_map_le l g f (fun x hx => h x (List.mem_cons_of_mem a hx))
    rcases List.mem_cons.mp hx₀ with rfl | hx
    · omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem a hx)) hx
      have := h a (List.mem_cons_self a l)
      omega

/-- `drop i` of a list with a known prefix, at an index inside the prefix. -/
theorem drop_of_prefix (body rule : List β) (hp : body <+: rule) (i : Nat)
    (hi : i < body.length) : rule.drop i = body[i] :: rule.drop (i + 1) := by
  obtain ⟨rest, rfl⟩ := hp
  rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem drop_eq_cons_getElem? (l : List β) (p : Nat) (a : β) (t : List β)
    (h : l.drop p = a :: t) : l[p]? = some a ∧ l.drop (p + 1) = t := by
  have hp : p < l.length := by
    apply Nat.lt_of_not_le
    intro hle
    rw [List.drop_eq_nil_of_le hle] at h
    exact List.noConfusion h
  rw [List.drop_eq_getElem_cons hp] at h
  cases h
  exact ⟨List.getElem?_eq_getElem hp, rfl⟩

/-! #### unfolding lemmas -/

@[simp] theorem stackLeaves_nil (T : DOL (Option α)) (n : Nat) : stackLeaves T n [] = [] := rfl
@[simp] theorem stackLeaves_cons (T : DOL (Option α)) (n : Nat) (f : Frame α) (rest) :
    stackLeaves T n (f :: rest) = frameLeaves T n f ++ stackLeaves T n rest := List.flatMap_cons ..
@[simp] theorem stackPend_nil (T : DOL (Option α)) (n : Nat) : stackPend T n [] = [] := rfl
@[simp] theorem stackPend_cons (T : DOL (Option α)) (n : Nat) (f : Frame α) (rest) :
    stackPend T n (f :: rest) = framePend T n f ++ stackPend T n rest := List.flatMap_cons ..
@[simp] theorem stackNodes_nil (T : DOL (Option α)) (n : Nat) : stackNodes T n [] = [] := rfl
@[simp] theorem stackNodes_cons (T : DOL (Option α)) (n : Nat) (f : Frame α) (rest) :
    stackNodes T n (f :: rest) = f.1 :: framePend T n f ++ stackNodes T n rest := List.flatMap_cons ..
@[simp] theorem frameLeaves_mk (T : DOL (Option α)) (n : Nat) (sym d i) :
    frameLeaves T n (sym, d, i) = T.iter (n - d) ((T.rule sym).drop i) := rfl
@[simp] theorem framePend_mk (T : DOL (Option α)) (n : Nat) (sym d i) :
    framePend T n (sym, d, i) = (List.range (n - d)).flatMap fun j => T.iter j ((T.rule sym).drop i) := rfl

@[simp] theorem step_single (S : DOL α) (c : α) : S.step [c] = S.rule c := by
  simp [step_cons]

theorem iter_succ_single (T : DOL (Option α)) (m : Nat) (c : Option α) :
    T.iter (m + 1) [c] = T.iter m (T.rule c) := by
  simp [DOL.iter]

theorem frameRem_eq (T : DOL (Option α)) (n : Nat) (f : Frame α) :
    frameRem T n f = (frameLeaves T n f).length := by
  rcases f with ⟨s, d, i⟩; rfl

theorem stackRem_eq_length (T : DOL (Option α)) (n : Nat) (stack : List (Frame α)) :
    stackRem T n stack = (stackLeaves T n stack).length := by
  induction stack with
  | nil => rfl
  | cons f rest ih =>
    simp only [stackRem, stackLeaves, List.map_cons, List.sum_cons, List.flatMap_cons,
      List.length_append] at ih ⊢
    rw [ih, frameRem_eq]

theorem slack_congr [DecidableEq α] (sigma : List α) (T : DOL (Option α)) (R R' : Rules α)
    (h : ∀ x, (lookupR R' x).1 = (lookupR R x).1) : slack sigma T R' = slack sigma T R := by
  unfold slack
  congr 1
  apply List.map_congr_left
  intro x _
  rw [h x]

/-- Reading the next owed leaf off the invariant. -/
theorem next_leaf (w : List α) (pos : Nat) (c : Option α) (t : List (Option α))
    (h : (w.map some).drop pos = c :: t) :
    ∃ c', w[pos]? = some c' ∧ c = some c' ∧ (w.map some).drop (pos + 1) = t ∧ pos < w.length := by
  obtain ⟨h1, h2⟩ := drop_eq_cons_getElem? _ _ _ _ h
  rw [List.getElem?_map] at h1
  have hlt : pos < w.length := by
    apply Nat.lt_of_not_le; intro hle
    rw [List.getElem?_eq_none hle] at h1
    exact Option.noConfusion h1
  cases hw : w[pos]? with
  | none => rw [hw] at h1; exact Option.noConfusion h1
  | some c' =>
    rw [hw] at h1
    exact ⟨c', rfl, (Option.some.inj h1).symm, h2, hlt⟩

/-! #### Transition A: match a leaf (depth `n`) -/

theorem step_leaf [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (T : DOL (Option α))
    (R : Rules α) (sym : Option α) (i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hp : OnPath w n T ⟨R, (sym, n, i) :: rest, pos⟩)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i < body.length) :
    ∃ c, w[pos]? = some c ∧ body[i] = some c ∧
      OnPath w n T ⟨R, (sym, n, i + 1) :: rest, pos + 1⟩ ∧
      measure sigma n T ⟨R, (sym, n, i + 1) :: rest, pos + 1⟩ + 1
        = measure sigma n T ⟨R, (sym, n, i) :: rest, pos⟩ := by
  have hpre : body <+: T.rule sym := by have := hp.open_prefix sym; rwa [hb] at this
  have hdrop := drop_of_prefix body (T.rule sym) hpre i hi
  have hl := hp.leaves
  simp only [stackLeaves_cons, frameLeaves_mk, Nat.sub_self, DOL.iter, hdrop, List.cons_append] at hl
  obtain ⟨c, hw, hc, hrest, hlt⟩ := next_leaf w pos _ _ hl.symm
  refine ⟨c, hw, hc, ?_, ?_⟩
  · refine ⟨?_, hp.closed_eq, hp.open_prefix, ?_, ?_, hp.closed_used, ?_, ?_⟩
    · simp only [stackLeaves_cons, frameLeaves_mk, Nat.sub_self, DOL.iter]; exact hrest.symm
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simp only [hb]; exact hi
      · exact hp.idx f (List.mem_cons_of_mem _ hf)
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hp.level (sym, n, i) (List.mem_cons_self _ _)
      · exact hp.level f (List.mem_cons_of_mem _ hf)
    · intro x hx
      have := hp.used x hx
      simpa [stackNodes_cons, framePend_mk, Nat.sub_self] using this
    · show pos + 1 ≤ w.length; omega
  · simp only [measure, stackPend_cons, framePend_mk, Nat.sub_self, List.range_zero,
      List.flatMap_nil, stackLeaves_cons, frameLeaves_mk, DOL.iter, hdrop, List.length_append,
      List.length_cons, List.nil_append]
    omega

/-! #### Transition B: expand an interior child (depth `d < n`) -/

/-- Pending nodes of a frame whose next child is `c`, split into the child's own
subtree plus the frame's remaining children. -/
theorem framePend_split (T : DOL (Option α)) (m : Nat) (c : Option α) (X : List (Option α)) :
    (List.range (m + 1)).flatMap (fun j => T.iter j (c :: X))
      = (List.range (m + 1)).flatMap (fun j => T.iter j [c] ++ T.iter j X) := by
  congr 1; funext j; exact iter_cons T j c X

theorem framePend_split' (T : DOL (Option α)) (k : Nat) (c : Option α) (X : List (Option α)) :
    (List.range k).flatMap (fun j => T.iter j (c :: X))
      = (List.range k).flatMap (fun j => T.iter j [c] ++ T.iter j X) := by
  congr 1; funext j; exact iter_cons T j c X

theorem length_pend_single (T : DOL (Option α)) (m : Nat) (c : Option α) :
    ((List.range (m + 1)).flatMap fun j => T.iter j [c]).length
      = 1 + ((List.range m).flatMap fun j => T.iter j (T.rule c)).length := by
  rw [flatMap_range_succ]
  simp only [DOL.iter, List.length_append, List.length_singleton, step_single]

theorem mem_pend_single (T : DOL (Option α)) (m : Nat) (c x : Option α)
    (hx : x ∈ (List.range (m + 1)).flatMap fun j => T.iter j [c]) :
    x = c ∨ x ∈ (List.range m).flatMap fun j => T.iter j (T.rule c) := by
  rw [flatMap_range_succ] at hx
  simp only [DOL.iter, List.mem_append, List.mem_singleton, step_single] at hx
  exact hx

theorem step_expand [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (T : DOL (Option α))
    (R : Rules α) (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hp : OnPath w n T ⟨R, (sym, d, i) :: rest, pos⟩)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i < body.length) (hd : d ≠ n) :
    OnPath w n T ⟨R, (body[i], d + 1, 0) :: (sym, d, i + 1) :: rest, pos⟩ ∧
      measure sigma n T ⟨R, (body[i], d + 1, 0) :: (sym, d, i + 1) :: rest, pos⟩ + 1
        = measure sigma n T ⟨R, (sym, d, i) :: rest, pos⟩ := by
  have hpre : body <+: T.rule sym := by have := hp.open_prefix sym; rwa [hb] at this
  have hdrop := drop_of_prefix body (T.rule sym) hpre i hi
  have hlev := hp.level (sym, d, i) (List.mem_cons_self _ _)
  have hdn : d < n := Nat.lt_of_le_of_ne hlev.1 hd
  have hm : n - d = (n - (d + 1)) + 1 := by omega
  have hcmem : body[i] ∈ T.rule sym := hpre.subset (List.getElem_mem hi)
  generalize hc : body[i] = c at hdrop hcmem ⊢
  generalize hm' : n - (d + 1) = m at hm ⊢
  have hleaves : T.iter (n - d) ((T.rule sym).drop i)
      = T.iter m (T.rule c) ++ T.iter (n - d) ((T.rule sym).drop (i + 1)) := by
    rw [hdrop, iter_cons, hm, iter_succ_single]
  have hpend : (List.range (n - d)).flatMap (fun j => T.iter j ((T.rule sym).drop i))
      = (List.range (n - d)).flatMap (fun j => T.iter j [c] ++ T.iter j ((T.rule sym).drop (i + 1))) := by
    rw [hdrop, framePend_split' ]
  constructor
  · refine ⟨?_, hp.closed_eq, hp.open_prefix, ?_, ?_, hp.closed_used, ?_, hp.pos_le⟩
    · have hl := hp.leaves
      simp only [stackLeaves_cons, frameLeaves_mk] at hl ⊢
      rw [hleaves, List.append_assoc] at hl
      rw [← hl]; simp [List.drop_zero, hm']
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact Nat.zero_le _
      rcases List.mem_cons.mp hf with rfl | hf
      · simp only [hb]; exact hi
      · exact hp.idx f (List.mem_cons_of_mem _ hf)
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨show d + 1 ≤ n by omega, mem_rule_mem_level T d sym hlev.2 c hcmem⟩
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hlev
      · exact hp.level f (List.mem_cons_of_mem _ hf)
    · intro x hx
      rcases hp.used x hx with h | h
      · exact Or.inl h
      · right
        simp only [stackNodes_cons, framePend_mk, List.mem_cons, List.mem_append] at h ⊢
        rcases h with (rfl | h) | h
        · exact Or.inr (Or.inl (Or.inl rfl))
        · rw [hpend, List.mem_flatMap] at h
          obtain ⟨j, hj, hxj⟩ := h
          rw [List.mem_append] at hxj
          rcases hxj with hxj | hxj
          · have := mem_pend_single T m c x (by rw [← hm]; exact List.mem_flatMap.mpr ⟨j, hj, hxj⟩)
            rcases this with rfl | this
            · exact Or.inl (Or.inl rfl)
            · exact Or.inl (Or.inr (by rw [hm']; simpa [List.drop_zero] using this))
          · exact Or.inr (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨j, hj, hxj⟩)))
        · exact Or.inr (Or.inr h)
  · simp only [measure, stackPend_cons, framePend_mk, stackLeaves_cons, frameLeaves_mk,
      List.length_append, List.length_cons, List.drop_zero, hm']
    have e1 : ((List.range (n - d)).flatMap fun j => T.iter j ((T.rule sym).drop i)).length
        = 1 + ((List.range m).flatMap fun j => T.iter j (T.rule c)).length
          + ((List.range (n - d)).flatMap fun j => T.iter j ((T.rule sym).drop (i + 1))).length := by
      rw [hpend, length_flatMap_append, hm, length_pend_single]
    have e2 : (T.iter (n - d) ((T.rule sym).drop i)).length
        = (T.iter m (T.rule c)).length + (T.iter (n - d) ((T.rule sym).drop (i + 1))).length := by
      rw [hleaves, List.length_append]
    omega

theorem flatMap_fun_nil {β γ : Type} (l : List β) :
    (l.flatMap fun _ => ([] : List γ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-! #### Transition C: pop a finished node (rule complete and closed) -/

theorem step_pop [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (T : DOL (Option α))
    (R R' : Rules α) (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hp : OnPath w n T ⟨R, (sym, d, i) :: rest, pos⟩)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i = body.length) (hbr : body = T.rule sym)
    (hself : lookupR R' sym = (body, true))
    (hother : ∀ y, y ≠ sym → lookupR R' y = lookupR R y) :
    OnPath w n T ⟨R', rest, pos⟩ ∧
      measure sigma n T ⟨R', rest, pos⟩ + 2 = measure sigma n T ⟨R, (sym, d, i) :: rest, pos⟩ := by
  have hdrop : (T.rule sym).drop i = [] := by rw [hi, hbr, List.drop_length]
  have hlev := hp.level (sym, d, i) (List.mem_cons_self _ _)
  have hsym_used : sym ∈ usedT T n := mem_usedT_of_level T n d hlev.1 sym hlev.2
  have hlk : ∀ x, (lookupR R' x).1 = (lookupR R x).1 := by
    intro x
    by_cases hx : x = sym
    · subst hx; rw [hself, hb]
    · rw [hother x hx]
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hp.pos_le⟩
    · have := hp.leaves
      simpa [hdrop, iter_nil] using this
    · intro x hx
      by_cases hxs : x = sym
      · subst hxs; rw [hself]; exact hbr
      · rw [hother x hxs] at hx ⊢; exact hp.closed_eq x hx
    · intro x
      by_cases hxs : x = sym
      · subst hxs; rw [hself]; exact ⟨[], by rw [List.append_nil, hbr]⟩
      · rw [hother x hxs]; exact hp.open_prefix x
    · intro f hf
      rw [hlk]; exact hp.idx f (List.mem_cons_of_mem _ hf)
    · intro f hf; exact hp.level f (List.mem_cons_of_mem _ hf)
    · intro x hx
      by_cases hxs : x = sym
      · subst hxs; exact hsym_used
      · rw [hother x hxs] at hx; exact hp.closed_used x hx
    · intro x hx
      rcases hp.used x hx with h | h
      · left
        by_cases hxs : x = sym
        · subst hxs; rw [hself]
        · rw [hother x hxs]; exact h
      · simp [stackNodes_cons, framePend_mk, hdrop, iter_nil, flatMap_fun_nil] at h
        rcases h with rfl | h
        · left; rw [hself]
        · right; exact h
  · simp only [measure, stackPend_cons, framePend_mk, stackLeaves_cons, frameLeaves_mk, hdrop,
      iter_nil, flatMap_fun_nil, List.append_eq, List.nil_append, List.length_cons,
      slack_congr sigma T R R' hlk]
    omega

/-! #### Transition D: extend an open rule by its next true symbol -/

theorem step_extend [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (T : DOL (Option α)) (hT : TOk sigma B T)
    (R : Rules α) (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hp : OnPath w n T ⟨R, (sym, d, i) :: rest, pos⟩)
    (body : List (Option α)) (hb : lookupR R sym = (body, false))
    (hi : i = body.length) (hbr : body ≠ T.rule sym) :
    ∃ c, body.length < (T.rule sym).length ∧ (T.rule sym)[body.length]? = some c ∧
      body.length < (if sym = none then B.maxAxiom else B.maxRule) ∧
      c ∈ sigma.map some ∧
      (d = n → ∃ c', w[pos]? = some c' ∧ c = some c') ∧
      OnPath w n T ⟨(sym, (body ++ [c], false)) :: R, (sym, d, i) :: rest, pos⟩ ∧
      measure sigma n T ⟨(sym, (body ++ [c], false)) :: R, (sym, d, i) :: rest, pos⟩
        < measure sigma n T ⟨R, (sym, d, i) :: rest, pos⟩ := by
  have hpre : body <+: T.rule sym := by have := hp.open_prefix sym; rwa [hb] at this
  obtain ⟨tail, htail⟩ := hpre
  have hlev := hp.level (sym, d, i) (List.mem_cons_self _ _)
  have hsyms : sym ∈ allSyms sigma := mem_iter_syms sigma B T hT d sym hlev.2
  cases tail with
  | nil => exact absurd (by rw [← htail, List.append_nil]) hbr
  | cons c tail' =>
  have hlen : body.length < (T.rule sym).length := by rw [← htail]; simp
  have hcmem : c ∈ T.rule sym := by rw [← htail]; simp
  have hdropi : (T.rule sym).drop i = c :: tail' := by rw [hi, ← htail, List.drop_left]
  refine ⟨c, hlen, ?_, ?_, hT.mem sym hsyms c hcmem, ?_, ?_, ?_⟩
  · rw [← htail, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; simp
  · have := hT.len sym hsyms; omega
  · intro hd
    subst hd
    have hl := hp.leaves
    simp only [stackLeaves_cons, frameLeaves_mk, Nat.sub_self, DOL.iter, hdropi,
      List.cons_append] at hl
    obtain ⟨c', hw, hc, -, -⟩ := next_leaf w pos _ _ hl.symm
    exact ⟨c', hw, hc⟩
  · refine ⟨hp.leaves, ?_, ?_, ?_, hp.level, ?_, ?_, hp.pos_le⟩
    · intro x hx
      by_cases hxs : x = sym
      · subst hxs; rw [lookupR_cons_self] at hx; exact absurd hx (by simp)
      · rw [lookupR_cons_ne R sym x _ hxs] at hx ⊢; exact hp.closed_eq x hx
    · intro x
      by_cases hxs : x = sym
      · subst hxs; rw [lookupR_cons_self]
        exact ⟨tail', by rw [List.append_assoc, ← htail]; rfl⟩
      · rw [lookupR_cons_ne R sym x _ hxs]; exact hp.open_prefix x
    · intro f hf
      have := hp.idx f hf
      by_cases hxs : f.1 = sym
      · rw [hxs, lookupR_cons_self]; rw [hxs, hb] at this; simp only at this; simp; omega
      · rw [lookupR_cons_ne R sym _ _ hxs]; exact this
    · intro x hx
      by_cases hxs : x = sym
      · subst hxs; rw [lookupR_cons_self] at hx; exact absurd hx (by simp)
      · rw [lookupR_cons_ne R sym x _ hxs] at hx; exact hp.closed_used x hx
    · intro x hx
      rcases hp.used x hx with h | h
      · by_cases hxs : x = sym
        · subst hxs; rw [hb] at h; exact absurd h (by simp)
        · left; rw [lookupR_cons_ne R sym x _ hxs]; exact h
      · right; exact h
  · simp only [measure]
    have : slack sigma T ((sym, (body ++ [c], false)) :: R) < slack sigma T R := by
      unfold slack
      apply sum_map_lt _ _ _ _ sym hsyms
      · rw [lookupR_cons_self, hb]; simp; omega
      · intro x _
        by_cases hxs : x = sym
        · subst hxs; rw [lookupR_cons_self, hb]; simp; omega
        · rw [lookupR_cons_ne R sym x _ hxs]; exact Nat.le_refl _
    omega

/-! #### Terminal state: the search emits exactly the expected key -/

theorem terminal [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (T : DOL (Option α)) (R : Rules α) (pos : Nat) (hp : OnPath w n T ⟨R, [], pos⟩) :
    pos = w.length ∧ toKey sigma B R = expectedKey sigma B n T := by
  have hl := hp.leaves
  simp only [stackLeaves_nil] at hl
  have hpos : pos = w.length := by
    have h1 := congrArg List.length hl
    rw [List.length_drop, List.length_map, List.length_nil] at h1
    have h2 := hp.pos_le
    simp only at h2
    omega
  refine ⟨hpos, ?_⟩
  have hclosed : ∀ x ∈ usedT T n, (lookupR R x).2 = true := by
    intro x hx
    rcases hp.used x hx with h | h
    · exact h
    · simp at h
  unfold toKey expectedKey
  have hax : (lookupR R none).1 = T.rule none :=
    hp.closed_eq none (hclosed none (none_mem_usedT T n))
  rw [hax]
  congr 2
  funext a
  rcases hb : lookupR R (some a) with ⟨body, closed⟩
  simp only
  by_cases hu : some a ∈ usedT T n
  · have hc := hclosed _ hu
    rw [hb] at hc
    simp only at hc
    subst hc
    have he := hp.closed_eq (some a) (by rw [hb])
    rw [hb] at he
    simp only at he
    simp [hu, he]
  · have : closed = false := by
      cases closed
      · rfl
      · exact absurd (hp.closed_used (some a) (by rw [hb])) hu
    subst this
    simp [hu]

/-! #### The completeness theorem -/

theorem search_complete [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (T : DOL (Option α)) (hT : TOk sigma B T) :
    ∀ fuel (st : St α), OnPath w n T st → measure sigma n T st < fuel →
      expectedKey sigma B n T ∈ search w n sigma B fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _ h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro st hp hμ
    rcases st with ⟨R, stack, pos⟩
    cases stack with
    | nil =>
      obtain ⟨hpos, hkey⟩ := terminal w n sigma B T R pos hp
      simp only [search, hpos, ite_true, hkey, List.mem_singleton]
    | cons f rest =>
      rcases f with ⟨sym, d, i⟩
      have hinv : pos + stackRem T n ((sym, d, i) :: rest) = w.length := by
        rw [stackRem_eq_length, hp.leaves, List.length_drop, List.length_map]
        have h2 := hp.pos_le
        simp only at h2
        show pos + (w.length - pos) = w.length
        omega
      have hprune := prune_safe w n B.allowEmpty T ⟨R, (sym, d, i) :: rest, pos⟩
        hp.open_prefix hT.ne hinv
      rcases hb : lookupR R sym with ⟨body, closed⟩
      simp only [search, hb]
      rw [ite_eq_right_right hprune]
      by_cases hi : i < body.length
      · rw [dite_eq_left hi]
        by_cases hd : d = n
        · subst hd
          obtain ⟨c, hw, hc, hp', hμ'⟩ := step_leaf w d sigma T R sym i rest pos hp body closed hb hi
          rw [ite_eq_left rfl, hw]
          simp only [hc, if_true]
          exact ih _ hp' (by omega)
        · rw [ite_eq_right hd]
          obtain ⟨hp', hμ'⟩ := step_expand w n sigma T R sym d i rest pos hp body closed hb hi hd
          exact ih _ hp' (by omega)
      · rw [dite_eq_right hi]
        have hidx := hp.idx (sym, d, i) (List.mem_cons_self _ _)
        rw [hb] at hidx
        simp only at hidx
        have hi' : i = body.length := by omega
        cases closed with
        | true =>
          rw [ite_eq_left rfl]
          have hbr : body = T.rule sym := by
            have := hp.closed_eq sym (by rw [hb]); rwa [hb] at this
          obtain ⟨hp', hμ'⟩ := step_pop w n sigma T R R sym d i rest pos hp body true hb hi' hbr hb
            (fun y _ => rfl)
          exact ih _ hp' (by omega)
        | false =>
          rw [ite_eq_right Bool.false_ne_true]
          by_cases hbr : body = T.rule sym
          · have hcond : (decide (1 ≤ body.length) || (B.allowEmpty && sym.isSome)) = true := by
              cases hae : B.allowEmpty
              · have hne := hT.ne hae sym
                rw [← hbr] at hne
                have := List.length_pos.mpr hne
                simp; omega
              · cases sym with
                | none =>
                  have hne : body ≠ [] := by rw [hbr]; exact hT.ne'
                  have := List.length_pos.mpr hne
                  simp; omega
                | some a => simp
            simp only [hcond, if_true]
            apply List.mem_append_left
            obtain ⟨hp', hμ'⟩ := step_pop w n sigma T R ((sym, (body, true)) :: R) sym d i rest pos
              hp body false hb hi' hbr (lookupR_cons_self R sym _)
              (fun y hy => lookupR_cons_ne R sym y _ hy)
            exact ih _ hp' (by omega)
          · obtain ⟨c, hlen, hget, hmax, hcs, hdn, hp', hμ'⟩ :=
              step_extend w n sigma B T hT R sym d i rest pos hp body hb hi' hbr
            apply List.mem_append_right
            rw [ite_eq_left hmax, List.mem_flatMap]
            refine ⟨c, ?_, ih _ hp' (by omega)⟩
            by_cases hd : d = n
            · rw [ite_eq_left hd]
              obtain ⟨c', hw, rfl⟩ := hdn hd
              rw [hw]
              have hc' : c' ∈ sigma := by
                rw [List.mem_map] at hcs; obtain ⟨a, ha, hac⟩ := hcs
                exact (Option.some.inj hac) ▸ ha
              simp [hc']
            · rw [ite_eq_right hd]; exact hcs

/-! ### Canonical form (rules of unused symbols are irrelevant) -/

def usedSymbols [DecidableEq α] (S : DOL α) : Nat → List α
  | 0     => []
  | n + 1 => S.derive n ++ usedSymbols S n

def canon [DecidableEq α] (sigma : List α) (n : Nat) (P : Presented α) : Presented α :=
  let S := P.toDOL
  let u := usedSymbols S n
  (P.1, sigma.filterMap fun a => if a ∈ u then some (a, S.rule a) else none)

/-! ### From `sol` to `infer`: lifting, the initial state, and canonical forms -/

theorem tok_of_bounded [DecidableEq α] (sigma : List α) (B : Bounds) (S : DOL α)
    (hS : Bounded sigma B S) : TOk sigma B (lift S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    simp only [allSyms, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨a, ha, rfl⟩
    · simp only [lift, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact List.mem_map.mpr ⟨z, hS.start_mem z hz, rfl⟩
    · simp only [lift, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact List.mem_map.mpr ⟨z, hS.rule_mem a ha z hz, rfl⟩
  · intro x hx
    simp only [allSyms, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨a, ha, rfl⟩
    · simp [lift, hS.start_len_hi]
    · simp [lift, hS.rule_len_hi a ha]
  · intro hae x
    cases x with
    | none =>
      simp only [lift]
      intro h
      have h1 := congrArg List.length h
      simp only [List.length_map, List.length_nil] at h1
      have := hS.start_len_lo
      omega
    | some a =>
      simp only [lift]
      intro h
      have h1 := congrArg List.length h
      simp only [List.length_map, List.length_nil] at h1
      by_cases ha : a ∈ sigma
      · have := hS.rule_len_lo a ha; rw [hae] at this; simp at this; omega
      · rw [hS.rule_default a ha] at h1; simp at h1
  · show S.start.map some ≠ []
    intro h
    have h1 := congrArg List.length h
    simp only [List.length_map, List.length_nil] at h1
    have := hS.start_len_lo
    omega

theorem initial_onPath [DecidableEq α] (w : List α) (n : Nat) (S : DOL α)
    (hw : S.derive n = w) : OnPath w n (lift S) ⟨[], [(none, 0, 0)], 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _⟩
  · simp only [stackLeaves_cons, stackLeaves_nil, frameLeaves_mk, Nat.sub_zero, List.drop_zero,
      List.append_nil]
    show (lift S).iter n (S.start.map some) = w.map some
    rw [iter_lift_map, ← derive_eq_iter, hw]
  · intro x hx; simp [lookupR] at hx
  · intro x; simp [lookupR]
  · intro f hf; simp at hf; subst hf; exact Nat.zero_le _
  · intro f hf; simp at hf; subst hf; exact ⟨Nat.zero_le _, by simp [DOL.iter]⟩
  · intro x hx; simp [lookupR] at hx
  · intro x hx
    right
    simp only [stackNodes_cons, stackNodes_nil, framePend_mk, Nat.sub_zero, List.drop_zero,
      List.append_nil, List.mem_cons]
    have := mem_pend_single (lift S) n none x hx
    rcases this with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h

theorem filterMap_id_map_some (l : List α) : (l.map some).filterMap id = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filterMap_cons, ih]

/-- Symbols of `S.derive j` for `j < n` are used symbols. -/
theorem mem_derive_mem_used [DecidableEq α] (S : DOL α) (n j : Nat) (hj : j < n) (a : α)
    (ha : a ∈ S.derive j) : a ∈ usedSymbols S n := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [usedSymbols, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact Or.inr (ih hj)
    · exact Or.inl ha

/-- `some a` is a used symbol of the lift iff `a` is a used symbol of `S`. -/
theorem mem_usedT_lift_iff [DecidableEq α] (S : DOL α) (n : Nat) (a : α) :
    some a ∈ usedT (lift S) n ↔ a ∈ usedSymbols S n := by
  constructor
  · intro h
    rcases mem_pend_single (lift S) n none (some a) h with h | h
    · exact Option.noConfusion h
    · rw [List.mem_flatMap] at h
      obtain ⟨j, hj, hx⟩ := h
      rw [List.mem_range] at hj
      have : (lift S).rule none = S.start.map some := rfl
      rw [this, iter_lift_map, ← derive_eq_iter, List.mem_map] at hx
      obtain ⟨b, hb, hab⟩ := hx
      have hba : b = a := Option.some.inj hab
      subst hba
      exact mem_derive_mem_used S n j hj _ hb
  · intro h
    simp only [usedT, List.mem_flatMap, List.mem_range]
    induction n with
    | zero => simp [usedSymbols] at h
    | succ n ih =>
      simp only [usedSymbols, List.mem_append] at h
      rcases h with h | h
      · exact ⟨n + 1, by omega, by rw [iter_lift_none]; exact List.mem_map.mpr ⟨a, h, rfl⟩⟩
      · obtain ⟨j, hj, hx⟩ := ih h
        exact ⟨j, by omega, hx⟩

theorem lookup_filterMap_some [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p]
    (g : α → List α) (a : α) (ha : a ∈ l) (hp : p a) :
    (l.filterMap fun x => if p x then some (x, g x) else none).lookup a = some (g a) := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil _)
  | cons b l ih =>
    simp only [List.filterMap_cons]
    by_cases hb : p b
    · rw [ite_eq_left hb]
      by_cases hab : a = b
      · subst hab; simp [List.lookup]
      · have : (a == b) = false := beq_false_of_ne hab
        simp only [List.lookup, this]
        exact ih (by rcases List.mem_cons.mp ha with rfl | h; exact absurd rfl hab; exact h)
    · rw [ite_eq_right hb]
      exact ih (by rcases List.mem_cons.mp ha with rfl | h; exact absurd hp hb; exact h)

theorem lookup_filterMap_none [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p]
    (g : α → List α) (a : α) (ha : a ∉ l) :
    (l.filterMap fun x => if p x then some (x, g x) else none).lookup a = none := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.filterMap_cons]
    have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self _ _)
    have hl : a ∉ l := fun h => ha (List.mem_cons_of_mem _ h)
    by_cases hb : p b
    · rw [ite_eq_left hb]
      have := beq_false_of_ne hab
      simp only [List.lookup, this]; exact ih hl
    · rw [ite_eq_right hb]; exact ih hl

theorem step_congr (S K : DOL α) (s : List α) (h : ∀ a ∈ s, K.rule a = S.rule a) :
    K.step s = S.step s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [step_cons]
    rw [h a (List.mem_cons_self _ _), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- If `K` agrees with `S` on used symbols and on the axiom, derivations agree up to `n`. -/
theorem derive_eq_of_agree [DecidableEq α] (S K : DOL α) (n : Nat) (hst : K.start = S.start)
    (hr : ∀ a ∈ usedSymbols S n, K.rule a = S.rule a) :
    ∀ j ≤ n, K.derive j = S.derive j := by
  intro j
  induction j with
  | zero => intro _; exact hst
  | succ j ih =>
    intro hj
    simp only [DOL.derive]
    rw [ih (by omega)]
    exact step_congr S K _ (fun a ha => hr a (mem_derive_mem_used S n j (by omega) a ha))

theorem usedSymbols_eq_of_agree [DecidableEq α] (S K : DOL α) (n : Nat)
    (h : ∀ j ≤ n, K.derive j = S.derive j) : usedSymbols K n = usedSymbols S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [usedSymbols]
    rw [h n (by omega), ih (fun j hj => h j (by omega))]

theorem lookup_map_pair [DecidableEq α] (l : List α) (f : α → List α) (a : α) :
    (l.map fun x => (x, f x)).lookup a = if a ∈ l then some (f a) else none := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons]
    by_cases hab : a = b
    · subst hab; simp [List.lookup]
    · have : (a == b) = false := beq_false_of_ne hab
      simp only [List.lookup, this, ih]
      by_cases hal : a ∈ l
      · simp [hal, hab]
      · simp [hal, hab]

/-- The expected key canonicalizes to the same thing as the candidate it came from. -/
theorem canon_expectedKey [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat)
    (P : Presented α) (hB : Bounded sigma B P.toDOL) :
    canon sigma n (expectedKey sigma B n (lift P.toDOL)) = canon sigma n P := by
  have hkey : expectedKey sigma B n (lift P.toDOL)
      = (P.1, sigma.map fun a =>
          (a, if a ∈ usedSymbols P.toDOL n then P.toDOL.rule a else defaultBody B a)) := by
    unfold expectedKey
    have h1 : (lift P.toDOL).rule none = P.toDOL.start.map some := rfl
    have h2 : ∀ a, (lift P.toDOL).rule (some a) = (P.toDOL.rule a).map some := fun a => rfl
    simp only [h1, h2, filterMap_id_map_some]
    congr 2
    funext a
    by_cases h : a ∈ usedSymbols P.toDOL n
    · rw [ite_eq_left h, ite_eq_left ((mem_usedT_lift_iff _ _ _).mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((mem_usedT_lift_iff _ _ _).mp h'))]
  rw [hkey]
  generalize hK : Presented.toDOL (P.1, sigma.map fun a =>
        (a, if a ∈ usedSymbols P.toDOL n then P.toDOL.rule a else defaultBody B a)) = K
  have toDOL_rule_mk : ∀ (ax : List α) (t : List (α × List α)) (a : α),
      (Presented.toDOL (ax, t)).rule a = match t.lookup a with | some r => r | none => [a] :=
    fun _ _ _ => rfl
  have hrule : ∀ a ∈ usedSymbols P.toDOL n, K.rule a = P.toDOL.rule a := by
    intro a ha
    rw [← hK, toDOL_rule_mk, lookup_map_pair]
    by_cases hs : a ∈ sigma
    · rw [ite_eq_left hs]; simp only [ite_eq_left ha]
    · rw [ite_eq_right hs, hB.rule_default a hs]
  have hst : K.start = P.toDOL.start := by rw [← hK]; rfl
  have hder := derive_eq_of_agree P.toDOL K n hst hrule
  have hused := usedSymbols_eq_of_agree P.toDOL K n hder
  unfold canon
  simp only [hK, hused, hst]
  show (P.toDOL.start, _) = (P.1, _)
  congr 2
  funext a
  by_cases h : a ∈ usedSymbols P.toDOL n
  · rw [ite_eq_left h, ite_eq_left h, hrule a h]
  · rw [ite_eq_right h, ite_eq_right h]

/-- **Completeness corollary.** Every bounded solution is found by the search,
up to rules of unused symbols. -/
theorem sol_subset_infer [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat)
    (P : Presented α) (hP : P ∈ sol sigma B w n) :
    ∃ fuel, ∃ Q ∈ infer sigma B w n fuel, canon sigma n Q = canon sigma n P := by
  have hA : P ∈ allSystems sigma B := (List.mem_filter.mp hP).1
  have hw : P.toDOL.derive n = w := sol_sound sigma B w n P hP
  have hB := bounded_of_mem_allSystems sigma B P hA
  have hT := tok_of_bounded sigma B P.toDOL hB
  have h0 := initial_onPath w n P.toDOL hw
  refine ⟨measure sigma n (lift P.toDOL) ⟨[], [(none, 0, 0)], 0⟩ + 1,
    expectedKey sigma B n (lift P.toDOL), ?_, canon_expectedKey sigma B n P hB⟩
  -- the guard holds: some symbol of sigma has a legal rule body
  have hguard : (if B.allowEmpty then 0 else 1) ≤ B.maxRule := by
    cases hs : sigma with
    | nil =>
      -- no symbols at all: no axiom is possible, so `sol` is empty
      exfalso
      have := hB.start_len_lo
      have hm := hB.start_mem
      rw [hs] at hm
      cases hst : P.toDOL.start with
      | nil => rw [hst] at this; simp at this
      | cons c _ => exact absurd (hm c (by rw [hst]; exact List.mem_cons_self _ _)) (by simp)
    | cons a rest =>
      have h1 := hB.rule_len_lo a (by rw [hs]; exact List.mem_cons_self _ _)
      have h2 := hB.rule_len_hi a (by rw [hs]; exact List.mem_cons_self _ _)
      omega
  unfold infer
  rw [ite_eq_left hguard]
  exact search_complete w n sigma B (lift P.toDOL) hT _ _ h0 (Nat.lt_succ_self _)

/-! ### Soundness: forward side-conditions, the final system, and the extension relation -/

/-- Properties every reachable search state satisfies (proved forward). -/
structure Good [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (st : St α) : Prop where
  bodies     : ∀ x, ∀ y ∈ (lookupR st.rules x).1, ∃ a ∈ sigma, y = some a
  len        : ∀ x, (lookupR st.rules x).1.length ≤ (if x = none then B.maxAxiom else B.maxRule)
  closed_ne  : ∀ x, (lookupR st.rules x).2 = true → B.allowEmpty = false → (lookupR st.rules x).1 ≠ []
  open_frame : ∀ x, (lookupR st.rules x).2 = false → (lookupR st.rules x).1 ≠ [] →
                 ∃ f ∈ st.stack, f.1 = x
  idx        : ∀ f ∈ st.stack, f.2.2 ≤ (lookupR st.rules f.1).1.length
  depth      : ∀ f ∈ st.stack, f.2.1 ≤ n
  syms       : ∀ f ∈ st.stack, f.1 ∈ allSyms sigma
  entry_syms : ∀ x, lookupR st.rules x ≠ ([], false) → x ∈ allSyms sigma
  axiom_ne   : (lookupR st.rules none).2 = true → (lookupR st.rules none).1 ≠ []

/-- Properties of the final rule table. -/
structure GoodF [DecidableEq α] (sigma : List α) (B : Bounds) (R : Rules α) : Prop where
  bodies     : ∀ x, ∀ y ∈ (lookupR R x).1, ∃ a ∈ sigma, y = some a
  len        : ∀ x, (lookupR R x).1.length ≤ (if x = none then B.maxAxiom else B.maxRule)
  closed_ne  : ∀ x, (lookupR R x).2 = true → B.allowEmpty = false → (lookupR R x).1 ≠ []
  open_nil   : ∀ x, (lookupR R x).2 = false → (lookupR R x).1 = []
  entry_syms : ∀ x, lookupR R x ≠ ([], false) → x ∈ allSyms sigma
  axiom_ne   : (lookupR R none).2 = true → (lookupR R none).1 ≠ []

theorem goodF_of_good [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (R : Rules α)
    (pos : Nat) (hg : Good sigma B n ⟨R, [], pos⟩) : GoodF sigma B R :=
  ⟨hg.bodies, hg.len, hg.closed_ne,
   fun x ho => by
     apply Decidable.byContradiction
     intro hne
     obtain ⟨f, hf, -⟩ := hg.open_frame x ho hne
     simp at hf,
   hg.entry_syms, hg.axiom_ne⟩

/-- The system read off a final rule table: closed bodies become rules; symbols of `sigma`
never rewritten get the default body; symbols outside `sigma` are fixed. -/
def finalS [DecidableEq α] (sigma : List α) (B : Bounds) (R : Rules α) : DOL α :=
  ⟨(lookupR R none).1.filterMap id,
   fun a => if (lookupR R (some a)).2 then (lookupR R (some a)).1.filterMap id
            else if a ∈ sigma then defaultBody B a else [a]⟩

theorem map_some_filterMap_id (l : List (Option α)) (h : ∀ y ∈ l, ∃ a, y = some a) :
    (l.filterMap id).map some = l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    obtain ⟨a, rfl⟩ := h y (List.mem_cons_self _ _)
    simp [List.filterMap_cons, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem lift_finalS_rule_closed [DecidableEq α] (sigma : List α) (B : Bounds) (R : Rules α)
    (hR : GoodF sigma B R) (x : Option α) (hx : (lookupR R x).2 = true) :
    (lift (finalS sigma B R)).rule x = (lookupR R x).1 := by
  have hb := hR.bodies x
  cases x with
  | none =>
    show ((lookupR R none).1.filterMap id).map some = _
    exact map_some_filterMap_id _ (fun y hy => let ⟨a, _, h⟩ := hb y hy; ⟨a, h⟩)
  | some a =>
    show (if (lookupR R (some a)).2 = true then (lookupR R (some a)).1.filterMap id
          else if a ∈ sigma then defaultBody B a else [a]).map some = _
    rw [ite_eq_left hx]
    exact map_some_filterMap_id _ (fun y hy => let ⟨a, _, h⟩ := hb y hy; ⟨a, h⟩)

/-- `Rf` extends `R`: closed entries are kept verbatim, open bodies may grow. -/
def Ext [DecidableEq α] (R Rf : Rules α) : Prop :=
  ∀ x, ((lookupR R x).2 = true → lookupR Rf x = lookupR R x) ∧
       (lookupR R x).1 <+: (lookupR Rf x).1

theorem ext_refl [DecidableEq α] (R : Rules α) : Ext R R :=
  fun x => ⟨fun _ => rfl, ⟨[], List.append_nil _⟩⟩

/-- Through an extension, the final system is consistent with the current table. -/
theorem ext_closed_eq [DecidableEq α] (sigma : List α) (B : Bounds) (R Rf : Rules α)
    (hR : GoodF sigma B Rf) (he : Ext R Rf) (x : Option α) (hx : (lookupR R x).2 = true) :
    (lookupR R x).1 = (lift (finalS sigma B Rf)).rule x := by
  have h1 := (he x).1 hx
  rw [lift_finalS_rule_closed sigma B Rf hR x (by rw [h1]; exact hx), h1]

theorem ext_prefix [DecidableEq α] (sigma : List α) (B : Bounds) (R Rf : Rules α)
    (hR : GoodF sigma B Rf) (he : Ext R Rf) (x : Option α) :
    (lookupR R x).1 <+: (lift (finalS sigma B Rf)).rule x := by
  have hp := (he x).2
  cases hc : (lookupR Rf x).2 with
  | true => rw [lift_finalS_rule_closed sigma B Rf hR x hc]; exact hp
  | false =>
    rw [hR.open_nil x hc] at hp
    have : (lookupR R x).1 = [] := List.prefix_nil.mp hp
    rw [this]; exact ⟨_, rfl⟩

/-! #### enumeration completeness -/

theorem mem_words_of (sigma : List α) (v : List α) (hs : ∀ x ∈ v, x ∈ sigma) :
    v ∈ words sigma v.length := by
  induction v with
  | nil => simp [words]
  | cons a v ih =>
    simp only [List.length_cons, words, List.mem_flatMap, List.mem_map]
    exact ⟨v, ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)), a, hs a (List.mem_cons_self _ _), rfl⟩

theorem mem_wordsUpTo_of (sigma : List α) (lo hi : Nat) (v : List α)
    (h1 : lo ≤ v.length) (h2 : v.length ≤ hi) (hs : ∀ x ∈ v, x ∈ sigma) :
    v ∈ wordsUpTo sigma lo hi := by
  simp only [wordsUpTo, List.mem_flatMap, List.mem_filter, List.mem_range]
  exact ⟨v.length, ⟨by omega, by simpa using h1⟩, mem_words_of sigma v hs⟩

theorem mem_ruleTables_of (sigma : List α) (bodies : List (List α)) (f : α → List α)
    (hf : ∀ a ∈ sigma, f a ∈ bodies) :
    sigma.map (fun a => (a, f a)) ∈ ruleTables sigma bodies := by
  induction sigma with
  | nil => simp [ruleTables]
  | cons c sigma ih =>
    simp only [ruleTables, List.foldr_cons, List.map_cons, List.mem_flatMap, List.mem_map]
    exact ⟨f c, hf c (List.mem_cons_self _ _), sigma.map (fun a => (a, f a)),
      ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)), rfl⟩

theorem DOL.ext' (S K : DOL α) (hs : S.start = K.start) (hr : ∀ a, S.rule a = K.rule a) : S = K := by
  cases S; cases K
  simp only at hs hr
  subst hs
  congr
  funext a
  exact hr a

/-- `canon` depends only on the axiom and the induced system. -/
theorem canon_congr [DecidableEq α] (sigma : List α) (n : Nat) (P Q : Presented α)
    (h1 : P.1 = Q.1) (h2 : P.toDOL = Q.toDOL) : canon sigma n P = canon sigma n Q := by
  unfold canon; rw [h1, h2]

/-! #### The backward invariant -/

def Inv [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds) (st : St α)
    (Rf : Rules α) : Prop :=
  stackLeaves (lift (finalS sigma B Rf)) n st.stack = (w.map some).drop st.pos ∧ Ext st.rules Rf

theorem drop_pos_eq (w : List α) (pos : Nat) (c : α) (h : w[pos]? = some c) :
    (w.map some).drop pos = some c :: (w.map some).drop (pos + 1) := by
  have hp : pos < w.length := by
    apply Nat.lt_of_not_le; intro hle
    rw [List.getElem?_eq_none hle] at h; exact Option.noConfusion h
  rw [List.drop_eq_getElem_cons (by simpa using hp), List.getElem_map]
  have : w[pos] = c := by
    have := List.getElem?_eq_getElem hp
    rw [h] at this; exact (Option.some.inj this).symm
  rw [this]

/-! #### Transition A (leaf) -/

theorem good_leaf [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (R : Rules α)
    (sym : Option α) (i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hg : Good sigma B n ⟨R, (sym, n, i) :: rest, pos⟩)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i < body.length) : Good sigma B n ⟨R, (sym, n, i + 1) :: rest, pos + 1⟩ := by
  refine ⟨hg.bodies, hg.len, hg.closed_ne, ?_, ?_, ?_, ?_, hg.entry_syms, hg.axiom_ne⟩
  · intro x ho hne
    obtain ⟨f, hf, hfx⟩ := hg.open_frame x ho hne
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨(sym, n, i + 1), List.mem_cons_self _ _, hfx⟩
    · exact ⟨f, List.mem_cons_of_mem _ hf, hfx⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · simp only [hb]; exact hi
    · exact hg.idx f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hg.depth (sym, n, i) (List.mem_cons_self _ _)
    · exact hg.depth f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hg.syms (sym, n, i) (List.mem_cons_self _ _)
    · exact hg.syms f (List.mem_cons_of_mem _ hf)

theorem inv_leaf [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (R Rf : Rules α) (hR : GoodF sigma B Rf)
    (sym : Option α) (i : Nat) (rest : List (Frame α)) (pos : Nat)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i < body.length) (c : α) (hw : w[pos]? = some c) (hc : body[i] = some c)
    (hinv : Inv w n sigma B ⟨R, (sym, n, i + 1) :: rest, pos + 1⟩ Rf) :
    Inv w n sigma B ⟨R, (sym, n, i) :: rest, pos⟩ Rf := by
  obtain ⟨hl, he⟩ := hinv
  refine ⟨?_, he⟩
  have hpre := ext_prefix sigma B R Rf hR he sym
  rw [hb] at hpre
  simp only at hpre
  have hdrop := drop_of_prefix body _ hpre i hi
  simp only [stackLeaves_cons, frameLeaves_mk, Nat.sub_self, DOL.iter] at hl ⊢
  rw [hdrop, hc, List.cons_append, hl, drop_pos_eq w pos c hw]

/-! #### Transition B (expand) -/

theorem good_expand [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (R : Rules α)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hg : Good sigma B n ⟨R, (sym, d, i) :: rest, pos⟩)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i < body.length) (hd : d ≠ n) :
    Good sigma B n ⟨R, (body[i], d + 1, 0) :: (sym, d, i + 1) :: rest, pos⟩ := by
  have hdn := hg.depth (sym, d, i) (List.mem_cons_self _ _)
  simp only at hdn
  have hcb : body[i] ∈ (lookupR R sym).1 := by rw [hb]; exact List.getElem_mem hi
  obtain ⟨a, ha, hca⟩ := hg.bodies sym _ hcb
  refine ⟨hg.bodies, hg.len, hg.closed_ne, ?_, ?_, ?_, ?_, hg.entry_syms, hg.axiom_ne⟩
  · intro x ho hne
    obtain ⟨f, hf, hfx⟩ := hg.open_frame x ho hne
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨(sym, d, i + 1), List.mem_cons_of_mem _ (List.mem_cons_self _ _), hfx⟩
    · exact ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), hfx⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Nat.zero_le _
    rcases List.mem_cons.mp hf with rfl | hf
    · simp only [hb]; exact hi
    · exact hg.idx f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · show d + 1 ≤ n; omega
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hdn
    · exact hg.depth f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · show body[i] ∈ allSyms sigma
      rw [hca]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hg.syms (sym, d, i) (List.mem_cons_self _ _)
    · exact hg.syms f (List.mem_cons_of_mem _ hf)

theorem inv_expand [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (R Rf : Rules α) (hR : GoodF sigma B Rf)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i < body.length) (hd : d ≠ n) (hdn : d ≤ n)
    (hinv : Inv w n sigma B ⟨R, (body[i], d + 1, 0) :: (sym, d, i + 1) :: rest, pos⟩ Rf) :
    Inv w n sigma B ⟨R, (sym, d, i) :: rest, pos⟩ Rf := by
  obtain ⟨hl, he⟩ := hinv
  refine ⟨?_, he⟩
  have hpre := ext_prefix sigma B R Rf hR he sym
  rw [hb] at hpre
  simp only at hpre
  have hdrop := drop_of_prefix body _ hpre i hi
  have hm : n - d = (n - (d + 1)) + 1 := by omega
  simp only [stackLeaves_cons, frameLeaves_mk, List.drop_zero] at hl ⊢
  rw [hdrop, iter_cons, hm, iter_succ_single, ← hm, List.append_assoc, hl]

/-! #### Transitions C/D (pop, with the table unchanged or closed) -/

theorem good_pop [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (R R' : Rules α)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hg : Good sigma B n ⟨R, (sym, d, i) :: rest, pos⟩)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hself : lookupR R' sym = (body, true))
    (hother : ∀ y, y ≠ sym → lookupR R' y = lookupR R y)
    (hne : B.allowEmpty = false → body ≠ []) (hax : sym = none → body ≠ []) :
    Good sigma B n ⟨R', rest, pos⟩ := by
  have hsym := hg.syms (sym, d, i) (List.mem_cons_self _ _)
  simp only at hsym
  have hlk : ∀ x, (lookupR R' x).1 = (lookupR R x).1 := by
    intro x
    by_cases hx : x = sym
    · subst hx; rw [hself, hb]
    · rw [hother x hx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hlk]; exact hg.bodies x
  · intro x; rw [hlk]; exact hg.len x
  · intro x hc hae
    by_cases hx : x = sym
    · subst hx; rw [hself]; exact hne hae
    · rw [hother x hx] at hc ⊢; exact hg.closed_ne x hc hae
  · intro x ho hne'
    by_cases hx : x = sym
    · subst hx; rw [hself] at ho; exact absurd ho (by simp)
    · rw [hother x hx] at ho hne'
      obtain ⟨f, hf, hfx⟩ := hg.open_frame x ho hne'
      rcases List.mem_cons.mp hf with rfl | hf
      · exact absurd hfx.symm hx
      · exact ⟨f, hf, hfx⟩
  · intro f hf; rw [hlk]; exact hg.idx f (List.mem_cons_of_mem _ hf)
  · intro f hf; exact hg.depth f (List.mem_cons_of_mem _ hf)
  · intro f hf; exact hg.syms f (List.mem_cons_of_mem _ hf)
  · intro x hx
    by_cases hxs : x = sym
    · subst hxs; exact hsym
    · rw [hother x hxs] at hx; exact hg.entry_syms x hx
  · intro hc
    by_cases hxs : (none : Option α) = sym
    · rw [← hxs] at hself; rw [hself]; exact hax hxs.symm
    · rw [hother none hxs] at hc ⊢; exact hg.axiom_ne hc

theorem inv_pop [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (R R' Rf : Rules α) (hR : GoodF sigma B Rf)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i = body.length)
    (hself : lookupR R' sym = (body, true))
    (hother : ∀ y, y ≠ sym → lookupR R' y = lookupR R y)
    (hinv : Inv w n sigma B ⟨R', rest, pos⟩ Rf) :
    Inv w n sigma B ⟨R, (sym, d, i) :: rest, pos⟩ Rf := by
  obtain ⟨hl, he⟩ := hinv
  have hRf : lookupR Rf sym = (body, true) := by
    have := (he sym).1 (by rw [hself]); rwa [hself] at this
  have hrule : (lift (finalS sigma B Rf)).rule sym = body := by
    rw [lift_finalS_rule_closed sigma B Rf hR sym (by rw [hRf]), hRf]
  constructor
  · simp only [stackLeaves_cons, frameLeaves_mk, hrule, hi, List.drop_length, iter_nil,
      List.nil_append]
    exact hl
  · intro x
    by_cases hx : x = sym
    · subst hx
      rw [hb]
      refine ⟨fun hc => ?_, ?_⟩
      · rw [hRf]; simp only at hc; subst hc; rfl
      · rw [hRf]; exact ⟨[], List.append_nil _⟩
    · have := he x; rw [hother x hx] at this; exact this

/-! #### Transition E (extend) -/

theorem good_extend [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (R : Rules α)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (hg : Good sigma B n ⟨R, (sym, d, i) :: rest, pos⟩)
    (body : List (Option α)) (hb : lookupR R sym = (body, false))
    (a : α) (ha : a ∈ sigma)
    (hlen : body.length + 1 ≤ (if sym = none then B.maxAxiom else B.maxRule)) :
    Good sigma B n ⟨(sym, (body ++ [some a], false)) :: R, (sym, d, i) :: rest, pos⟩ := by
  have hsym := hg.syms (sym, d, i) (List.mem_cons_self _ _)
  simp only at hsym
  refine ⟨?_, ?_, ?_, ?_, ?_, hg.depth, hg.syms, ?_, ?_⟩
  · intro x y hy
    by_cases hx : x = sym
    · subst x
      rw [lookupR_cons_self] at hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · have := hg.bodies sym y; rw [hb] at this; exact this hy
      · exact ⟨a, ha, rfl⟩
    · rw [lookupR_cons_ne R sym x _ hx] at hy; exact hg.bodies x y hy
  · intro x
    by_cases hx : x = sym
    · subst x; rw [lookupR_cons_self]; simpa using hlen
    · rw [lookupR_cons_ne R sym x _ hx]; exact hg.len x
  · intro x hc hae
    by_cases hx : x = sym
    · subst x; rw [lookupR_cons_self] at hc; exact absurd hc (by simp)
    · rw [lookupR_cons_ne R sym x _ hx] at hc ⊢; exact hg.closed_ne x hc hae
  · intro x ho hne
    by_cases hx : x = sym
    · subst x; exact ⟨(sym, d, i), List.mem_cons_self _ _, rfl⟩
    · rw [lookupR_cons_ne R sym x _ hx] at ho hne; exact hg.open_frame x ho hne
  · intro f hf
    have := hg.idx f hf
    by_cases hx : f.1 = sym
    · rw [hx, lookupR_cons_self]; rw [hx, hb] at this; simp only at this; simp; omega
    · rw [lookupR_cons_ne R sym _ _ hx]; exact this
  · intro x hx
    by_cases hxs : x = sym
    · subst hxs; exact hsym
    · rw [lookupR_cons_ne R sym x _ hxs] at hx; exact hg.entry_syms x hx
  · intro hc
    by_cases hxs : (none : Option α) = sym
    · rw [← hxs, lookupR_cons_self] at hc; exact absurd hc (by simp)
    · rw [lookupR_cons_ne R sym none _ hxs] at hc ⊢; exact hg.axiom_ne hc

theorem inv_extend [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (R Rf : Rules α)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (body : List (Option α)) (hb : lookupR R sym = (body, false)) (c : Option α)
    (hinv : Inv w n sigma B ⟨(sym, (body ++ [c], false)) :: R, (sym, d, i) :: rest, pos⟩ Rf) :
    Inv w n sigma B ⟨R, (sym, d, i) :: rest, pos⟩ Rf := by
  obtain ⟨hl, he⟩ := hinv
  refine ⟨hl, ?_⟩
  intro x
  by_cases hx : x = sym
  · subst x
    have h2 := (he sym).2
    rw [lookupR_cons_self] at h2
    rw [hb]
    refine ⟨fun hc => absurd hc (by simp), ?_⟩
    simp only
    obtain ⟨t, ht⟩ := h2
    exact ⟨[c] ++ t, by rw [← List.append_assoc]; exact ht⟩
  · have := he x; rw [lookupR_cons_ne R sym x _ hx] at this; exact this

/-! #### Terminal and initial states -/

theorem inv_terminal [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (R : Rules α) : Inv w n sigma B ⟨R, [], w.length⟩ R := by
  refine ⟨?_, ext_refl R⟩
  simp only [stackLeaves_nil]
  rw [List.drop_eq_nil_of_le (by simp)]

theorem good_init [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) :
    Good sigma B n ⟨[], [(none, 0, 0)], 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hy; simp [lookupR] at hy
  · intro x; simp [lookupR]
  · intro x hc; simp [lookupR] at hc
  · intro x _ hne; simp [lookupR] at hne
  · intro f hf; simp at hf; subst hf; exact Nat.zero_le _
  · intro f hf; simp at hf; subst hf; exact Nat.zero_le _
  · intro f hf; simp at hf; subst hf; simp [allSyms]
  · intro x hx; simp [lookupR] at hx
  · intro hc; simp [lookupR] at hc

/-! #### The soundness theorem -/

theorem search_sound [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds) :
    ∀ fuel (st : St α), Good sigma B n st → ∀ Q ∈ search w n sigma B fuel st,
      ∃ Rf, Q = toKey sigma B Rf ∧ GoodF sigma B Rf ∧ Inv w n sigma B st Rf ∧
        ∀ f ∈ st.stack, (lookupR Rf f.1).2 = true := by
  intro fuel
  induction fuel with
  | zero => intro st _ Q hQ; simp [search] at hQ
  | succ fuel ih =>
    intro st hg Q hQ
    rcases st with ⟨R, stack, pos⟩
    cases stack with
    | nil =>
      simp only [search] at hQ
      split at hQ
      · rename_i hpos
        simp only [List.mem_singleton] at hQ
        subst hQ
        subst hpos
        exact ⟨R, rfl, goodF_of_good sigma B n R _ hg, inv_terminal w n sigma B R, by simp⟩
      · simp at hQ
    | cons f rest =>
      rcases f with ⟨sym, d, i⟩
      rcases hb : lookupR R sym with ⟨body, closed⟩
      simp only [search, hb] at hQ
      split at hQ
      · simp at hQ
      by_cases hi : i < body.length
      · rw [dite_eq_left hi] at hQ
        by_cases hd : d = n
        · subst hd
          rw [ite_eq_left rfl] at hQ
          cases hw' : w[pos]? with
          | none => rw [hw'] at hQ; simp at hQ
          | some c =>
            rw [hw'] at hQ
            simp only at hQ
            split at hQ
            · rename_i hc
              obtain ⟨Rf, hQ', hRf, hinv, hcl⟩ :=
                ih _ (good_leaf sigma B d R sym i rest pos hg body closed hb hi) Q hQ
              refine ⟨Rf, hQ', hRf,
                inv_leaf w d sigma B R Rf hRf sym i rest pos body closed hb hi c hw' hc hinv, ?_⟩
              intro f hf
              rcases List.mem_cons.mp hf with rfl | hf
              · exact hcl (sym, d, i + 1) (List.mem_cons_self _ _)
              · exact hcl f (List.mem_cons_of_mem _ hf)
            · simp at hQ
        · rw [ite_eq_right hd] at hQ
          obtain ⟨Rf, hQ', hRf, hinv, hcl⟩ :=
            ih _ (good_expand sigma B n R sym d i rest pos hg body closed hb hi hd) Q hQ
          have hdn := hg.depth (sym, d, i) (List.mem_cons_self _ _)
          refine ⟨Rf, hQ', hRf,
            inv_expand w n sigma B R Rf hRf sym d i rest pos body closed hb hi hd hdn hinv, ?_⟩
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hcl (sym, d, i + 1) (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
          · exact hcl f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
      · rw [dite_eq_right hi] at hQ
        have hidx := hg.idx (sym, d, i) (List.mem_cons_self _ _)
        rw [hb] at hidx
        simp only at hidx
        have hi' : i = body.length := by omega
        cases closed with
        | true =>
          rw [ite_eq_left rfl] at hQ
          have hne : B.allowEmpty = false → body ≠ [] := fun hae => by
            have := hg.closed_ne sym (by rw [hb]) hae; rwa [hb] at this
          have hax : sym = none → body ≠ [] := fun hs => by
            subst hs; have := hg.axiom_ne (by rw [hb]); rwa [hb] at this
          obtain ⟨Rf, hQ', hRf, hinv, hcl⟩ :=
            ih _ (good_pop sigma B n R R sym d i rest pos hg body true hb hb (fun y _ => rfl) hne hax) Q hQ
          refine ⟨Rf, hQ', hRf,
            inv_pop w n sigma B R R Rf hRf sym d i rest pos body true hb hi' hb (fun y _ => rfl) hinv, ?_⟩
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · have := (hinv.2 sym).1 (by rw [hb]); rw [this, hb]
          · exact hcl f hf
        | false =>
          rw [ite_eq_right Bool.false_ne_true, List.mem_append] at hQ
          rcases hQ with hQ | hQ
          · split at hQ
            · rename_i hcond
              have hne : B.allowEmpty = false → body ≠ [] := by
                intro hae
                rw [hae] at hcond
                simp at hcond
                exact List.ne_nil_of_length_pos hcond
              have hax : sym = none → body ≠ [] := by
                intro hs
                subst hs
                simp at hcond
                exact List.ne_nil_of_length_pos hcond
              obtain ⟨Rf, hQ', hRf, hinv, hcl⟩ :=
                ih _ (good_pop sigma B n R _ sym d i rest pos hg body false hb
                  (lookupR_cons_self R sym _) (fun y hy => lookupR_cons_ne R sym y _ hy) hne hax) Q hQ
              refine ⟨Rf, hQ', hRf,
                inv_pop w n sigma B R _ Rf hRf sym d i rest pos body false hb hi'
                  (lookupR_cons_self R sym _) (fun y hy => lookupR_cons_ne R sym y _ hy) hinv, ?_⟩
              intro f hf
              rcases List.mem_cons.mp hf with rfl | hf
              · have := (hinv.2 sym).1 (by rw [lookupR_cons_self])
                rw [this, lookupR_cons_self]
              · exact hcl f hf
            · simp at hQ
          · by_cases hmax : body.length < (if sym = none then B.maxAxiom else B.maxRule)
            · rw [ite_eq_left hmax, List.mem_flatMap] at hQ
              obtain ⟨c, hc, hQ⟩ := hQ
              have hca : ∃ a ∈ sigma, c = some a := by
                split at hc
                · cases hw' : w[pos]? with
                  | none => rw [hw'] at hc; simp at hc
                  | some c' =>
                    rw [hw'] at hc
                    simp only at hc
                    by_cases hcs : c' ∈ sigma
                    · rw [ite_eq_left hcs] at hc; simp at hc; exact ⟨c', hcs, hc⟩
                    · rw [ite_eq_right hcs] at hc; simp at hc
                · rw [List.mem_map] at hc
                  obtain ⟨a, ha, rfl⟩ := hc
                  exact ⟨a, ha, rfl⟩
              obtain ⟨a, ha, rfl⟩ := hca
              obtain ⟨Rf, hQ', hRf, hinv, hcl⟩ :=
                ih _ (good_extend sigma B n R sym d i rest pos hg body hb a ha (by omega)) Q hQ
              exact ⟨Rf, hQ', hRf, inv_extend w n sigma B R Rf sym d i rest pos body hb (some a) hinv, hcl⟩
            · rw [ite_eq_right hmax] at hQ; simp at hQ

/-! ### Master theorem

`infer` and `sol` agree up to rules of unused symbols: completeness here, soundness
(`infer_sound`, no side conditions) after the backward invariant below. -/

/-- **Completeness** (proved): every bounded solution is found by the search. -/
theorem infer_complete [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
    ∀ P ∈ sol sigma B w n, ∃ fuel, ∃ Q ∈ infer sigma B w n fuel,
      canon sigma n Q = canon sigma n P :=
  fun P hP => sol_subset_infer sigma B w n P hP

/-! #### Assembling `infer_sound` -/

theorem length_filterMap_id_of_some (l : List (Option α)) (h : ∀ y ∈ l, ∃ a, y = some a) :
    (l.filterMap id).length = l.length := by
  have := congrArg List.length (map_some_filterMap_id l h)
  rwa [List.length_map] at this

/-- The system read off the final table is bounded, given a legal rule body exists. -/
theorem finalS_bounded [DecidableEq α] (sigma : List α) (B : Bounds) (Rf : Rules α)
    (hR : GoodF sigma B Rf) (hguard : (if B.allowEmpty then 0 else 1) ≤ B.maxRule)
    (hne : (finalS sigma B Rf).start ≠ []) : Bounded sigma B (finalS sigma B Rf) := by
  have hsome : ∀ x, ∀ y ∈ (lookupR Rf x).1, ∃ a, y = some a :=
    fun x y hy => let ⟨a, _, h⟩ := hR.bodies x y hy; ⟨a, h⟩
  have hmemS : ∀ x, ∀ a ∈ (lookupR Rf x).1.filterMap id, a ∈ sigma := by
    intro x a ha
    have : some a ∈ (lookupR Rf x).1 := by
      rw [← map_some_filterMap_id _ (hsome x)]; exact List.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := hR.bodies x _ this
    cases hab; exact hb
  have hclosed_not_mem : ∀ a, a ∉ sigma → (lookupR Rf (some a)).2 = false := by
    intro a ha
    cases hc : (lookupR Rf (some a)).2
    · rfl
    · exfalso
      have : lookupR Rf (some a) ≠ ([], false) := by
        intro h; rw [h] at hc; exact Bool.noConfusion hc
      have := hR.entry_syms _ this
      simp only [allSyms, List.mem_cons, List.mem_map] at this
      rcases this with h | ⟨b, hb, hab⟩
      · exact Option.noConfusion h
      · exact ha (Option.some.inj hab ▸ hb)
  have hrule : ∀ a, (finalS sigma B Rf).rule a
      = if (lookupR Rf (some a)).2 = true then (lookupR Rf (some a)).1.filterMap id
        else if a ∈ sigma then defaultBody B a else [a] := fun a => rfl
  refine ⟨?_, ?_, hmemS none, ?_, ?_, ?_, ?_⟩
  · exact List.length_pos.mpr hne
  · show ((lookupR Rf none).1.filterMap id).length ≤ B.maxAxiom
    rw [length_filterMap_id_of_some _ (hsome none)]
    simpa using hR.len none
  · intro a ha
    rw [hrule]
    cases hc : (lookupR Rf (some a)).2
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_left_left_left_left_left ha]
      unfold defaultBody
      by_cases h0 : B.maxRule = 0
      · rw [ite_eq_left h0]; simp only [List.length_nil]; rw [h0] at hguard; exact hguard
      · rw [ite_eq_right h0]; simp only [List.length_singleton]; split <;> omega
    · rw [ite_eq_left rfl, length_filterMap_id_of_some _ (hsome _)]
      cases hae : B.allowEmpty
      · rw [ite_eq_right Bool.false_ne_true]
        exact List.length_pos.mpr (hR.closed_ne _ hc hae)
      · rw [ite_eq_left rfl]; exact Nat.zero_le _
  · intro a ha
    rw [hrule]
    cases hc : (lookupR Rf (some a)).2
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_left ha]
      unfold defaultBody
      by_cases h0 : B.maxRule = 0
      · rw [ite_eq_left h0]; simp
      · rw [ite_eq_right h0]; simp only [List.length_singleton]; omega
    · rw [ite_eq_left rfl, length_filterMap_id_of_some _ (hsome _)]
      simpa using hR.len (some a)
  · intro a ha x hx
    rw [hrule] at hx
    cases hc : (lookupR Rf (some a)).2
    · rw [hc, ite_eq_right Bool.false_ne_true, ite_eq_left ha] at hx
      unfold defaultBody at hx
      by_cases h0 : B.maxRule = 0
      · rw [ite_eq_left h0] at hx; simp at hx
      · rw [ite_eq_right h0] at hx; simp at hx; subst hx; exact ha
    · rw [hc, ite_eq_left rfl] at hx; exact hmemS _ x hx
  · intro a ha
    rw [hrule, hclosed_not_mem a ha, ite_eq_right Bool.false_ne_true, ite_eq_right ha]

/-- The emitted key is literally the presentation of `finalS`. -/
theorem toKey_eq [DecidableEq α] (sigma : List α) (B : Bounds) (Rf : Rules α) :
    toKey sigma B Rf = ((finalS sigma B Rf).start, sigma.map fun a => (a, (finalS sigma B Rf).rule a)) := by
  unfold toKey finalS
  simp only
  congr 1
  apply List.map_congr_left
  intro a ha
  rcases h : lookupR Rf (some a) with ⟨b, c⟩
  simp only [ite_eq_left ha]

/-- **Soundness** (proved, no side conditions): every emitted key is a bounded solution. -/
theorem infer_sound [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
    ∀ fuel, ∀ Q ∈ infer sigma B w n fuel, ∃ P ∈ sol sigma B w n,
      canon sigma n Q = canon sigma n P := by
  intro fuel Q hQ
  unfold infer at hQ
  by_cases hguard : (if B.allowEmpty then 0 else 1) ≤ B.maxRule
  · rw [ite_eq_left_left hguard] at hQ
    obtain ⟨Rf, hQk, hRf, ⟨hleaves, -⟩, hcl⟩ :=
      search_sound w n sigma B fuel _ (good_init sigma B n) Q hQ
    have hder : (finalS sigma B Rf).derive n = w := by
      simp only [stackLeaves_cons, stackLeaves_nil, frameLeaves_mk, Nat.sub_zero, List.drop_zero,
        List.append_nil] at hleaves
      have h1 : (lift (finalS sigma B Rf)).rule none = (finalS sigma B Rf).start.map some := rfl
      rw [h1, iter_lift_map, ← derive_eq_iter] at hleaves
      have := congrArg (List.filterMap id) hleaves
      rwa [filterMap_id_map_some, filterMap_id_map_some] at this
    have hstart : (finalS sigma B Rf).start ≠ [] := by
      have hc := hcl (none, 0, 0) (List.mem_cons_self _ _)
      have := hRf.axiom_ne hc
      show (lookupR Rf none).1.filterMap id ≠ []
      intro h0
      apply this
      have := congrArg (List.map some) h0
      rwa [map_some_filterMap_id _ (fun y hy => let ⟨a, _, h⟩ := hRf.bodies none y hy; ⟨a, h⟩)] at this
    have hB := finalS_bounded sigma B Rf hRf hguard hstart
    refine ⟨Q, ?_, rfl⟩
    rw [hQk, toKey_eq]
    have hPD : Presented.toDOL ((finalS sigma B Rf).start, sigma.map fun a => (a, (finalS sigma B Rf).rule a))
        = finalS sigma B Rf := by
      refine DOL.ext' _ _ rfl ?_
      intro a
      show (match (sigma.map fun a => (a, (finalS sigma B Rf).rule a)).lookup a with
        | some r => r | none => [a]) = (finalS sigma B Rf).rule a
      rw [lookup_map_pair]
      by_cases ha : a ∈ sigma
      · rw [ite_eq_left ha]
      · rw [ite_eq_right ha]; exact (hB.rule_default a ha).symm
    unfold sol
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true (by rw [hPD]; exact hder)⟩
    simp only [allSystems, List.mem_flatMap, List.mem_map]
    refine ⟨(finalS sigma B Rf).start, ?_, sigma.map fun a => (a, (finalS sigma B Rf).rule a), ?_, rfl⟩
    · exact mem_wordsUpTo_of sigma 1 B.maxAxiom _ hB.start_len_lo hB.start_len_hi hB.start_mem
    · apply mem_ruleTables_of
      intro a ha
      exact mem_wordsUpTo_of sigma _ B.maxRule _ (hB.rule_len_lo a ha) (hB.rule_len_hi a ha)
        (hB.rule_mem a ha)
  · rw [ite_eq_right hguard] at hQ; simp at hQ

/-! ### Problem A: which `(w, n)` admit a non-trivial system over Σ(w)?

"Non-trivial" = axiom strictly shorter than `w`, no hidden symbols.
Two complete answers: the unary alphabet (iff some `m ≥ 2` has `m^n ∣ L`), and the
regime `n ≤ |Σ(w)|` (always, via a chain of distinct letters of `w`). -/

/-! #### Unary alphabet -/

theorem sum_map_unit (S : DOL Unit) (s : List Unit) :
    (s.map fun a => (S.rule a).length).sum = s.length * (S.rule ()).length := by
  have hall : ∀ a : Unit, S.rule a = S.rule () := fun a => by cases a; rfl
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, hall a]
    rw [Nat.succ_mul]; omega

theorem length_derive_unit (S : DOL Unit) (n : Nat) :
    (S.derive n).length = S.start.length * (S.rule ()).length ^ n := by
  induction n with
  | zero => simp [DOL.derive]
  | succ n ih =>
    simp only [DOL.derive, length_step, sum_map_unit, ih, Nat.pow_succ, Nat.mul_assoc]

theorem eq_replicate_unit (l : List Unit) : l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a; simp [List.replicate_succ]; exact ih

/-- **Unary characterization.** `a^L` has a non-trivial system at step `n ≥ 1`
iff `L` is divisible by an `n`-th power `m^n` with `m ≥ 2`. -/
theorem unary_iff (L n : Nat) (hL : 1 ≤ L) (hn : 1 ≤ n) :
    (∃ S : DOL Unit, S.start.length < L ∧ S.derive n = List.replicate L ())
      ↔ ∃ m, 2 ≤ m ∧ m ^ n ∣ L := by
  constructor
  · rintro ⟨S, hlt, hd⟩
    have hlen := congrArg List.length hd
    rw [length_derive_unit, List.length_replicate] at hlen
    refine ⟨(S.rule ()).length, ?_, ⟨S.start.length, by rw [Nat.mul_comm]; exact hlen.symm⟩⟩
    -- r ≥ 2: r = 0 forces L = 0, r = 1 forces |start| = L
    match hr : (S.rule ()).length with
    | 0 => rw [hr, Nat.zero_pow (by omega)] at hlen; omega
    | 1 => rw [hr, Nat.one_pow] at hlen; omega
    | r + 2 => omega
  · rintro ⟨m, hm, j, hj⟩
    refine ⟨⟨List.replicate j (), fun _ => List.replicate m ()⟩, ?_, ?_⟩
    · simp only [List.length_replicate]
      have h2 : 2 ≤ m ^ n := by
        calc 2 ≤ m := hm
          _ = m ^ 1 := (Nat.pow_one m).symm
          _ ≤ m ^ n := Nat.pow_le_pow_right (by omega) hn
      have : j ≠ 0 := by rintro rfl; simp at hj; omega
      have : j * 1 < j * m ^ n := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      rw [hj, Nat.mul_comm]; omega
    · rw [eq_replicate_unit (DOL.derive _ _), length_derive_unit]
      simp only [List.length_replicate]
      rw [hj, Nat.mul_comm]

/-! #### A chain of `n` distinct letters of `w` -/

/-- If `c₀ → c₁ → ⋯ → c_{n-1} → w`, then `n` steps from `c₀` give `w`. -/
theorem derive_chain (S : DOL α) (cs : List α) (n : Nat) (hn : cs.length = n) (hpos : 1 ≤ n)
    (hchain : ∀ i (h : i + 1 < cs.length), S.rule cs[i] = [cs[i + 1]])
    (hlast : S.rule (cs.getLast (by intro h; rw [h] at hn; simp at hn; omega)) = w)
    (hstart : S.start = [cs[0]'(by omega)]) :
    S.derive n = w := by
  have key : ∀ i (h : i < cs.length), S.iter i S.start = [cs[i]] := by
    intro i
    induction i with
    | zero => intro h; rw [hstart]; rfl
    | succ i ih =>
      intro h
      rw [iter_step_comm, ih (by omega), step_single, hchain i h]
  rw [derive_eq_iter]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [iter_step_comm, key k (by omega), step_single]
  rw [List.getLast_eq_getElem] at hlast
  simp only [hn] at hlast
  exact hlast

theorem lookup_zip_getElem [DecidableEq α] (cs : List α) (bs : List (List α))
    (hnd : cs.Nodup) (i : Nat) (hi : i < cs.length) (hib : i < bs.length) :
    (cs.zip bs).lookup cs[i] = some bs[i] := by
  induction cs generalizing bs i with
  | nil => simp at hi
  | cons c cs ih =>
    cases bs with
    | nil => simp at hib
    | cons b bs =>
      cases i with
      | zero => simp [List.lookup]
      | succ i =>
        have hi' : i < cs.length := by simp at hi; omega
        have hib' : i < bs.length := by simp at hib; omega
        simp only [List.zip_cons_cons, List.getElem_cons_succ]
        have hne : cs[i]'hi' ≠ c := by
          intro h
          have := List.nodup_cons.mp hnd
          exact this.1 (h ▸ List.getElem_mem hi')
        have : (cs[i]'hi' == c) = false := beq_false_of_ne hne
        simp only [List.lookup, this]
        exact ih bs (List.nodup_cons.mp hnd).2 i hi' hib'

theorem lookup_zip_none [DecidableEq α] (cs : List α) (bs : List (List α)) (a : α)
    (ha : a ∉ cs) : (cs.zip bs).lookup a = none := by
  induction cs generalizing bs with
  | nil => simp
  | cons c cs ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      have hne : a ≠ c := fun h => ha (h ▸ List.mem_cons_self _ _)
      have : (a == c) = false := beq_false_of_ne hne
      simp only [List.zip_cons_cons, List.lookup, this]
      exact ih bs (fun h => ha (List.mem_cons_of_mem _ h))

/-- **Chain theorem.** If `w` contains `n ≥ 1` distinct letters, there is a system over
`Σ(w)` (identity elsewhere) with a length-1 axiom deriving `w` in `n` steps. -/
theorem chain_exists [DecidableEq α] (w : List α) (n : Nat) (hn : 1 ≤ n)
    (cs : List α) (hlen : cs.length = n) (hnd : cs.Nodup) (hcs : ∀ c ∈ cs, c ∈ w) :
    ∃ S : DOL α, S.start.length = 1 ∧ S.derive n = w ∧
      (∀ a ∈ S.start, a ∈ w) ∧ (∀ a, a ∉ w → S.rule a = [a]) := by
  -- bodies: [c₁], [c₂], …, [c_{n-1}], w
  let bs : List (List α) := (cs.drop 1).map (fun c => [c]) ++ [w]
  have hbs : bs.length = n := by simp [bs, hlen]; omega
  let S : DOL α := ⟨[cs[0]'(by omega)],
    fun a => match (cs.zip bs).lookup a with | some r => r | none => [a]⟩
  have hbs_get : ∀ i (h : i + 1 < cs.length), bs[i]'(by omega) = [cs[i + 1]] := by
    intro i h
    simp only [bs]
    rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_drop]
    simp only [Nat.add_comm]
  have hbs_last : bs[n - 1]'(by omega) = w := by
    simp only [bs]
    rw [List.getElem_append_right (by simp; omega)]
    simp [hlen]
  refine ⟨S, rfl, ?_, ?_, ?_⟩
  · apply derive_chain S cs n hlen hn
    · intro i h
      show (match (cs.zip bs).lookup cs[i] with | some r => r | none => [cs[i]]) = _
      rw [lookup_zip_getElem cs bs hnd i (by omega) (by omega), hbs_get i h]
    · rw [List.getLast_eq_getElem]
      show (match (cs.zip bs).lookup cs[cs.length - 1] with | some r => r | none => _) = _
      rw [lookup_zip_getElem cs bs hnd _ (by omega) (by omega)]
      simp only [hlen]
      exact hbs_last
    · rfl
  · intro a ha
    simp [S] at ha
    subst ha
    exact hcs _ (List.getElem_mem _)
  · intro a ha
    show (match (cs.zip bs).lookup a with | some r => r | none => [a]) = [a]
    have hnot : a ∉ cs := fun h => ha (hcs a h)
    rw [lookup_zip_none cs bs a hnot]

/-! ### Problem B: counting — some word of length `L` has no bounded system

Pigeonhole: `allSystems` is a finite list, `words sigma L` has `|sigma|^L` distinct
entries, so if the former is shorter some word is underivable at every `n`. -/

theorem nodup_subset_length_le [DecidableEq α] (l₁ l₂ : List α) (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    obtain ⟨hat, hnt⟩ := List.nodup_cons.mp hnd
    have ha : a ∈ l₂ := hsub (List.mem_cons_self _ _)
    have hsub' : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hat (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub (List.mem_cons_of_mem _ hx))
    have := ih (l₂.erase a) hnt hsub'
    rw [List.length_erase_of_mem ha] at this
    have : 1 ≤ l₂.length := List.length_pos.mpr (List.ne_nil_of_mem ha)
    simp only [List.length_cons]; omega

theorem nodup_flatMap {β γ : Type} (l : List β) (f : β → List γ) (hl : l.Nodup)
    (hf : ∀ x ∈ l, (f x).Nodup)
    (hdisj : ∀ x ∈ l, ∀ y ∈ l, ∀ z, z ∈ f x → z ∈ f y → x = y) : (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hal, hnl⟩ := List.nodup_cons.mp hl
    simp only [List.flatMap_cons]
    unfold List.Nodup
    rw [List.pairwise_append]
    refine ⟨hf a (List.mem_cons_self _ _), ?_, ?_⟩
    · exact ih hnl (fun x hx => hf x (List.mem_cons_of_mem _ hx))
        (fun x hx y hy => hdisj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    · intro z hz z' hz' hzz
      subst hzz
      rw [List.mem_flatMap] at hz'
      obtain ⟨y, hy, hzy⟩ := hz'
      have := hdisj a (List.mem_cons_self _ _) y (List.mem_cons_of_mem _ hy) z hz hzy
      exact hal (this ▸ hy)

theorem nodup_map_cons (sigma : List α) (v : List α) (hs : sigma.Nodup) :
    (sigma.map fun c => c :: v).Nodup := by
  unfold List.Nodup
  exact List.Pairwise.map _ (fun a b h hab => h (List.cons.inj hab).1) hs

theorem words_nodup (sigma : List α) (hs : sigma.Nodup) (k : Nat) : (words sigma k).Nodup := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    simp only [words]
    apply nodup_flatMap _ _ ih
    · intro v _; exact nodup_map_cons sigma v hs
    · intro x _ y _ z hzx hzy
      rw [List.mem_map] at hzx hzy
      obtain ⟨c, _, rfl⟩ := hzx
      obtain ⟨c', _, h⟩ := hzy
      exact (List.cons.inj h).2.symm

theorem length_flatMap_const {β γ : Type} (l : List β) (f : β → List γ) (c : Nat)
    (h : ∀ x ∈ l, (f x).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (List.mem_cons_self _ _), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rw [Nat.succ_mul]; omega

theorem length_words (sigma : List α) (k : Nat) : (words sigma k).length = sigma.length ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    simp only [words]
    rw [length_flatMap_const _ _ sigma.length (fun _ _ => List.length_map _ _), ih, Nat.pow_succ]

theorem length_ruleTables (sigma : List α) (bodies : List (List α)) :
    (ruleTables sigma bodies).length = bodies.length ^ sigma.length := by
  induction sigma with
  | nil => simp [ruleTables]
  | cons c sigma ih =>
    show (bodies.flatMap fun b => (ruleTables sigma bodies).map fun t => (c, b) :: t).length = _
    rw [length_flatMap_const _ _ (ruleTables sigma bodies).length
      (fun _ _ => List.length_map _ _), ih, List.length_cons, Nat.pow_succ, Nat.mul_comm]

theorem length_allSystems (sigma : List α) (B : Bounds) :
    (allSystems sigma B).length
      = (wordsUpTo sigma 1 B.maxAxiom).length
        * (wordsUpTo sigma (if B.allowEmpty then 0 else 1) B.maxRule).length ^ sigma.length := by
  simp only [allSystems]
  rw [length_flatMap_const _ _ _ (fun _ _ => List.length_map _ _), length_ruleTables]

/-- **Counting bound.** If there are fewer bounded systems than words of length `L`,
some word of length `L` over `sigma` has no bounded system at step `n` — for every `n`. -/
theorem exists_underivable [DecidableEq α] (sigma : List α) (hs : sigma.Nodup) (B : Bounds)
    (n L : Nat) (hcount : (allSystems sigma B).length < sigma.length ^ L) :
    ∃ w ∈ words sigma L, sol sigma B w n = [] := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ w ∈ words sigma L, sol sigma B w n ≠ [] := by
    intro w hw hsol; exact hno ⟨w, hw, hsol⟩
  have hsub : words sigma L ⊆ (allSystems sigma B).map fun P => P.toDOL.derive n := by
    intro w hw
    have := hall w hw
    cases hsol : sol sigma B w n with
    | nil => exact absurd hsol this
    | cons P _ =>
      have hP : P ∈ sol sigma B w n := by rw [hsol]; exact List.mem_cons_self _ _
      have hA : P ∈ allSystems sigma B := (List.mem_filter.mp hP).1
      have hd := sol_sound sigma B w n P hP
      exact List.mem_map.mpr ⟨P, hA, hd⟩
  have := nodup_subset_length_le _ _ (words_nodup sigma hs L) hsub
  rw [List.length_map, length_words] at this
  omega

-- Concrete instance: over two letters with axiom ≤ 2 and rules ≤ 2 (no erasing),
-- there are 216 systems, so some binary word of length 8 has no such system at any step.
set_option maxRecDepth 100000 in
theorem underivable_binary_8 (n : Nat) :
    ∃ w ∈ words [0, 1] 8, sol [0, 1] ⟨2, 2, false⟩ w n = [] :=
  exists_underivable [0, 1] (by decide) ⟨2, 2, false⟩ n 8 (by rw [length_allSystems]; decide)

/-! ### Problem B, size version: incompressibility by total description length

A system over `sigma` is encoded as `axiom # rule a₁ # ⋯ # rule a_k #…#` over
`none :: sigma.map some`, padded with `#` to length `s + k + 1`. Decoding splits on `#`. -/

/-- Split on `none` (the separator). Always returns at least one segment. -/
def segs : List (Option α) → List (List α)
  | [] => [[]]
  | none :: t => [] :: segs t
  | some a :: t =>
    match segs t with
    | s :: ss => (a :: s) :: ss
    | [] => [[a]]

theorem segs_ne_nil (c : List (Option α)) : segs c ≠ [] := by
  induction c with
  | nil => simp [segs]
  | cons x t ih =>
    cases x with
    | none => simp [segs]
    | some a =>
      simp only [segs]
      split <;> simp

theorem segs_some_cons (a : α) (t : List (Option α)) :
    segs (some a :: t) = (a :: (segs t).headD []) :: (segs t).drop 1 := by
  simp only [segs]
  split
  · rename_i s ss h; rw [h]; rfl
  · rename_i h; exact absurd h (segs_ne_nil t)

theorem segs_map_some_append (u : List α) (rest : List (Option α)) :
    segs (u.map some ++ none :: rest) = u :: segs rest := by
  induction u with
  | nil => simp [segs]
  | cons a u ih =>
    simp only [List.map_cons, List.cons_append]
    rw [segs_some_cons, ih]
    rfl

/-- The description size of a system restricted to `sigma`. -/
def dsize (sigma : List α) (S : DOL α) : Nat :=
  S.start.length + (sigma.map fun a => (S.rule a).length).sum

def encodeS (sigma : List α) (S : DOL α) (pad : Nat) : List (Option α) :=
  S.start.map some ++ none ::
    ((sigma.flatMap fun a => (S.rule a).map some ++ [none]) ++ List.replicate pad none)

def decodeS [DecidableEq α] (sigma : List α) (code : List (Option α)) : DOL α :=
  ⟨(segs code).headD [],
   fun a => match (sigma.zip ((segs code).drop 1)).lookup a with | some r => r | none => [a]⟩

theorem segs_rules (sigma : List α) (S : DOL α) (rest : List (Option α)) :
    segs ((sigma.flatMap fun a => (S.rule a).map some ++ [none]) ++ rest)
      = sigma.map S.rule ++ segs rest := by
  induction sigma with
  | nil => rfl
  | cons a sigma ih =>
    simp only [List.flatMap_cons, List.map_cons, List.append_assoc, List.singleton_append]
    rw [List.cons_append, segs_map_some_append, ih]
    rfl

theorem zip_map_append (l : List α) (f : α → List α) (t : List (List α)) :
    l.zip (l.map f ++ t) = l.map fun a => (a, f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.zip_cons_cons, ih]

theorem decode_encode [DecidableEq α] (sigma : List α) (S : DOL α) (pad : Nat)
    (hid : ∀ a, a ∉ sigma → S.rule a = [a]) : decodeS sigma (encodeS sigma S pad) = S := by
  have hsegs : segs (encodeS sigma S pad)
      = S.start :: (sigma.map S.rule ++ segs (List.replicate pad none)) := by
    unfold encodeS
    rw [segs_map_some_append, segs_rules]
  apply DOL.ext'
  · simp [decodeS, hsegs]
  · intro a
    simp only [decodeS, hsegs, List.drop_succ_cons, List.drop_zero]
    rw [zip_map_append, lookup_map_pair]
    by_cases ha : a ∈ sigma
    · rw [ite_eq_left ha]
    · rw [ite_eq_right ha, hid a ha]

theorem length_encodeS (sigma : List α) (S : DOL α) (pad : Nat) :
    (encodeS sigma S pad).length = dsize sigma S + sigma.length + 1 + pad := by
  unfold encodeS dsize
  simp only [List.length_append, List.length_map, List.length_cons, List.length_replicate]
  have : ∀ l : List α, ((l.flatMap fun a => (S.rule a).map some ++ [none]).length)
      = (l.map fun a => (S.rule a).length).sum + l.length := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, ih]; omega
  rw [this]; omega

theorem encodeS_mem (sigma : List α) (S : DOL α) (pad : Nat)
    (hst : ∀ x ∈ S.start, x ∈ sigma) (hr : ∀ a ∈ sigma, ∀ x ∈ S.rule a, x ∈ sigma) :
    ∀ y ∈ encodeS sigma S pad, y ∈ allSyms sigma := by
  intro y hy
  unfold encodeS at hy
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_flatMap,
    List.mem_replicate, List.mem_singleton] at hy
  simp only [allSyms, List.mem_cons, List.mem_map]
  rcases hy with ⟨x, hx, rfl⟩ | rfl | ⟨a, ha, ⟨x, hx, rfl⟩ | h⟩ | ⟨-, rfl⟩
  · exact Or.inr ⟨x, hst x hx, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, hr a ha x hx, rfl⟩
  · simp at h; exact Or.inl h
  · exact Or.inl rfl

/-- **Incompressibility.** If `(k+1)^(s+k+1) < k^L` then some word of length `L` over
`sigma` (|sigma| = k) is not derivable, at step `n`, by any system over `sigma` of
description size ≤ `s`. -/
theorem exists_incompressible [DecidableEq α] (sigma : List α) (hs : sigma.Nodup) (n L s : Nat)
    (hcount : (sigma.length + 1) ^ (s + sigma.length + 1) < sigma.length ^ L) :
    ∃ w ∈ words sigma L, ∀ S : DOL α,
      (∀ x ∈ S.start, x ∈ sigma) → (∀ a ∈ sigma, ∀ x ∈ S.rule a, x ∈ sigma) →
      (∀ a, a ∉ sigma → S.rule a = [a]) → dsize sigma S ≤ s → S.derive n ≠ w := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ w ∈ words sigma L, ∃ S : DOL α,
      (∀ x ∈ S.start, x ∈ sigma) ∧ (∀ a ∈ sigma, ∀ x ∈ S.rule a, x ∈ sigma) ∧
      (∀ a, a ∉ sigma → S.rule a = [a]) ∧ dsize sigma S ≤ s ∧ S.derive n = w := by
    intro w hw
    apply Classical.byContradiction
    intro hne
    apply hno
    refine ⟨w, hw, fun S h1 h2 h3 h4 h5 => hne ⟨S, h1, h2, h3, h4, h5⟩⟩
  have hsub : words sigma L ⊆
      (words (allSyms sigma) (s + sigma.length + 1)).map fun c => (decodeS sigma c).derive n := by
    intro w hw
    obtain ⟨S, h1, h2, h3, h4, h5⟩ := hall w hw
    rw [List.mem_map]
    refine ⟨encodeS sigma S (s - dsize sigma S), ?_, by rw [decode_encode sigma S _ h3]; exact h5⟩
    have := mem_words_of (allSyms sigma) (encodeS sigma S (s - dsize sigma S)) (encodeS_mem sigma S _ h1 h2)
    rw [length_encodeS] at this
    have heq : dsize sigma S + sigma.length + 1 + (s - dsize sigma S) = s + sigma.length + 1 := by omega
    rw [heq] at this
    exact this
  have := nodup_subset_length_le _ _ (words_nodup sigma hs L) hsub
  rw [List.length_map, length_words, length_words] at this
  simp only [allSyms, List.length_cons, List.length_map] at this
  omega

/-- Concrete: some binary word of length 12 needs description size > 4. -/
theorem incompressible_binary_12 (n : Nat) :
    ∃ w ∈ words [0, 1] 12, ∀ S : DOL Nat,
      (∀ x ∈ S.start, x ∈ [0, 1]) → (∀ a ∈ [0, 1], ∀ x ∈ S.rule a, x ∈ [0, 1]) →
      (∀ a, a ∉ [0, 1] → S.rule a = [a]) → dsize [0, 1] S ≤ 4 → S.derive n ≠ w :=
  exists_incompressible [0, 1] (by decide) n 12 4 (by decide)

/-! ### Problem A, the `n > |Σ|` regime: the weak bound

Over the two-letter alphabet `Bool`, a non-erasing system with a short axiom that
derives a word `w` containing both letters, with `|w| < 2^(n/2)`, must have one letter
fixed and the other mapped to `x^p (!x) x^q`: the *insertion family*. -/

/-! #### growth lemmas -/

theorem length_derive_pow (S : DOL α) (hk : ∀ a, 2 ≤ (S.rule a).length) (n : Nat) :
    2 ^ n * S.start.length ≤ (S.derive n).length := by
  induction n with
  | zero => simp [DOL.derive]
  | succ n ih =>
    have := length_step_ge S 2 hk (S.derive n)
    simp only [DOL.derive]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    omega

theorem length_step_mono (S : DOL α) (hne : ∀ a, S.rule a ≠ []) (s : List α) :
    s.length ≤ (S.step s).length := by
  have := length_step_ge S 1 (fun a => List.length_pos.mpr (hne a)) s
  omega

theorem length_derive_mono (S : DOL α) (hne : ∀ a, S.rule a ≠ []) (n : Nat) :
    (S.derive n).length ≤ (S.derive (n + 1)).length :=
  length_step_mono S hne _

/-- `rule x = [!x]` with `!x` growing: every letter at least doubles over two steps. -/
theorem length_step2_ge (S : DOL Bool) (hne : ∀ a, S.rule a ≠ []) (x : Bool)
    (hx : S.rule x = [!x]) (hy : 2 ≤ (S.rule (!x)).length) (s : List Bool) :
    2 * s.length ≤ (S.step (S.step s)).length := by
  induction s with
  | nil => simp
  | cons c s ih =>
    rw [step_cons, step_append, List.length_append, List.length_cons]
    have hc : 2 ≤ (S.step (S.rule c)).length := by
      rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with rfl | rfl
      · rw [hx, step_single]; exact hy
      · exact Nat.le_trans hy (length_step_mono S hne _)
    omega

theorem length_derive_two_pow (S : DOL Bool) (hne : ∀ a, S.rule a ≠ []) (x : Bool)
    (hx : S.rule x = [!x]) (hy : 2 ≤ (S.rule (!x)).length) (n : Nat) :
    2 ^ (n / 2) * S.start.length ≤ (S.derive n).length := by
  have h2 : ∀ m, 2 ^ m * S.start.length ≤ (S.derive (2 * m)).length := by
    intro m
    induction m with
    | zero => simp [DOL.derive]
    | succ m ih =>
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [e]
      simp only [DOL.derive]
      have := length_step2_ge S hne x hx hy (S.derive (2 * m))
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc]
      omega
  have hmono : ∀ k j, k ≤ j → (S.derive k).length ≤ (S.derive j).length := by
    intro k j hkj
    induction j with
    | zero => have : k = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j ih =>
      rcases Nat.lt_or_eq_of_le hkj with h | rfl
      · exact Nat.le_trans (ih (by omega)) (length_derive_mono S hne j)
      · exact Nat.le_refl _
  exact Nat.le_trans (h2 (n / 2)) (hmono _ _ (by omega))

/-- All rules of length 1: lengths never change. -/
theorem length_derive_const (S : DOL α) (h1 : ∀ a, (S.rule a).length = 1) (n : Nat) :
    (S.derive n).length = S.start.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [DOL.derive, length_step]
    rw [← ih]
    have : ∀ s : List α, (s.map fun a => (S.rule a).length).sum = s.length := by
      intro s; induction s with
      | nil => rfl
      | cons a s ihs =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, h1 a, ihs]; omega
    exact this _

/-! #### counting the moving letter -/

theorem count_step (S : DOL α) [BEq α] (y : α) (s : List α) :
    (S.step s).count y = (s.map fun a => (S.rule a).count y).sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [List.count_append, ih]

/-- With `rule x = [x]`, the count of `!x` is multiplied by `k` each step. -/
theorem count_step_fixed (S : DOL Bool) (x : Bool) (hx : S.rule x = [x]) (s : List Bool) :
    (S.step s).count (!x) = s.count (!x) * (S.rule (!x)).count (!x) := by
  rw [count_step]
  induction s with
  | nil => simp
  | cons c s ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hne : (!x) ≠ x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h | h <;> subst c
    · rw [hx, List.count_cons_of_ne hne, List.count_cons_of_ne hne, List.count_nil]; omega
    · rw [List.count_cons_self, Nat.add_mul]; omega

theorem count_derive_fixed (S : DOL Bool) (x : Bool) (hx : S.rule x = [x]) (n : Nat) :
    (S.derive n).count (!x) = S.start.count (!x) * (S.rule (!x)).count (!x) ^ n := by
  induction n with
  | zero => simp [DOL.derive]
  | succ n ih => simp only [DOL.derive, count_step_fixed S x hx, ih, Nat.pow_succ, Nat.mul_assoc]

/-- A Bool list with no `!x` is all `x`'s. -/
theorem eq_replicate_of_count_zero (x : Bool) (l : List Bool) (h : l.count (!x) = 0) :
    l = List.replicate l.length x := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hne : (!x) ≠ x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h' | h' <;> subst c
    · rw [List.count_cons_of_ne hne] at h
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (x :: ·) (ih h)
    · rw [List.count_cons_self] at h; omega

/-- A Bool list with exactly one `!x` is `x^p (!x) x^q`. -/
theorem eq_insertion_of_count_one (x : Bool) (l : List Bool) (h : l.count (!x) = 1) :
    ∃ p q, l = List.replicate p x ++ (!x) :: List.replicate q x := by
  induction l with
  | nil => simp at h
  | cons c l ih =>
    have hne : (!x) ≠ x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h' | h' <;> subst c
    · rw [List.count_cons_of_ne hne] at h
      obtain ⟨p, q, rfl⟩ := ih h
      exact ⟨p + 1, q, by simp [List.replicate_succ]⟩
    · rw [List.count_cons_self] at h
      have h0 : l.count (!x) = 0 := by omega
      refine ⟨0, l.length, ?_⟩
      simp only [List.replicate_zero, List.nil_append]
      exact congrArg ((!x) :: ·) (eq_replicate_of_count_zero x l h0)

/-! #### the theorem -/

theorem step_replicate (S : DOL Bool) (x : Bool) (hx : S.rule x = [x]) (m : Nat) :
    S.step (List.replicate m x) = List.replicate m x := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, step_cons, hx, ih]

/-- Under insertion rules, `n` steps replace every `!x` by `x^(np) (!x) x^(nq)`. -/
theorem derive_insertion (S : DOL Bool) (x : Bool) (p q : Nat) (hx : S.rule x = [x])
    (hy : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x) (n : Nat) :
    S.derive n = S.start.flatMap fun c =>
      if c = x then [x] else List.replicate (n * p) x ++ (!x) :: List.replicate (n * q) x := by
  induction n with
  | zero =>
    simp only [DOL.derive, Nat.zero_mul, List.replicate_zero, List.nil_append]
    have : ∀ s : List Bool, (s.flatMap fun c => if c = x then [x] else [!x]) = s := by
      intro s; induction s with
      | nil => rfl
      | cons c s ih =>
        rw [List.flatMap_cons, ih]
        rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with rfl | rfl <;> simp
    exact (this _).symm
  | succ n ih =>
    simp only [DOL.derive, ih, DOL.step, List.flatMap_assoc]
    congr 1
    funext c
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with rfl | rfl
    · simp [hx]
    · simp only [Bool.not_eq_self, ite_false]
      show S.step (List.replicate (n * p) x ++ (!x) :: List.replicate (n * q) x) = _
      rw [step_append, step_cons, step_replicate S x hx, step_replicate S x hx, hy]
      simp only [Nat.succ_mul, List.append_assoc, List.cons_append]
      rw [← List.append_assoc, List.append_replicate_replicate, List.append_replicate_replicate,
        Nat.add_comm q (n * q)]

theorem small_implies_insertion_aux (S : DOL Bool) (n : Nat) (w : List Bool)
    (hne : ∀ a, S.rule a ≠ []) (hw : S.derive n = w) (hshort : S.start.length < w.length)
    (hboth : ∀ c, c ∈ w) (hsmall : w.length < 2 ^ (n / 2))
    (x : Bool) (h1 : (S.rule x).length = 1) :
    ∃ p q, S.rule x = [x] ∧ S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x ∧
      1 ≤ p + q := by
  have hstart_pos : 1 ≤ S.start.length := by
    apply Nat.lt_of_not_le; intro h0
    have : S.start = [] := List.eq_nil_of_length_eq_zero (by omega)
    have : S.derive n = [] := by rw [derive_eq_iter, this, iter_nil]
    rw [hw] at this; subst this; simp at hboth
  obtain ⟨y, hy⟩ := List.length_eq_one.mp h1
  rcases (show y = x ∨ y = !x by cases x <;> cases y <;> simp) with hyx | hyx <;> subst y
  · -- rule x = [x]: count the moving letter
    have hcount := count_derive_fixed S x hy n
    rw [hw] at hcount
    have hcs : 1 ≤ S.start.count (!x) := by
      apply Nat.lt_of_not_le; intro h0
      have h0 : S.start.count (!x) = 0 := by omega
      have hs := eq_replicate_of_count_zero x _ h0
      have : S.derive n = S.start := by
        rw [derive_eq_iter]
        have : ∀ k, S.iter k S.start = S.start := by
          intro k; induction k with
          | zero => rfl
          | succ k ih => rw [iter_step_comm, ih]; conv => lhs; rw [hs]
                         rw [step_replicate S x hy]; exact hs.symm
        exact this n
      rw [hw] at this
      have := congrArg List.length this; omega
    match hk : (S.rule (!x)).count (!x) with
    | 0 =>
      rw [hk] at hcount
      cases n with
      | zero => simp [DOL.derive] at hw; subst hw; omega
      | succ n =>
        simp at hcount
        have := List.count_eq_zero.mp hcount
        exact absurd (hboth (!x)) this
    | 1 =>
      obtain ⟨p, q, hpq⟩ := eq_insertion_of_count_one x _ hk
      refine ⟨p, q, hy, hpq, ?_⟩
      apply Nat.lt_of_not_le; intro h0
      have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      subst hp hq
      simp at hpq
      have hall : ∀ a, (S.rule a).length = 1 := by
        intro a
        rcases (show a = x ∨ a = !x by cases x <;> cases a <;> simp) with rfl | rfl
        · rw [hy]; rfl
        · rw [hpq]; rfl
      have := length_derive_const S hall n
      rw [hw] at this; omega
    | k + 2 =>
      rw [hk] at hcount
      have hcw : (S.start.count (!x)) * (k + 2) ^ n ≤ w.length :=
        hcount ▸ List.count_le_length _ _
      have h2n : 2 ^ n ≤ (k + 2) ^ n := Nat.pow_le_pow_left (by omega) n
      have h2h : 2 ^ (n / 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
      have : 1 * 2 ^ n ≤ S.start.count (!x) * (k + 2) ^ n :=
        Nat.mul_le_mul hcs h2n
      omega
  · -- rule x = [!x]
    by_cases hy2 : 2 ≤ (S.rule (!x)).length
    · have := length_derive_two_pow S hne x hy hy2 n
      rw [hw] at this
      have : 1 * 2 ^ (n / 2) ≤ 2 ^ (n / 2) * S.start.length := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hstart_pos
      omega
    · have hall : ∀ a, (S.rule a).length = 1 := by
        intro a
        have := List.length_pos.mpr (hne (!x))
        rcases (show a = x ∨ a = !x by cases x <;> cases a <;> simp) with rfl | rfl
        · exact h1
        · omega
      have := length_derive_const S hall n
      rw [hw] at this; omega

/-- **Weak bound** (proved). A non-erasing binary system with a short axiom that derives,
in `n` steps, a word using both letters and shorter than `2^(n/2)`, is an insertion
system: one letter is fixed and the other maps to `x^p (!x) x^q` with `p + q ≥ 1`. -/
theorem small_implies_insertion (S : DOL Bool) (n : Nat) (w : List Bool)
    (hne : ∀ a, S.rule a ≠ []) (hw : S.derive n = w) (hshort : S.start.length < w.length)
    (hboth : ∀ c, c ∈ w) (hsmall : w.length < 2 ^ (n / 2)) :
    ∃ x p q, S.rule x = [x] ∧ S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x ∧
      1 ≤ p + q := by
  by_cases h : ∃ x, (S.rule x).length = 1
  · obtain ⟨x, hx⟩ := h
    obtain ⟨p, q, h1, h2, h3⟩ := small_implies_insertion_aux S n w hne hw hshort hboth hsmall x hx
    exact ⟨x, p, q, h1, h2, h3⟩
  · have hk : ∀ a, 2 ≤ (S.rule a).length := by
      intro a
      have := List.length_pos.mpr (hne a)
      have : (S.rule a).length ≠ 1 := fun h1 => h ⟨a, h1⟩
      omega
    have := length_derive_pow S hk n
    rw [hw] at this
    have hstart_pos : 1 ≤ S.start.length := by
      apply Nat.lt_of_not_le; intro h0
      have : S.start = [] := List.eq_nil_of_length_eq_zero (by omega)
      have : S.derive n = [] := by rw [derive_eq_iter, this, iter_nil]
      rw [hw] at this; subst this; simp at hboth
    have h2h : 2 ^ (n / 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 * 2 ^ n ≤ 2 ^ n * S.start.length := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hstart_pos
    omega

/-! ### The sharp bound: Parikh-vector growth

With `rule x = [!x]`, write `α, β` for the number of `x`, `!x` in `rule (!x)`. The counts
`(p, q)` of `(x, !x)` evolve as `p' = α q`, `q' = p + β q`. Fibonacci growth when
`α, β ≥ 1`; doubling-every-two-steps when `β = 0`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_succ_succ (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

theorem fib_mono_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  induction n with
  | zero => simp [fib]
  | succ n ih => rw [fib_succ_succ]; omega

theorem fib_le_two_pow (n : Nat) : fib (n + 1) ≤ 2 ^ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [fib]
    | 1 => simp [fib]
    | n + 2 =>
      rw [show n + 2 + 1 = n + 1 + 2 from rfl, fib_succ_succ]
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      have : 2 ^ (n + 2) = 2 ^ n + 2 ^ n + 2 ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      omega

/-- The sharp threshold `T(n) = min(F_{n+1}, D(n))`. -/
def sharpT (n : Nat) : Nat :=
  min (fib (n + 1)) (if n % 2 = 0 then 2 * 2 ^ (n / 2) else 3 * 2 ^ (n / 2))

theorem count_add_count_not (x : Bool) (l : List Bool) : l.count x + l.count (!x) = l.length := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hne : (!x) ≠ x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h | h <;> subst c
    · rw [List.count_cons_self, List.count_cons_of_ne hne, List.length_cons]; omega
    · rw [List.count_cons_self, List.count_cons_of_ne hne.symm, List.length_cons]; omega

/-- Two-letter count recurrence for one step. -/
theorem count_step_bool (S : DOL Bool) (x y : Bool) (s : List Bool) :
    (S.step s).count y = s.count x * (S.rule x).count y + s.count (!x) * (S.rule (!x)).count y := by
  rw [count_step]
  induction s with
  | nil => simp
  | cons c s ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hne : (!x) ≠ x := by cases x <;> decide
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h | h <;> subst c
    · rw [List.count_cons_self, List.count_cons_of_ne hne, Nat.succ_mul]; omega
    · rw [List.count_cons_self, List.count_cons_of_ne hne.symm, Nat.succ_mul]; omega

/-- Under `rule x = [!x]`: `p' = α q`, `q' = p + β q`. -/
theorem parikh_step (S : DOL Bool) (x : Bool) (hx : S.rule x = [!x]) (s : List Bool) :
    (S.step s).count x = s.count (!x) * (S.rule (!x)).count x ∧
    (S.step s).count (!x) = s.count x + s.count (!x) * (S.rule (!x)).count (!x) := by
  have hne : (!x) ≠ x := by cases x <;> decide
  constructor
  · rw [count_step_bool S x x, hx, List.count_singleton]
    simp [hne]
  · rw [count_step_bool S x (!x), hx, List.count_singleton]
    simp

/-- Fibonacci lower bound when `α ≥ 1` and `β ≥ 1`. -/
theorem parikh_fib (S : DOL Bool) (x : Bool) (hx : S.rule x = [!x])
    (ha : 1 ≤ (S.rule (!x)).count x) (hb : 1 ≤ (S.rule (!x)).count (!x)) (i : Nat) :
    S.start.count x * fib i + S.start.count (!x) * fib (i + 1) ≤ (S.derive (i + 1)).count x ∧
    S.start.count x * fib (i + 1) + S.start.count (!x) * fib (i + 2) ≤ (S.derive (i + 1)).count (!x) := by
  induction i with
  | zero =>
    simp only [DOL.derive]
    obtain ⟨h1, h2⟩ := parikh_step S x hx S.start
    rw [h1, h2]
    simp only [fib, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    constructor
    · exact Nat.le_mul_of_pos_right _ ha
    · have := Nat.le_mul_of_pos_right (S.start.count (!x)) hb; omega
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    show _ ≤ (S.step (S.derive (i + 1))).count x ∧ _ ≤ (S.step (S.derive (i + 1))).count (!x)
    obtain ⟨h1, h2⟩ := parikh_step S x hx (S.derive (i + 1))
    rw [h1, h2]
    constructor
    · exact Nat.le_trans ih2 (Nat.le_mul_of_pos_right _ ha)
    · rw [fib_succ_succ, fib_succ_succ (i + 1), Nat.mul_add, Nat.mul_add]
      have := Nat.le_mul_of_pos_right ((S.derive (i + 1)).count (!x)) hb
      rw [show fib (i + 1 + 1) = fib (i + 2) from rfl]
      omega

/-- Doubling-every-two-steps when `β = 0`. -/
theorem parikh_double (S : DOL Bool) (x : Bool) (hx : S.rule x = [!x])
    (hb : (S.rule (!x)).count (!x) = 0) (m : Nat) :
    (S.derive (2 * m)).count x = (S.rule (!x)).count x ^ m * S.start.count x ∧
    (S.derive (2 * m)).count (!x) = (S.rule (!x)).count x ^ m * S.start.count (!x) ∧
    (S.derive (2 * m + 1)).count x = (S.rule (!x)).count x ^ (m + 1) * S.start.count (!x) ∧
    (S.derive (2 * m + 1)).count (!x) = (S.rule (!x)).count x ^ m * S.start.count x := by
  induction m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, DOL.derive, Nat.pow_zero, Nat.one_mul, Nat.pow_one]
    obtain ⟨h1, h2⟩ := parikh_step S x hx S.start
    rw [h1, h2, hb]; simp [Nat.mul_comm]
  | succ m ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have e1 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [e1]
    obtain ⟨a1, a2⟩ := parikh_step S x hx (S.derive (2 * m + 1))
    have b1 : (S.derive (2 * m + 1 + 1)).count x = _ := a1
    have b2 : (S.derive (2 * m + 1 + 1)).count (!x) = _ := a2
    obtain ⟨c1, c2⟩ := parikh_step S x hx (S.derive (2 * m + 1 + 1))
    have d1 : (S.derive (2 * m + 1 + 1 + 1)).count x = _ := c1
    have d2 : (S.derive (2 * m + 1 + 1 + 1)).count (!x) = _ := c2
    rw [b1, b2, d1, d2, b1, b2, i3, i4, hb]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_succ]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- With `rule x = [!x]` and `α = 0`, `x` disappears after one step. -/
theorem count_zero_of_alpha_zero (S : DOL Bool) (x : Bool) (hx : S.rule x = [!x])
    (ha : (S.rule (!x)).count x = 0) (n : Nat) : (S.derive (n + 1)).count x = 0 := by
  show (S.step (S.derive n)).count x = 0
  rw [(parikh_step S x hx _).1, ha]; simp

/-- **Sharp bound** (proved). Below `T(n) = min(F_{n+1}, D(n))`, every non-erasing binary
solution with a short axiom is an insertion system. -/
theorem sharp_implies_insertion (S : DOL Bool) (n : Nat) (w : List Bool)
    (hne : ∀ a, S.rule a ≠ []) (hw : S.derive n = w) (hshort : S.start.length < w.length)
    (hboth : ∀ c, c ∈ w) (hsmall : w.length < sharpT n) :
    ∃ x p q, S.rule x = [x] ∧ S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x ∧
      1 ≤ p + q := by
  -- reduce to the weak theorem's case analysis, with sharper bounds in the exponential cases
  have hstart_pos : 1 ≤ S.start.length := by
    apply Nat.lt_of_not_le; intro h0
    have : S.start = [] := List.eq_nil_of_length_eq_zero (by omega)
    have : S.derive n = [] := by rw [derive_eq_iter, this, iter_nil]
    rw [hw] at this; subst this; simp at hboth
  have hT_fib : sharpT n ≤ fib (n + 1) := Nat.min_le_left _ _
  have hT_D : sharpT n ≤ (if n % 2 = 0 then 2 * 2 ^ (n / 2) else 3 * 2 ^ (n / 2)) :=
    Nat.min_le_right _ _
  have hn1 : 1 ≤ n := by
    apply Nat.lt_of_not_le; intro h0
    have : n = 0 := by omega
    subst this; simp [DOL.derive] at hw; subst hw; omega
  by_cases h : ∃ x, (S.rule x).length = 1
  · obtain ⟨x, h1⟩ := h
    obtain ⟨y, hy⟩ := List.length_eq_one.mp h1
    rcases (show y = x ∨ y = !x by cases x <;> cases y <;> simp) with hyx | hyx <;> subst y
    · -- rule x = [x]: identical to the weak case (only uses |w| ≥ 2^n ≥ fib(n+1) bound)
      have hcount := count_derive_fixed S x hy n
      rw [hw] at hcount
      have hcs : 1 ≤ S.start.count (!x) := by
        apply Nat.lt_of_not_le; intro h0
        have h0 : S.start.count (!x) = 0 := by omega
        have hs := eq_replicate_of_count_zero x _ h0
        have : S.derive n = S.start := by
          rw [derive_eq_iter]
          have : ∀ k, S.iter k S.start = S.start := by
            intro k; induction k with
            | zero => rfl
            | succ k ih => rw [iter_step_comm, ih]; conv => lhs; rw [hs]
                           rw [step_replicate S x hy]; exact hs.symm
          exact this n
        rw [hw] at this
        have := congrArg List.length this; omega
      match hk : (S.rule (!x)).count (!x) with
      | 0 =>
        rw [hk] at hcount
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp at hcount
        exact absurd (hboth (!x)) (List.count_eq_zero.mp hcount)
      | 1 =>
        obtain ⟨p, q, hpq⟩ := eq_insertion_of_count_one x _ hk
        refine ⟨x, p, q, hy, hpq, ?_⟩
        apply Nat.lt_of_not_le; intro h0
        have hp : p = 0 := by omega
        have hq : q = 0 := by omega
        subst hp hq
        simp at hpq
        have hall : ∀ a, (S.rule a).length = 1 := by
          intro a
          rcases (show a = x ∨ a = !x by cases x <;> cases a <;> simp) with rfl | rfl
          · rw [hy]; rfl
          · rw [hpq]; rfl
        have := length_derive_const S hall n
        rw [hw] at this; omega
      | k + 2 =>
        rw [hk] at hcount
        have hcw : (S.start.count (!x)) * (k + 2) ^ n ≤ w.length :=
          hcount ▸ List.count_le_length _ _
        have h2n : 2 ^ n ≤ (k + 2) ^ n := Nat.pow_le_pow_left (by omega) n
        have hf := fib_le_two_pow n
        have : 1 * 2 ^ n ≤ S.start.count (!x) * (k + 2) ^ n := Nat.mul_le_mul hcs h2n
        omega
    · -- rule x = [!x]: Parikh analysis
      have hlen := count_add_count_not x (S.rule (!x))
      have hlenw := count_add_count_not x w
      have hlen0 := count_add_count_not x S.start
      by_cases hy2 : 2 ≤ (S.rule (!x)).length
      · match ha : (S.rule (!x)).count x, hb : (S.rule (!x)).count (!x) with
        | 0, _ =>
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          have := count_zero_of_alpha_zero S x hy ha m
          rw [hw] at this
          exact absurd (hboth x) (List.count_eq_zero.mp this)
        | a + 1, 0 =>
          -- doubling
          have hα : 2 ≤ a + 1 := by omega
          have hpw : 1 ≤ w.count x := List.count_pos_iff.mpr (hboth x)
          have hqw : 1 ≤ w.count (!x) := List.count_pos_iff.mpr (hboth (!x))
          obtain ⟨d1, d2, d3, d4⟩ := parikh_double S x hy hb (n / 2)
          rw [ha] at d1 d2 d3 d4
          simp only [Nat.succ_eq_add_one] at d1 d2 d3 d4
          have h2m : 2 ^ (n / 2) ≤ (a + 1) ^ (n / 2) := Nat.pow_le_pow_left hα _
          have h2m1 : 2 ^ (n / 2 + 1) ≤ (a + 1) ^ (n / 2 + 1) := Nat.pow_le_pow_left hα _
          rcases Nat.mod_two_eq_zero_or_one n with he | ho
          · have hn2 : 2 * (n / 2) = n := by omega
            rw [hn2, hw] at d1 d2
            rw [he] at hT_D; simp at hT_D
            have hp0 : 1 ≤ S.start.count x := by
              apply Nat.lt_of_not_le; intro h0; have : S.start.count x = 0 := by omega
              rw [this] at d1; omega
            have hq0 : 1 ≤ S.start.count (!x) := by
              apply Nat.lt_of_not_le; intro h0; have : S.start.count (!x) = 0 := by omega
              rw [this] at d2; omega
            have := Nat.mul_le_mul h2m hp0
            have := Nat.mul_le_mul h2m hq0
            omega
          · have hn2 : 2 * (n / 2) + 1 = n := by omega
            rw [hn2, hw] at d3 d4
            rw [ho] at hT_D; simp at hT_D
            have hp0 : 1 ≤ S.start.count x := by
              apply Nat.lt_of_not_le; intro h0; have : S.start.count x = 0 := by omega
              rw [this] at d4; omega
            have hq0 : 1 ≤ S.start.count (!x) := by
              apply Nat.lt_of_not_le; intro h0; have : S.start.count (!x) = 0 := by omega
              rw [this] at d3; omega
            have := Nat.mul_le_mul h2m1 hq0
            have := Nat.mul_le_mul h2m hp0
            have : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by rw [Nat.pow_succ]; omega
            omega
        | a + 1, b + 1 =>
          -- Fibonacci
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          obtain ⟨f1, f2⟩ := parikh_fib S x hy (by omega) (by omega) m
          rw [hw] at f1 f2
          rw [show fib (m + 1 + 1) = fib (m + 2) from rfl] at f2 hT_fib
          have hpos : 1 ≤ S.start.count x + S.start.count (!x) := by omega
          have e1 : fib m + fib (m + 1) = fib (m + 2) := (fib_succ_succ m).symm
          have e2 : fib (m + 1) + fib (m + 2) = fib (m + 3) := (fib_succ_succ (m + 1)).symm
          have hA : S.start.count x * fib (m + 2)
              ≤ S.start.count x * fib m + S.start.count x * fib (m + 1) := by
            rw [← Nat.mul_add, e1]; exact Nat.le_refl _
          have hB : S.start.count (!x) * fib (m + 3)
              ≤ S.start.count (!x) * fib (m + 1) + S.start.count (!x) * fib (m + 2) := by
            rw [← Nat.mul_add, e2]; exact Nat.le_refl _
          have hD : S.start.count (!x) * fib (m + 2) ≤ S.start.count (!x) * fib (m + 3) :=
            Nat.mul_le_mul_left _ (fib_mono_succ (m + 2))
          have hE : fib (m + 2) ≤ S.start.count x * fib (m + 2) + S.start.count (!x) * fib (m + 2) := by
            rw [← Nat.add_mul]; exact Nat.le_mul_of_pos_left _ hpos
          omega
      · have hall : ∀ a, (S.rule a).length = 1 := by
          intro a
          have := List.length_pos.mpr (hne (!x))
          rcases (show a = x ∨ a = !x by cases x <;> cases a <;> simp) with rfl | rfl
          · exact h1
          · omega
        have := length_derive_const S hall n
        rw [hw] at this; omega
  · have hk : ∀ a, 2 ≤ (S.rule a).length := by
      intro a
      have := List.length_pos.mpr (hne a)
      have : (S.rule a).length ≠ 1 := fun h1 => h ⟨a, h1⟩
      omega
    have := length_derive_pow S hk n
    rw [hw] at this
    have hf := fib_le_two_pow n
    have : 1 * 2 ^ n ≤ 2 ^ n * S.start.length := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hstart_pos
    omega

/-! ### The run-length criterion for insertion words

`runs x w` lists the lengths of the maximal `x`-blocks of `w`, separated by the `!x`'s.
`Crit n x w`: at least one `!x`; every inner run ≥ n; leading or trailing run ≥ n. -/

def runs (x : Bool) : List Bool → List Nat
  | [] => [0]
  | c :: t => if c = x then
      (match runs x t with | r :: rs => (r + 1) :: rs | [] => [1])
    else 0 :: runs x t

theorem runs_ne_nil (x : Bool) (w : List Bool) : runs x w ≠ [] := by
  induction w with
  | nil => simp [runs]
  | cons c t ih =>
    simp only [runs]
    split
    · split <;> simp
    · simp

theorem runs_x_cons (x : Bool) (t : List Bool) :
    runs x (x :: t) = ((runs x t).headD 0 + 1) :: (runs x t).drop 1 := by
  simp only [runs, ite_true]
  split
  · rename_i r rs h; rw [h]; rfl
  · rename_i h; exact absurd h (runs_ne_nil x t)

theorem runs_notx_cons (x : Bool) (t : List Bool) : runs x ((!x) :: t) = 0 :: runs x t := by
  have : (!x) = x ↔ False := by cases x <;> simp
  simp [runs, this]

theorem runs_replicate_append (x : Bool) (k : Nat) (t : List Bool) :
    runs x (List.replicate k x ++ t) = ((runs x t).headD 0 + k) :: (runs x t).drop 1 := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero]
    obtain ⟨r, rs, h⟩ : ∃ r rs, runs x t = r :: rs := by
      cases h : runs x t with
      | nil => exact absurd h (runs_ne_nil x t)
      | cons r rs => exact ⟨r, rs, rfl⟩
    rw [h]; rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, runs_x_cons, ih]
    simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
    rfl

/-- Rebuild a word from its runs. -/
def fromRuns (x : Bool) : List Nat → List Bool
  | [] => []
  | [r] => List.replicate r x
  | r :: rs => List.replicate r x ++ (!x) :: fromRuns x rs

theorem fromRuns_runs (x : Bool) (w : List Bool) : fromRuns x (runs x w) = w := by
  induction w with
  | nil => rfl
  | cons c t ih =>
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h | h <;> subst c
    · rw [runs_x_cons]
      obtain ⟨r, rs, h⟩ : ∃ r rs, runs x t = r :: rs := by
        cases h : runs x t with
        | nil => exact absurd h (runs_ne_nil x t)
        | cons r rs => exact ⟨r, rs, rfl⟩
      rw [h] at ih ⊢
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
      cases rs with
      | nil => simp only [fromRuns, List.replicate_succ] at ih ⊢; rw [ih]
      | cons r' rs' => simp only [fromRuns, List.replicate_succ, List.cons_append] at ih ⊢; rw [ih]
    · rw [runs_notx_cons]
      obtain ⟨r, rs, h⟩ : ∃ r rs, runs x t = r :: rs := by
        cases h : runs x t with
        | nil => exact absurd h (runs_ne_nil x t)
        | cons r rs => exact ⟨r, rs, rfl⟩
      rw [h] at ih ⊢
      simp only [fromRuns, List.replicate_zero, List.nil_append]
      rw [ih]

/-- The insertion map on a word. -/
def ins (x : Bool) (a b : Nat) (ω : List Bool) : List Bool :=
  ω.flatMap fun c => if c = x then [x] else List.replicate a x ++ (!x) :: List.replicate b x

/-- How runs transform under insertion: first `+a`, last `+b`, inner `+(a+b)`. -/
def adjust (a b : Nat) : List Nat → List Nat
  | [] => []
  | [r] => [r]
  | r :: rs => (r + a) :: (match adjust a b rs with | s :: ss => (s + b) :: ss | [] => [])

theorem runs_ins (x : Bool) (a b : Nat) (ω : List Bool) :
    runs x (ins x a b ω) = adjust a b (runs x ω) := by
  induction ω with
  | nil => rfl
  | cons c t ih =>
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h | h <;> subst c
    · have e : ins x a b (x :: t) = x :: ins x a b t := by simp [ins]
      rw [e, runs_x_cons, runs_x_cons, ih]
      obtain ⟨r, rs, h⟩ : ∃ r rs, runs x t = r :: rs := by
        cases h : runs x t with
        | nil => exact absurd h (runs_ne_nil x t)
        | cons r rs => exact ⟨r, rs, rfl⟩
      rw [h]
      cases rs with
      | nil => try rfl
      | cons r' rs' =>
        simp only [adjust, List.headD_cons, List.drop_succ_cons, List.drop_zero]
        rw [Nat.add_right_comm]
    · have e : ins x a b ((!x) :: t)
          = List.replicate a x ++ (!x) :: (List.replicate b x ++ ins x a b t) := by
        simp [ins]
      rw [e, runs_replicate_append, runs_notx_cons, runs_replicate_append, ih, runs_notx_cons]
      obtain ⟨r, rs, h⟩ : ∃ r rs, runs x t = r :: rs := by
        cases h : runs x t with
        | nil => exact absurd h (runs_ne_nil x t)
        | cons r rs => exact ⟨r, rs, rfl⟩
      rw [h]
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero, adjust, Nat.zero_add]
      cases rs with
      | nil => simp [adjust]
      | cons r' rs' => simp [adjust]

/-- The criterion. -/
def Crit (n : Nat) (x : Bool) (w : List Bool) : Prop :=
  2 ≤ (runs x w).length ∧ (∀ r ∈ ((runs x w).drop 1).dropLast, n ≤ r) ∧
    (n ≤ (runs x w).headD 0 ∨ n ≤ (runs x w).getLastD 0)

instance (n : Nat) (x : Bool) (w : List Bool) : Decidable (Crit n x w) := by
  unfold Crit; infer_instance

/-! #### necessity -/

theorem adjust_length (a b : Nat) (rs : List Nat) : (adjust a b rs).length = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    cases rs with
    | nil => rfl
    | cons r' rs' =>
      simp only [adjust, List.length_cons]
      cases h : adjust a b (r' :: rs') with
      | nil => rw [h] at ih; simp at ih
      | cons s ss => rw [h] at ih; simp at ih ⊢; omega

theorem adjust_spec (a b : Nat) (rs : List Nat) (h2 : 2 ≤ rs.length) :
    a ≤ (adjust a b rs).headD 0 ∧ b ≤ (adjust a b rs).getLastD 0 ∧
    ∀ r ∈ ((adjust a b rs).drop 1).dropLast, a + b ≤ r := by
  induction rs with
  | nil => simp at h2
  | cons r rs ih =>
    cases rs with
    | nil => simp at h2
    | cons r' rs' =>
      simp only [adjust]
      cases rs' with
      | nil => simp [adjust]
      | cons r'' rs'' =>
        obtain ⟨i1, i2, i3⟩ := ih (by simp)
        cases h : adjust a b (r' :: r'' :: rs'') with
        | nil => have := adjust_length a b (r' :: r'' :: rs''); rw [h] at this; simp at this
        | cons s ss =>
          rw [h] at i1 i2 i3
          simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero] at i1 i2 i3 ⊢
          refine ⟨by omega, ?_, ?_⟩
          · cases ss with
            | nil => simp at i2 ⊢; try omega
            | cons u us => simpa using i2
          · intro q hq
            cases ss with
            | nil => simp at hq
            | cons u us =>
              simp only [List.dropLast_cons₂, List.mem_cons] at hq i3
              rcases hq with rfl | hq
              · omega
              · exact i3 q hq

theorem runs_length_pos_of_mem (x : Bool) (w : List Bool) (hm : (!x) ∈ w) :
    2 ≤ (runs x w).length := by
  induction w with
  | nil => simp at hm
  | cons c t ih =>
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with hc | hc <;> subst c
    · have hne : (!x) ≠ x := by cases x <;> decide
      have hmt : (!x) ∈ t := by
        rcases List.mem_cons.mp hm with h' | h'
        · exact absurd h' hne
        · exact h'
      have := ih hmt
      rw [runs_x_cons]
      obtain ⟨r, rs, hr⟩ : ∃ r rs, runs x t = r :: rs := by
        cases hr : runs x t with
        | nil => exact absurd hr (runs_ne_nil x t)
        | cons r rs => exact ⟨r, rs, rfl⟩
      rw [hr] at this ⊢; simpa using this
    · rw [runs_notx_cons]
      have := List.length_pos.mpr (runs_ne_nil x t)
      simp; omega

/-- **Necessity.** An insertion system with a short axiom deriving `w` forces the criterion. -/
theorem crit_of_insertion (S : DOL Bool) (x : Bool) (p q n : Nat) (hx : S.rule x = [x])
    (hy : S.rule (!x) = List.replicate p x ++ (!x) :: List.replicate q x) (hpq : 1 ≤ p + q)
    (w : List Bool) (hw : S.derive n = w) (hmem : (!x) ∈ w) : Crit n x w := by
  have hform : w = ins x (n * p) (n * q) S.start := by
    rw [← hw, derive_insertion S x p q hx hy n]; rfl
  have hmem0 : (!x) ∈ S.start := by
    rw [hform] at hmem
    simp only [ins, List.mem_flatMap] at hmem
    obtain ⟨c, hc, hcm⟩ := hmem
    rcases (show c = x ∨ c = !x by cases x <;> cases c <;> simp) with h | h <;> subst c
    · exfalso; cases x <;> simp at hcm
    · exact hc
  have h2 := runs_length_pos_of_mem x S.start hmem0
  obtain ⟨a1, a2, a3⟩ := adjust_spec (n * p) (n * q) (runs x S.start) h2
  refine ⟨?_, ?_, ?_⟩
  · rw [hform, runs_ins, adjust_length]; exact h2
  · intro r hr
    rw [hform, runs_ins] at hr
    have := a3 r hr
    have : n ≤ n * p + n * q := by rw [← Nat.mul_add]; exact Nat.le_mul_of_pos_right _ hpq
    omega
  · rw [hform, runs_ins]
    rcases Nat.lt_or_ge p 1 with hp | hp
    · have hq : 1 ≤ q := by omega
      right; have := Nat.le_mul_of_pos_right n hq; omega
    · left; have := Nat.le_mul_of_pos_right n hp; omega

/-! #### sufficiency -/

/-- Subtract `n` from every run except the last (resp. first). -/
def shrinkL (n : Nat) : List Nat → List Nat
  | [] => []
  | [r] => [r]
  | r :: rs => (r - n) :: shrinkL n rs

theorem adjust_shrinkL (n : Nat) (rs : List Nat) (h2 : 2 ≤ rs.length)
    (hinner : ∀ r ∈ (rs.drop 1).dropLast, n ≤ r) (hhead : n ≤ rs.headD 0) :
    adjust n 0 (shrinkL n rs) = rs := by
  induction rs with
  | nil => simp at h2
  | cons r rs ih =>
    cases rs with
    | nil => simp at h2
    | cons r' rs' =>
      simp only [shrinkL, adjust]
      simp only [List.headD_cons] at hhead
      cases rs' with
      | nil => simp [shrinkL, adjust]; omega
      | cons r'' rs'' =>
        have hr' : n ≤ r' := hinner r' (by simp)
        have := ih (by simp) (fun q hq => hinner q (by
          simp only [List.drop_succ_cons, List.drop_zero, List.dropLast_cons_cons, List.mem_cons] at hq ⊢
          exact Or.inr hq)) (by simpa using hr')
        simp only [shrinkL] at this ⊢
        rw [show adjust n 0 ((r - n) :: (r' - n) :: shrinkL n (r'' :: rs''))
          = (r - n + n) :: (match adjust n 0 ((r' - n) :: shrinkL n (r'' :: rs'')) with
              | s :: ss => (s + 0) :: ss | [] => []) from rfl, this]
        simp; omega

theorem ins_eq_of_runs (x : Bool) (a b : Nat) (ω w : List Bool)
    (h : runs x (ins x a b ω) = runs x w) : ins x a b ω = w := by
  rw [← fromRuns_runs x (ins x a b ω), h, fromRuns_runs]

/-- The system realizing a word that meets the criterion with a long leading run. -/
def insSys (x : Bool) (n : Nat) (w : List Bool) : DOL Bool :=
  ⟨fromRuns x (shrinkL n (runs x w)),
   fun c => if c = x then [x] else List.replicate 1 x ++ (!x) :: List.replicate 0 x⟩

theorem insSys_derive (x : Bool) (n : Nat) (w : List Bool) (hc : Crit n x w)
    (hhead : n ≤ (runs x w).headD 0) : (insSys x n w).derive n = w := by
  obtain ⟨h2, hinner, -⟩ := hc
  have hx : (insSys x n w).rule x = [x] := by simp [insSys]
  have hy : (insSys x n w).rule (!x) = List.replicate 1 x ++ (!x) :: List.replicate 0 x := by
    have : (!x) = x ↔ False := by cases x <;> simp
    simp [insSys, this]
  rw [derive_insertion _ x 1 0 hx hy n]
  show ins x (n * 1) (n * 0) (fromRuns x (shrinkL n (runs x w))) = w
  simp only [Nat.mul_one, Nat.mul_zero]
  apply ins_eq_of_runs
  rw [runs_ins]
  -- runs (fromRuns rs) = rs for the shrunken list (nonempty, length ≥ 2)
  have hrr : ∀ rs : List Nat, rs ≠ [] → runs x (fromRuns x rs) = rs := by
    intro rs
    induction rs with
    | nil => intro h; exact absurd rfl h
    | cons r rs ih =>
      intro _
      cases rs with
      | nil => simp only [fromRuns]; rw [← List.append_nil (List.replicate r x), runs_replicate_append]; simp [runs]
      | cons r' rs' =>
        simp only [fromRuns]
        rw [runs_replicate_append, runs_notx_cons, ih (by simp)]
        simp
  have hsl : shrinkL n (runs x w) ≠ [] := by
    cases h : runs x w with
    | nil => exact absurd h (runs_ne_nil x w)
    | cons r rs => cases rs <;> simp [shrinkL]
  rw [hrr _ hsl, adjust_shrinkL n _ h2 hinner hhead]

theorem length_fromRuns_shrinkL_lt (x : Bool) (n : Nat) (hn : 1 ≤ n) (w : List Bool)
    (h2 : 2 ≤ (runs x w).length) (hhead : n ≤ (runs x w).headD 0) :
    (fromRuns x (shrinkL n (runs x w))).length < w.length := by
  have hlen : ∀ rs : List Nat, (fromRuns x rs).length = rs.sum + (rs.length - 1) := by
    intro rs; induction rs with
    | nil => rfl
    | cons r rs ih =>
      cases rs with
      | nil => simp [fromRuns]
      | cons r' rs' =>
        simp only [fromRuns, List.length_append, List.length_replicate, List.length_cons, ih,
          List.sum_cons]
        simp; omega
  have key : ∀ l : List Nat, (shrinkL n l).sum ≤ l.sum ∧ (shrinkL n l).length = l.length := by
    intro l; induction l with
    | nil => simp [shrinkL]
    | cons u l ihl =>
      cases l with
      | nil => simp [shrinkL]
      | cons v l' =>
        have e : shrinkL n (u :: v :: l') = (u - n) :: shrinkL n (v :: l') := rfl
        rw [e]; simp only [List.sum_cons, List.length_cons] at ihl ⊢; omega
  obtain ⟨r, rs, hr⟩ : ∃ r rs, runs x w = r :: rs := by
    cases hr : runs x w with
    | nil => exact absurd hr (runs_ne_nil x w)
    | cons r rs => exact ⟨r, rs, rfl⟩
  cases rs with
  | nil => rw [hr] at h2; simp at h2
  | cons r' rs' =>
    rw [hr] at hhead; simp only [List.headD_cons] at hhead
    conv => rhs; rw [← fromRuns_runs x w]
    rw [hr, hlen, hlen]
    have e : shrinkL n (r :: r' :: rs') = (r - n) :: shrinkL n (r' :: rs') := rfl
    rw [e]; simp only [List.sum_cons, List.length_cons]
    have := key (r' :: rs')
    simp only [List.sum_cons, List.length_cons] at this ⊢
    omega

/-- **Sufficiency.** A word meeting the criterion is derived by an insertion system with a
shorter axiom (reverse the word for the trailing-run case). -/
theorem insertion_of_crit (n : Nat) (hn : 1 ≤ n) (x : Bool) (w : List Bool) (hc : Crit n x w)
    (hhead : n ≤ (runs x w).headD 0) :
    ∃ S : DOL Bool, S.rule x = [x] ∧ S.start.length < w.length ∧ S.derive n = w :=
  ⟨insSys x n w, by simp [insSys], length_fromRuns_shrinkL_lt x n hn w hc.1 hhead,
   insSys_derive x n w hc hhead⟩

/-! #### sharpness witnesses, checked by kernel evaluation -/

/-- Fibonacci system `a → ab, b → a` (false = a, true = b), axiom `b`. -/
def fibS : DOL Bool := ⟨[true], fun c => if c then [false] else [false, true]⟩
/-- Doubling system `a → b, b → aa` with axiom `ab`. -/
def dblS : DOL Bool := ⟨[false, true], fun c => if c then [false, false] else [true]⟩

/-- For `n = 2..7`, `fibS.derive n` has length exactly `T(n)` and meets neither criterion. -/
theorem sharp_witness_fib :
    ∀ n ∈ [2, 3, 4, 5, 6, 7], (fibS.derive n).length = sharpT n ∧
      fibS.start.length < (fibS.derive n).length ∧
      ¬ Crit n false (fibS.derive n) ∧ ¬ Crit n true (fibS.derive n) := by decide

-- For `n = 8, 9`, `dblS.derive n` has length exactly `T(n)` and meets neither criterion.
set_option maxRecDepth 100000 in
theorem sharp_witness_dbl :
    ∀ n ∈ [8, 9], (dblS.derive n).length = sharpT n ∧
      dblS.start.length < (dblS.derive n).length ∧
      ¬ Crit n false (dblS.derive n) ∧ ¬ Crit n true (dblS.derive n) := by decide

/-! ### Sharpness for every `n`

For `n ≥ 2` some word of length exactly `T(n)` is derivable (non-erasing, short axiom, both
letters) and fails both criteria: the Fibonacci iterate for `n ≤ 7`, the doubling word for `n ≥ 8`. -/

/-! #### Crit forces a long run, hence a long factor -/

theorem getLastD_mem (l : List Nat) (d : Nat) (h : l ≠ []) : l.getLastD d ∈ l := by
  induction l generalizing d with
  | nil => exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' => rw [List.getLastD_cons]; exact List.mem_cons_of_mem _ (ih a (by simp))

theorem headD_mem (l : List Nat) (d : Nat) (h : l ≠ []) : l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

theorem crit_imp_run (n : Nat) (x : Bool) (w : List Bool) (hc : Crit n x w) :
    ∃ r ∈ runs x w, n ≤ r := by
  obtain ⟨-, -, h⟩ := hc
  rcases h with h | h
  · exact ⟨_, headD_mem _ _ (runs_ne_nil x w), h⟩
  · exact ⟨_, getLastD_mem _ _ (runs_ne_nil x w), h⟩

theorem fromRuns_factor (x : Bool) (rs : List Nat) (r : Nat) (hr : r ∈ rs) :
    ∃ u v, fromRuns x rs = u ++ List.replicate r x ++ v := by
  induction rs with
  | nil => simp at hr
  | cons r0 rs ih =>
    cases rs with
    | nil => simp at hr; subst hr; exact ⟨[], [], by simp [fromRuns]⟩
    | cons r1 rest =>
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨[], (!x) :: fromRuns x (r1 :: rest), by simp [fromRuns]⟩
      · obtain ⟨u, v, huv⟩ := ih hr'
        exact ⟨List.replicate r0 x ++ (!x) :: u, v, by simp [fromRuns, huv]⟩

theorem crit_imp_factor (n : Nat) (x : Bool) (w : List Bool) (hc : Crit n x w) :
    ∃ u v, w = u ++ List.replicate n x ++ v := by
  obtain ⟨r, hr, hnr⟩ := crit_imp_run n x w hc
  obtain ⟨u, v, huv⟩ := fromRuns_factor x (runs x w) r hr
  rw [fromRuns_runs] at huv
  refine ⟨u, List.replicate (r - n) x ++ v, ?_⟩
  have e : List.replicate r x = List.replicate n x ++ List.replicate (r - n) x := by
    rw [List.append_replicate_replicate]; congr 1; omega
  rw [huv, e, List.append_assoc, List.append_assoc, List.append_assoc]

/-! #### the Fibonacci iterates avoid `bb` and `aaa` -/

def nobb : List Bool → Bool
  | true :: true :: _ => false
  | _ :: t => nobb t
  | [] => true

def noaaa : List Bool → Bool
  | false :: false :: false :: _ => false
  | _ :: t => noaaa t
  | [] => true

theorem nobb_cons (c : Bool) (t : List Bool) : nobb (c :: t) = true →
    nobb t = true := by
  cases c <;> cases t with
  | nil => simp [nobb]
  | cons d t' => cases d <;> simp [nobb]

theorem noaaa_cons (c : Bool) (t : List Bool) : noaaa (c :: t) = true → noaaa t = true := by
  cases c <;> cases t with
  | nil => simp [noaaa]
  | cons d t' =>
    cases d <;> cases t' with
    | nil => simp [noaaa]
    | cons e t'' => cases e <;> simp [noaaa]

theorem nobb_factor (u v : List Bool) : nobb (u ++ [true, true] ++ v) = false := by
  induction u with
  | nil => rfl
  | cons c u ih =>
    rw [List.cons_append, List.cons_append]
    cases h : nobb (c :: (u ++ [true, true] ++ v))
    · rfl
    · have := nobb_cons c _ h; rw [ih] at this; exact absurd this Bool.false_ne_true

theorem noaaa_factor (u v : List Bool) : noaaa (u ++ [false, false, false] ++ v) = false := by
  induction u with
  | nil => rfl
  | cons c u ih =>
    rw [List.cons_append, List.cons_append]
    cases h : noaaa (c :: (u ++ [false, false, false] ++ v))
    · rfl
    · have := noaaa_cons c _ h; rw [ih] at this; exact absurd this Bool.false_ne_true

/-- Every nonempty Fibonacci step starts with `a`. -/
theorem fib_step_head (t : List Bool) (ht : t ≠ []) : ∃ r, fibS.step t = false :: r := by
  cases t with
  | nil => exact absurd rfl ht
  | cons c t' =>
    cases c
    · exact ⟨true :: fibS.step t', rfl⟩
    · exact ⟨fibS.step t', rfl⟩

theorem fib_step_nobb_noaaa (w : List Bool) (h : nobb w = true) :
    nobb (fibS.step w) = true ∧ noaaa (fibS.step w) = true := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons c t ih =>
    obtain ⟨ih1, ih2⟩ := ih (nobb_cons c t h)
    cases c
    · -- a ↦ ab
      show nobb (false :: true :: fibS.step t) = true ∧ noaaa (false :: true :: fibS.step t) = true
      cases ht : t with
      | nil => exact ⟨rfl, rfl⟩
      | cons d t' =>
        obtain ⟨r, hr⟩ := fib_step_head (d :: t') (by simp)
        rw [← ht] at hr ⊢
        rw [hr] at ih1 ih2 ⊢
        exact ⟨by simpa [nobb] using ih1, by simpa [noaaa] using ih2⟩
    · -- b ↦ a
      show nobb (false :: fibS.step t) = true ∧ noaaa (false :: fibS.step t) = true
      cases ht : t with
      | nil => exact ⟨rfl, rfl⟩
      | cons d t' =>
        cases d
        · -- t = a :: t' ; step t = a :: b :: step t'
          have e : fibS.step (false :: t') = false :: true :: fibS.step t' := rfl
          rw [← ht] at e ⊢
          rw [e] at ih1 ih2 ⊢
          exact ⟨by simpa [nobb] using ih1, by simpa [noaaa] using ih2⟩
        · -- t = b :: t' contradicts nobb (b :: b :: t')
          subst ht; simp [nobb] at h

theorem fib_derive_nobb_noaaa (n : Nat) :
    nobb (fibS.derive n) = true ∧ noaaa (fibS.derive n) = true := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => exact fib_step_nobb_noaaa _ ih.1

theorem fib_not_crit (n : Nat) (hn : 3 ≤ n) (x : Bool) : ¬ Crit n x (fibS.derive n) := by
  intro hc
  obtain ⟨u, v, huv⟩ := crit_imp_factor n x _ hc
  obtain ⟨h1, h2⟩ := fib_derive_nobb_noaaa n
  cases x
  · -- a^n with n ≥ 3 contains aaa
    have e : List.replicate n false = [false, false, false] ++ List.replicate (n - 3) false := by
      show List.replicate n false = List.replicate 3 false ++ List.replicate (n - 3) false
      rw [List.append_replicate_replicate]; congr 1; omega
    have : fibS.derive n = u ++ [false, false, false] ++ (List.replicate (n - 3) false ++ v) := by
      rw [huv, e]; simp [List.append_assoc]
    rw [this, noaaa_factor] at h2; exact Bool.noConfusion h2
  · have e : List.replicate n true = [true, true] ++ List.replicate (n - 2) true := by
      show List.replicate n true = List.replicate 2 true ++ List.replicate (n - 2) true
      rw [List.append_replicate_replicate]; congr 1; omega
    have : fibS.derive n = u ++ [true, true] ++ (List.replicate (n - 2) true ++ v) := by
      rw [huv, e]; simp [List.append_assoc]
    rw [this, nobb_factor] at h1; exact Bool.noConfusion h1

/-! #### Fibonacci lengths and letters -/

theorem fib_counts (n : Nat) :
    (fibS.derive (n + 1)).count false = fib (n + 1) ∧ (fibS.derive (n + 1)).count true = fib n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    show (fibS.step (fibS.derive (n + 1))).count false = _ ∧
         (fibS.step (fibS.derive (n + 1))).count true = _
    rw [count_step_bool fibS false false, count_step_bool fibS false true]
    simp only [Bool.not_false]
    have r1 : fibS.rule false = [false, true] := rfl
    have r2 : fibS.rule true = [false] := rfl
    rw [r1, r2, ih1, ih2]
    simp [List.count_cons, fib_succ_succ]
    omega

theorem fib_length (n : Nat) : (fibS.derive n).length = fib (n + 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    obtain ⟨h1, h2⟩ := fib_counts m
    have := count_add_count_not false (fibS.derive (m + 1))
    simp only [Bool.not_false] at this
    rw [← this, h1, h2, fib_succ_succ, Nat.add_comm]

theorem fib_both (n : Nat) (hn : 2 ≤ n) : ∀ c, c ∈ fibS.derive n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h1, h2⟩ := fib_counts m
  intro c
  have hpos : ∀ k, 1 ≤ k → 1 ≤ fib k := by
    intro k hk; induction k with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => decide
      | succ k => rw [fib_succ_succ]; have := ih (by omega); omega
  cases c
  · exact List.count_pos_iff.mp (by rw [h1]; exact hpos _ (by omega))
  · exact List.count_pos_iff.mp (by rw [h2]; exact hpos _ (by omega))

/-! #### the doubling word -/

theorem dbl_step_a (m : Nat) : dblS.step (List.replicate m false) = List.replicate m true := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, step_cons, ih]; rfl

theorem dbl_step_b (m : Nat) : dblS.step (List.replicate m true) = List.replicate (2 * m) false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, step_cons, ih, show 2 * (m + 1) = 2 + 2 * m by omega,
      ← List.append_replicate_replicate]
    rfl

theorem dbl_closed (k : Nat) :
    dblS.derive (2 * k) = List.replicate (2 ^ k) false ++ List.replicate (2 ^ k) true ∧
    dblS.derive (2 * k + 1) = List.replicate (2 ^ k) true ++ List.replicate (2 ^ (k + 1)) false := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have e2 : 2 ^ (k + 1 + 1) = 2 * (2 * 2 ^ k) := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    constructor
    · rw [e]
      show dblS.step (dblS.derive (2 * k + 1)) = _
      rw [i2, step_append, dbl_step_b, dbl_step_a, e1]
    · rw [e]
      show dblS.step (dblS.step (dblS.derive (2 * k + 1))) = _
      rw [i2, step_append, dbl_step_b, dbl_step_a, step_append, dbl_step_a, dbl_step_b, e1, e2]

theorem runs_block (x : Bool) (M N : Nat) :
    runs x (List.replicate M x ++ List.replicate N (!x)) = M :: List.replicate N 0 := by
  rw [runs_replicate_append]
  have : ∀ N, runs x (List.replicate N (!x)) = List.replicate (N + 1) 0 := by
    intro N; induction N with
    | zero => rfl
    | succ N ih => rw [List.replicate_succ, runs_notx_cons, ih]; rfl
  rw [this, List.replicate_succ]; simp

theorem runs_block' (x : Bool) (M N : Nat) :
    runs x (List.replicate M (!x) ++ List.replicate N x) = List.replicate M 0 ++ [N] := by
  induction M with
  | zero => rw [List.replicate_zero, List.nil_append, ← List.append_nil (List.replicate N x),
      runs_replicate_append]; simp [runs]
  | succ M ih => rw [List.replicate_succ, List.cons_append, runs_notx_cons, ih]; rfl

/-- A two-block word `x^M (!x)^N` with `N ≥ 2` fails `Crit n x` for every `n ≥ 1`. -/
theorem block_not_crit (n : Nat) (hn : 1 ≤ n) (x : Bool) (M N : Nat) (hN : 2 ≤ N) :
    ¬ Crit n x (List.replicate M x ++ List.replicate N (!x)) := by
  intro hc
  obtain ⟨-, hinner, -⟩ := hc
  rw [runs_block] at hinner
  have : 0 ∈ ((M :: List.replicate N 0).drop 1).dropLast := by
    simp only [List.drop_succ_cons, List.drop_zero]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 2 := ⟨N - 2, by omega⟩
    rw [List.replicate_succ, List.replicate_succ, List.dropLast_cons_cons]; simp
  have := hinner 0 this; omega

theorem block_not_crit' (n : Nat) (hn : 1 ≤ n) (x : Bool) (M N : Nat) (hM : 2 ≤ M) :
    ¬ Crit n x (List.replicate M (!x) ++ List.replicate N x) := by
  intro hc
  obtain ⟨-, hinner, -⟩ := hc
  rw [runs_block'] at hinner
  have : 0 ∈ ((List.replicate M 0 ++ [N]).drop 1).dropLast := by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
    simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons, List.drop_zero]
    cases M' with
    | zero => simp
    | succ M'' => rw [List.replicate_succ, List.cons_append, List.dropLast_cons_cons]; simp
  have := hinner 0 this; omega

theorem dbl_not_crit (n : Nat) (hn : 2 ≤ n) (x : Bool) : ¬ Crit n x (dblS.derive n) := by
  have h2k : 2 ≤ 2 ^ (n / 2) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨d1, d2⟩ := dbl_closed (n / 2)
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [show 2 * (n / 2) = n by omega] at d1
    rw [d1]
    cases x
    · exact block_not_crit n (by omega) false _ _ h2k
    · exact block_not_crit' n (by omega) true _ _ h2k
  · rw [show 2 * (n / 2) + 1 = n by omega] at d2
    rw [d2]
    cases x
    · exact block_not_crit' n (by omega) false _ _ h2k
    · exact block_not_crit n (by omega) true _ _ (by rw [Nat.pow_succ]; omega)

theorem dbl_length (n : Nat) :
    (dblS.derive n).length = (if n % 2 = 0 then 2 * 2 ^ (n / 2) else 3 * 2 ^ (n / 2)) := by
  obtain ⟨d1, d2⟩ := dbl_closed (n / 2)
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [show 2 * (n / 2) = n by omega] at d1
    rw [d1, ite_eq_left he]; simp; omega
  · rw [show 2 * (n / 2) + 1 = n by omega] at d2
    rw [d2, ite_eq_right (by omega)]; simp [Nat.pow_succ]; omega

theorem dbl_both (n : Nat) : ∀ c, c ∈ dblS.derive n := by
  obtain ⟨d1, d2⟩ := dbl_closed (n / 2)
  have hp : 1 ≤ 2 ^ (n / 2) := Nat.pos_pow_of_pos _ (by omega)
  have hp' : 1 ≤ 2 ^ (n / 2 + 1) := Nat.pos_pow_of_pos _ (by omega)
  intro c
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [show 2 * (n / 2) = n by omega] at d1; rw [d1]
    cases c <;> simp <;> omega
  · rw [show 2 * (n / 2) + 1 = n by omega] at d2; rw [d2]
    cases c <;> simp <;> omega

/-! #### which witness is shorter -/

def Dn (n : Nat) : Nat := if n % 2 = 0 then 2 * 2 ^ (n / 2) else 3 * 2 ^ (n / 2)

theorem Dn_succ_succ (n : Nat) : Dn (n + 2) = 2 * Dn n := by
  unfold Dn
  have : (n + 2) / 2 = n / 2 + 1 := by omega
  have h2 : (n + 2) % 2 = n % 2 := by omega
  rw [this, h2, Nat.pow_succ]
  split <;> omega

theorem fib_two_step (n : Nat) : 2 * fib (n + 1) ≤ fib (n + 3) := by
  rw [fib_succ_succ (n + 1), fib_succ_succ n]
  have := fib_mono_succ n
  omega

theorem Dn_le_fib (n : Nat) (hn : 8 ≤ n) : Dn n ≤ fib (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h | h
    · rcases (show n = 8 ∨ n = 9 by omega) with rfl | rfl <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [Dn_succ_succ]
      have := ih m (by omega) (by omega)
      have := fib_two_step m
      rw [show m + 2 + 1 = m + 3 from rfl]
      omega

theorem sharpT_eq (n : Nat) :
    sharpT n = (if n ≤ 7 then fib (n + 1) else Dn n) := by
  unfold sharpT
  by_cases h : n ≤ 7
  · rw [ite_eq_left h]
    apply Nat.min_eq_left
    show fib (n + 1) ≤ Dn n
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [ite_eq_right h]
    exact Nat.min_eq_right (Dn_le_fib n (by omega))

/-- **Sharpness for all `n ≥ 2`** (proved). Some word of length exactly `T(n)` is derived in
`n` steps by a non-erasing system with a shorter axiom, uses both letters, and meets neither
criterion. -/
theorem sharp_witness (n : Nat) (hn : 2 ≤ n) :
    ∃ (S : DOL Bool) (w : List Bool), (∀ a, S.rule a ≠ []) ∧ S.derive n = w ∧
      S.start.length < w.length ∧ (∀ c, c ∈ w) ∧ w.length = sharpT n ∧
      ¬ Crit n false w ∧ ¬ Crit n true w := by
  rw [sharpT_eq]
  by_cases h : n ≤ 7
  · rw [ite_eq_left h]
    refine ⟨fibS, fibS.derive n, by decide, rfl, ?_, fib_both n hn, fib_length n, ?_, ?_⟩
    · rw [fib_length]
      show 1 < fib (n + 1)
      rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
      · decide
      · exact fib_not_crit n h3 false
    · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
      · decide
      · exact fib_not_crit n h3 true
  · rw [ite_eq_right h]
    refine ⟨dblS, dblS.derive n, by decide, rfl, ?_, dbl_both n, dbl_length n,
      dbl_not_crit n hn false, dbl_not_crit n hn true⟩
    rw [dbl_length]
    show 2 < _
    have : 2 ≤ 2 ^ (n / 2) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by omega) (by omega)
    split <;> omega

/-! ### Executable checks inside Lean -/

def sameSet [DecidableEq β] (xs ys : List β) : Bool :=
  xs.all (· ∈ ys) && ys.all (· ∈ xs)

def check [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) : Bool :=
  sameSet ((infer sigma B w n).map (canon sigma n)) ((sol sigma B w n).map (canon sigma n))

#eval (List.range 10).map fun n => (n, sharpT n)   -- expect 2,3,5,8,13,21,32,48 for n = 2..9
-- Fibonacci word, n = 5.
#eval infer [0, 1] ⟨2, 3, false⟩ [0,1,0,0,1,0,1,0,0,1,0,0,1] 5
#eval check [0, 1] ⟨2, 3, false⟩ [0,1,0,0,1,0,1,0,0,1,0,0,1] 5
#eval check [0, 1] ⟨2, 2, true⟩ [0,1,1,0,1] 2
#eval check [0, 1, 2] ⟨1, 2, false⟩ [0,1,2,0] 2
#eval check [0, 1] ⟨2, 2, false⟩ [0,1,1,0,1,0,0,1] 3
#eval check [0, 1] ⟨2, 2, true⟩ [0] 3

end LSys

-- ===================================================================== PFA additions
-- Paper-facing statements: concrete alphabets (`Nat`, `Unit`, `Bool`), every hypothesis a
-- named explicit binder. Each is proved by appeal to the corresponding `LSys` theorem.

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

end Paper
