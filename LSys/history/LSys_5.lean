/-
Inverse L-system inference, formalized (Lean 4 core, no Mathlib).

Master statement (goal):   infer w n B  computes  Sol w n B
Corollaries proved here:   existence (trivial, and with one hidden symbol),
                           impossibility over a singleton alphabet,
                           soundness of the brute-force Sol.
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

/-- Extract the finished system: axiom from `none`, closed rules for `sigma`. -/
def toKey [DecidableEq α] (sigma : List α) (R : Rules α) : Presented α :=
  ((lookupR R none).1.filterMap id,
   sigma.filterMap fun a =>
     let (body, closed) := lookupR R (some a)
     if closed then some (a, body.filterMap id) else none)

def search [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds) :
    Nat → St α → List (Presented α)
  | 0, _ => []
  | fuel + 1, st =>
    match st.stack with
    | [] => if st.pos = w.length then [toKey sigma st.rules] else []
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
          if 1 ≤ body.length || B.allowEmpty then
            search w n sigma B fuel ⟨(sym, (body, true)) :: st.rules, rest, st.pos⟩
          else []
        let maxlen := if sym = none then B.maxAxiom else B.maxRule
        let extBr :=
          if body.length < maxlen then
            let cands : List (Option α) :=
              if d = n then (match w[st.pos]? with | some c => [some c] | none => [])
              else sigma.map some
            cands.flatMap fun c =>
              search w n sigma B fuel ⟨(sym, (body ++ [c], false)) :: st.rules, st.stack, st.pos⟩
          else []
        closeBr ++ extBr

def infer [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat)
    (fuel : Nat := 1000000) : List (Presented α) :=
  search w n sigma B fuel ⟨[], [(none, 0, 0)], 0⟩

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
def expectedKey [DecidableEq α] (sigma : List α) (n : Nat) (T : DOL (Option α)) : Presented α :=
  ((T.rule none).filterMap id,
   sigma.filterMap fun a =>
     if some a ∈ usedT T n then some (a, (T.rule (some a)).filterMap id) else none)

/-- What we know about a lifted bounded candidate. -/
structure TOk [DecidableEq α] (sigma : List α) (B : Bounds) (T : DOL (Option α)) : Prop where
  mem : ∀ x ∈ allSyms sigma, ∀ y ∈ T.rule x, y ∈ sigma.map some
  len : ∀ x ∈ allSyms sigma, (T.rule x).length ≤ (if x = none then B.maxAxiom else B.maxRule)
  ne  : B.allowEmpty = false → ∀ x, T.rule x ≠ []

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

theorem terminal [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (T : DOL (Option α))
    (R : Rules α) (pos : Nat) (hp : OnPath w n T ⟨R, [], pos⟩) :
    pos = w.length ∧ toKey sigma R = expectedKey sigma n T := by
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
      expectedKey sigma n T ∈ search w n sigma B fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _ h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro st hp hμ
    rcases st with ⟨R, stack, pos⟩
    cases stack with
    | nil =>
      obtain ⟨hpos, hkey⟩ := terminal w n sigma T R pos hp
      simp only [search, hpos, if_true, hkey, List.mem_singleton]
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
      rw [if_neg hprune]
      by_cases hi : i < body.length
      · rw [dif_pos hi]
        by_cases hd : d = n
        · subst hd
          obtain ⟨c, hw, hc, hp', hμ'⟩ := step_leaf w d sigma T R sym i rest pos hp body closed hb hi
          rw [if_pos rfl, hw]
          simp only [hc, if_true]
          exact ih _ hp' (by omega)
        · rw [if_neg hd]
          obtain ⟨hp', hμ'⟩ := step_expand w n sigma T R sym d i rest pos hp body closed hb hi hd
          exact ih _ hp' (by omega)
      · rw [dif_neg hi]
        have hidx := hp.idx (sym, d, i) (List.mem_cons_self _ _)
        rw [hb] at hidx
        simp only at hidx
        have hi' : i = body.length := by omega
        cases closed with
        | true =>
          rw [if_pos rfl]
          have hbr : body = T.rule sym := by
            have := hp.closed_eq sym (by rw [hb]); rwa [hb] at this
          obtain ⟨hp', hμ'⟩ := step_pop w n sigma T R R sym d i rest pos hp body true hb hi' hbr hb
            (fun y _ => rfl)
          exact ih _ hp' (by omega)
        | false =>
          rw [if_neg Bool.false_ne_true]
          by_cases hbr : body = T.rule sym
          · have hcond : (decide (1 ≤ body.length) || B.allowEmpty) = true := by
              cases hae : B.allowEmpty
              · have hne := hT.ne hae sym
                rw [← hbr] at hne
                have := List.length_pos.mpr hne
                simp; omega
              · simp
            simp only [hcond, if_true]
            apply List.mem_append_left
            obtain ⟨hp', hμ'⟩ := step_pop w n sigma T R ((sym, (body, true)) :: R) sym d i rest pos
              hp body false hb hi' hbr (lookupR_cons_self R sym _)
              (fun y hy => lookupR_cons_ne R sym y _ hy)
            exact ih _ hp' (by omega)
          · obtain ⟨c, hlen, hget, hmax, hcs, hdn, hp', hμ'⟩ :=
              step_extend w n sigma B T hT R sym d i rest pos hp body hb hi' hbr
            apply List.mem_append_right
            rw [if_pos hmax, List.mem_flatMap]
            refine ⟨c, ?_, ih _ hp' (by omega)⟩
            by_cases hd : d = n
            · rw [if_pos hd]
              obtain ⟨c', hw, rfl⟩ := hdn hd
              rw [hw]; simp
            · rw [if_neg hd]; exact hcs

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
  refine ⟨?_, ?_, ?_⟩
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
    · rw [if_pos hb]
      by_cases hab : a = b
      · subst hab; simp [List.lookup]
      · have : (a == b) = false := beq_false_of_ne hab
        simp only [List.lookup, this]
        exact ih (by rcases List.mem_cons.mp ha with rfl | h; exact absurd rfl hab; exact h)
    · rw [if_neg hb]
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
    · rw [if_pos hb]
      have := beq_false_of_ne hab
      simp only [List.lookup, this]; exact ih hl
    · rw [if_neg hb]; exact ih hl

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

/-- The expected key canonicalizes to the same thing as the candidate it came from. -/
theorem canon_expectedKey [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat)
    (P : Presented α) (hB : Bounded sigma B P.toDOL) :
    canon sigma n (expectedKey sigma n (lift P.toDOL)) = canon sigma n P := by
  have hkey : expectedKey sigma n (lift P.toDOL)
      = (P.1, sigma.filterMap fun a =>
          if a ∈ usedSymbols P.toDOL n then some (a, P.toDOL.rule a) else none) := by
    unfold expectedKey
    have h1 : (lift P.toDOL).rule none = P.toDOL.start.map some := rfl
    have h2 : ∀ a, (lift P.toDOL).rule (some a) = (P.toDOL.rule a).map some := fun a => rfl
    simp only [h1, h2, filterMap_id_map_some]
    congr 2
    funext a
    by_cases h : a ∈ usedSymbols P.toDOL n
    · rw [if_pos h, if_pos ((mem_usedT_lift_iff _ _ _).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((mem_usedT_lift_iff _ _ _).mp h'))]
  rw [hkey]
  generalize hK : Presented.toDOL (P.1, sigma.filterMap fun a =>
        if a ∈ usedSymbols P.toDOL n then some (a, P.toDOL.rule a) else none) = K
  have toDOL_rule_mk : ∀ (ax : List α) (t : List (α × List α)) (a : α),
      (Presented.toDOL (ax, t)).rule a = match t.lookup a with | some r => r | none => [a] :=
    fun _ _ _ => rfl
  have hrule : ∀ a ∈ usedSymbols P.toDOL n, K.rule a = P.toDOL.rule a := by
    intro a ha
    rw [← hK, toDOL_rule_mk]
    by_cases hs : a ∈ sigma
    · have := lookup_filterMap_some sigma (fun x => x ∈ usedSymbols P.toDOL n)
        (fun x => P.toDOL.rule x) a hs ha
      simp only at this
      rw [this]
    · have := lookup_filterMap_none sigma (fun x => x ∈ usedSymbols P.toDOL n)
        (fun x => P.toDOL.rule x) a hs
      simp only at this
      rw [this, hB.rule_default a hs]
  have hst : K.start = P.toDOL.start := by rw [← hK]; rfl
  have hder := derive_eq_of_agree P.toDOL K n hst hrule
  have hused := usedSymbols_eq_of_agree P.toDOL K n hder
  unfold canon
  simp only [hK, hused, hst]
  show (P.toDOL.start, _) = (P.1, _)
  congr 2
  funext a
  by_cases h : a ∈ usedSymbols P.toDOL n
  · rw [if_pos h, if_pos h, hrule a h]
  · rw [if_neg h, if_neg h]

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
    expectedKey sigma n (lift P.toDOL), ?_, canon_expectedKey sigma B n P hB⟩
  exact search_complete w n sigma B (lift P.toDOL) hT _ _ h0 (Nat.lt_succ_self _)

/-! ### Master theorem

`infer` and `sol` agree up to rules of unused symbols. Completeness is proved;
soundness (every emitted key comes from a bounded solution) is the remaining goal. -/

/-- **Completeness** (proved): every bounded solution is found by the search. -/
theorem infer_complete [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
    ∀ P ∈ sol sigma B w n, ∃ fuel, ∃ Q ∈ infer sigma B w n fuel,
      canon sigma n Q = canon sigma n P :=
  fun P hP => sol_subset_infer sigma B w n P hP

/-- **Soundness** (goal): every emitted key is a bounded solution. -/
theorem infer_sound [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
    ∀ fuel, ∀ Q ∈ infer sigma B w n fuel, ∃ P ∈ sol sigma B w n,
      canon sigma n Q = canon sigma n P := by
  sorry

/-! ### Executable checks inside Lean -/

def sameSet [DecidableEq β] (xs ys : List β) : Bool :=
  xs.all (· ∈ ys) && ys.all (· ∈ xs)

def check [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) : Bool :=
  sameSet ((infer sigma B w n).map (canon sigma n)) ((sol sigma B w n).map (canon sigma n))

-- Fibonacci word, n = 5.
#eval infer [0, 1] ⟨2, 3, false⟩ [0,1,0,0,1,0,1,0,0,1,0,0,1] 5
#eval check [0, 1] ⟨2, 3, false⟩ [0,1,0,0,1,0,1,0,0,1,0,0,1] 5
#eval check [0, 1] ⟨2, 2, true⟩ [0,1,1,0,1] 2
#eval check [0, 1, 2] ⟨1, 2, false⟩ [0,1,2,0] 2
#eval check [0, 1] ⟨2, 2, false⟩ [0,1,1,0,1,0,0,1] 3
#eval check [0, 1] ⟨2, 2, true⟩ [0] 3

end LSys
