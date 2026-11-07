/-
Inverse L-system inference, formalized (Lean 4.15 core, no Mathlib). No `sorry`.

Master theorem, in two halves (both proved):
  infer_complete : every bounded solution in `sol` is emitted by the pruned search `infer`
  infer_sound    : every key emitted by `infer` is a bounded solution in `sol`
both up to `canon` (rules of symbols that are never rewritten are irrelevant).
`infer_sound` needs three side conditions discovered during the proof:
  w ⊆ sigma, w ≠ [], 1 ≤ maxRule — each is a genuine discrepancy otherwise.

Also proved: existence (identity; one hidden symbol gives a length-1 axiom),
impossibility over a one-letter alphabet, and the growth/length lemmas.

Problem A (non-trivial systems over Σ(w), axiom shorter than w):
  unary_iff    : a^L at step n  ⟺  ∃ m ≥ 2, m^n ∣ L
  chain_exists : n ≤ |Σ(w)|  ⟹  a length-1 axiom works
Problem B (counting):
  exists_underivable : fewer bounded systems than |sigma|^L words ⟹ some word of
                       length L has no bounded system at any step
  underivable_binary_8 : concrete instance, decided inside Lean
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

/-- Properties of the final rule table. -/
structure GoodF [DecidableEq α] (sigma : List α) (B : Bounds) (R : Rules α) : Prop where
  bodies     : ∀ x, ∀ y ∈ (lookupR R x).1, ∃ a ∈ sigma, y = some a
  len        : ∀ x, (lookupR R x).1.length ≤ (if x = none then B.maxAxiom else B.maxRule)
  closed_ne  : ∀ x, (lookupR R x).2 = true → B.allowEmpty = false → (lookupR R x).1 ≠ []
  open_nil   : ∀ x, (lookupR R x).2 = false → (lookupR R x).1 = []
  entry_syms : ∀ x, lookupR R x ≠ ([], false) → x ∈ allSyms sigma

theorem goodF_of_good [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) (R : Rules α)
    (pos : Nat) (hg : Good sigma B n ⟨R, [], pos⟩) : GoodF sigma B R :=
  ⟨hg.bodies, hg.len, hg.closed_ne,
   fun x ho => by
     apply Decidable.byContradiction
     intro hne
     obtain ⟨f, hf, -⟩ := hg.open_frame x ho hne
     simp at hf,
   hg.entry_syms⟩

/-- The system read off a final rule table: closed bodies become rules, the rest is identity. -/
def finalS [DecidableEq α] (R : Rules α) : DOL α :=
  ⟨(lookupR R none).1.filterMap id,
   fun a => if (lookupR R (some a)).2 then (lookupR R (some a)).1.filterMap id else [a]⟩

theorem map_some_filterMap_id (l : List (Option α)) (h : ∀ y ∈ l, ∃ a, y = some a) :
    (l.filterMap id).map some = l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    obtain ⟨a, rfl⟩ := h y (List.mem_cons_self _ _)
    simp [List.filterMap_cons, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem lift_finalS_rule_closed [DecidableEq α] (sigma : List α) (B : Bounds) (R : Rules α)
    (hR : GoodF sigma B R) (x : Option α) (hx : (lookupR R x).2 = true) :
    (lift (finalS R)).rule x = (lookupR R x).1 := by
  have hb := hR.bodies x
  cases x with
  | none =>
    show ((lookupR R none).1.filterMap id).map some = _
    exact map_some_filterMap_id _ (fun y hy => let ⟨a, _, h⟩ := hb y hy; ⟨a, h⟩)
  | some a =>
    show (if (lookupR R (some a)).2 = true then (lookupR R (some a)).1.filterMap id else [a]).map some = _
    rw [if_pos hx]
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
    (lookupR R x).1 = (lift (finalS Rf)).rule x := by
  have h1 := (he x).1 hx
  rw [lift_finalS_rule_closed sigma B Rf hR x (by rw [h1]; exact hx), h1]

theorem ext_prefix [DecidableEq α] (sigma : List α) (B : Bounds) (R Rf : Rules α)
    (hR : GoodF sigma B Rf) (he : Ext R Rf) (x : Option α) :
    (lookupR R x).1 <+: (lift (finalS Rf)).rule x := by
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

def Inv [DecidableEq α] (w : List α) (n : Nat) (st : St α) (Rf : Rules α) : Prop :=
  stackLeaves (lift (finalS Rf)) n st.stack = (w.map some).drop st.pos ∧ Ext st.rules Rf

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
  refine ⟨hg.bodies, hg.len, hg.closed_ne, ?_, ?_, ?_, ?_, hg.entry_syms⟩
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
    (hinv : Inv w n ⟨R, (sym, n, i + 1) :: rest, pos + 1⟩ Rf) :
    Inv w n ⟨R, (sym, n, i) :: rest, pos⟩ Rf := by
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
  refine ⟨hg.bodies, hg.len, hg.closed_ne, ?_, ?_, ?_, ?_, hg.entry_syms⟩
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
    (hinv : Inv w n ⟨R, (body[i], d + 1, 0) :: (sym, d, i + 1) :: rest, pos⟩ Rf) :
    Inv w n ⟨R, (sym, d, i) :: rest, pos⟩ Rf := by
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
    (hne : B.allowEmpty = false → body ≠ []) :
    Good sigma B n ⟨R', rest, pos⟩ := by
  have hsym := hg.syms (sym, d, i) (List.mem_cons_self _ _)
  simp only at hsym
  have hlk : ∀ x, (lookupR R' x).1 = (lookupR R x).1 := by
    intro x
    by_cases hx : x = sym
    · subst hx; rw [hself, hb]
    · rw [hother x hx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem inv_pop [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (R R' Rf : Rules α) (hR : GoodF sigma B Rf)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (body : List (Option α)) (closed : Bool) (hb : lookupR R sym = (body, closed))
    (hi : i = body.length)
    (hself : lookupR R' sym = (body, true))
    (hother : ∀ y, y ≠ sym → lookupR R' y = lookupR R y)
    (hinv : Inv w n ⟨R', rest, pos⟩ Rf) :
    Inv w n ⟨R, (sym, d, i) :: rest, pos⟩ Rf := by
  obtain ⟨hl, he⟩ := hinv
  have hRf : lookupR Rf sym = (body, true) := by
    have := (he sym).1 (by rw [hself]); rwa [hself] at this
  have hrule : (lift (finalS Rf)).rule sym = body := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, hg.depth, hg.syms, ?_⟩
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

theorem inv_extend [DecidableEq α] (w : List α) (n : Nat)
    (R Rf : Rules α)
    (sym : Option α) (d i : Nat) (rest : List (Frame α)) (pos : Nat)
    (body : List (Option α)) (hb : lookupR R sym = (body, false)) (c : Option α)
    (hinv : Inv w n ⟨(sym, (body ++ [c], false)) :: R, (sym, d, i) :: rest, pos⟩ Rf) :
    Inv w n ⟨R, (sym, d, i) :: rest, pos⟩ Rf := by
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

theorem inv_terminal [DecidableEq α] (w : List α) (n : Nat) (R : Rules α) :
    Inv w n ⟨R, [], w.length⟩ R := by
  refine ⟨?_, ext_refl R⟩
  simp only [stackLeaves_nil]
  rw [List.drop_eq_nil_of_le (by simp)]

theorem good_init [DecidableEq α] (sigma : List α) (B : Bounds) (n : Nat) :
    Good sigma B n ⟨[], [(none, 0, 0)], 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hy; simp [lookupR] at hy
  · intro x; simp [lookupR]
  · intro x hc; simp [lookupR] at hc
  · intro x _ hne; simp [lookupR] at hne
  · intro f hf; simp at hf; subst hf; exact Nat.zero_le _
  · intro f hf; simp at hf; subst hf; exact Nat.zero_le _
  · intro f hf; simp at hf; subst hf; simp [allSyms]
  · intro x hx; simp [lookupR] at hx

/-! #### The soundness theorem -/

theorem search_sound [DecidableEq α] (w : List α) (n : Nat) (sigma : List α) (B : Bounds)
    (hw : ∀ c ∈ w, c ∈ sigma) :
    ∀ fuel (st : St α), Good sigma B n st → ∀ Q ∈ search w n sigma B fuel st,
      ∃ Rf, Q = toKey sigma Rf ∧ GoodF sigma B Rf ∧ Inv w n st Rf := by
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
        exact ⟨R, rfl, goodF_of_good sigma B n R _ hg, inv_terminal w n R⟩
      · simp at hQ
    | cons f rest =>
      rcases f with ⟨sym, d, i⟩
      rcases hb : lookupR R sym with ⟨body, closed⟩
      simp only [search, hb] at hQ
      split at hQ
      · simp at hQ
      by_cases hi : i < body.length
      · rw [dif_pos hi] at hQ
        by_cases hd : d = n
        · subst hd
          rw [if_pos rfl] at hQ
          cases hw' : w[pos]? with
          | none => rw [hw'] at hQ; simp at hQ
          | some c =>
            rw [hw'] at hQ
            simp only at hQ
            split at hQ
            · rename_i hc
              obtain ⟨Rf, hQ', hRf, hinv⟩ :=
                ih _ (good_leaf sigma B d R sym i rest pos hg body closed hb hi) Q hQ
              exact ⟨Rf, hQ', hRf,
                inv_leaf w d sigma B R Rf hRf sym i rest pos body closed hb hi c hw' hc hinv⟩
            · simp at hQ
        · rw [if_neg hd] at hQ
          obtain ⟨Rf, hQ', hRf, hinv⟩ :=
            ih _ (good_expand sigma B n R sym d i rest pos hg body closed hb hi hd) Q hQ
          have hdn := hg.depth (sym, d, i) (List.mem_cons_self _ _)
          exact ⟨Rf, hQ', hRf,
            inv_expand w n sigma B R Rf hRf sym d i rest pos body closed hb hi hd hdn hinv⟩
      · rw [dif_neg hi] at hQ
        have hidx := hg.idx (sym, d, i) (List.mem_cons_self _ _)
        rw [hb] at hidx
        simp only at hidx
        have hi' : i = body.length := by omega
        cases closed with
        | true =>
          rw [if_pos rfl] at hQ
          have hne : B.allowEmpty = false → body ≠ [] := fun hae => by
            have := hg.closed_ne sym (by rw [hb]) hae; rwa [hb] at this
          obtain ⟨Rf, hQ', hRf, hinv⟩ :=
            ih _ (good_pop sigma B n R R sym d i rest pos hg body true hb hb (fun y _ => rfl) hne) Q hQ
          exact ⟨Rf, hQ', hRf,
            inv_pop w n sigma B R R Rf hRf sym d i rest pos body true hb hi' hb (fun y _ => rfl) hinv⟩
        | false =>
          rw [if_neg Bool.false_ne_true, List.mem_append] at hQ
          rcases hQ with hQ | hQ
          · split at hQ
            · rename_i hcond
              have hne : B.allowEmpty = false → body ≠ [] := by
                intro hae
                rw [hae] at hcond
                simp at hcond
                exact List.ne_nil_of_length_pos hcond
              obtain ⟨Rf, hQ', hRf, hinv⟩ :=
                ih _ (good_pop sigma B n R _ sym d i rest pos hg body false hb
                  (lookupR_cons_self R sym _) (fun y hy => lookupR_cons_ne R sym y _ hy) hne) Q hQ
              exact ⟨Rf, hQ', hRf,
                inv_pop w n sigma B R _ Rf hRf sym d i rest pos body false hb hi'
                  (lookupR_cons_self R sym _) (fun y hy => lookupR_cons_ne R sym y _ hy) hinv⟩
            · simp at hQ
          · by_cases hmax : body.length < (if sym = none then B.maxAxiom else B.maxRule)
            · rw [if_pos hmax, List.mem_flatMap] at hQ
              obtain ⟨c, hc, hQ⟩ := hQ
              have hca : ∃ a ∈ sigma, c = some a := by
                split at hc
                · cases hw' : w[pos]? with
                  | none => rw [hw'] at hc; simp at hc
                  | some c' =>
                    rw [hw'] at hc
                    simp at hc
                    subst hc
                    exact ⟨c', hw c' (List.mem_of_getElem? hw'), rfl⟩
                · rw [List.mem_map] at hc
                  obtain ⟨a, ha, rfl⟩ := hc
                  exact ⟨a, ha, rfl⟩
              obtain ⟨a, ha, rfl⟩ := hca
              obtain ⟨Rf, hQ', hRf, hinv⟩ :=
                ih _ (good_extend sigma B n R sym d i rest pos hg body hb a ha (by omega)) Q hQ
              exact ⟨Rf, hQ', hRf, inv_extend w n R Rf sym d i rest pos body hb (some a) hinv⟩
            · rw [if_neg hmax] at hQ; simp at hQ

/-! ### Master theorem

`infer` and `sol` agree up to rules of unused symbols. Completeness is proved;
soundness (every emitted key comes from a bounded solution) is the remaining goal. -/

/-- **Completeness** (proved): every bounded solution is found by the search. -/
theorem infer_complete [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
    ∀ P ∈ sol sigma B w n, ∃ fuel, ∃ Q ∈ infer sigma B w n fuel,
      canon sigma n Q = canon sigma n P :=
  fun P hP => sol_subset_infer sigma B w n P hP

/-! #### Assembling `infer_sound` -/

theorem lookup_filterMap_none' [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p]
    (g : α → List α) (a : α) (hp : ¬ p a) :
    (l.filterMap fun x => if p x then some (x, g x) else none).lookup a = none := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.filterMap_cons]
    by_cases hb : p b
    · rw [if_pos hb]
      have hab : a ≠ b := fun h => hp (h ▸ hb)
      have := beq_false_of_ne hab
      simp only [List.lookup, this]; exact ih
    · rw [if_neg hb]; exact ih

theorem toKey_snd [DecidableEq α] (sigma : List α) (R : Rules α) :
    (toKey sigma R).2 = sigma.filterMap fun a =>
      if (lookupR R (some a)).2 = true then some (a, (lookupR R (some a)).1.filterMap id) else none := by
  unfold toKey
  simp only

theorem length_filterMap_id_of_some (l : List (Option α)) (h : ∀ y ∈ l, ∃ a, y = some a) :
    (l.filterMap id).length = l.length := by
  have := congrArg List.length (map_some_filterMap_id l h)
  rwa [List.length_map] at this

/-- The system read off the final table is bounded, and has the identity on symbols outside `sigma`. -/
theorem finalS_bounded [DecidableEq α] (sigma : List α) (B : Bounds) (Rf : Rules α)
    (hR : GoodF sigma B Rf) (hmr : 1 ≤ B.maxRule) (hne : (finalS Rf).start ≠ []) :
    Bounded sigma B (finalS Rf) := by
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
  refine ⟨?_, ?_, hmemS none, ?_, ?_, ?_, ?_⟩
  · exact List.length_pos.mpr hne
  · show ((lookupR Rf none).1.filterMap id).length ≤ B.maxAxiom
    rw [length_filterMap_id_of_some _ (hsome none)]
    simpa using hR.len none
  · intro a ha
    show (if B.allowEmpty then 0 else 1) ≤ (if (lookupR Rf (some a)).2 = true
        then (lookupR Rf (some a)).1.filterMap id else [a]).length
    cases hc : (lookupR Rf (some a)).2
    · rw [if_neg Bool.false_ne_true]; simp only [List.length_singleton]; split <;> omega
    · rw [if_pos rfl]
      rw [length_filterMap_id_of_some _ (hsome _)]
      cases hae : B.allowEmpty
      · rw [if_neg Bool.false_ne_true]
        exact List.length_pos.mpr (hR.closed_ne _ hc hae)
      · rw [if_pos rfl]; exact Nat.zero_le _
  · intro a ha
    show (if (lookupR Rf (some a)).2 = true
        then (lookupR Rf (some a)).1.filterMap id else [a]).length ≤ B.maxRule
    cases hc : (lookupR Rf (some a)).2
    · rw [if_neg Bool.false_ne_true]; simpa using hmr
    · rw [if_pos rfl]
      rw [length_filterMap_id_of_some _ (hsome _)]
      simpa using hR.len (some a)
  · intro a ha x hx
    have hx' : x ∈ (if (lookupR Rf (some a)).2 = true
        then (lookupR Rf (some a)).1.filterMap id else [a]) := hx
    cases hc : (lookupR Rf (some a)).2
    · rw [hc, if_neg Bool.false_ne_true] at hx'; simp at hx'; subst hx'; exact ha
    · rw [hc, if_pos rfl] at hx'; exact hmemS _ x hx'
  · intro a ha
    show (if (lookupR Rf (some a)).2 = true
        then (lookupR Rf (some a)).1.filterMap id else [a]) = [a]
    rw [hclosed_not_mem a ha]; rfl

/-- **Soundness** (proved): every emitted key is, up to unused rules, a bounded solution. -/
theorem infer_sound [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat)
    (hw : ∀ c ∈ w, c ∈ sigma) (hne : w ≠ []) (hmr : 1 ≤ B.maxRule) :
    ∀ fuel, ∀ Q ∈ infer sigma B w n fuel, ∃ P ∈ sol sigma B w n,
      canon sigma n Q = canon sigma n P := by
  intro fuel Q hQ
  obtain ⟨Rf, hQk, hRf, hleaves, -⟩ :=
    search_sound w n sigma B hw fuel _ (good_init sigma B n) Q hQ
  -- the induced system derives w
  have hder : (finalS Rf).derive n = w := by
    simp only [stackLeaves_cons, stackLeaves_nil, frameLeaves_mk, Nat.sub_zero, List.drop_zero,
      List.append_nil] at hleaves
    have h1 : (lift (finalS Rf)).rule none = (finalS Rf).start.map some := rfl
    rw [h1, iter_lift_map, ← derive_eq_iter] at hleaves
    have := congrArg (List.filterMap id) hleaves
    rwa [filterMap_id_map_some, filterMap_id_map_some] at this
  have hstart : (finalS Rf).start ≠ [] := by
    intro h0
    apply hne
    rw [← hder, derive_eq_iter, h0, iter_nil]
  have hB := finalS_bounded sigma B Rf hRf hmr hstart
  -- the presented solution
  let P : Presented α := ((finalS Rf).start, sigma.map fun a => (a, (finalS Rf).rule a))
  have hPD : P.toDOL = finalS Rf := by
    refine DOL.ext' _ _ rfl ?_
    intro a
    show (match (sigma.map fun a => (a, (finalS Rf).rule a)).lookup a with
      | some r => r | none => [a]) = (finalS Rf).rule a
    rw [lookup_map_pair]
    by_cases ha : a ∈ sigma
    · rw [if_pos ha]
    · rw [if_neg ha]; exact (hB.rule_default a ha).symm
  have hPA : P ∈ allSystems sigma B := by
    simp only [allSystems, List.mem_flatMap, List.mem_map]
    refine ⟨(finalS Rf).start, ?_, sigma.map fun a => (a, (finalS Rf).rule a), ?_, rfl⟩
    · exact mem_wordsUpTo_of sigma 1 B.maxAxiom _ hB.start_len_lo hB.start_len_hi hB.start_mem
    · apply mem_ruleTables_of
      intro a ha
      exact mem_wordsUpTo_of sigma _ B.maxRule _ (hB.rule_len_lo a ha) (hB.rule_len_hi a ha)
        (hB.rule_mem a ha)
  have hPsol : P ∈ sol sigma B w n := by
    unfold sol
    rw [List.mem_filter]
    exact ⟨hPA, decide_eq_true (by rw [hPD]; exact hder)⟩
  refine ⟨P, hPsol, ?_⟩
  -- Q and P induce the same system
  have hQD : Q.toDOL = finalS Rf := by
    subst hQk
    refine DOL.ext' _ _ rfl ?_
    intro a
    show (match (toKey sigma Rf).2.lookup a with | some r => r | none => [a]) = (finalS Rf).rule a
    rw [toKey_snd]
    by_cases ha : a ∈ sigma
    · cases hc : (lookupR Rf (some a)).2
      · have := lookup_filterMap_none' sigma (fun x => (lookupR Rf (some x)).2 = true)
          (fun x => (lookupR Rf (some x)).1.filterMap id) a (by simp [hc])
        simp only at this
        rw [this]
        show [a] = (if (lookupR Rf (some a)).2 = true then _ else [a])
        rw [hc]; rfl
      · have := lookup_filterMap_some sigma (fun x => (lookupR Rf (some x)).2 = true)
          (fun x => (lookupR Rf (some x)).1.filterMap id) a ha hc
        simp only at this
        rw [this]
        show _ = (if (lookupR Rf (some a)).2 = true then _ else [a])
        rw [hc]; rfl
    · have := lookup_filterMap_none sigma (fun x => (lookupR Rf (some x)).2 = true)
        (fun x => (lookupR Rf (some x)).1.filterMap id) a ha
      simp only at this
      rw [this]
      exact (hB.rule_default a ha).symm
  apply canon_congr
  · subst hQk; rfl
  · rw [hQD, hPD]

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
    · rw [if_pos ha]
    · rw [if_neg ha, hid a ha]

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
