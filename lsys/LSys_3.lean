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

/-- Lower bound on leaves still to be produced by the whole stack. -/
def need [DecidableEq α] (R : Rules α) (allowEmpty : Bool) (n : Nat)
    (stack : List (Option α × Nat × Nat)) : Nat :=
  (stack.map fun (sym, d, i) =>
    let (body, closed) := lookupR R sym
    (if i = 0 && body.isEmpty && !closed && !allowEmpty then 1 else 0)
      + ((body.drop i).map (minexp R allowEmpty (n - d))).sum).sum

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

/-! ### Canonical form (rules of unused symbols are irrelevant) -/

def usedSymbols [DecidableEq α] (S : DOL α) : Nat → List α
  | 0     => []
  | n + 1 => S.derive n ++ usedSymbols S n

def canon [DecidableEq α] (sigma : List α) (n : Nat) (P : Presented α) : Presented α :=
  let S := P.toDOL
  let u := usedSymbols S n
  (P.1, sigma.filterMap fun a => if a ∈ u then some (a, S.rule a) else none)

-- **Master theorem (goal).** For enough fuel, the pruned search and the
-- brute-force specification agree, up to rules of unused symbols.
-- theorem infer_eq_sol [DecidableEq α] (sigma : List α) (B : Bounds) (w : List α) (n : Nat) :
--     ∃ fuel, ∀ P, (∃ Q ∈ infer sigma B w n fuel, canon sigma n Q = P)
--                 ↔ (∃ Q ∈ sol sigma B w n, canon sigma n Q = P) := sorry

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
