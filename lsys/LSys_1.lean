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

/-! ### Master theorem (goal)

`infer` is the pruned search of `lsys_pure.py`, to be transcribed here.
The theorem to prove: it returns exactly `sol`, up to rules of unused symbols.
-/

-- def infer ... : List (Presented α) := sorry
-- theorem infer_eq_sol : (infer sigma B w n).toFinset = (sol sigma B w n).toFinset := sorry

/-- Sanity check: the Fibonacci system. -/
example : (DOL.mk [0] fun a => if a = 0 then [0, 1] else [0] : DOL Nat).derive 5
    = [0,1,0,0,1,0,1,0,0,1,0,0,1] := by decide

end LSys
