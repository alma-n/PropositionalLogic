import Mathlib.Tactic.DeriveCountable

set_option linter.style.longLine false

namespace PropositionalLogic

inductive Formula where
  | Symbol (n : ℕ)
  | Not (f : Formula)
  | And (f₁ : Formula) (f₂ : Formula)
  | Or (f₁ : Formula) (f₂ : Formula)
  | Imp (f₁ : Formula) (f₂ : Formula)
  | Iff (f₁ : Formula) (f₂ : Formula)
deriving Inhabited, DecidableEq, Countable

abbrev Context := Set Formula

inductive Deduction : (C : Context) → Formula → Prop where
  | Hyp : ∀ A ∈ C, Deduction C A
  | And_intro : ∀ A B, Deduction C A → Deduction C B → Deduction C (A.And B)
  | Or_intro_left : ∀ A B, Deduction C A → Deduction C (A.Or B)
  | Or_intro_right : ∀ A B : Formula, Deduction C B → Deduction C (A.Or B)
  | Imp_intro : ∀ A B : Formula, Deduction ({A} ∪ C) B → Deduction C (A.Imp B)
  | Not_intro : ∀ A B : Formula, Deduction ({A} ∪ C) (B.And B.Not) → Deduction C A.Not
  | Iff_intro : ∀ A B : Formula, Deduction ({A} ∪ C) B → Deduction ({B} ∪ C) A → Deduction C (A.Iff B)
  | And_elim_left : ∀ A B : Formula, Deduction C (A.And B) → Deduction C A
  | And_elim_right : ∀ A B : Formula, Deduction C (A.And B) → Deduction C B
  | Or_elim : ∀ A B C  : Formula, Deduction D (A.Or B) → Deduction (D ∪ {A}) C → Deduction (D ∪ {B}) C → Deduction D C
  | Imp_elim : ∀ A B : Formula, Deduction C (A.Imp B) → Deduction C A → Deduction C B
  | Not_elim : ∀ A : Formula, Deduction C (A.Not.Not) → Deduction C A
  | Iff_elim_left : ∀ A B : Formula, Deduction C (A.Iff B) → Deduction C A → Deduction C B
  | Iff_elim_right : ∀ A B : Formula, Deduction C (A.Iff B) → Deduction C B → Deduction C A

notation C " ⊢p " A => Deduction C A

section Examples
open Formula

example : {Symbol 1} ⊢p Symbol 1 := by
  apply Deduction.Hyp
  simp

example (C) (A B : Formula) (ha : A ∈ C) (hb : B ∈ C) : C ⊢p A.And B := by
  apply Deduction.And_intro
  · apply Deduction.Hyp _ ha
  · apply Deduction.Hyp _ hb

example (C) (A B : Formula) (ha : A ∈ C) : C ⊢p A.Or B := by
  apply Deduction.Or_intro_left
  · apply Deduction.Hyp _ ha

end Examples

def Contradictory (C : Context) := ∃ (A : Formula), C ⊢p (A.And (A.Not))

-- Definition 7.17
def MaximallyConsistent (C : Context) := ¬(Contradictory C) ∧ ∀ D : Context, C ⊆ D ∧ C ≠ D → Contradictory D

open Classical in
noncomputable
def S (C : Context) (f : ℕ → Formula) (n : ℕ) := match n with
  | 0 => C
  | m + 1 => if ¬(Contradictory ((S C f m) ∪ {f m}))
                then ((S C f m) ∪ {f m})
                else (S C f m) ∪ {(f m).Not}

noncomputable
def f : ℕ → Formula := by
  have P := (@countable_iff_exists_surjective Formula _).mp inferInstance
  exact P.choose


abbrev Val := ℕ → Bool

def Val.eval (v : Val) (f : Formula) := match f with
  | .Symbol (n : ℕ) =>
    v n
  | .Not (f : Formula) =>
    ¬ (v.eval f)
  | .And (f₁ : Formula) (f₂ : Formula) =>
    (v.eval f₁) ∧ (v.eval f₂)
  | .Or (f₁ : Formula) (f₂ : Formula) =>
    (v.eval f₁) ∨ (v.eval f₂)
  | .Imp (f₁ : Formula) (f₂ : Formula) =>
    ¬ (v.eval f₁) ∨ (v.eval f₂)
  | .Iff (f₁ : Formula) (f₂ : Formula) =>
    (v.eval f₁) ↔ (v.eval f₂)

def Val.Satisfies (v : Val) (f) := v.eval f = true

-- notation v " ⊨v " f => Satisfies v f

def Satisfies (v : Val) (C : Context) := ∀ c ∈ C,  v.Satisfies c

def Consequence (C : Context) (f : Formula) := ∀ v : Val, Satisfies v C → v.Satisfies f

notation C " ⊨ " f => Consequence C f

open Classical in -- Says all propositions are decidable
noncomputable
def w (C : Context) (n : ℕ) : Bool := (Formula.Symbol n) ∈ C

end PropositionalLogic
