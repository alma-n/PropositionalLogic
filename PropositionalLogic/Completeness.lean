import PropositionalLogic.Lindenbaum

set_option linter.style.longLine false

namespace PropositionalLogic

open Formula
open Set

theorem completeness_of_natural_deduction (A : Formula) (C : Context) (hc : C ⊨ A) : C ⊢p A := by
  unfold Consequence at hc
  contrapose! hc
  rw [union_contradictory_iff] at hc
  obtain ⟨C', hc1, hc2, hs⟩ := @lindenbaum' _ ({A.Not} ∪ C) hc rfl
  use w C'
  constructor
  · unfold Satisfies
    intro c ch
    rw [wb_iff _ _ hc hs]
    apply hc2
    rw [mem_union]
    right
    exact ch
  · intro hf
    rw [wb_iff _ _ hc hs] at hf
    unfold MaximallyConsistent at hc1
    apply hc1.1
    use A
    apply Deduction.And_intro
    · apply Deduction.Hyp
      exact hf
    · apply Deduction.Hyp
      apply hc2
      rw [mem_union]
      left
      simp

end PropositionalLogic

