import PropositionalLogic.Defs
import PropositionalLogic.Basic

set_option linter.style.longLine false


namespace PropositionalLogic

open Formula
open Set

lemma lindenbaum' (C : Context) (hc : ¬ (Contradictory C)) (hs : S' = ⋃ i, S C f i) : ∃ D : Context, MaximallyConsistent D ∧ C ⊆ D ∧ D = S' := by
  use S'
  refine ⟨?_, ?_, ?_⟩
  · exact (maximally_consistent_S' S' C hs hc f_surjective).1
  · rw [hs]
    intro c hc
    rw [mem_iUnion]
    use 0
    unfold S
    exact hc
  · grind

-- Lemma 7.18 (Lindenbaumin lemma)
lemma lindenbaum (C : Context) (hc : ¬ (Contradictory C)) (hs : S' = ⋃ i, S C f i) : ∃ D : Context, MaximallyConsistent D ∧ C ⊆ D := by
  have ⟨D, hd⟩ := lindenbaum' C hc hs
  use D
  constructor
  · grind
  · grind

end PropositionalLogic
