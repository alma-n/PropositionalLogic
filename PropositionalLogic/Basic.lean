import PropositionalLogic.Defs
import Mathlib.Tactic

set_option linter.style.longLine false

namespace PropositionalLogic

open Formula
open Set

lemma weaken_self (C : Context) : ({A} ∪ C) ⊢p A := by
  apply Deduction.Hyp
  simp


lemma weaken {D F : Context} (h : D ⊢p P) : (F ∪ D) ⊢p P := by
  induction h with
  | Hyp A h =>
      apply Deduction.Hyp
      rw [mem_union]
      right
      exact h
  | And_intro A B _ _ h3 h4 =>
      apply Deduction.And_intro
      · specialize h3
        exact h3
      · specialize h4
        exact h4
  | Or_intro_left A B h1 h2 =>
      apply Deduction.Or_intro_left
      exact h2
  | Or_intro_right A B h1 h2 =>
      apply Deduction.Or_intro_right
      exact h2
  | @Imp_intro C A B _ h2 =>
      apply Deduction.Imp_intro
      have : F ∪ ({A} ∪ C) = {A} ∪ (F ∪ C) := by
        exact union_left_comm F {A} C
      rw [← this]
      exact h2
  | @Not_intro C A B _ h2 =>
      apply Deduction.Not_intro _ B
      have : F ∪ ({A} ∪ C) = {A} ∪ (F ∪ C) := by
        exact union_left_comm F {A} C
      rw [← this]
      exact h2
  | And_elim_left A B h1 h2 =>
      apply Deduction.And_elim_left at h2
      exact h2
  | And_elim_right A B _ h2 =>
      apply Deduction.And_elim_right at h2
      exact h2
  | Or_elim A B C ha hb hc h1 h2 h3 =>
      apply Deduction.Or_elim at h1
      apply h1
      · rw [union_assoc]
        exact h2
      rw [union_assoc]
      exact h3
  | Imp_elim A B _ _ h3 h4 =>
      apply Deduction.Imp_elim A
      · exact h3
      · exact h4
  | Not_elim A _ h2 =>
      apply Deduction.Not_elim at h2
      exact h2
  | Iff_intro A B ha hb h1 h2 =>
      apply Deduction.Iff_intro
      · grind
      · grind
  | Iff_elim_left A B _ _ h1 h2 =>
      apply Deduction.Iff_elim_left A
      · exact h1
      · exact h2
  | Iff_elim_right A B _ _ h1 h2 =>
      apply Deduction.Iff_elim_right A B
      · exact h1
      · exact h2

lemma weaken' {D F : Context} (h : F ⊢p P) : (F ∪ D) ⊢p P := by
  rw [union_comm F D]
  exact weaken h


-- Lemma 7.15 part 1
lemma contradictory_iff : Contradictory C ↔ ∃ (A : Formula), (C ⊢p A) ∧ (C ⊢p A.Not) := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    use a
    constructor
    · apply Deduction.And_elim_left _ a.Not ha
    · apply Deduction.And_elim_right at ha
      exact ha
  · intro h
    obtain ⟨a, ha⟩ := h
    use a
    apply Deduction.And_intro
    · exact ha.1
    · exact ha.2

-- Lemma 7.15 part 2
lemma contradictory_iff' : Contradictory C ↔ ∀ (A : Formula), C ⊢p A := by
  constructor
  · intro h a
    unfold Contradictory at h
    obtain ⟨A, ha⟩ := h
    apply Deduction.Not_elim
    apply Deduction.Not_intro _ A
    apply weaken _
    exact ha
  · intro h
    unfold Contradictory
    have A : Formula := Inhabited.default
    use A
    apply Deduction.And_intro
    · specialize h A
      exact h
    · specialize h A.Not
      exact h

-- lemma 7.16
lemma union_contradictory_iff (A : Formula) (C : Context) : Deduction C A ↔ Contradictory ({A.Not} ∪ C) := by
  constructor
  · intro h
    use A
    apply Deduction.And_intro
    · apply weaken _
      exact h
    · apply Deduction.Hyp
      simp
  · intro h
    by_cases hc : Contradictory C
    · rw [contradictory_iff'] at hc
      exact hc A
    · unfold Contradictory at *
      obtain ⟨B, hb⟩ := h
      simp at hc
      apply Deduction.Not_intro at hb
      apply Deduction.Not_elim _ hb

lemma have_ (P : Formula) (hc : C ⊢p P) : ((C ∪ {P}) ⊢p F) ↔ (C ⊢p F) := by
  constructor
  · intro h
    apply Deduction.Imp_elim P
    · apply Deduction.Imp_intro
      rw [union_comm]
      exact h
    · exact hc
  · intro h
    apply weaken'
    exact h

lemma mem_maximally_consistent (S : Context) (hs : MaximallyConsistent S) : ∀ A : Formula, (S ⊢p A) ∨ (S ⊢p A.Not) := by
  intro A
  unfold MaximallyConsistent at hs
  obtain ⟨hs, hd⟩ :=  hs
  unfold Contradictory at *
  by_cases h : S ⊢p A
  · left
    exact h
  · have : S ⊆ S ∪ {A} ∧ S ≠ S ∪ {A} := by
      constructor
      · simp
      · intro hf
        apply h
        rw [hf]
        apply Deduction.Hyp
        simp
    specialize hd (S ∪ {A}) this
    obtain ⟨B, hb⟩ := hd
    right
    rw [union_contradictory_iff, union_comm]
    unfold Contradictory
    use B
    rw [union_comm] at hb
    have gona : (S ∪ {A.Not.Not}) ⊢p A := by
      apply weaken
      apply Deduction.Not_elim
      apply Deduction.Hyp
      simp
    apply weaken (F := {A.Not.Not}) at hb
    rw [← union_assoc, union_comm, ← union_assoc] at hb
    rw [have_ A gona (F := B.And B.Not)] at hb
    exact hb

lemma Sj_contains_a_or_na (hf : f.Surjective) : ∀ A, ∃ n, A ∈ S C f n ∨ A.Not ∈ S C f n := by
  intro A
  have ⟨n, hn⟩ := hf A
  use (n + 1)
  unfold S
  by_cases hgona : Contradictory (S C f n ∪ {f n})
  · simp_rw [hgona]
    simp [hn]
  · simp_rw [hgona]
    simp [hn]

lemma contradictory_not_not (hc : Contradictory (C ∪ {A})) : Contradictory (C ∪ {A.Not.Not}) := by
  unfold Contradictory at *
  obtain ⟨B, hb⟩ := hc
  use B
  rw [union_comm]
  apply Deduction.Imp_elim A
  · apply Deduction.Imp_intro
    rw [union_comm, union_assoc]
    apply weaken
    exact hb
  · apply Deduction.Not_elim
    apply Deduction.Hyp
    grind

lemma Sn_consistent (C : Context) (f : ℕ → Formula) (n : ℕ) (hc : ¬ Contradictory C) : ¬ (Contradictory (S C f n)) := by
  induction n with
  | zero =>
      exact hc
  | succ n ih =>
      unfold S
      by_cases h_contra : Contradictory (S C f n ∪ {f (n)})
      · simp_rw [h_contra]
        simp only [not_true_eq_false, ↓reduceIte, union_singleton]
        have := union_contradictory_iff (f n).Not (S C f n)
        -- rw [union_comm, ← this] at h_contra
        have gona1 := this.mpr ?_
        · intro h_gona
          have := union_contradictory_iff (f n) (S C f n)
          have gona := this.mpr ?_
          · apply ih
            use (f n)
            apply Deduction.And_intro
            · exact gona
            · exact gona1
          exact h_gona
        have gona := contradictory_not_not (C := S C f n) (A := f n) h_contra
        rw [union_comm]
        exact gona
        -- exact ih
      · simp_rw [h_contra]
        simp only [not_false_eq_true, ↓reduceIte, union_singleton]
        intro h
        rw [insert_eq, union_comm] at h
        contradiction

lemma Sn_subset_succ : S C f n ⊆ S C f (n + 1) := by
  intro x hx
  unfold S
  split
  · simp [hx]
  · simp [hx]

lemma Sn_subset_iff (h : k ≤ m) : S C f k ⊆  S C f m := by
  let d := m - k
  have : m = k + d := by
    grind
  rw [this] at *
  clear h this
  clear_value d
  induction d with
  | zero => rfl
  | succ n ih =>
    apply Subset.trans ih
    simp_rw [← Nat.add_assoc k n]
    exact Sn_subset_succ

lemma subset_consistent (C D : Context) (h : D ⊆ C) (hc : ¬ Contradictory C) : ¬ Contradictory D := by
  unfold Contradictory at *
  intro hd
  obtain ⟨A, ha⟩ := hd
  apply weaken (F := C) at ha
  have : C ∪ D = C := by
    grind
  rw [this] at ha
  apply hc
  use A

theorem finiteness_ (C : Context) (hc : C ⊢p A) : ∃ F, F ⊆ C ∧ F.Finite ∧ F ⊢p A := by
  induction hc with
  | Hyp A h1 =>
    use {A}
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
    · apply Deduction.Hyp
      simp
  | And_intro A B ha hb ih1 ih2 =>
    obtain ⟨F1, _, _, h1⟩ := ih1
    obtain ⟨F2, _, _, h2⟩ := ih2
    use (F1 ∪ F2)
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · apply Deduction.And_intro
      · apply weaken'
        exact h1
      · apply weaken
        exact h2
  | Or_intro_left A B ha ih =>
    obtain ⟨F, _, _, hf⟩ := ih
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · apply Deduction.Or_intro_left
      exact hf
  | Or_intro_right A B ha ih =>
    obtain ⟨F, _, _, hf⟩ := ih
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · apply Deduction.Or_intro_right
      exact hf
  | Imp_intro A B hb ih =>
    obtain ⟨F, h1, h2, hf⟩ := ih
    use (F \ {A})
    refine ⟨?_, ?_, ?_⟩
    · grind
    · exact Finite.diff h2
    · apply Deduction.Imp_intro
      simp only [union_diff_self, singleton_union]
      apply weaken
      exact hf
  | Not_intro A B hf ih =>
    obtain ⟨F, h1, h2, hf⟩ := ih
    use (F \ {A})
    refine ⟨?_, ?_, ?_⟩
    · grind
    · exact Finite.diff h2
    · apply Deduction.Not_intro _ B
      simp only [union_diff_self, singleton_union]
      apply weaken
      exact hf
  | And_elim_left A B h ih =>
    obtain ⟨F, h1, h2, hf⟩ := ih
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · apply Deduction.And_elim_left at hf
      exact hf
  | And_elim_right A B h ih =>
    obtain ⟨F, h1, h2, hf⟩ := ih
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · apply Deduction.And_elim_right at hf
      exact hf
  | Or_elim A B C h1 h2 h3 ih1 ih2 ih3 =>
    obtain ⟨F1, _, _, h1⟩ := ih1
    obtain ⟨F2, _, _, h2⟩ := ih2
    obtain ⟨F3, _, _, h3⟩ := ih3
    use (F1 ∪ (F2 \ {A}) ∪ (F3 \ {B}))
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      constructor <;>
      · simp_all
    · apply Deduction.Or_elim A B
      · apply weaken'
        apply weaken'
        exact h1
      · rw [union_assoc, union_comm, union_assoc]
        apply weaken
        rw [← union_assoc, union_comm, ← union_assoc, diff_union_self]
        apply weaken'
        apply weaken'
        exact h2
      · rw [union_assoc, union_comm]
        apply weaken'
        rw [diff_union_self]
        apply weaken'
        exact h3
  | Imp_elim A B h1 h2 ih1 ih2 =>
    obtain ⟨F1, _, _, h1⟩ := ih1
    obtain ⟨F2, _, _, h2⟩ := ih2
    use (F1 ∪ F2)
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · apply Deduction.Imp_elim A
      · apply weaken'
        exact h1
      · apply weaken
        exact h2
  | Not_elim A ha ih =>
    obtain ⟨F, h1, h2, hf⟩ := ih
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · apply Deduction.Not_elim at hf
      exact hf
  | Iff_intro A B _ _ ih1 ih2 =>
    obtain ⟨F1, _, hf1, h1⟩ := ih1
    obtain ⟨F2, _, hf2, h2⟩ := ih2
    use ((F1 \ {A}) ∪ (F2 \ {B}))
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp only [finite_union]
      constructor
      · exact Finite.diff hf1
      · exact Finite.diff hf2
    · apply Deduction.Iff_intro
      · rw [← union_assoc, union_comm]
        apply weaken
        rw [union_diff_self]
        apply weaken
        exact h1
      · rw [union_comm, union_assoc]
        apply weaken
        rw [union_comm, union_diff_self]
        apply weaken
        exact h2
  | Iff_elim_left A B ha hb ih1 ih2 =>
    obtain ⟨F1, _, _, h1⟩ := ih1
    obtain ⟨F2, _, _, h2⟩ := ih2
    use F1 ∪ F2
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · apply Deduction.Iff_elim_left A
      · apply weaken'
        exact h1
      · apply weaken
        exact h2
  | Iff_elim_right A B _ _ ih1 ih2 =>
    obtain ⟨F1, _, _, h1⟩ := ih1
    obtain ⟨F2, _, _, h2⟩ := ih2
    use F1 ∪ F2
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · apply Deduction.Iff_elim_right A B
      · apply weaken'
        exact h1
      · apply weaken
        exact h2


lemma exists_finite_inconsistent_subset_of_inconsistent' (C _F : Context) (A : Formula) (hc : C ⊢p A.And A.Not) : ∃ F, F ⊆ C ∧ F.Finite ∧ Contradictory F := by
  cases hc with
  | Hyp B h =>
    use {A.And A.Not}
    constructor
    · grind
    · constructor
      · simp
      · use A
        apply Deduction.Hyp
        simp
  | And_intro P B h1 h2 =>
    apply finiteness_ at h1
    apply finiteness_ at h2
    obtain ⟨F1, hf1⟩ := h1
    obtain ⟨F2, hf2⟩ := h2
    use (F1 ∪ F2)
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · unfold Contradictory
      use A
      apply Deduction.And_intro
      · apply weaken' hf1.2.2
      · apply weaken hf2.2.2
  | And_elim_left A B h1 =>
    apply finiteness_ at h1
    obtain ⟨F, hf, hf2, hf3⟩ := h1
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · unfold Contradictory
      use A
      apply Deduction.And_elim_left
      exact hf3
  | And_elim_right D B h1 =>
    apply finiteness_ at h1
    obtain ⟨F, hf, hf2, hf3⟩ := h1
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · use A
      apply Deduction.And_elim_right at hf3
      exact hf3
  | Or_elim a b  c h h1 h2 =>
    apply finiteness_ at h1
    apply finiteness_ at h2
    obtain ⟨F1, hf1, hf11, h1⟩ := h1
    obtain ⟨F2, hf2, hf22, h2⟩ := h2
    obtain ⟨C', hc1, hc2, h3⟩ := finiteness_ _ h
    use (C' ∪ (F1 \ {a}) ∪ (F2 \ {b}))
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp only [finite_union]
      constructor
      · constructor
        · grind
        · exact Finite.diff hf11
      · exact Finite.diff hf22
    · use A
      apply Deduction.Or_elim a b
      · apply weaken'
        apply weaken'
        exact h3
      · rw [union_assoc, union_assoc]
        apply weaken
        rw [← union_assoc, union_comm, ← union_assoc]
        apply weaken'
        rw [union_diff_self]
        apply weaken
        exact h1
      · rw [union_assoc, diff_union_self]
        apply weaken
        apply weaken'
        exact h2
  | Imp_elim D B h1 h2 =>
    apply finiteness_ at h1
    apply finiteness_ at h2
    obtain ⟨F1, _, _, h1⟩ := h1
    obtain ⟨F2, _, _, h2⟩ := h2
    use (F1 ∪ F2)
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · use A
      apply Deduction.Imp_elim D
      · apply weaken'
        exact h1
      · apply weaken
        exact h2
  | Not_elim A h1 =>
    apply finiteness_ at h1
    obtain ⟨F, _, _, hf⟩ := h1
    use F
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · apply Deduction.Not_elim at hf
      use A
  | Iff_elim_left D B h1 h2 =>
    apply finiteness_ at h1
    apply finiteness_ at h2
    obtain ⟨F1, _, _, hf1⟩ := h1
    obtain ⟨F2, _, _, hf2⟩ := h2
    use F1 ∪ F2
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · use A
      apply Deduction.Iff_elim_left D
      · apply weaken'
        exact hf1
      · apply weaken
        exact hf2
  | Iff_elim_right D B h1 h2 =>
    apply finiteness_ at h1
    apply finiteness_ at h2
    obtain ⟨F1, _, _, hf1⟩ := h1
    obtain ⟨F2, _, _, hf2⟩ := h2
    use F1 ∪ F2
    refine ⟨?_, ?_, ?_⟩
    · grind
    · simp
      grind
    · use A
      apply Deduction.Iff_elim_right (A.And A.Not) B
      · apply weaken'
        exact hf1
      · apply weaken
        exact hf2

lemma exists_finite_inconsistent_subset_of_inconsistent (C : Context) (hc : Contradictory C) : ∃ F, F ⊆ C ∧ F.Finite ∧ Contradictory F := by
  unfold Contradictory at *
  obtain ⟨A, ha⟩ := hc
  apply finiteness_ at ha
  obtain ⟨F, _, _, hf⟩ := ha
  use F
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · use A

lemma exists_Sj_of_finite_subset (F : Context) (h_finite : F.Finite) (hf : F ⊆ ⋃ i, S C f i) : ∃ j, F ⊆ S C f j := by
  by_cases h_nonempty : F.Nonempty
  · apply finite_subset_iUnion at hf
    · obtain ⟨I, h1, h2⟩ := hf
      have : Fintype I := by
        exact h1.fintype
      have : I.toFinset.Nonempty := by
        by_contra h_gona
        rw [toFinset_nonempty, ← nonempty_coe_sort, nonempty_subtype, not_exists] at h_gona
        simp only [h_gona, iUnion_of_empty, iUnion_empty, subset_empty_iff] at h2
        subst F
        simp at h_nonempty
      use I.toFinset.max' this
      intro A ha
      apply h2 at ha
      rw [mem_iUnion] at ha
      obtain ⟨i, hi⟩ := ha
      rw [mem_iUnion] at hi
      obtain ⟨j, hj⟩ := hi
      apply Sn_subset_iff (k := i) (m := I.toFinset.max' this)
      · apply Finset.le_max'
        simp [j]
      · exact hj
    · exact h_finite
  · simp [Set.Nonempty, ← eq_empty_iff_forall_notMem] at h_nonempty
    subst F
    simp

lemma iUnion_Sj_consistent (hc : ¬ Contradictory C) : ∀ j, ¬ Contradictory (⋃ i ≤ j, S C f i) := by
  intro j
  have : ⋃ i ≤ j, S C f i ⊆ S C f j := by
    intro i hi
    rw [mem_iUnion] at hi
    obtain ⟨l, hl⟩ := hi
    rw [mem_iUnion] at hl
    obtain ⟨k, hk⟩ := hl
    apply Sn_subset_iff
    · exact k
    · exact hk
  have gona : ¬ Contradictory (S C f j) := by
    exact Sn_consistent C f j hc
  exact subset_consistent (S C f j) _ this gona


lemma iUnion_S_consistent (C S' : Context) (hc : ¬ Contradictory C) (hs : S' = ⋃ n, S C f n) : ¬(Contradictory S') := by
  intro h
  apply exists_finite_inconsistent_subset_of_inconsistent at h
  obtain ⟨F, h1, h2, hf⟩ := h
  rw [hs] at h1
  have := exists_Sj_of_finite_subset (C := C) F h2 h1
  obtain ⟨j, h⟩ := this
  have := Sn_consistent C f j hc
  apply subset_consistent at h
  specialize h this
  contradiction

lemma iUnion_not_contains_na (C S' : Context) (hc : ¬ Contradictory C) (hs : S' = ⋃ n, S C f n) (ha : A ∈ S') : ¬ (A.Not ∈ S') := by
  intro hna
  have := iUnion_S_consistent C S' hc hs
  apply this
  unfold Contradictory
  use A
  apply Deduction.And_intro
  · apply Deduction.Hyp
    exact ha
  · apply Deduction.Hyp
    exact hna

lemma iUnion_contains_a_or_na (C S' : Context) (hf : f.Surjective) (hs : S' = ⋃ n, S C f n) : ∀ A : Formula, A ∈ S' ∨ A.Not ∈ S' := by
  intro A
  have ⟨n, hn⟩ := Sj_contains_a_or_na (C := C) hf A
  cases hn with
  | inl hn =>
    left
    rw [hs, mem_iUnion]
    use n
  | inr hn =>
    right
    rw [hs, mem_iUnion]
    use n


lemma maximally_consistent_S' (S' C : Context) (hs : S' = ⋃ i, S C f i) (hc : ¬ Contradictory C) (hf : Function.Surjective f) : MaximallyConsistent S' ∧ C ⊆ S' := by
  constructor
  · unfold MaximallyConsistent
    constructor
    · exact iUnion_S_consistent C S' hc hs
    · intro D hd
      have hS := iUnion_S_consistent C S' hc hs
      have gona := iUnion_contains_a_or_na C S' hf hs
      have : (D \ S').Nonempty := by
        apply nonempty_of_not_subset
        intro h
        have : D = S' := by
          apply Subset.antisymm
          · exact h
          · exact hd.1
        apply hd.2
        exact this.symm
      obtain ⟨A, ha⟩ := this
      specialize gona A
      cases gona with
      | inl hf =>
        simp at ha
        grind
      | inr hf =>
        unfold Contradictory
        use A
        apply Deduction.And_intro
        · apply Deduction.Hyp
          exact ha.1
        · apply Deduction.Hyp
          apply hd.1
          exact hf
  · intro F hf
    rw [hs, mem_iUnion]
    use 0
    unfold S
    exact hf

lemma f_surjective : f.Surjective := by
  have P := (@countable_iff_exists_surjective Formula _).mp inferInstance
  exact P.choose_spec


lemma mem_S' (C : Context) (A : Formula) (hs : S' = ⋃ i, S C f i) : A ∈ S' ∨ A.Not ∈ S' := by
  have ⟨n, hn⟩ := Sj_contains_a_or_na f_surjective A (C := C)
  cases hn with
  | inl h =>
    left
    rw [hs, mem_iUnion]
    use n
  | inr h =>
    right
    rw [hs, mem_iUnion]
    use n

lemma mem_S'_iff (hc : ¬ Contradictory C) (hs : S' = ⋃ i, S C f i) (A : Formula) : A ∈ S' ↔ (A.Not ∉ S') := by
  constructor
  · intro ha hf
    have := maximally_consistent_S' S' C hs hc f_surjective
    unfold MaximallyConsistent at this
    apply this.1.1
    use A
    apply Deduction.And_intro
    · apply Deduction.Hyp _ ha
    · apply Deduction.Hyp _ hf
  · intro ha
    have := mem_S' C A hs
    grind

lemma mem_S'_iff_and (hc : ¬ Contradictory C) (hs : S' = ⋃ i, S C f i) (A : Formula) : A ∈ S' ∧ B ∈ S' ↔ (A.And B ∈ S') := by
  have := maximally_consistent_S' S' C hs hc f_surjective
  unfold MaximallyConsistent at this
  constructor
  · intro ha
    rw [mem_S'_iff hc hs]
    intro hf
    apply this.1.1
    use A.And B
    apply Deduction.And_intro
    · apply Deduction.And_intro
      · apply Deduction.Hyp _ ha.1
      · apply Deduction.Hyp _ ha.2
    · apply Deduction.Hyp _ hf
  · intro ha
    rw [mem_S'_iff hc hs, mem_S'_iff hc hs (A := B)]
    constructor
    · intro hf
      apply this.1.1
      use A
      apply Deduction.And_intro
      · apply Deduction.And_elim_left A B
        apply Deduction.Hyp
        exact ha
      · apply Deduction.Hyp
        exact hf
    · intro hf
      apply this.1.1
      use B
      apply Deduction.And_intro
      · apply Deduction.And_elim_right A B
        apply Deduction.Hyp
        exact ha
      · apply Deduction.Hyp
        exact hf

lemma mem_S'_iff_or (hc : ¬ Contradictory C) (hs : S' = ⋃ i, S C f i) (A : Formula) : A ∈ S' ∨ B ∈ S' ↔ (A.Or B ∈ S') := by
  have := maximally_consistent_S' S' C hs hc f_surjective
  unfold MaximallyConsistent at this
  constructor
  · intro ha
    rw [mem_S'_iff hc hs]
    intro hf
    apply this.1.1
    cases ha with
    | inl ha =>
      use (A.Or B)
      apply Deduction.And_intro
      · apply Deduction.Or_intro_left
        apply Deduction.Hyp _ ha
      · apply Deduction.Hyp _ hf
    | inr hb =>
      use (A.Or B)
      apply Deduction.And_intro
      · apply Deduction.Or_intro_right
        apply Deduction.Hyp _ hb
      · apply Deduction.Hyp _ hf
  · intro ha
    rw [mem_S'_iff hc hs, mem_S'_iff hc hs (A := B)]
    have := mem_S' C A hs
    cases this with
    | inl h =>
      left
      rw [← mem_S'_iff hc hs]
      exact h
    | inr h =>
      right
      intro hb
      apply this.1.1
      use B
      apply Deduction.And_intro
      · apply Deduction.Or_elim A B
        · apply Deduction.Hyp
          exact ha
        · have gona : Contradictory (S' ∪ {A}) := by
            use A
            apply Deduction.And_intro
            · apply Deduction.Hyp
              simp
            · apply Deduction.Hyp
              simp [h]
          rw [contradictory_iff'] at gona
          grind
        · apply Deduction.Hyp
          simp
      · apply Deduction.Hyp
        exact hb

lemma mem_S'_iff_imp (hc : ¬ Contradictory C) (hs : S' = ⋃ i, S C f i) (A : Formula) : A.Not.Or B ∈ S' ↔ (A.Imp B ∈ S') := by
  have := maximally_consistent_S' S' C hs hc f_surjective
  constructor
  · intro h
    rw [← mem_S'_iff_or hc hs] at h
    cases h with
    | inl ha =>
      rw [mem_S'_iff hc hs]
      intro hf
      apply this.1.1
      use A.Imp B
      · apply Deduction.And_intro
        · apply Deduction.Imp_intro
          have gona : Contradictory (S' ∪ {A}) := by
              use A
              apply Deduction.And_intro
              · apply Deduction.Hyp
                simp
              · apply Deduction.Hyp
                simp [ha]
          rw [contradictory_iff'] at gona
          grind
        · apply Deduction.Hyp _ hf
    | inr hb =>
      rw [mem_S'_iff hc hs]
      intro hf
      apply this.1.1
      use A.Imp B
      · apply Deduction.And_intro
        · apply Deduction.Imp_intro
          apply Deduction.Hyp
          grind
        · apply Deduction.Hyp _ hf
  · intro h
    rw [← mem_S'_iff_or hc hs]
    have := mem_S' C A hs
    cases this with
    | inl ha =>
      right
      rw [mem_S'_iff hc hs]
      intro hf
      apply this.1.1
      use B
      apply Deduction.And_intro
      · apply Deduction.Imp_elim A
        · apply Deduction.Hyp _ h
        · apply Deduction.Hyp _ ha
      · apply Deduction.Hyp _ hf
    | inr hna =>
      simp [hna]


lemma mem_S'_iff_iff (hc : ¬ Contradictory C) (hs : S' = ⋃ i, S C f i) (A : Formula) :(A ∈ S' ↔ B ∈ S') ↔ (A.Iff B ∈ S') := by
  have := maximally_consistent_S' S' C hs hc f_surjective
  constructor
  · intro h
    rw [mem_S'_iff hc hs]
    intro hf
    apply this.1.1
    use A.Iff B
    apply Deduction.And_intro
    · apply Deduction.Iff_intro
      · have := mem_S' C A hs
        cases this
        · apply Deduction.Hyp
          grind
        · have gona : Contradictory (S' ∪ {A}) := by
            use A
            apply Deduction.And_intro
            · apply Deduction.Hyp
              simp
            · apply Deduction.Hyp
              left
              grind
          rw [contradictory_iff'] at gona
          grind
      · have := mem_S' C B hs
        cases this
        · apply Deduction.Hyp
          grind
        · have gona : Contradictory (S' ∪ {B}) := by
            use B
            apply Deduction.And_intro
            · apply Deduction.Hyp
              simp
            · apply Deduction.Hyp
              left
              grind
          rw [contradictory_iff'] at gona
          grind
    · apply Deduction.Hyp _ hf
  · intro h
    constructor
    · intro ha
      rw [mem_S'_iff hc hs]
      intro hb
      apply this.1.1
      use B
      apply Deduction.And_intro
      · apply Deduction.Iff_elim_left A B
        · apply Deduction.Hyp _ h
        · apply Deduction.Hyp _ ha
      · apply Deduction.Hyp _ hb
    · intro ha
      rw [mem_S'_iff hc hs]
      intro hb
      apply this.1.1
      use A
      apply Deduction.And_intro
      · apply Deduction.Iff_elim_right A B
        · apply Deduction.Hyp _ h
        · apply Deduction.Hyp _ ha
      · apply Deduction.Hyp _ hb

lemma wb_iff (C : Context) (B : Formula) (hc : ¬ (Contradictory C)) (hs : S' = ⋃ i, S C f i) : (Val.Satisfies (w S') B) ↔ B ∈ S' := by
  have := maximally_consistent_S' S' C hs hc f_surjective
  induction B with
    unfold Val.Satisfies Val.eval
  | Symbol n =>
    unfold w
    simp
  | Not f ih =>
    simp only [Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true]
    rw [← Bool.not_eq_true, ← Val.Satisfies]
    simp_rw [ih]
    rw [mem_S'_iff hc hs]
    simp
  | And f₁ f₂ f₁_ih f₂_ih =>
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true]
    rw [← Val.Satisfies, ← Val.Satisfies]
    simp_rw [f₁_ih, f₂_ih]
    rw [mem_S'_iff_and hc hs]
  | Or f₁ f₂ f₁_ih f₂_ih =>
    simp only [Bool.decide_or, Bool.decide_eq_true, Bool.or_eq_true]
    rw [← Val.Satisfies, ← Val.Satisfies]
    simp_rw [f₁_ih, f₂_ih]
    rw [mem_S'_iff_or hc hs]
  | Imp f₁ f₂ f₁_ih f₂_ih =>
    simp only [Bool.not_eq_true, Bool.decide_or, Bool.decide_eq_false, Bool.decide_eq_true,
      Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    rw [← Bool.not_eq_true, ← Val.Satisfies, ← Val.Satisfies]
    simp_rw [f₁_ih, f₂_ih]
    rw [mem_S'_iff hc hs]
    push_neg
    rw [mem_S'_iff_or hc hs]
    rw [mem_S'_iff_imp hc hs]
  | Iff f₁ f₂ f₁_ih f₂_ih =>
    simp only [decide_eq_true_eq]
    rw [← Val.Satisfies, ← Val.Satisfies]
    simp_rw [f₁_ih, f₂_ih]
    rw [mem_S'_iff_iff hc hs]

end PropositionalLogic
