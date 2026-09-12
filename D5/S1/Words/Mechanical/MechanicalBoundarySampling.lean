/- GID: D5/S1/Words/Mechanical/MechanicalBoundarySampling
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalBoundarySampling
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Arbitrary sampling schedules have exact boundary-pair residuals, and each
     added sample can eliminate at most two distinct boundary-pair ambiguities. -/

import D5.S1.Words.Mechanical.MechanicalPastSeparation

set_option autoImplicit false

namespace D5.S1.Words.Mechanical.BoundarySampling

open PastSeparation

/-- Boundary indices detected by a specified set of sample times. -/
def detectedBy (A : Set Int) : Set Int := {m | m - 1 ∈ A ∨ m ∈ A}

/-- Residuals are indexed by actual lower/upper pairs at the same boundary.
This does not silently identify different boundary indices or arbitrary phases. -/
def residual (alpha : Real) (A B : Set Int) : Set Int :=
  {m | Set.EqOn (lower alpha m) (upper alpha m) A ∧
    ¬ Set.EqOn (lower alpha m) (upper alpha m) B}

/-- All samples agree precisely when neither of the two differing sites was observed. -/
theorem samples_agree_iff {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (A : Set Int) (m : Int) :
    Set.EqOn (lower alpha m) (upper alpha m) A ↔ m ∉ detectedBy A := by
  constructor
  · intro he hm
    rcases hm with hp | hq
    · exact ((disagree_iff ha0 ha1 ha m (m - 1)).mpr (Or.inl rfl)) (he hp)
    · exact ((disagree_iff ha0 ha1 ha m m).mpr (Or.inr rfl)) (he hq)
  · intro hn t ht
    by_contra hd
    apply hn
    rcases (disagree_iff ha0 ha1 ha m t).mp hd with hp | hq
    · exact Or.inl (by simpa [hp] using ht)
    · exact Or.inr (by simpa [hq] using ht)

/-- An exact closed form for target-relevant residuals under arbitrary, even infinite, schedules. -/
theorem residual_eq {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (A B : Set Int) : residual alpha A B = detectedBy B \ detectedBy A := by
  classical
  ext m
  simp only [residual, Set.mem_setOf_eq, samples_agree_iff ha0 ha1 ha,
    Set.mem_diff]
  tauto

/-- A necessary and sufficient target-recovery test on all actual paired boundary sides.
It is not a claim of full-state recovery over arbitrary pairs of phases. -/
theorem pair_target_recovery_iff {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (A B : Set Int) :
    (∀ m : Int, Set.EqOn (lower alpha m) (upper alpha m) A →
      Set.EqOn (lower alpha m) (upper alpha m) B) ↔ detectedBy B ⊆ detectedBy A := by
  constructor
  · intro h m hm
    by_contra hn
    have hp := (samples_agree_iff ha0 ha1 ha A m).mpr hn
    exact (samples_agree_iff ha0 ha1 ha B m).mp (h m hp) hm
  · intro h m hp
    apply (samples_agree_iff ha0 ha1 ha B m).mpr
    intro hm
    exact (samples_agree_iff ha0 ha1 ha A m).mp hp (h hm)

theorem detectedBy_union (A C : Set Int) :
    detectedBy (A ∪ C) = detectedBy A ∪ detectedBy C := by
  ext m
  simp only [detectedBy, Set.mem_setOf_eq, Set.mem_union]
  tauto

/-- Additional information removes exactly the residual pairs it actually separates. -/
theorem residual_after_samples {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (A B C : Set Int) :
    residual alpha (A ∪ C) B = residual alpha A B \ detectedBy C := by
  rw [residual_eq ha0 ha1 ha, residual_eq ha0 ha1 ha, detectedBy_union]
  ext m
  simp only [Set.mem_diff, Set.mem_union]
  tauto

/-- For a complete scalar past t<J and target samples 0,...,M-1,
the unresolved paired boundary indices are exactly J<m<=M. -/
theorem past_to_segment_residual {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha) (J M : Nat) :
    residual alpha (Set.Iio (J : Int)) (Set.Ico (0 : Int) (M : Int)) =
      Set.Ioc (J : Int) (M : Int) := by
  rw [residual_eq ha0 ha1 ha]
  ext m
  change (((0 ≤ m - 1 ∧ m - 1 < (M : Int)) ∨ (0 ≤ m ∧ m < (M : Int))) ∧
    ¬ (m - 1 < (J : Int) ∨ m < (J : Int))) ↔ ((J : Int) < m ∧ m ≤ (M : Int))
  omega

/-- Finite representation of the two neighboring boundary indices detected by each sample. -/
def detectedFinite (S : Finset Int) : Finset Int := S ∪ S.image (fun t => t + 1)

theorem mem_detectedFinite (S : Finset Int) (m : Int) :
    m ∈ detectedFinite S ↔ m - 1 ∈ S ∨ m ∈ S := by
  simp only [detectedFinite, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hm | ⟨t, ht, htm⟩)
    · exact Or.inr hm
    · have he : t = m - 1 := by omega
      exact Or.inl (by simpa [he] using ht)
  · rintro (hm | hm)
    · exact Or.inr ⟨m - 1, hm, by omega⟩
    · exact Or.inl hm

theorem detectedFinite_card_le (S : Finset Int) :
    (detectedFinite S).card ≤ 2 * S.card := by
  calc
    (detectedFinite S).card ≤ S.card + (S.image (fun t => t + 1)).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = 2 * S.card := by omega

/-- Eliminating r specified real boundary-pair ambiguities needs at least ceil(r/2)
point samples. This is a bound for that pair family, not a full observer-design claim. -/
theorem boundary_probe_lower_bound {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (R S : Finset Int)
    (h : ∀ m ∈ R, ¬ Set.EqOn (lower alpha m) (upper alpha m) (S : Set Int)) :
    R.card ≤ 2 * S.card := by
  have hsub : R ⊆ detectedFinite S := by
    intro m hm
    apply (mem_detectedFinite S m).mpr
    by_contra hn
    exact h m hm ((samples_agree_iff ha0 ha1 ha (S : Set Int) m).mpr hn)
  exact (Finset.card_le_card hsub).trans (detectedFinite_card_le S)

/-- Boundary-pair coverage is not a sufficient criterion for arbitrary states.
For every slope in (1/4,1/3), two actual lower traces read 000 and 010.
Their endpoint samples agree, although the middle target differs. -/
theorem boundary_cover_not_full_recovery {alpha : Real}
    (ha0 : (1 : Real) / 4 < alpha) (ha1 : alpha < (1 : Real) / 3) :
    detectedBy ({1} : Set Int) ⊆ detectedBy ({0, 2} : Set Int) ∧
      ∃ u v : Int → Int, BoundaryTrace alpha u ∧ BoundaryTrace alpha v ∧
        Set.EqOn u v ({0, 2} : Set Int) ∧ u 1 ≠ v 1 := by
  have hf1 : ⌊alpha⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hf2 : ⌊2 * alpha⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hf3 : ⌊3 * alpha⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hf4 : ⌊4 * alpha⌋ = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hf5 : ⌊5 * alpha⌋ = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  constructor
  · intro m hm
    simp only [detectedBy, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hm ⊢
    omega
  · refine ⟨lower alpha 0, lower alpha (-2), ⟨0, Or.inl rfl⟩,
      ⟨-2, Or.inl rfl⟩, ?_, ?_⟩
    · intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl <;>
        norm_num [lower, hf1, hf2, hf3, hf4, hf5]
    · norm_num [lower, hf1, hf2, hf3, hf4, hf5]

#print axioms residual_eq
#print axioms pair_target_recovery_iff
#print axioms past_to_segment_residual
#print axioms boundary_probe_lower_bound
#print axioms boundary_cover_not_full_recovery

end D5.S1.Words.Mechanical.BoundarySampling
