/- GID: D5/S3/ArithUnits/CyclicPlaneAffineCommutator
   generality: I
   mirror-B: D5/B/S3/ArithUnits/CyclicPlaneAffineCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct affine centers generate a nonzero translation and collapse invariant supports modulo 157. -/

import D5.S3.ArithUnits.TranslationInvariantLowMoments

/-! The commutator of two centered affine multipliers is a translation. -/

namespace D5.S3.ArithUnits.CyclicPlaneAffineCommutator

open D5.S3.ArithUnits.TranslationInvariantLowMoments

def affineDouble (center x : ZMod 157) : ZMod 157 :=
  center + 2 * (x - center)

def affineTriple (center x : ZMod 157) : ZMod 157 :=
  center + 3 * (x - center)

/-- The two affine multipliers have a translation as their commutator. -/
theorem affine_commutator_translation_invariant (D : Finset (ZMod 157))
    (c d : ZMod 157)
    (h₂ : D.image (affineDouble c) = D)
    (h₃ : D.image (affineTriple d) = D) :
    D.image (fun x => x + 2 * (c - d)) = D := by
  have hfg : D.image (fun x => affineDouble c (affineTriple d x)) = D := by
    calc
      D.image (fun x => affineDouble c (affineTriple d x)) =
          (D.image (affineTriple d)).image (affineDouble c) := by
        simp only [Finset.image_image, Function.comp_def]
      _ = D.image (affineDouble c) := by rw [h₃]
      _ = D := h₂
  have hgf : D.image (fun x => affineTriple d (affineDouble c x)) = D := by
    calc
      D.image (fun x => affineTriple d (affineDouble c x)) =
          (D.image (affineDouble c)).image (affineTriple d) := by
        simp only [Finset.image_image, Function.comp_def]
      _ = D.image (affineTriple d) := by rw [h₂]
      _ = D := h₃
  have htranslate :
      (D.image (fun x => affineTriple d (affineDouble c x))).image
          (fun y => y + 2 * (c - d)) =
        D.image (fun x => affineDouble c (affineTriple d x)) := by
    simp only [Finset.image_image, Function.comp_def]
    apply Finset.image_congr
    intro x hx
    dsimp [affineDouble, affineTriple]
    ring
  calc
    D.image (fun x => x + 2 * (c - d)) =
        (D.image (fun x => affineTriple d (affineDouble c x))).image
          (fun y => y + 2 * (c - d)) := by rw [hgf]
    _ = D.image (fun x => affineDouble c (affineTriple d x)) := htranslate
    _ = D := hfg

/-- Distinct affine centers force the support cardinality to be divisible by 157. -/
theorem card_dvd_of_distinct_center_affine_invariant (D : Finset (ZMod 157))
    (c d : ZMod 157)
    (h₂ : D.image (affineDouble c) = D)
    (h₃ : D.image (affineTriple d) = D)
    (hcd : c ≠ d) :
    157 ∣ D.card := by
  classical
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  have htwo : (2 : ZMod 157) ≠ 0 := by decide
  have ht : (2 : ZMod 157) * (c - d) ≠ 0 := by
    exact mul_ne_zero htwo (sub_ne_zero.mpr hcd)
  have htrans := affine_commutator_translation_invariant D c d h₂ h₃
  rw [Subsingleton.elim (ZMod.decidableEq 157) (Classical.decEq (ZMod 157))] at htrans
  have hsum := power_sum_eq_zero_of_add_invariant D
    (2 * (c - d)) 0 ht htrans (by norm_num)
  have hcast : (D.card : ZMod 157) = 0 := by
    simpa using hsum
  exact (CharP.cast_eq_zero_iff (ZMod 157) 157 D.card).mp hcast

/-- With distinct centers, an invariant finite subset is empty or the full field. -/
theorem distinct_center_affine_classification (D : Finset (ZMod 157))
    (c d : ZMod 157)
    (h₂ : D.image (affineDouble c) = D)
    (h₃ : D.image (affineTriple d) = D)
    (hcd : c ≠ d) :
    D = ∅ ∨ D = Finset.univ := by
  have hdvd := card_dvd_of_distinct_center_affine_invariant D c d h₂ h₃ hcd
  have hle : D.card ≤ 157 := by
    simpa using (Finset.card_le_univ D)
  have hcases : D.card = 0 ∨ D.card = 157 := by omega
  rcases hcases with hempty | hfull
  · exact Or.inl (Finset.card_eq_zero.mp hempty)
  · exact Or.inr (Finset.eq_of_subset_of_card_le (Finset.subset_univ D) (by simp [hfull]))

/-- In particular, no thirteen-element support can have two distinct affine centers. -/
theorem no_thirteen_element_distinct_center_affine_invariant
    (D : Finset (ZMod 157)) (hcard : D.card = 13)
    (c d : ZMod 157)
    (h₂ : D.image (affineDouble c) = D)
    (h₃ : D.image (affineTriple d) = D)
    (hcd : c ≠ d) : False := by
  have hdvd := card_dvd_of_distinct_center_affine_invariant D c d h₂ h₃ hcd
  norm_num [hcard] at hdvd

#print axioms affine_commutator_translation_invariant
#print axioms card_dvd_of_distinct_center_affine_invariant
#print axioms distinct_center_affine_classification
#print axioms no_thirteen_element_distinct_center_affine_invariant

end D5.S3.ArithUnits.CyclicPlaneAffineCommutator
