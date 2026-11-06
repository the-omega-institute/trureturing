/- GID: D5/S3/ArithUnits/AffineGroupCommutatorRigidity
   generality: G
   mirror-B: D5/B/S3/ArithUnits/AffineGroupCommutatorRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct fixed centers in a prime-field affine action produce a
   translation commutator and cardinality rigidity. -/

import D5.S3.ArithUnits.TranslationInvariantLowMoments

/-! The affine commutator is a translation in every prime residue field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.AffineGroupCommutatorRigidity

open D5.S3.ArithUnits.TranslationInvariantLowMoments

def centeredAffine {p : ℕ} (multiplier center x : ZMod p) : ZMod p :=
  center + multiplier * (x - center)

def commutatorShift {p : ℕ} (a b c d : ZMod p) : ZMod p :=
  (a - 1) * (b - 1) * (c - d)

/-- The two centered affine compositions differ by the affine-group commutator
translation `(a - 1) * (b - 1) * (c - d)`. -/
theorem centeredAffine_commutator_formula
    {p : ℕ} (a b c d x : ZMod p) :
    centeredAffine a c (centeredAffine b d x) =
      centeredAffine b d (centeredAffine a c x) + commutatorShift a b c d := by
  dsimp [centeredAffine, commutatorShift]
  ring

/-- Over a prime residue field, the centered affine maps commute exactly in the
degenerate cases: a trivial multiplier, or equal centers. -/
theorem commutatorShift_eq_zero_iff
    {p : ℕ} [Fact p.Prime] (a b c d : ZMod p) :
    commutatorShift a b c d = 0 ↔ a = 1 ∨ b = 1 ∨ c = d := by
  simp [commutatorShift, sub_eq_zero, mul_eq_zero] <;> tauto

/-- A support invariant under both centered affine maps is invariant under their
translation commutator. -/
theorem affine_commutator_translation_invariant
    {p : ℕ} (D : Finset (ZMod p)) (a b c d : ZMod p)
    (hA : D.image (centeredAffine a c) = D)
    (hB : D.image (centeredAffine b d) = D) :
    D.image (fun x => x + commutatorShift a b c d) = D := by
  have hfg : D.image (fun x => centeredAffine a c (centeredAffine b d x)) = D := by
    calc
      D.image (fun x => centeredAffine a c (centeredAffine b d x)) =
          (D.image (centeredAffine b d)).image (centeredAffine a c) := by
        simp only [Finset.image_image, Function.comp_def]
      _ = D.image (centeredAffine a c) := by rw [hB]
      _ = D := hA
  have hgf : D.image (fun x => centeredAffine b d (centeredAffine a c x)) = D := by
    calc
      D.image (fun x => centeredAffine b d (centeredAffine a c x)) =
          (D.image (centeredAffine a c)).image (centeredAffine b d) := by
        simp only [Finset.image_image, Function.comp_def]
      _ = D.image (centeredAffine b d) := by rw [hA]
      _ = D := hB
  have htranslate :
      (D.image (fun x => centeredAffine b d (centeredAffine a c x))).image
          (fun y => y + commutatorShift a b c d) =
        D.image (fun x => centeredAffine a c (centeredAffine b d x)) := by
    simp only [Finset.image_image, Function.comp_def]
    apply Finset.image_congr
    intro x hx
    exact (centeredAffine_commutator_formula a b c d x).symm
  calc
    D.image (fun x => x + commutatorShift a b c d) =
        (D.image (fun x => centeredAffine b d (centeredAffine a c x))).image
          (fun y => y + commutatorShift a b c d) := by rw [hgf]
    _ = D.image (fun x => centeredAffine a c (centeredAffine b d x)) := htranslate
    _ = D := hfg

/-- If both multipliers are nontrivial and the centers differ, the commutator
translation is nonzero. -/
theorem commutatorShift_ne_zero
    {p : ℕ} [Fact p.Prime] (a b c d : ZMod p)
    (ha : a ≠ 1) (hb : b ≠ 1) (hcd : c ≠ d) :
    commutatorShift a b c d ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb))
    (sub_ne_zero.mpr hcd)

/-- The translation commutator forces the support cardinality to be divisible by
the field characteristic. This is the orbit/cardinality consequence of the
affine-group commutator. -/
theorem card_dvd_of_nontrivial_distinct_center_affine_invariant
    {p : ℕ} [Fact p.Prime] (D : Finset (ZMod p)) (a b c d : ZMod p)
    (hA : D.image (centeredAffine a c) = D)
    (hB : D.image (centeredAffine b d) = D)
    (ha : a ≠ 1) (hb : b ≠ 1) (hcd : c ≠ d) :
    p ∣ D.card := by
  classical
  have hshift := commutatorShift_ne_zero a b c d ha hb hcd
  have htrans := affine_commutator_translation_invariant D a b c d hA hB
  have hp : Nat.Prime p := Fact.out
  have hsum := power_sum_eq_zero_of_add_invariant D
    (commutatorShift a b c d) 0 hshift
    (by
      rw [Subsingleton.elim (ZMod.decidableEq p) (Classical.decEq (ZMod p))] at htrans
      exact htrans)
    (by simpa using hp.one_lt)
  have hcast : (D.card : ZMod p) = 0 := by
    simpa using hsum
  exact (CharP.cast_eq_zero_iff (ZMod p) p D.card).mp hcast

/-- A nontrivial distinct-center affine pair leaves only the empty and full
supports in the prime residue field. -/
theorem distinct_center_affine_classification
    {p : ℕ} [Fact p.Prime] (D : Finset (ZMod p)) (a b c d : ZMod p)
    (hA : D.image (centeredAffine a c) = D)
    (hB : D.image (centeredAffine b d) = D)
    (ha : a ≠ 1) (hb : b ≠ 1) (hcd : c ≠ d) :
    D = ∅ ∨ D = Finset.univ := by
  have hdvd := card_dvd_of_nontrivial_distinct_center_affine_invariant
    D a b c d hA hB ha hb hcd
  have hle : D.card ≤ p := by
    simpa [ZMod.card] using (Finset.card_le_univ D)
  obtain ⟨k, hk⟩ := hdvd
  have hp : Nat.Prime p := Fact.out
  have hk_le : p * k ≤ p * 1 := by simpa [hk] using hle
  have hk_one : k ≤ 1 := Nat.le_of_mul_le_mul_left hk_le hp.pos
  rcases Nat.eq_zero_or_pos k with hk_zero | hk_pos
  · left
    exact Finset.card_eq_zero.mp (hk.trans (by simp [hk_zero]))
  · have hk_eq : k = 1 := by omega
    right
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ D)
    simp [hk, hk_eq, ZMod.card]

/-- Any prescribed cardinality not divisible by `p` is excluded by the same
affine commutator hypotheses. -/
theorem no_card_not_dvd_of_nontrivial_distinct_center_affine_invariant
    {p n : ℕ} [Fact p.Prime] (D : Finset (ZMod p)) (a b c d : ZMod p)
    (hcard : D.card = n)
    (hA : D.image (centeredAffine a c) = D)
    (hB : D.image (centeredAffine b d) = D)
    (ha : a ≠ 1) (hb : b ≠ 1) (hcd : c ≠ d)
    (hnot : ¬ p ∣ n) : False := by
  apply hnot
  rw [← hcard]
  exact card_dvd_of_nontrivial_distinct_center_affine_invariant
    D a b c d hA hB ha hb hcd

#print axioms centeredAffine_commutator_formula
#print axioms affine_commutator_translation_invariant
#print axioms card_dvd_of_nontrivial_distinct_center_affine_invariant
#print axioms distinct_center_affine_classification
#print axioms no_card_not_dvd_of_nontrivial_distinct_center_affine_invariant

end D5.S3.ArithUnits.AffineGroupCommutatorRigidity
