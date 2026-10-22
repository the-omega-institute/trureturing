/- GID: D5/S3/VertexAlgebra/SourceReconstruction/CurrentRecurrences
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceReconstruction/CurrentRecurrences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite original current insertion and charged commutation recurrences. -/

import D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockOriginalMixedIterate LatticeHalfFockFirstDescendant
open LatticeHalfFockAllStateCurrentCommutator OscillatorWords
open LatticeActualStateFieldCalculus MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

theorem negative_binomial (degree offset : ℕ) :
    (-1 : ℂ) ^ offset * Ring.choose (-(degree : ℂ) - 1) offset =
      ((degree + offset).choose degree : ℂ) := by
  rw [show -(degree : ℂ) - 1 = -((degree : ℂ) + 1) by ring, Ring.choose_neg]
  simp only [Units.smul_def, Int.cast_negOnePow_natCast, zsmul_eq_mul]
  rw [show (degree : ℂ) + 1 + offset - 1 = ((degree + offset : ℕ) : ℂ) by
    push_cast; ring, Ring.choose_natCast, ← mul_assoc, ← pow_add]
  simp only [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact_mod_cast (Nat.choose_symm_add (a := degree) (b := offset)).symm

theorem negative_integer_binomial (degree offset : ℕ) :
    (-1 : ℂ) ^ offset * ((Ring.choose (-(degree : ℤ) - 1) offset : ℤ) : ℂ) =
      ((degree + offset).choose degree : ℂ) := by
  change (-1 : ℂ) ^ offset * (Int.castRingHom ℂ)
    (Ring.choose (-(degree : ℤ) - 1) offset) = _
  rw [Ring.map_choose]
  simpa using negative_binomial degree offset

theorem descendant_phase (degree : ℕ) :
    (-1 : ℂ) ^ (-(degree : ℤ) - 1) = -((-1 : ℂ) ^ degree) := by
  rw [show -(degree : ℤ) - 1 = -((degree : ℤ) + 1) by omega,
    zpow_neg, zpow_add₀ (by norm_num), zpow_natCast]
  simp
  rw [← inv_pow]
  norm_num

def insertionFirst (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) (offset : ℕ) : Carrier D :=
  ((unitCurrent D colour)[[-(degree : ℤ) - 1 - offset]])
    (mu D source (mode + offset) target)

def insertionSecond (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) (offset : ℕ) : Carrier D :=
  mu D source (mode - degree - 1 - offset)
    (((unitCurrent D colour)[[(offset : ℤ)]]) target)

theorem insertionFirst_finite (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) :
    Function.HasFiniteSupport (insertionFirst D colour degree mode source target) := by
  classical
  let lower := ((HahnModule.of ℂ).symm (Y D source target)).order
  apply (Finset.range ((-lower - mode).toNat + 1)).finite_toSet.subset
  intro offset nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  have zero : mu D source (mode + offset) target = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    change -((mode + offset : ℤ)) - 1 < lower
    omega
  exact nonzero (by simp [insertionFirst, zero])

theorem insertionSecond_finite (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) :
    Function.HasFiniteSupport (insertionSecond D colour degree mode source target) := by
  apply (Finset.range (vectorFrequencyBound D target + 1)).finite_toSet.subset
  intro offset nonzero
  apply sourceCurrent_nat_support D (Pi.single colour 1) target
  intro zero
  exact nonzero (by simp [insertionSecond, unitCurrent, zero, mu])

theorem source_insertion (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) :
    mu D (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) source) mode target =
      ∑ᶠ offset : ℕ, ((degree + offset).choose degree : ℂ) •
        (insertionFirst D colour degree mode source target offset +
          (-1 : ℂ) ^ degree • insertionSecond D colour degree mode source target offset) := by
  have original := stateField_iterate D
    (originalFirstDescendant D (Pi.single colour 1) 0) source target (-(degree : ℤ) - 1) mode
  change _ ∧ _ ∧ mu D (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) source) mode target = _
    at original
  have finiteFirst : Function.HasFiniteSupport (fun offset : ℕ =>
      ((degree + offset).choose degree : ℂ) •
        insertionFirst D colour degree mode source target offset) :=
    Function.HasFiniteSupport.smul_right
    (fun offset : ℕ => ((degree + offset).choose degree : ℂ))
    (insertionFirst_finite D colour degree mode source target)
  have finiteSecond : Function.HasFiniteSupport (fun offset : ℕ =>
      ((degree + offset).choose degree : ℂ) •
        insertionSecond D colour degree mode source target offset) :=
    Function.HasFiniteSupport.smul_right
    (fun offset : ℕ => ((degree + offset).choose degree : ℂ))
    (insertionSecond_finite D colour degree mode source target)
  have normalized := original.2.2
  simp only [negative_integer_binomial, descendant_phase, neg_smul, sub_neg_eq_add] at normalized
  have reorder (offset : ℕ) : -(degree : ℤ) - 1 + mode - offset =
      mode - degree - 1 - offset := by omega
  simp_rw [reorder] at normalized
  change _ = (∑ᶠ offset : ℕ, ((degree + offset).choose degree : ℂ) •
      insertionFirst D colour degree mode source target offset) +
    (-1 : ℂ) ^ degree • (∑ᶠ offset : ℕ, ((degree + offset).choose degree : ℂ) •
      insertionSecond D colour degree mode source target offset) at normalized
  have finiteScaled : Function.HasFiniteSupport (fun offset : ℕ => (-1 : ℂ) ^ degree •
      (((degree + offset).choose degree : ℂ) •
        insertionSecond D colour degree mode source target offset)) :=
    Function.HasFiniteSupport.smul_right (fun _ : ℕ => (-1 : ℂ) ^ degree) finiteSecond
  rw [normalized, smul_finsum' _ finiteSecond,
    ← finsum_add_distrib finiteFirst finiteScaled]
  apply finsum_congr
  intro offset
  rw [smul_add, smul_comm]

theorem ground_nonnegative_current (D : LatticeData) (colour : Fin D.rank)
    (charge : Charge D) (offset : ℕ) :
    ((unitCurrent D colour)[[(offset : ℤ)]]) (Finsupp.single charge 1) =
      if offset = 0 then (bilinear D (unitCharge D colour) charge : ℂ) •
        Finsupp.single charge 1 else 0 := by
  rw [unitCurrent_mode, neutralMode_single]
  by_cases zero : offset = 0
  · subst offset
    simp [neutralPolynomialMode]
  · simp [neutralPolynomialMode, zero, show ¬ (offset : ℤ) < 0 by omega]

theorem source_charged_commutation (D : LatticeData) (colour : Fin D.rank)
    (charge : Charge D) (degree : ℕ) (mode : ℤ) (target : Carrier D) :
    mu D (Finsupp.single charge 1) mode
        (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) target) =
      ((unitCurrent D colour)[[-(degree : ℤ) - 1]])
        (mu D (Finsupp.single charge 1) mode target) -
      (bilinear D (unitCharge D colour) charge : ℂ) •
        mu D (Finsupp.single charge 1) (mode - degree - 1) target := by
  have commutator := mode_commutator D
    (originalFirstDescendant D (Pi.single colour 1) 0) (Finsupp.single charge 1)
    (-(degree : ℤ) - 1) mode
  have collapsed : (∑ᶠ offset : ℕ, commutatorTerm D
      (originalFirstDescendant D (Pi.single colour 1) 0) (Finsupp.single charge 1)
      (-(degree : ℤ) - 1) mode offset) =
      (bilinear D (unitCharge D colour) charge : ℂ) •
        ((Y D (Finsupp.single charge 1))[[mode - degree - 1]]) := by
    rw [finsum_eq_single _ 0]
    · change _ • ((Y D (((unitCurrent D colour)[[(0 : ℤ)]])
        (Finsupp.single charge 1)))[[_]]) = _
      have groundZero : ((unitCurrent D colour)[[(0 : ℤ)]]) (Finsupp.single charge 1) =
          (bilinear D (unitCharge D colour) charge : ℂ) • Finsupp.single charge 1 := by
        simpa using ground_nonnegative_current D colour charge 0
      rw [groundZero]
      simp [StateFieldResidueReconstruction.integerBinomial,
        show -(degree : ℤ) - 1 + mode - 0 = mode - degree - 1 by omega]
    · intro offset different
      unfold commutatorTerm
      change _ • ((Y D (((unitCurrent D colour)[[(offset : ℤ)]])
        (Finsupp.single charge 1)))[[_]]) = 0
      simp [ground_nonnegative_current, different]
  rw [collapsed] at commutator
  have applied := LinearMap.congr_fun commutator target
  change ((unitCurrent D colour)[[-(degree : ℤ) - 1]])
      (mu D (Finsupp.single charge 1) mode target) -
      mu D (Finsupp.single charge 1) mode
        (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) target) = _ at applied
  have rearranged := sub_eq_iff_eq_add.mp applied
  apply eq_sub_iff_add_eq.mpr
  simpa only [LinearMap.smul_apply, mu, add_comm] using rearranged.symm

end
end D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences
