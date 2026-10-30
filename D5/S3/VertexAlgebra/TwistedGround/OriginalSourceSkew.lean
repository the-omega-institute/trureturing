/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalSourceSkew
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalSourceSkew
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite skew exchange of the original two twisted inputs on the original fixed source. -/

import D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

/-! Classical finite contragredient skew calculus on the literal original carriers. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint
open CorrectedInversion ActualOddGradeOrthogonality
open HalfFock.ActualEnergyCovariance
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeHalfFockFiniteCorrection (sourceWeight)
open SourceBPZ.OriginalSourcePairing SourceBPZ.SourcePairingLaws
open private originalL1 original_l1_grade original_l1_fixed T
  homogeneous_coefficient ambientCoefficient liftGrade
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private actual_homogeneous_transpose
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
open private theta_grade from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
open private conformal_polynomial_homogeneous conformal_polynomial_lowering
  negative_support basis_parity from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

private theorem projection_homogeneous (D : LatticeData) (d n : ℤ)
    (a : Carrier D) (ha : a ∈ grade D d) :
    gradeProjection D n a = if d = n then a else 0 := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext i
  rw [gradeProjection_coeff]
  by_cases hd : d = n
  · subst n
    by_cases hi : energy D i = d
    · simp [hi]
    · have hz : carrierCoeffEquiv D a i = 0 := by
        change (a i.1).coeff i.2 = 0
        exact (mem_grade_iff D d a).mp ha i hi
      simp [hi, hz]
  · by_cases hi : energy D i = n
    · have hz : carrierCoeffEquiv D a i = 0 := by
        change (a i.1).coeff i.2 = 0
        exact (mem_grade_iff D d a).mp ha i (by omega)
      simp [hi, hd, hz]
    · simp [hi, hd]

private theorem theta_projection (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℤ) (a : Carrier D) :
    theta D (gradeProjection D n a) = gradeProjection D n (theta D a) := by
  classical
  conv_lhs => arg 2; rw [← sum_gradeProjections D a]
  conv_rhs => arg 2; rw [← sum_gradeProjections D a]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [projection_homogeneous D d n _ (gradeProjection_mem D d a),
    projection_homogeneous D d n _
      (theta_grade D hu d _ (gradeProjection_mem D d a))]
  split_ifs <;> simp

private def gradeOrderEquiv (D : LatticeData) (d : ℤ) :
    FixedGradedDuality.FixedGrade D d ≃ₗ[ℂ] fixedGrade D d where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def gradeDualOrderEquiv (D : LatticeData) (d : ℤ) :
    Module.Dual ℂ (FixedGradedDuality.FixedGrade D d) ≃ₗ[ℂ]
      Module.Dual ℂ (fixedGrade D d) where
  toFun f := f.comp (gradeOrderEquiv D d).symm.toLinearMap
  invFun f := f.comp (gradeOrderEquiv D d).toLinearMap
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem source_orthogonal (D : LatticeData) (m n : ℤ)
    (x y : Carrier D) (hx : x ∈ grade D m) (hy : y ∈ grade D n)
    (hmn : m ≠ n) : sourcePairing D x y = 0 :=
  sourcePairing_grade D m n hmn x y hx hy

/-- The concrete original source-pairing identification, with only the order
of the two grade/fixed subtypes changed in the supplied restricted dual. -/
def sourcePairingDualEquiv (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    FixedCarrier D ≃ₗ[ℂ] FixedRestrictedDual D :=
  (FixedGradedDuality.fixedRestrictedDualEquiv D (sourcePairing D)
    (sourcePairing_nondegenerate D hu) (theta_projection D hu)
    (sourcePairing_theta D) (source_orthogonal D) hD).trans
      (DirectSum.congrLinearEquiv (gradeDualOrderEquiv D))

private theorem sourcePairingDualEquiv_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (x : FixedCarrier D) (d : ℤ) (a : fixedGrade D d) :
    sourcePairingDualEquiv D hu hD x d a = sourcePairing D x.val a.val := by
  let e := FixedGradedDuality.fixedEnergyDecomposition D (theta_projection D hu)
  let b := (gradeOrderEquiv D d).symm a
  have single : e b.val = DirectSum.of (FixedGradedDuality.FixedGrade D) d b := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact (DirectSum.coeLinearMap_of (FixedGradedDuality.fixedGradeSubmodule D) d b).symm
  have ev := FixedGradedDuality.fixedRestrictedDualEquiv_ambient_evaluation D
    (sourcePairing D) (sourcePairing_nondegenerate D hu) (theta_projection D hu)
    (sourcePairing_theta D) (source_orthogonal D) hD x b.val
  simp only [FixedGradedDuality.fixedRestrictedDualEvaluation,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at ev
  rw [show FixedGradedDuality.fixedEnergyDecomposition D (theta_projection D hu) b.val =
    DirectSum.of (FixedGradedDuality.FixedGrade D) d b from single] at ev
  have eval_single : ((DFinsupp.lsum ℂ) (fun h =>
      (FixedGradedDuality.fixedRestrictedDualEquiv D (sourcePairing D)
        (sourcePairing_nondegenerate D hu) (theta_projection D hu)
        (sourcePairing_theta D) (source_orthogonal D) hD x) h))
        (DirectSum.of (FixedGradedDuality.FixedGrade D) d b) =
      (FixedGradedDuality.fixedRestrictedDualEquiv D (sourcePairing D)
        (sourcePairing_nondegenerate D hu) (theta_projection D hu)
        (sourcePairing_theta D) (source_orthogonal D) hD x) d b :=
    DFinsupp.lsum_single ℂ _ d b
  exact eval_single.symm.trans ev

/-- The two-twisted-input coefficient on the literal original fixed source. -/
def originalCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m : ℤ) :
    paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ] FixedCarrier D :=
  (normalizedCoefficient D hu m).compr₂
    (sourcePairingDualEquiv D hu hD).symm.toLinearMap

private def loweredTest (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) (a : fixedGrade D d) (j : ℕ) : fixedGrade D (d-(j : ℤ)) :=
  ⟨(originalL1 D ^ j) a.val,
    original_l1_grade D hu d a.val a.property.1 j,
    (mem_fixedSpace D _).mpr (original_l1_fixed D hu a.val a.property.2 j)⟩

private def testCutoff (D : LatticeData) (a : Carrier D) : ℕ :=
  a.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a c)) + 1

private theorem source_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (j : ℕ) (hj : testCutoff D a ≤ j) :
    (originalL1 D ^ j) a = 0 := by
  have killed : (originalL1 D ^ testCutoff D a) a = 0 :=
    SourceMobius.actual_sugawara_one_bound D hu a
  rw [show j = (j-testCutoff D a)+testCutoff D a by omega,
    pow_add, Module.End.mul_apply, killed, map_zero]

private theorem source_stress_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (x a : Carrier D) :
    sourcePairing D (LatticeSugawaraConformal.translation D x) a =
      sourcePairing D x (originalL1 D a) := by
  classical
  let H := (LatticeSugawaraCurrents.gramComplex D)⁻¹
  let w := LatticeActualConformalState.omega D H
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  have grade_w : w ∈ grade D 2 := by
    apply (actualL0_eigen_iff_grade D H hHG hGH 2 w).mp
    simpa [w, LatticeActualConformalState.omega, bilinear] using
      LatticeSugawaraConformal.sugawaraMode_weighted_homogeneous D H hHG hGH
        0 (LatticeActualConformalState.conformalPolynomial D H) 2
        (conformal_polynomial_homogeneous D H)
  have killed : originalL1 D w = 0 := by
    rw [show originalL1 D w = sugawaraMode D H 1
      (Finsupp.single 0 (LatticeActualConformalState.conformalPolynomial D H)) from rfl,
      SourceMobius.sugawara_one_single D H hHG hGH,
      conformal_polynomial_lowering, Finsupp.single_zero]
  have powers (j : ℕ) (hj : j ≠ 0) : (originalL1 D ^ j) w = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, killed, map_zero]
  have law := SourceBPZ.AllStateTranspose.sourcePairing_allState D hu 2 0 w grade_w x a
  rw [Finset.sum_eq_single 0] at law
  · have modes0 := LatticeActualConformalState.omega_modes D H (-1)
    have modes2 := LatticeActualConformalState.omega_modes D H 1
    norm_num only at modes0 modes2
    norm_num only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
      inv_one, one_mul, Nat.cast_zero] at law
    rw [modes0, LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation
      D H hHG hGH, modes2] at law
    exact law
  · intro j hj hne
    rw [powers j hne]
    simp
  · simp

private theorem source_power_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (j : ℕ) (x : FixedCarrier D) (a : Carrier D) :
    sourcePairing D ((fixedTranslation D ^ j) x).val a =
      sourcePairing D x.val ((originalL1 D ^ j) a) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    change sourcePairing D (LatticeSugawaraConformal.translation D
      ((fixedTranslation D ^ j) x).val) a = _
    rw [source_stress_adjoint D hu, ih, pow_succ, Module.End.mul_apply]

private def vectorCutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (m : ℤ) (u v : paritySpace D hu (-1)) : ℕ :=
  ((ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ) +
    (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ) + 3 + 1 - m).toNat

private theorem coefficient_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) (u v : paritySpace D hu (-1)) (j : ℕ)
    (hj : vectorCutoff D hu m u v ≤ j) :
    normalizedCoefficient D hu (m+(j : ℤ)) v u = 0 := by
  apply normalizedCoefficient_truncation D hu hD
  dsimp [vectorCutoff] at hj
  have hb := Int.self_le_toNat ((ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ) +
    (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ) + 3 + 1 - m)
  omega

private theorem skew_family_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u)) := by
  classical
  apply (Finset.range (vectorCutoff D hu m u v)).finite_toSet.subset
  intro j hj
  by_contra hout
  have tail := coefficient_tail D hu hD m u v j (by simpa using hout)
  apply hj
  simp [originalCoefficient, tail]

private theorem transpose_at_cutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (d s : ℤ) (a : Carrier D) (ha : a ∈ grade D d)
    (x y : ActualTensor D hu) (R : ℕ) (hR : testCutoff D a ≤ R) :
    actualForm D hu x ((correctedField D hu a).coeff (2*s) y) =
      ∑ j ∈ Finset.range R, (((-1 : ℂ)^d)/(j.factorial : ℂ)) *
        actualForm D hu y ((correctedField D hu ((originalL1 D ^ j) a)).coeff
          (-2*s-4*d+2*(j : ℤ)) x) := by
  classical
  rw [(ActualPairingSymmetry.actualForm_symmetric D hu).eq,
    actual_homogeneous_transpose D hu d (2*s) a ha y x]
  simp only [neg_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra outside
  have tail := source_tail D hu a j
    (hR.trans (by simpa using outside))
  apply hj
  simp [tail]

private theorem exchange_phase (H K : ℕ) (m d : ℤ) (p q j : ℕ)
    (hd : d = (H : ℤ) + (K : ℤ) - m - 1) :
    let s : ℤ := m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
    let t : ℤ := m+(j : ℤ)+1-(q : ℤ)-2*(K : ℤ)+(p : ℤ)
    (((-1 : ℂ)^((H : ℤ)+s))/((p.factorial : ℂ)*(q.factorial : ℂ))) *
      (((-1 : ℂ)^d)/(j.factorial : ℂ)) =
    (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) *
      (((-1 : ℂ)^((K : ℤ)+t))/((q.factorial : ℂ)*(p.factorial : ℂ))) := by
  dsimp only
  have sign : (-1 : ℂ)^((H : ℤ)+(m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ))) *
      (-1 : ℂ)^d = (-1 : ℂ)^(m+(j : ℤ)+1) *
      (-1 : ℂ)^((K : ℤ)+(m+(j : ℤ)+1-(q : ℤ)-2*(K : ℤ)+(p : ℤ))) := by
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    have parity : ((H : ℤ)+(m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ))+d) % 2 =
        (m+(j : ℤ)+1+((K : ℤ)+(m+(j : ℤ)+1-(q : ℤ)-2*(K : ℤ)+(p : ℤ)))) % 2 := by
      omega
    simp only [neg_one_zpow_eq_ite, ← Int.not_odd_iff_even, Int.odd_iff, parity]
  simp only [div_eq_mul_inv, mul_inv_rev]
  linear_combination (p.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ *
    (j.factorial : ℂ)⁻¹ * sign

private theorem coefficient_exchange_homogeneous
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (H K : ℕ) (m d : ℤ) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (a : fixedGrade D d) (R : ℕ) (hR : testCutoff D a.val ≤ R) :
    normalizedCoefficient D hu m u v d a =
      ∑ j ∈ Finset.range R,
        (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) *
          normalizedCoefficient D hu (m+(j : ℤ)) v u (d-(j : ℤ))
            (loweredTest D hu d a j) := by
  classical
  by_cases hd : d = (H : ℤ)+(K : ℤ)-m-1
  · rw [normalizedCoefficient_pairing D hu h24 H K m u v huH hvK d a]
    simp_rw [transpose_at_cutoff D hu d _ a.val a.property.1 _ _ R hR,
      Finset.mul_sum]
    conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    rw [normalizedCoefficient_pairing D hu h24 K H (m+(j : ℤ)) v u hvK huH
      (d-(j : ℤ)) (loweredTest D hu d a j)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro p hp
    have index : -2*(m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ))-4*d+2*(j : ℤ) =
        2*(m+(j : ℤ)+1-(q : ℤ)-2*(K : ℤ)+(p : ℤ)) := by rw [hd]; ring
    change _ = _ * (_ * actualForm D hu _
      ((correctedField D hu ((originalL1 D ^ j) a.val)).coeff _ _))
    rw [index, ← mul_assoc, exchange_phase H K m d p q j hd, mul_assoc]
  · have off (L J : ℕ) (n e : ℤ) (x y : paritySpace D hu (-1))
        (hx : actualTensorL0 D hu x.val = (L : ℂ) • x.val)
        (hy : actualTensorL0 D hu y.val = (J : ℂ) • y.val)
        (b : fixedGrade D e) (he : e ≠ (L : ℤ)+(J : ℤ)-n-1) :
        normalizedCoefficient D hu n x y e b = 0 := by
      change ambientCoefficient D hu n x.val y.val e b = 0
      rw [homogeneous_coefficient D hu h24 L J n x.val y.val hx hy]
      simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply, Ne.symm he]
    rw [off H K m d u v huH hvK a hd]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [off K H (m+(j : ℤ)) (d-(j : ℤ)) v u hvK huH
      (loweredTest D hu d a j) (by omega), mul_zero]

private def coefficientReadout (D : LatticeData) (hu : IsUnit D.G.det)
    (m d : ℤ) (a : fixedGrade D d) :
    ActualTensor D hu →ₗ[ℂ] ActualTensor D hu →ₗ[ℂ] ℂ :=
  (ambientCoefficient D hu m).compr₂
    { toFun := fun f => f d a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem coefficientReadout_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (m d : ℤ) (a : fixedGrade D d) (x y : ActualTensor D hu) :
    coefficientReadout D hu m d a x y = ambientCoefficient D hu m x y d a := rfl

private theorem coefficient_exchange (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (m d : ℤ) (u v : paritySpace D hu (-1))
    (a : fixedGrade D d) (R : ℕ) (hR : testCutoff D a.val ≤ R) :
    normalizedCoefficient D hu m u v d a =
      ∑ j ∈ Finset.range R,
        (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) *
          normalizedCoefficient D hu (m+(j : ℤ)) v u (d-(j : ℤ))
            (loweredTest D hu d a j) := by
  classical
  change ambientCoefficient D hu m u.val v.val d a =
    ∑ j ∈ Finset.range R,
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) *
        ambientCoefficient D hu (m+(j : ℤ)) v.val u.val (d-(j : ℤ))
          (loweredTest D hu d a j)
  let F := coefficientReadout D hu m d a -
    ∑ j ∈ Finset.range R,
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (coefficientReadout D hu (m+(j : ℤ)) (d-(j : ℤ))
          (loweredTest D hu d a j)).flip
  suffices hz : F u.val v.val = 0 by
    simpa only [F, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, coefficientReadout_apply,
      smul_eq_mul] using sub_eq_zero.mp hz
  let b := actualAmbientBasis D hu
  rw [← b.linearCombination_repr u.val, ← b.linearCombination_repr v.val]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  apply smul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro i hi
  apply smul_eq_zero.mpr
  right
  have hiOdd := negative_support D hu u i hi
  have hkOdd := negative_support D hu v k hk
  let H := (oddWeight D i.1+3)/2
  let K := (oddWeight D k.1+3)/2
  have hiH : actualTensorL0 D hu (b i) = (H : ℂ) • b i := by
    rw [actual_basis_eigenvalue, h24]
    have he : oddWeight D i.1+3 = 2*H := by dsimp [H]; omega
    congr 1
    have hc : (oddWeight D i.1 : ℂ)+3 = 2*(H : ℂ) := by exact_mod_cast he
    linear_combination hc / 2
  have hkK : actualTensorL0 D hu (b k) = (K : ℂ) • b k := by
    rw [actual_basis_eigenvalue, h24]
    have he : oddWeight D k.1+3 = 2*K := by dsimp [K]; omega
    congr 1
    have hc : (oddWeight D k.1 : ℂ)+3 = 2*(K : ℂ) := by exact_mod_cast he
    linear_combination hc / 2
  have parity (l : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu))
      (hl : oddWeight D l.1 % 2 = 1) : b l ∈ paritySpace D hu (-1) := by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rw [basis_parity, neg_one_pow_eq_pow_mod_two, hl, pow_one]
  let x : paritySpace D hu (-1) := ⟨b i, parity i hiOdd⟩
  let y : paritySpace D hu (-1) := ⟨b k, parity k hkOdd⟩
  have exchange := coefficient_exchange_homogeneous D hu h24 H K m d x y
    hiH hkK a R hR
  change coefficientReadout D hu m d a (b i) (b k) -
    (∑ j ∈ Finset.range R,
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (coefficientReadout D hu (m+(j : ℤ)) (d-(j : ℤ))
          (loweredTest D hu d a j)).flip) (b i) (b k) = 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.flip_apply,
    coefficientReadout_apply, smul_eq_mul]
  exact sub_eq_zero.mpr exchange

/-
proof_shape: originalCoefficient_skew: content
admission_basis: escape-witness
escape_witness: coefficient_exchange_homogeneous transposes each ordered
kernel summand once and establishes the signed mode permutation and finite
sum exchange; coefficient_exchange consumes it on the actual finite basis.
The source-pairing identification and stress transport are consumed plumbing.
-/
/-- Finite skew exchange of arbitrary original negative-parity twisted inputs,
with every integer standard mode, on the original theta-fixed source. -/
theorem originalCoefficient_skew (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h24 : D.rank = 24) (m : ℤ) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u)) ∧
    originalCoefficient D hu hD m u v = ∑ᶠ j : ℕ,
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u) := by
  classical
  have finite := skew_family_finite D hu hD m u v
  refine ⟨finite, ?_⟩
  let E := sourcePairingDualEquiv D hu hD
  have equiv_coefficient (n : ℤ) (x y : paritySpace D hu (-1)) :
      E (originalCoefficient D hu hD n x y) = normalizedCoefficient D hu n x y :=
    E.apply_symm_apply _
  let f := fun j : ℕ =>
    (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
      (fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u)
  apply E.injective
  apply DFinsupp.ext
  intro d
  apply LinearMap.ext
  intro a
  let R := max (testCutoff D a.val) (vectorCutoff D hu m u v)
  have finite_sum : (∑ᶠ j : ℕ, f j) = ∑ j ∈ Finset.range R, f j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have hjR : R ≤ j := by simpa using outside
    have tail := coefficient_tail D hu hD m u v j ((le_max_right _ _).trans hjR)
    apply hj
    simp [f, originalCoefficient, tail]
  change E (originalCoefficient D hu hD m u v) d a = E (∑ᶠ j : ℕ, f j) d a
  rw [finite_sum, map_sum, equiv_coefficient]
  rw [coefficient_exchange D hu h24 m d u v a R (le_max_left _ _)]
  simp only [DirectSum.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [f]
  rw [map_smul]
  change _ = _ * sourcePairingDualEquiv D hu hD
    ((fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u)) d a
  rw [sourcePairingDualEquiv_apply, source_power_adjoint D hu]
  exact congrArg (fun z : ℂ =>
    (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) * z)
      (((congrArg (fun z : FixedRestrictedDual D => z (d-(j : ℤ))
        (loweredTest D hu d a j)) (equiv_coefficient (m+(j : ℤ)) v u)).symm).trans
        (sourcePairingDualEquiv_apply D hu hD
          (originalCoefficient D hu hD (m+(j : ℤ)) v u) (d-(j : ℤ))
            (loweredTest D hu d a j)))

#print axioms originalCoefficient_skew

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
