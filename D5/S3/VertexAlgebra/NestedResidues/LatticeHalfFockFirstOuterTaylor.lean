/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual current/source fused residues of the original Laurent numerator. -/

import D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation

/-! The current/source residue retains the original surviving labels A,B.
Its two complete orders are transported to the binary Laurent evaluator.
The original numerator and every signed exponent remain unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation LatticeHalfFockClearedTaylorReadout
open BinaryLaurentEvaluation LatticeHalfFockABLocalResidue
open LatticeHalfFockSliceQuotient
open UniformGradedLocalCorrelator LatticeGeneratingFieldLocality
open LatticeHalfFockChargedTensorCoefficients LatticeSugawaraCurrents
open LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization (remainingVariable)
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.LocalResidueCurrying
open scoped BigOperators VertexOperator
noncomputable section

private abbrev JAField := CoefficientField ℂ (0 : Fin 3)
private def jaLabels : Remaining (0 : Fin 3) ≃ Remaining (1 : Fin 3) :=
  (finSuccAboveEquiv (0 : Fin 3)).symm.trans (finSuccAboveEquiv (1 : Fin 3))
private def jaExponents : (Remaining (0 : Fin 3) → ℤ) ≃+ BinaryExponent :=
  { toFun := fun e j => e (jaLabels.symm j)
    invFun := fun e j => e (jaLabels j)
    left_inv := by intro e; ext j; simp
    right_inv := by intro e; ext j; simp
    map_add' := by intros; rfl }
private def jaPolynomial : CoefficientPolynomial ℂ (0 : Fin 3) ≃+* BinaryPolynomial :=
  AddMonoidAlgebra.domCongr ℂ ℂ jaExponents
private def jaRename : JAField ≃+* ABField :=
  IsFractionRing.ringEquivOfRingEquiv jaPolynomial
private theorem ja_expansion (reverse : Bool) (F : JAField) :
    coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau reverse) F =
      binaryExpansion reverse (jaRename F) := by
  have maps : coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau reverse) =
      (binaryExpansion reverse).comp jaRename.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := CoefficientPolynomial ℂ (0 : Fin 3))
    intro Q
    induction Q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add P Q hP hQ => simp only [map_add, RingHom.comp_apply] at hP hQ ⊢; rw [hP, hQ]
    | single e c =>
      change coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau reverse)
          (algebraMap _ JAField (AddMonoidAlgebra.single e c)) =
        binaryExpansion reverse (jaRename (algebraMap _ JAField (AddMonoidAlgebra.single e c)))
      rw [jaRename, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      unfold binaryExpansion jaPolynomial coefficientHahn
      rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
      change SupportedFieldWords.FiniteConvolution.scalarPolynomial
          ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents 1 1 0 (currentSourceTau reverse)))
            (AddMonoidAlgebra.single e c)) =
        SupportedFieldWords.FiniteConvolution.scalarPolynomial
          ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents 1 1 1 _))
            ((AddMonoidAlgebra.domCongr ℂ ℂ jaExponents) (AddMonoidAlgebra.single e c)))
      simp only [AddMonoidAlgebra.domCongr_single,
        SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
      apply congrArg (fun g => (HahnSeries.single g c : HahnSeries (Indices 2) ℂ))
      apply congrArg (exponentAddEquiv 2)
      cases reverse <;> ext j <;> fin_cases j <;> rfl
  exact congrArg (fun f : JAField →+* HahnSeries (Indices 2) ℂ => f F) maps

private def jaShift (ell : ℕ) : JAField :=
  algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) JAField
    (AddMonoidAlgebra.single (Pi.single ⟨1, by decide⟩ (-(ell : ℤ))) 1)

private def completeJA (s d : ℤ) (L : ℕ) (R : CommonRational ℂ 3) : JAField :=
  ∑ ell ∈ Finset.range ((L : ℤ) - d).toNat,
    algebraMap ℂ JAField (Ring.choose (-(s : ℂ) / 2) ell) * jaShift ell *
      localResidue ℂ (0 : Fin 3) ⟨1, by decide⟩
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
          ⟨1, by decide⟩ ^ (d + ell) * R)

private theorem ja_shift (reverse : Bool) (ell : ℕ) (F : JAField) (a b : ℤ) :
    (coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau reverse) (jaShift ell * F)).coeff
      (exponents 2 (if reverse then ![b, a] else ![a, b])) =
    (coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau reverse) F).coeff
      (exponents 2 (if reverse then ![b, a + ell] else ![a + ell, b])) := by
  have shift : coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau reverse) (jaShift ell) =
      HahnSeries.single (exponents 2
        (if reverse then ![0, -(ell : ℤ)] else ![-(ell : ℤ), 0])) 1 := by
    unfold jaShift coefficientHahn
    rw [IsFractionRing.lift_algebraMap]
    change SupportedFieldWords.FiniteConvolution.scalarPolynomial
      ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents 1 1 (0 : Fin 3) _))
        (AddMonoidAlgebra.single (Pi.single ⟨1, by decide⟩ (-(ell : ℤ))) 1)) = _
    rw [AddMonoidAlgebra.domCongr_single,
      SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
    apply congrArg (fun g => (HahnSeries.single g (1 : ℂ) : HahnSeries (Indices 2) ℂ))
    apply congrArg (exponentAddEquiv 2)
    have h0 : (finSuccAboveEquiv (0 : Fin 3)) (0 : Fin 2) = ⟨1, by decide⟩ := rfl
    have h1 : (finSuccAboveEquiv (0 : Fin 3)) (1 : Fin 2) = ⟨2, by decide⟩ := rfl
    cases reverse <;> ext j <;> fin_cases j <;>
      simp [currentSourceTau, Equiv.swap_apply_def, h0, h1]
  rw [map_mul, shift, HahnSeries.coeff_single_mul, one_mul]
  congr 1
  change (exponentAddEquiv 2) _ - (exponentAddEquiv 2) _ = (exponentAddEquiv 2) _
  rw [← map_sub]
  apply congrArg (exponentAddEquiv 2)
  cases reverse <;> ext j <;> fin_cases j <;> simp

private theorem ja_orders (reverse : Bool) (s d k l : ℤ) (L : ℕ)
    (R : CommonRational ℂ 3) :
    currentSourceLocalQ reverse s d L k l R =
      binaryModes reverse (jaRename (completeJA s d L R))
        (if reverse then l else k) (if reverse then k else l) := by
  classical
  unfold binaryModes
  rw [← ja_expansion]
  unfold completeJA
  simp only [map_sum, HahnSeries.coeff_sum]
  unfold currentSourceLocalQ
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_mul, map_mul, coefficient_scalar, mul_assoc, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero]
  have shifted := ja_shift reverse ell
    (localResidue ℂ (0 : Fin 3) ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ (d + ell) * R)) (-k - 1) (-l - 1)
  rw [map_mul] at shifted
  have same : coefficientHahn ℂ 2 0 (0 : Fin 3) (currentSourceTau true) =
      coefficientHahn ℂ 1 1 (0 : Fin 3) (currentSourceTau true) := rfl
  cases reverse <;> simpa only [fused_residue_square, same,
    Bool.false_eq_true, ite_false, ite_true,
    show -k - 1 + (ell : ℤ) = -k + ell - 1 by omega] using
      congrArg (fun c : ℂ => Ring.choose (-(s : ℂ) / 2) ell * c) shifted.symm

private theorem variable_power {N : ℕ} (zz : Fin N) (j : Remaining zz) (p : ℤ) :
    algebraMap (CoefficientPolynomial ℂ zz) (CoefficientField ℂ zz)
      (AddMonoidAlgebra.single (Pi.single j p) 1) = remainingVariable ℂ zz j ^ p := by
  let m : Multiplicative (Remaining zz → ℤ) →* CoefficientField ℂ zz :=
    (algebraMap (CoefficientPolynomial ℂ zz) (CoefficientField ℂ zz)).toMonoidHom.comp
      (AddMonoidAlgebra.of ℂ (Remaining zz → ℤ))
  have h := m.map_zpow (Multiplicative.ofAdd (Pi.single j (1 : ℤ))) p
  change algebraMap (CoefficientPolynomial ℂ zz) (CoefficientField ℂ zz)
    (AddMonoidAlgebra.single (p • (Pi.single j (1 : ℤ) : Remaining zz → ℤ)) 1) =
    remainingVariable ℂ zz j ^ p at h
  have index : p • (Pi.single j (1 : ℤ) : Remaining zz → ℤ) = Pi.single j p := by
    ext k
    by_cases hk : k = j <;> simp [hk]
  simpa only [index] using h

private theorem ja_single (e : Remaining (0 : Fin 3) → ℤ) (c : ℂ) :
    jaRename (algebraMap _ JAField (AddMonoidAlgebra.single e c)) =
      algebraMap _ ABField (AddMonoidAlgebra.single (jaExponents e) c) := by
  rw [jaRename, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap BinaryPolynomial ABField
    ((AddMonoidAlgebra.domCongr ℂ ℂ jaExponents) (AddMonoidAlgebra.single e c)) = _
  rw [AddMonoidAlgebra.domCongr_single]

private theorem ja_variable (j : Remaining (0 : Fin 3)) :
    jaRename (remainingVariable ℂ (0 : Fin 3) j) =
      remainingVariable ℂ (1 : Fin 3) (jaLabels j) := by
  rw [remainingVariable, ja_single]
  congr 2
  ext k
  change (Pi.single j (1 : ℤ) : Remaining (0 : Fin 3) → ℤ) (jaLabels.symm k) =
    (Pi.single (jaLabels j) (1 : ℤ) : BinaryExponent) k
  simp only [Pi.single_apply]
  have eqn : jaLabels.symm k = j ↔ k = jaLabels j := by
    constructor <;> intro h
    · rw [← h]; simp
    · rw [h]; simp
  simp only [eqn]

private theorem ja_complex (c : ℂ) :
    jaRename (algebraMap ℂ JAField c) = algebraMap ℂ ABField c := by
  rw [IsScalarTower.algebraMap_apply ℂ (CoefficientPolynomial ℂ (0 : Fin 3)) JAField]
  change jaRename (algebraMap _ JAField (AddMonoidAlgebra.single 0 c)) = _
  rw [ja_single, map_zero]
  rfl

private theorem y_nonzero : y ≠ 0 := by
  change algebraMap BinaryPolynomial ABField
    (AddMonoidAlgebra.single (Pi.single ⟨0, by decide⟩ (1 : ℤ)) 1) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (by simp)

private theorem binary_residue_coeff (F : ABField) (r n : ℤ) (ell : ℕ) :
    completeOuterResidue r n (binaryModes false F) (binaryModes true F) ell =
      (binaryKernel false (r + ell) * binaryExpansion false F).coeff
        (exponents 2 ![-1, -(n - ell) - 1]) -
      (binaryKernel true (r + ell) * binaryExpansion true F).coeff
        (exponents 2 ![-(n - ell) - 1, -1]) := by
  rw [forward_readout, reverse_readout]
  unfold completeOuterResidue
  rw [show r + (ell : ℤ) + (n - ell) = r + n by omega]

private theorem binary_readout_sum {ι : Type*} (S : Finset ι) (F : ι → ABField)
    (s r n : ℤ) (T : ℕ) :
    supportedQReadout s r T n (binaryModes false (∑ j ∈ S, F j))
      (binaryModes true (∑ j ∈ S, F j)) =
    ∑ j ∈ S, supportedQReadout s r T n (binaryModes false (F j)) (binaryModes true (F j)) := by
  classical
  change (∑ ell ∈ Finset.range ((T : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      completeOuterResidue r n (binaryModes false (∑ j ∈ S, F j))
        (binaryModes true (∑ j ∈ S, F j)) ell) =
    ∑ j ∈ S, ∑ ell ∈ Finset.range ((T : ℤ) - r).toNat,
      Ring.choose (-(s : ℂ) / 2) ell *
        completeOuterResidue r n (binaryModes false (F j)) (binaryModes true (F j)) ell
  simp_rw [binary_residue_coeff, map_sum, Finset.mul_sum, HahnSeries.coeff_sum,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_comm

private def fusedExponent (e : Exponent 3) (u : ℕ) : BinaryExponent :=
  fun j => if j.val = 0 then e 0 + e 1 - u else e 2


private theorem fused_monomial_map (e : Exponent 3) (c : ℂ) (u : ℕ) :
    algebraMap BinaryPolynomial ABField (AddMonoidAlgebra.single (fusedExponent e u) c) =
      jaRename (algebraMap _ JAField
        (AddMonoidAlgebra.single (fun j : Remaining (0 : Fin 3) => e j.val) c)) *
        y ^ (e 0 - u) := by
  rw [ja_single]
  change _ = _ * remainingVariable ℂ (1 : Fin 3) ⟨0, by decide⟩ ^ (e 0 - u)
  rw [← variable_power, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
  congr 2
  ext j
  have first : jaLabels.symm ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl
  have last : jaLabels.symm ⟨2, by decide⟩ = ⟨2, by decide⟩ := rfl
  change fusedExponent e u j = jaExponents (fun j : Remaining (0 : Fin 3) => e j.val) j +
    (Pi.single (⟨0, by decide⟩ : Remaining (1 : Fin 3)) (e 0 - u) : BinaryExponent) j
  change fusedExponent e u j = e (jaLabels.symm j).val + _
  rcases j with ⟨j, hj⟩
  fin_cases j
  · change fusedExponent e u ⟨0, by decide⟩ =
      e (jaLabels.symm ⟨0, by decide⟩).val +
        (Pi.single (⟨0, by decide⟩ : Remaining (1 : Fin 3)) (e 0 - u) : BinaryExponent) ⟨0, by decide⟩
    rw [first]
    simp [fusedExponent]
    omega
  · exact (hj rfl).elim
  · change fusedExponent e u ⟨2, by decide⟩ =
      e (jaLabels.symm ⟨2, by decide⟩).val +
        (Pi.single (⟨0, by decide⟩ : Remaining (1 : Fin 3)) (e 0 - u) : BinaryExponent) ⟨2, by decide⟩
    rw [last]
    simp [fusedExponent, show (2 : Fin 3) ≠ 0 by decide]

set_option maxHeartbeats 1600000 in
-- Preserve the complete signed Laurent coefficient telescope.
private theorem ja_monomial_terms (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (d : ℤ) (t ell : ℕ)
    (ht : (vectorFrequencyBound D a + 1 : ℕ) - d - 1 = (t : ℤ))
    (hell : ell ≤ t) (e : Exponent 3) (c : ℂ) :
    jaRename (algebraMap ℂ JAField (Ring.choose (-(1 : ℂ) / 2) ell) * jaShift ell *
      currentSourceMonomialValue D a b K e c (d + ell)) =
    ∑ u ∈ Finset.range (t - ell + 1),
      binaryRational
        ((Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
          ((Ring.choose (-((vectorFrequencyBound D b + 1 : ℕ) : ℤ)) (t - ell - u) : ℤ) : ℂ)) •
          AddMonoidAlgebra.single (fusedExponent e (ell + u)) c)
        (-((vectorFrequencyBound D b + 1 + K + t : ℕ) : ℤ) + (ell + u : ℕ)) := by
  classical
  let L : ℤ := vectorFrequencyBound D a + 1
  let M : ℤ := vectorFrequencyBound D b + 1
  let A : ABField := y - LatticeHalfFockABLocalResidue.z
  have low : d + (ell : ℤ) - (vectorFrequencyBound D a + 1 : ℕ) < 0 := by omega
  have index : (-(d + (ell : ℤ) - (vectorFrequencyBound D a + 1 : ℕ)) - 1).toNat = t - ell := by omega
  rw [currentSourceMonomialValue, ite_eq_left low, index]
  simp only [map_mul, map_sum, map_zpow₀, map_pow, map_sub, map_inv₀, map_intCast,
    ja_complex, ja_variable, Finset.mul_sum]
  have shift : jaRename (jaShift ell) = y ^ (-(ell : ℤ)) := by
    rw [jaShift, variable_power, map_zpow₀, ja_variable]
    rfl
  rw [shift]
  change (∑ u ∈ Finset.range (t - ell + 1),
    algebraMap ℂ ABField (Ring.choose (-(1 : ℂ) / 2) ell) * y ^ (-(ell : ℤ)) *
      ((jaRename (algebraMap _ JAField
          (AddMonoidAlgebra.single (fun j : Remaining (0 : Fin 3) => e j.val) c)) *
        A ^ (-(K : ℤ))) * (y ^ e 0 * A ^ (-M)) *
        (y⁻¹ ^ u * ((Ring.choose (e 0) u : ℤ) : ABField) *
          (A⁻¹ ^ (t - ell - u) * ((Ring.choose (-M) (t - ell - u) : ℤ) : ABField))))) = _
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u ≤ t - ell := by simpa using Finset.mem_range.mp hu
  let m := t - ell - u
  have yy : y ^ (-(ell : ℤ)) * y ^ e 0 * y⁻¹ ^ u = y ^ (e 0 - (ell + u : ℕ)) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ y_nonzero,
      ← zpow_add₀ y_nonzero]
    congr 1
    push_cast
    omega
  have aa : A ^ (-(K : ℤ)) * A ^ (-M) * A⁻¹ ^ m =
      A ^ (-((vectorFrequencyBound D b + 1 + K + t : ℕ) : ℤ) + (ell + u : ℕ)) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg,
      ← zpow_add₀ LatticeHalfFockABOuterTaylor.yz_ne_zero, ← zpow_add₀ LatticeHalfFockABOuterTaylor.yz_ne_zero]
    congr 1
    dsimp [M, m]
    push_cast
    omega
  rw [binaryRational, LatticeHalfFockABOuterTaylor.map_complex_smul,
    fused_monomial_map]
  have chooseCast : algebraMap ℂ ABField (Ring.choose (e 0 : ℂ) u) =
      ((Ring.choose (e 0) u : ℤ) : ABField) := by
    have h : ((Ring.choose (e 0) u : ℤ) : ℂ) = Ring.choose (e 0 : ℂ) u :=
      Ring.map_choose (Int.castRingHom ℂ) (e 0) u
    rw [← h, map_intCast]
  simp only [map_mul, map_intCast]
  rw [chooseCast]
  calc
    _ = algebraMap ℂ ABField (Ring.choose (-(1 : ℂ) / 2) ell) *
        ((Ring.choose (e 0) u : ℤ) : ABField) *
        ((Ring.choose (-M) m : ℤ) : ABField) *
        (jaRename (algebraMap _ JAField
          (AddMonoidAlgebra.single (fun j : Remaining (0 : Fin 3) => e j.val) c)) *
          (y ^ (-(ell : ℤ)) * y ^ e 0 * y⁻¹ ^ u) *
          (A ^ (-(K : ℤ)) * A ^ (-M) * A⁻¹ ^ m)) := by ring
    _ = _ := by rw [yy, aa]; dsimp only [A, M, m]; simp only [Nat.cast_add, Nat.cast_one, neg_add_rev]; ring

private theorem ja_finite_representation (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (d : ℤ) (t : ℕ)
    (ht : (vectorFrequencyBound D a + 1 : ℕ) - d - 1 = (t : ℤ)) :
    jaRename (completeJA 1 d (vectorFrequencyBound D a + 1) (originalRational D a b K P)) =
    ∑ ell ∈ Finset.range (t + 1), ∑ e ∈ P.coeff.support,
      ∑ u ∈ Finset.range (t - ell + 1),
        binaryRational
          ((Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
            ((Ring.choose (-((vectorFrequencyBound D b + 1 : ℕ) : ℤ)) (t - ell - u) : ℤ) : ℂ)) •
            AddMonoidAlgebra.single (fusedExponent e (ell + u)) (P.coeff e))
          (-((vectorFrequencyBound D b + 1 + K + t : ℕ) : ℤ) + (ell + u : ℕ)) := by
  classical
  unfold completeJA
  rw [show (((vectorFrequencyBound D a + 1 : ℕ) : ℤ) - d).toNat = t + 1 by omega]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [show localResidue ℂ (0 : Fin 3) ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ (d + ell) * originalRational D a b K P) =
      ∑ e ∈ P.coeff.support, currentSourceMonomialValue D a b K e (P.coeff e) (d + ell)
      from current_source_laurent_residue D a b K P (d + ell)]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  simpa only [Int.cast_one] using
    ja_monomial_terms D a b K d t ell ht (by simpa using Finset.mem_range.mp hell) e (P.coeff e)

private theorem fused_single_taylor (e : Exponent 3) (c : ℂ)
    (B u : ℕ) (gamma degree r n : ℤ)
    (homogeneous : totalExponent e = degree - n - 1)
    (order : (B : ℤ) - r - 1 = degree - u) :
    binaryTaylor (AddMonoidAlgebra.single (fusedExponent e u) c) B (gamma + 1) r n =
      if (u : ℤ) ≤ degree then
        c * Ring.choose ((e 0 : ℂ) + (e 1 : ℂ) - (u : ℂ) - ((gamma : ℂ) + 1) / 2)
          (degree - u).toNat else 0 := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [binaryTaylor]
  · have ey : fusedExponent e u ⟨0, by decide⟩ = e 0 + e 1 - u := by
      simp [fusedExponent]
    have ez : fusedExponent e u ⟨2, by decide⟩ = e 2 := by
      simp [fusedExponent, show (2 : Fin 3) ≠ 0 by decide]
    simp only [binaryTaylor, AddMonoidAlgebra.coeff_single,
      Finsupp.support_single_ne_zero _ hc, Finset.sum_singleton, Finsupp.single_eq_same,
      ey, ez]
    simp only [totalExponent, Fin.sum_univ_three] at homogeneous
    have total : e 0 + e 1 - (u : ℤ) + e 2 = (B : ℤ) - r - n - 2 := by omega
    have low : (r < (B : ℤ)) ↔ (u : ℤ) ≤ degree := by omega
    simp only [total, ↓reduceIte, low, order]
    split_ifs <;> push_cast <;> rfl

set_option maxHeartbeats 1600000 in
-- Preserve the complete signed Laurent coefficient telescope.
private theorem current_source_outer_associated_taylor
    (D : LatticeData) (a b : Carrier D) (K T : ℕ)
    (P : LabelledPolynomial ℂ 3) (gamma d r n : ℤ) (t : ℕ)
    (ht : (vectorFrequencyBound D a + 1 : ℕ) - d - 1 = (t : ℤ))
    (hT : vectorFrequencyBound D b + 1 + K + t ≤ T)
    (homogeneous : ∀ e ∈ P.coeff.support,
      totalExponent e =
        ((vectorFrequencyBound D a + 1 : ℕ) : ℤ) +
        (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - n - 3) :
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let degree : ℤ := L + M + K - d - r - 2
    nestedLeftLocalReadout (gamma + 1) 1 d r n L T (originalRational D a b K P) =
      ∑ u ∈ Finset.range (t + 1),
        (if (u : ℤ) ≤ degree then
          associatedTaylor P gamma u (degree - u).toNat else 0) *
        ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ) := by
  classical
  dsimp only
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let C := M + K + t
  let degree : ℤ := (L : ℤ) + M + K - d - r - 2
  have index : degree = (C : ℤ) - r - 1 := by dsimp [degree, C, M, L]; omega
  have hom (e : Exponent 3) (he : e ∈ P.coeff.support) :
      totalExponent e = degree - n - 1 := by
    rw [homogeneous e he]
    dsimp [degree, L, M]
    omega
  have forward :
      (fun k l => currentSourceLocalQ false 1 d L k l (originalRational D a b K P)) =
        binaryModes false (jaRename (completeJA 1 d L (originalRational D a b K P))) := by
    funext k l
    exact ja_orders false 1 d k l L _
  have backward :
      (fun k l => currentSourceLocalQ true 1 d L l k (originalRational D a b K P)) =
        binaryModes true (jaRename (completeJA 1 d L (originalRational D a b K P))) := by
    funext k l
    exact ja_orders true 1 d l k L _
  change supportedQReadout (gamma + 1) r T n _ _ =
    ∑ u ∈ Finset.range (t + 1),
      (if (u : ℤ) ≤ degree then associatedTaylor P gamma u (degree - u).toNat else 0) *
        ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ)
  rw [forward, backward, ja_finite_representation D a b K P d t ht]
  simp_rw [binary_readout_sum]
  have perTerm (ell : ℕ) (hell : ell ∈ Finset.range (t + 1))
      (e : Exponent 3) (he : e ∈ P.coeff.support)
      (u : ℕ) (hu : u ∈ Finset.range (t - ell + 1)) :
      supportedQReadout (gamma + 1) r T n
        (binaryModes false (binaryRational
          ((Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
            ((Ring.choose (-(M : ℤ)) (t - ell - u) : ℤ) : ℂ)) •
            AddMonoidAlgebra.single (fusedExponent e (ell + u)) (P.coeff e))
          (-(C : ℤ) + (ell + u : ℕ))))
        (binaryModes true (binaryRational
          ((Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
            ((Ring.choose (-(M : ℤ)) (t - ell - u) : ℤ) : ℂ)) •
            AddMonoidAlgebra.single (fusedExponent e (ell + u)) (P.coeff e))
          (-(C : ℤ) + (ell + u : ℕ)))) =
      Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
        ((if ((ell + u : ℕ) : ℤ) ≤ degree then
          P.coeff e * Ring.choose
            ((e 0 : ℂ) + (e 1 : ℂ) - (ell + u : ℕ) - ((gamma : ℂ) + 1) / 2)
            (degree - (ell + u : ℕ)).toNat else 0) *
          ((Ring.choose (-(M : ℤ)) (t - (ell + u)) : ℤ) : ℂ)) := by
    have hel : ell ≤ t := by simpa using Finset.mem_range.mp hell
    have huu : u ≤ t - ell := by simpa using Finset.mem_range.mp hu
    have cut : -(C : ℤ) + (ell + u : ℕ) = -((C - (ell + u) : ℕ) : ℤ) := by
      dsimp [C]; omega
    rw [cut, binary_fractional_taylor _ (C - (ell + u)) T _ _ _ (by omega)]
    rw [show ((Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
          ((Ring.choose (-(M : ℤ)) (t - ell - u) : ℤ) : ℂ)) •
          AddMonoidAlgebra.single (fusedExponent e (ell + u)) (P.coeff e)) =
        AddMonoidAlgebra.single (fusedExponent e (ell + u))
          ((Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
            ((Ring.choose (-(M : ℤ)) (t - ell - u) : ℤ) : ℂ)) * P.coeff e) by
      simp only [AddMonoidAlgebra.smul_single, smul_eq_mul]
    ]
    rw [fused_single_taylor _ _ _ _ gamma degree r n (hom e he) (by
      dsimp [C, M] at *; omega)]
    rw [Nat.sub_sub]
    split_ifs <;> ring
  calc
    _ = ∑ ell ∈ Finset.range (t + 1), ∑ e ∈ P.coeff.support,
          ∑ u ∈ Finset.range (t - ell + 1),
            Ring.choose (-(1 : ℂ) / 2) ell * Ring.choose (e 0 : ℂ) u *
              ((if ((ell + u : ℕ) : ℤ) ≤ degree then
                P.coeff e * Ring.choose
                  ((e 0 : ℂ) + (e 1 : ℂ) - (ell + u : ℕ) - ((gamma : ℂ) + 1) / 2)
                  (degree - (ell + u : ℕ)).toNat else 0) *
                ((Ring.choose (-(M : ℤ)) (t - (ell + u)) : ℤ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro u hu
      exact perTerm ell hell e he u hu
    _ = ∑ e ∈ P.coeff.support, ∑ u ∈ Finset.range (t + 1),
          Ring.choose ((e 0 : ℂ) - 1 / 2) u *
            ((if (u : ℤ) ≤ degree then
              P.coeff e * Ring.choose
                ((e 0 : ℂ) + (e 1 : ℂ) - (u : ℂ) - ((gamma : ℂ) + 1) / 2)
                (degree - u).toNat else 0) *
              ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      have h := LatticeHalfFockABOuterTaylor.triangle_vandermonde
        (-(1 : ℂ) / 2) (e 0 : ℂ) t
        (fun u => (if (u : ℤ) ≤ degree then
          P.coeff e * Ring.choose
            ((e 0 : ℂ) + (e 1 : ℂ) - (u : ℂ) - ((gamma : ℂ) + 1) / 2)
            (degree - u).toNat else 0) *
          ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ))
      rw [show -(1 : ℂ) / 2 + (e 0 : ℂ) = (e 0 : ℂ) - 1 / 2 by ring] at h
      exact h
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases inside : (u : ℤ) ≤ degree
      · simp only [ite_eq_left inside, associatedTaylor, Finsupp.linearCombination_apply,
          Finsupp.sum, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        ring
      · simp [inside]

set_option maxHeartbeats 1600000 in
-- Preserve the complete signed Laurent coefficient telescope.
private theorem first_actual_associated_convolution
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H₁ : ℕ)
    (locality₁ : (FieldNormalProductLocality.deltaEnd ^ H₁)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu (neutralMode D i d a) (gamma + 1))
        (targetSlice D hu b delta)) = 0)
    (hd : d < (vectorFrequencyBound D a + 1 : ℕ)) :
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let degree : ℤ := L + M + K - d - r - 2
    let t := ((L : ℤ) - d - 1).toNat
    phi (((qField (gamma + 1) r H₁
      (targetSlice D hu (neutralMode D i d a) (gamma + 1))
      (targetSlice D hu b delta))[[n]]) x) =
      ∑ u ∈ Finset.range (t + 1),
        (if (u : ℤ) ≤ degree then
          associatedTaylor P gamma u (degree - u).toNat else 0) *
        ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ) := by
  classical
  dsimp only
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let t := ((L : ℤ) - d - 1).toNat
  let C := M + K + t
  have ht : (L : ℤ) - d - 1 = (t : ℤ) := by dsimp [t, L]; omega
  have orders : (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) =
      (L : ℤ) + M + K := by
    have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
    simp [pairs, threeOrders, L, M, add_assoc]
  have homogeneous : ∀ e ∈ P.coeff.support,
      totalExponent e = (L : ℤ) + M + K - d - r - n - 3 := by
    intro e he
    have nz := Finsupp.mem_support_iff.mp he
    have eqn := coefficients e
    split_ifs at eqn with h
    · rwa [orders] at h
    · exact (nz eqn).elim
  have supplied := (actual_slice_quotient_compat D hu i a b K K gamma delta d r n
    x phi P P coefficients coefficients).2.2 H₁ 0 0
  have actual := supplied.1.1
  have completion := supplied.1.2 locality₁
  have pad := (completion.2 H₁ le_rfl).trans
    (completion.2 (max H₁ C) (Nat.le_max_left _ _)).symm
  rw [actual]
  change supportedQReadout (gamma + 1) r H₁ n _ _ = _
  rw [pad]
  exact current_source_outer_associated_taylor D a b K (max H₁ C) P gamma d r n t ht
    (Nat.le_max_right _ _) homogeneous

/- proof_shape: fused_weighted_identity: content
   admission_basis: escape-witness
   escape_witness: The actual current/source residue is expanded into both
   signed binary Laurent orders. Whole-field completion pads the original
   locality cutoff before binary evaluation; two finite Vandermonde
   contractions identify the associated and original same-P Taylor sums.
   The original numerator, all signed degrees and empty fibers are retained. -/
set_option maxHeartbeats 1600000 in
-- Preserve the original three-locality telescope during actual extraction.
/-- Exactly the first conjunct of sameNumeratorCollisionBridge, with its
original lets, supplied numerator and all three locality telescopes. -/
theorem fused_weighted_identity (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) (K : ℕ) (gamma delta d r : ℤ) :
    let J := targetCurrent D hu i
    let A := targetSlice D hu a gamma
    let B := targetSlice D hu b delta
    let Ad := targetSlice D hu (neutralMode D i d a) (gamma + 1)
    let Bj := fun j : ℕ => targetSlice D hu (neutralMode D i j b) (delta + 1)
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let degree : ℤ := L + M + K - d - r - 2
    ∀ (n : ℤ) (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
      (P : LabelledPolynomial ℂ 3),
      (∀ e : Exponent 3, P.coeff e =
        if totalExponent e =
            (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
        then phi (actualNumerator D hu i a b gamma delta K x e) else 0) →
      ∀ (H₁ : ℕ) (H₂ H₃ : ℕ → ℕ),
        (FieldNormalProductLocality.deltaEnd ^ H₁)
          (FieldNormalProductLocality.commutator Ad B) = 0 →
        (∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
          (FieldNormalProductLocality.deltaEnd ^ H₂ j)
            (FieldNormalProductLocality.commutator J (qField gamma (r + j) K A B)) = 0) →
        (∀ j ∈ Finset.range M,
          (FieldNormalProductLocality.deltaEnd ^ H₃ j)
            (FieldNormalProductLocality.commutator A (Bj j)) = 0) →
        phi (((qField (gamma + 1) r H₁ Ad B)[[n]]) x) =
          ∑ u ∈ Finset.range (degree + 1).toNat,
            collisionTaylor P gamma u (degree - u).toNat *
              fusedResidueWeight ((u : ℤ) - M) (d - L) := by
  classical
  dsimp only
  intro n x phi P coefficients H₁ H₂ H₃ locality₁ locality₂ locality₃
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let degree : ℤ := (L : ℤ) + M + K - d - r - 2
  by_cases hd : d < (L : ℤ)
  · let t := ((L : ℤ) - d - 1).toNat
    have ht : -(t : ℤ) - 1 = d - L := by dsimp [t]; omega
    have actual := first_actual_associated_convolution D hu i a b K gamma delta d r n
      x phi P coefficients H₁ locality₁ hd
    exact actual.trans (by
      simpa only [ht] using finite_left_outer_taylor P gamma degree M t)
  · have modeZero := neutralMode_vanish D i a d (by dsimp [L] at hd; omega)
    have sourceModes (m : ℤ) :
        (targetSlice D hu (neutralMode D i d a) (gamma + 1))[[m]] = 0 := by
      simp [targetSlice, modeZero, LatticeHalfFockPhysicalRescaling.physicalSlice_mode]
    have sourceZero : targetSlice D hu (neutralMode D i d a) (gamma + 1) = 0 := by
      apply HVertexOperator.coeff_inj
      funext e
      rw [VertexOperator.coeff_eq_ncoeff, sourceModes]
      simp
    have actualZero : phi (((qField (gamma + 1) r H₁
        (targetSlice D hu (neutralMode D i d a) (gamma + 1))
        (targetSlice D hu b delta))[[n]]) x) = 0 := by
      rw [sourceZero, qField,
        LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_mode]
      simp_rw [← LatticeHalfFockChargedResidue.physicalResidueCoefficient_eq_R]
      simp [LatticeHalfFockChargedResidue.physicalResidueCoefficient,
        LatticeHalfFockChargedResidue.physicalResidueLeft,
        LatticeHalfFockChargedResidue.physicalResidueRight]
    rw [actualZero]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    have high : ¬ d - ((vectorFrequencyBound D a + 1 : ℕ) : ℤ) < 0 := by
      dsimp [L] at hd
      omega
    simp only [fusedResidueWeight, ite_eq_right high, mul_zero]

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
