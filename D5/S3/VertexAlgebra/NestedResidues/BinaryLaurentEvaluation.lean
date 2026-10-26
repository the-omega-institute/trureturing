/- GID: D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete binary Laurent residues at arbitrary signed diagonal powers. -/

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockOuterTaylorEvaluation

/-! The two remaining labels are the original J and B. Every Laurent
numerator exponent is signed. The complete difference precedes evaluation;
no locality assertion is attached to a monomial or to an ordered half. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open CollisionRationalExpansions.OrderedRationalExpansion
open LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization
  (remainingVariable remainingVariable_injective curry_variable_z
    curry_variable_remaining curryPolynomial_single)
open OrderedCollisionCoordinates.LocalResidueCurrying
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open scoped BigOperators VertexOperator RatFunc
noncomputable section

abbrev ABField := CoefficientField ℂ (1 : Fin 3)

/-- Original remaining labels y=J and z=B; v=A is the curried variable. -/
def y : ABField := remainingVariable ℂ (1 : Fin 3) ⟨0, by decide⟩
def z : ABField := remainingVariable ℂ (1 : Fin 3) ⟨2, by decide⟩

def originalRational (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) : CommonRational ℂ 3 :=
  algebraMap _ (CommonRational ℂ 3) P /
    algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))

theorem coefficient_scalar (pre post : ℕ)
    (zz : Fin ((pre + 1) + post)) (tau : Fin (pre + post) ≃ Remaining zz) (c : ℂ) :
    coefficientHahn ℂ pre post zz tau (algebraMap ℂ _ c) = HahnSeries.C c := by
  rw [IsScalarTower.algebraMap_apply ℂ (CoefficientPolynomial ℂ zz) (CoefficientField ℂ zz)]
  unfold coefficientHahn
  rw [IsFractionRing.lift_algebraMap]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents pre post zz tau))
      (AddMonoidAlgebra.single 0 c)) = _
  rw [AddMonoidAlgebra.domCongr_single,
    SupportedFieldWords.FiniteConvolution.scalarPolynomial_single, map_zero]
  rfl

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue

/- The coefficient formula consumes the separately published original
contextual API. It does not copy the frozen private implementation. -/
namespace D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionLaurentKernels.LaurentCollision
open scoped BigOperators
noncomputable section

theorem binary_kernel_coeff (r a b : ℤ) :
    (contextPair ℂ 0 0 (kernelZX ℂ r)).coeff (pairIndex 0 0 (toLex (a, b))) =
      if 0 ≤ a then if b = r - a then
        BinomialKernelDelta.chooseSign r a.toNat else 0 else 0 := by
  simpa only [BinomialKernelDelta.chooseSign] using
    D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction.contextual_kernel_coeff ℂ 0 0 r a b



end
end D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport

namespace D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
noncomputable section

private theorem negative_kernel_choose (k j : ℕ) :
    BinomialKernelDelta.chooseSign (-(k : ℤ) - 1) j = ((k + j).choose k : ℂ) := by
  rw [BinomialKernelDelta.chooseSign,
    show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, Ring.choose_neg,
    show (k : ℤ) + 1 + j - 1 = ((k + j : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
    Int.cast_negOnePow_natCast, Int.cast_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num only [neg_mul_neg, one_mul, one_pow]
  rw [Nat.choose_symm_add]

theorem signed_kernel_choose (k : ℕ) (a : ℤ) :
    (if 0 ≤ a - k then
      BinomialKernelDelta.chooseSign (-(k : ℤ) - 1) (a - k).toNat else 0) -
    StateFieldResidueReconstruction.epsilon (-(k : ℤ) - 1) *
      (if 0 ≤ -a - 1 then
        BinomialKernelDelta.chooseSign (-(k : ℤ) - 1) (-a - 1).toNat else 0) =
    ((Ring.choose a k : ℤ) : ℂ) := by
  by_cases positive : (k : ℤ) ≤ a
  · rw [if_pos (by omega), if_neg (by omega), mul_zero, sub_zero,
      negative_kernel_choose]
    have nonnegative : 0 ≤ a := by omega
    have total : k + (a - k).toNat = a.toNat := by omega
    rw [total, ← Int.toNat_of_nonneg nonnegative, Ring.choose_natCast]
    rfl
  · by_cases nonnegative : 0 ≤ a
    · rw [if_neg (by omega), if_neg (by omega), mul_zero, sub_zero,
        ← Int.toNat_of_nonneg nonnegative, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · rw [if_neg (by omega), if_pos (by omega), zero_sub, negative_kernel_choose]
      have aform : a = -(((-a - 1).toNat : ℤ) + 1) := by omega
      conv_rhs => rw [aform, Ring.choose_neg,
        show (((-a - 1).toNat : ℤ) + 1) + k - 1 =
          ((k + (-a - 1).toNat : ℕ) : ℤ) by omega,
        Ring.choose_natCast]
      simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
        Int.cast_negOnePow_natCast, Int.cast_natCast]
      have sign : -StateFieldResidueReconstruction.epsilon (-(k : ℤ) - 1) =
          (-1 : ℂ) ^ k := by
        unfold StateFieldResidueReconstruction.epsilon
        rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega,
          zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one, pow_succ]
        ring
      rw [← neg_mul, sign]

end
end D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout

namespace D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockClearedTaylorReadout LatticeHalfFockABLocalResidue
open CollisionLaurentKernels.LaurentCollision
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.ContextualLaurentKernel
open LabelledRationalClearing.GlobalRationalCurry
open scoped BigOperators
noncomputable section

abbrev BinaryPolynomial := CoefficientPolynomial ℂ (1 : Fin 3)
abbrev BinaryExponent := Remaining (1 : Fin 3) → ℤ

def binaryRational (Q : BinaryPolynomial) (p : ℤ) : ABField :=
  algebraMap _ ABField Q * (y - LatticeHalfFockABLocalResidue.z) ^ p

def binaryExpansion (reverse : Bool) : ABField →+* HahnSeries (Indices 2) ℂ :=
  coefficientHahn ℂ 1 1 (1 : Fin 3)
    (if reverse then (Equiv.swap 0 1).trans (finSuccAboveEquiv 1)
      else finSuccAboveEquiv 1)

def binaryModes (reverse : Bool) (F : ABField) (m k : ℤ) : ℂ :=
  (binaryExpansion reverse F).coeff (exponents 2 ![-m - 1, -k - 1])

def binaryKernel (reverse : Bool) (p : ℤ) : HahnSeries (Indices 2) ℂ :=
  contextPair ℂ 0 0 (if reverse then kernelXZ ℂ p else kernelZX ℂ p)

private theorem expansion_single (reverse : Bool) (e : BinaryExponent) (c : ℂ) :
    binaryExpansion reverse (algebraMap _ ABField (AddMonoidAlgebra.single e c)) =
      HahnSeries.single (exponents 2
        (if reverse then ![e ⟨2, by decide⟩, e ⟨0, by decide⟩]
          else ![e ⟨0, by decide⟩, e ⟨2, by decide⟩])) c := by
  unfold binaryExpansion coefficientHahn
  rw [IsFractionRing.lift_algebraMap]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents 1 1 (1 : Fin 3) _))
      (AddMonoidAlgebra.single e c)) = _
  rw [AddMonoidAlgebra.domCongr_single,
    SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
  apply congrArg (fun g => HahnSeries.single g c)
  apply congrArg (exponentAddEquiv 2)
  cases reverse <;> ext i <;> fin_cases i <;> rfl

private theorem expansion_diagonal (reverse : Bool) :
    binaryExpansion reverse (y - LatticeHalfFockABLocalResidue.z) =
      binaryKernel reverse 1 := by
  rw [map_sub]
  unfold y LatticeHalfFockABLocalResidue.z LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
  rw [expansion_single, expansion_single]
  cases reverse <;>
    simp only [binaryKernel, Bool.false_eq_true, ite_false, ite_true,
      kernelZX_zpow, kernelXZ_zpow, zpow_one, deltaZX, deltaXZ, T,
      map_sub, HahnSeries.C_apply]
  all_goals
    change _ = contextPair ℂ 0 0 (HahnSeries.single _ (HahnSeries.single _ 1)) -
      contextPair ℂ 0 0 (HahnSeries.single _ (HahnSeries.single _ 1))
    rw [OrderedCollisionResidues.LabelledDiagonalResidue.context_single,
      OrderedCollisionResidues.LabelledDiagonalResidue.context_single]
    simp
    rfl

private theorem kernel_add (reverse : Bool) (p q : ℤ) :
    binaryKernel reverse (p + q) = binaryKernel reverse p * binaryKernel reverse q := by
  cases reverse <;> simp only [binaryKernel, Bool.false_eq_true, ite_false, ite_true]
  · rw [kernelZX_zpow, kernelZX_zpow, kernelZX_zpow,
      zpow_add₀ (deltaZX_ne_zero ℂ), map_mul]
  · rw [kernelXZ_zpow, kernelXZ_zpow, kernelXZ_zpow,
      zpow_add₀ (deltaXZ_ne_zero ℂ), map_mul]

private theorem expansion_power (reverse : Bool) (p : ℤ) :
    binaryExpansion reverse ((y - LatticeHalfFockABLocalResidue.z) ^ p) =
      binaryKernel reverse p := by
  rw [map_zpow₀, expansion_diagonal]
  cases reverse <;> simp only [binaryKernel, Bool.false_eq_true, ite_false, ite_true,
    kernelZX_zpow, kernelXZ_zpow, zpow_one, ← map_zpow₀]

private theorem backward_kernel_coeff (p a b : ℤ) :
    (binaryKernel true p).coeff (pairIndex 0 0 (toLex (a, b))) =
      StateFieldResidueReconstruction.epsilon p *
        (if 0 ≤ a then if b = p - a then
          BinomialKernelDelta.chooseSign p a.toNat else 0 else 0) := by
  have constant : contextPair ℂ 0 0
      (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon p))) =
      HahnSeries.C (StateFieldResidueReconstruction.epsilon p) := by
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
  unfold binaryKernel
  rw [ite_eq_left rfl, LatticeHalfFockNestedQReadout.reverse_kernel, map_mul, constant, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, binary_kernel_coeff]

private theorem high_kernel_jump (p a b : ℤ) (high : 0 ≤ p) (total : a + b = p) :
    (if 0 ≤ a then BinomialKernelDelta.chooseSign p a.toNat else 0) -
      StateFieldResidueReconstruction.epsilon p *
        (if 0 ≤ b then BinomialKernelDelta.chooseSign p b.toNat else 0) = 0 := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le high
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · have indices : a.toNat + b.toNat = N := by omega
      have signs : (-1 : ℂ) ^ N * (-1 : ℂ) ^ b.toNat = (-1 : ℂ) ^ a.toNat := by
        rw [← indices, pow_add, mul_assoc, ← pow_add]
        rw [show b.toNat + b.toNat = 2 * b.toNat by omega, pow_mul]
        norm_num
      simp only [ite_eq_left ha, ite_eq_left hb, BinomialKernelDelta.chooseSign,
        Ring.choose_natCast, Int.cast_natCast, StateFieldResidueReconstruction.epsilon,
        zpow_natCast]
      have symmChoose : N.choose b.toNat = N.choose a.toNat := by
        rw [← Nat.choose_symm (show b.toNat ≤ N by omega),
          show N - b.toNat = a.toNat by omega]
      rw [symmChoose, ← mul_assoc, signs, sub_self]
    · have large : N < a.toNat := by omega
      simp [ha, hb, BinomialKernelDelta.chooseSign, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt large]
  · have hb : 0 ≤ b := by omega
    have large : N < b.toNat := by omega
    simp [ha, hb, BinomialKernelDelta.chooseSign, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt large]

private theorem single_jump (p n : ℤ) (e : BinaryExponent) (c : ℂ) :
    (binaryKernel false p *
      binaryExpansion false (algebraMap _ ABField (AddMonoidAlgebra.single e c))).coeff
        (exponents 2 ![-1, -n - 1]) -
    (binaryKernel true p *
      binaryExpansion true (algebraMap _ ABField (AddMonoidAlgebra.single e c))).coeff
        (exponents 2 ![-n - 1, -1]) =
      if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = -p - n - 2 then
        if p < 0 then c * ((Ring.choose (e ⟨0, by decide⟩) (-p - 1).toNat : ℤ) : ℂ)
          else 0 else 0 := by
  rw [expansion_single, expansion_single, HahnSeries.coeff_mul_single,
    HahnSeries.coeff_mul_single]
  change (binaryKernel false p).coeff
      (pairIndex 0 0 (toLex (-n - 1 - e ⟨2, by decide⟩, -1 - e ⟨0, by decide⟩))) * c -
    (binaryKernel true p).coeff
      (pairIndex 0 0 (toLex (-1 - e ⟨0, by decide⟩, -n - 1 - e ⟨2, by decide⟩))) * c = _
  rw [show binaryKernel false p = contextPair ℂ 0 0 (kernelZX ℂ p) by rfl,
    binary_kernel_coeff, backward_kernel_coeff]
  by_cases total : e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = -p - n - 2
  · rw [ite_eq_left total,
      ite_eq_left (show -1 - e ⟨0, by decide⟩ = p - (-n - 1 - e ⟨2, by decide⟩) by omega),
      ite_eq_left (show -n - 1 - e ⟨2, by decide⟩ = p - (-1 - e ⟨0, by decide⟩) by omega)]
    by_cases low : p < 0
    · rw [ite_eq_left low]
      let k := (-p - 1).toNat
      have pp : p = -(k : ℤ) - 1 := by dsimp [k]; omega
      have aa : -n - 1 - e ⟨2, by decide⟩ = e ⟨0, by decide⟩ - k := by omega
      rw [aa, pp]
      have law := signed_kernel_choose k (e ⟨0, by decide⟩)
      rw [show -1 - e ⟨0, by decide⟩ = -e ⟨0, by decide⟩ - 1 by omega,
        show (-(-((k : ℤ)) - 1) - 1).toNat = k by omega]
      linear_combination c * law
    · rw [ite_eq_right low]
      have law := high_kernel_jump p (-n - 1 - e ⟨2, by decide⟩)
        (-1 - e ⟨0, by decide⟩) (by omega) (by omega)
      linear_combination c * law
  · rw [ite_eq_right total]
    have hf : -1 - e ⟨0, by decide⟩ ≠ p - (-n - 1 - e ⟨2, by decide⟩) := by omega
    have hg : -n - 1 - e ⟨2, by decide⟩ ≠ p - (-1 - e ⟨0, by decide⟩) := by omega
    simp only [ite_eq_right hf, ite_eq_right hg, ite_self, mul_zero, zero_mul, sub_self]

/- proof_shape: binary_laurent_jump: content
   admission_basis: escape-witness
   escape_witness: The complete two-order coefficient difference is evaluated
   for every signed diagonal exponent. Positive powers cancel; negative
   powers use the signed kernel identity, including negative numerator powers.
   consumer: binary_complete_residue -/
/-- The complete binary Laurent jump, with unrestricted numerator and
diagonal exponents. The degree filter is exact, including empty fibers. -/
theorem binary_laurent_jump (Q : BinaryPolynomial) (p n : ℤ) :
    (binaryKernel false p * binaryExpansion false (algebraMap _ ABField Q)).coeff
        (exponents 2 ![-1, -n - 1]) -
    (binaryKernel true p * binaryExpansion true (algebraMap _ ABField Q)).coeff
        (exponents 2 ![-n - 1, -1]) =
      ∑ e ∈ Q.coeff.support,
        if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = -p - n - 2 then
          if p < 0 then Q.coeff e * ((Ring.choose (e ⟨0, by decide⟩) (-p - 1).toNat : ℤ) : ℂ)
            else 0 else 0 := by
  classical
  have splitQ : (∑ e ∈ Q.coeff.support, AddMonoidAlgebra.single e (Q.coeff e)) = Q :=
    AddMonoidAlgebra.sum_coeff_single Q
  conv_lhs => rw [← splitQ]
  simp only [map_sum, Finset.mul_sum, HahnSeries.coeff_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  exact single_jump p n e (Q.coeff e)

theorem forward_readout (F : ABField) (q k : ℤ) :
    (binaryKernel false q * binaryExpansion false F).coeff
      (exponents 2 ![-1, -k - 1]) =
    ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign q u *
      binaryModes false F (q - u) (k + u) := by
  change (contextPair ℂ 0 0 (kernelZX ℂ q) * binaryExpansion false F).coeff _ = _
  rw [(ContextualKernelExtraction.contextual_kernel_extraction ℂ 0 0 q
    (binaryExpansion false F) (exponents 2 ![-1, -k - 1])).2]
  apply finsum_congr
  intro u
  change BinomialKernelDelta.chooseSign q u * _ = _
  congr 1
  unfold binaryModes
  congr 1
  change (exponentAddEquiv 2) ![-1, -k - 1] -
    (exponentAddEquiv 2) ![q - u, (u : ℤ)] =
      (exponentAddEquiv 2) ![-(q - u) - 1, -(k + u) - 1]
  rw [← map_sub]
  apply congrArg (exponentAddEquiv 2)
  ext i
  fin_cases i <;> simp <;> omega

theorem reverse_readout (F : ABField) (q k : ℤ) :
    (binaryKernel true q * binaryExpansion true F).coeff
      (exponents 2 ![-k - 1, -1]) =
    StateFieldResidueReconstruction.epsilon q *
      ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign q u *
        binaryModes true F (q + k - u) u := by
  have constant : contextPair ℂ 0 0
      (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon q))) =
      HahnSeries.C (StateFieldResidueReconstruction.epsilon q) := by
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
  unfold binaryKernel
  rw [ite_eq_left rfl, LatticeHalfFockNestedQReadout.reverse_kernel, map_mul, constant, mul_assoc, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul]
  rw [(ContextualKernelExtraction.contextual_kernel_extraction ℂ 0 0 q
    (binaryExpansion true F) (exponents 2 ![-k - 1, -1])).2]
  congr 1
  apply finsum_congr
  intro u
  change BinomialKernelDelta.chooseSign q u * _ = _
  congr 1
  unfold binaryModes
  congr 1
  change (exponentAddEquiv 2) ![-k - 1, -1] -
    (exponentAddEquiv 2) ![q - u, (u : ℤ)] =
      (exponentAddEquiv 2) ![-(q + k - u) - 1, -(u : ℤ) - 1]
  rw [← map_sub]
  apply congrArg (exponentAddEquiv 2)
  ext i
  fin_cases i <;> simp <;> omega

/- proof_shape: binary_complete_residue: content
   admission_basis: escape-witness
   escape_witness: Supported kernel extraction identifies the full residue
   with the two-order Laurent jump, preserving the signed diagonal and the
   cancellation of ell from the degree filter. -/
/-- Every complete ordinary residue of a finite binary Laurent rational is
an explicit finite signed-binomial sum. The fractional index only shifts
its Taylor order; the homogeneous degree filter stays fixed. -/
theorem binary_complete_residue (Q : BinaryPolynomial) (p r n : ℤ) (ell : ℕ) :
    completeOuterResidue r n (binaryModes false (binaryRational Q p))
      (binaryModes true (binaryRational Q p)) ell =
    ∑ e ∈ Q.coeff.support,
      if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = -p - r - n - 2 then
        if p + r + ell < 0 then
          Q.coeff e * ((Ring.choose (e ⟨0, by decide⟩) (-p - r - ell - 1).toNat : ℤ) : ℂ)
        else 0 else 0 := by
  have regroup (reverse : Bool) :
      binaryKernel reverse (r + ell) * binaryExpansion reverse (binaryRational Q p) =
      binaryKernel reverse (p + (r + ell)) *
        binaryExpansion reverse (algebraMap _ ABField Q) := by
    simp only [binaryRational, map_mul, expansion_power, kernel_add]
    ring
  have law := binary_laurent_jump Q (p + (r + ell)) (n - ell)
  rw [← regroup false, ← regroup true, forward_readout, reverse_readout] at law
  unfold completeOuterResidue
  have shifted : (r + (ell : ℤ)) + (n - ell) = r + n := by omega
  simp only [shifted, show p + (r + (ell : ℤ)) = p + r + ell by omega] at law
  simp only [
    show -(p + r + (ell : ℤ)) - (n - ell) - 2 = -p - r - n - 2 by omega,
    show -(p + r + (ell : ℤ)) - 1 = -p - r - ell - 1 by omega] at law
  exact law

/-- The finite binary Taylor value at its own denominator order. -/
def binaryTaylor (Q : BinaryPolynomial) (B : ℕ) (s r n : ℤ) : ℂ :=
  if r < B then
    ∑ e ∈ Q.coeff.support,
      if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = (B : ℤ) - r - n - 2 then
        Q.coeff e * Ring.choose ((e ⟨0, by decide⟩ : ℂ) - (s : ℂ) / 2)
          ((B : ℤ) - r - 1).toNat
      else 0
  else 0

/- proof_shape: binary_fractional_taylor: content
   admission_basis: escape-witness
   escape_witness: The complete residue tail is zero at the denominator
   order; the remaining finite sum contracts by Vandermonde at every signed
   numerator exponent. Empty and nonhomogeneous degree fibers are retained. -/
/-- Any fractional cutoff at least the binary pole order evaluates the
complete readout by a finite signed Taylor sum. This is rational evaluation,
without a locality hypothesis on either ordered expansion. -/
theorem binary_fractional_taylor (Q : BinaryPolynomial) (B T : ℕ)
    (s r n : ℤ) (larger : B ≤ T) :
    supportedQReadout s r T n (binaryModes false (binaryRational Q (-(B : ℤ))))
      (binaryModes true (binaryRational Q (-(B : ℤ)))) = binaryTaylor Q B s r n := by
  classical
  change (∑ ell ∈ Finset.range ((T : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      completeOuterResidue r n
        (binaryModes false (binaryRational Q (-(B : ℤ))))
        (binaryModes true (binaryRational Q (-(B : ℤ)))) ell) = _
  simp_rw [binary_complete_residue]
  simp only [neg_neg]
  unfold binaryTaylor
  by_cases low : r < B
  · rw [ite_eq_left low]
    let k := ((B : ℤ) - r - 1).toNat
    have kk : (k : ℤ) = B - r - 1 := by dsimp [k]; omega
    have truncate :
        (∑ ell ∈ Finset.range ((T : ℤ) - r).toNat,
          Ring.choose (-(s : ℂ) / 2) ell *
            ∑ e ∈ Q.coeff.support,
              if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = (B : ℤ) - r - n - 2 then
                if -(B : ℤ) + r + ell < 0 then
                  Q.coeff e * ((Ring.choose (e ⟨0, by decide⟩)
                    ((B : ℤ) - r - ell - 1).toNat : ℤ) : ℂ)
                else 0 else 0) =
        ∑ ell ∈ Finset.range (k + 1),
          Ring.choose (-(s : ℂ) / 2) ell *
            ∑ e ∈ Q.coeff.support,
              if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = (B : ℤ) - r - n - 2 then
                Q.coeff e * ((Ring.choose (e ⟨0, by decide⟩) (k - ell) : ℤ) : ℂ)
              else 0 := by
      have restrict :
          (∑ ell ∈ Finset.range ((T : ℤ) - r).toNat,
            Ring.choose (-(s : ℂ) / 2) ell *
              ∑ e ∈ Q.coeff.support,
                if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = (B : ℤ) - r - n - 2 then
                  if -(B : ℤ) + r + ell < 0 then
                    Q.coeff e * ((Ring.choose (e ⟨0, by decide⟩)
                      ((B : ℤ) - r - ell - 1).toNat : ℤ) : ℂ)
                  else 0 else 0) =
          ∑ ell ∈ Finset.range (k + 1),
            Ring.choose (-(s : ℂ) / 2) ell *
              ∑ e ∈ Q.coeff.support,
                if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = (B : ℤ) - r - n - 2 then
                  if -(B : ℤ) + r + ell < 0 then
                    Q.coeff e * ((Ring.choose (e ⟨0, by decide⟩)
                      ((B : ℤ) - r - ell - 1).toNat : ℤ) : ℂ)
                  else 0 else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro ell member outside
        have outside' : k + 1 ≤ ell := by simpa using outside
        simp only [ite_eq_right (show ¬ -(B : ℤ) + r + ell < 0 by omega),
          ite_self, Finset.sum_const_zero, mul_zero]
      rw [restrict]
      apply Finset.sum_congr rfl
      intro ell member
      have inside : ell ≤ k := by simpa using Finset.mem_range.mp member
      simp only [ite_eq_left (show -(B : ℤ) + r + ell < 0 by omega),
        show ((B : ℤ) - r - ell - 1).toNat = k - ell by omega]
    rw [truncate]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    by_cases degree : e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = (B : ℤ) - r - n - 2
    · simp only [ite_eq_left degree]
      simp_rw [show ∀ m, ((Ring.choose (e ⟨0, by decide⟩) m : ℤ) : ℂ) =
        Ring.choose (e ⟨0, by decide⟩ : ℂ) m from
          fun m => Ring.map_choose (Int.castRingHom ℂ) (e ⟨0, by decide⟩) m]
      have vandermonde := Ring.add_choose_eq (R := ℂ)
        (r := -(s : ℂ) / 2) (s := (e ⟨0, by decide⟩ : ℂ)) k (Commute.all _ _)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
      rw [show (e ⟨0, by decide⟩ : ℂ) - (s : ℂ) / 2 =
          -(s : ℂ) / 2 + (e ⟨0, by decide⟩ : ℂ) by ring,
        vandermonde, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell member
      ring
    · simp only [ite_eq_right degree, mul_zero, Finset.sum_const_zero]
  · rw [ite_eq_right low]
    apply Finset.sum_eq_zero
    intro ell member
    simp only [ite_eq_right (show ¬ -(B : ℤ) + r + ell < 0 by omega),
      ite_self, Finset.sum_const_zero, mul_zero]

end
end D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockABLocalResidue BinaryLaurentEvaluation
open LatticeHalfFockClearedTaylorReadout UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open scoped BigOperators VertexOperator
noncomputable section


theorem yz_ne_zero : y - LatticeHalfFockABLocalResidue.z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have labels := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable_injective
    ℂ (1 : Fin 3) h
  have impossible := congrArg Subtype.val labels
  exact (by decide : (0 : Fin 3) ≠ 2) impossible

theorem triangle_vandermonde (a b : ℂ) (t : ℕ) (F : ℕ → ℂ) :
    (∑ ell ∈ Finset.range (t + 1), ∑ u ∈ Finset.range (t - ell + 1),
      Ring.choose a ell * Ring.choose b u * F (ell + u)) =
    ∑ v ∈ Finset.range (t + 1), Ring.choose (a + b) v * F v := by
  have flip := Finset.sum_range_diag_flip (t + 1)
    (fun ell u => Ring.choose a ell * Ring.choose b u * F (ell + u))
  have reindex :
      (∑ ell ∈ Finset.range (t + 1), ∑ u ∈ Finset.range (t - ell + 1),
        Ring.choose a ell * Ring.choose b u * F (ell + u)) =
      ∑ v ∈ Finset.range (t + 1), ∑ ell ∈ Finset.range (v + 1),
        Ring.choose a ell * Ring.choose b (v - ell) * F v := by
    symm
    convert flip using 1
    · apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro ell hell
      have le : ell ≤ v := by simpa using Finset.mem_range.mp hell
      rw [Nat.add_sub_of_le le]
    · apply Finset.sum_congr rfl
      intro ell hell
      have le : ell ≤ t := by simpa using Finset.mem_range.mp hell
      rw [show t + 1 - ell = t - ell + 1 by omega]
  rw [reindex]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_mul]
  have h := Ring.add_choose_eq (R := ℂ) (r := a) (s := b) v (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [h]

theorem map_complex_smul (c : ℂ) (Q : BinaryPolynomial) :
    algebraMap BinaryPolynomial ABField (c • Q) =
      algebraMap ℂ ABField c * algebraMap BinaryPolynomial ABField Q := by
  rw [Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply ℂ BinaryPolynomial ABField]

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
