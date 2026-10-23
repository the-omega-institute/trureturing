/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/BinaryEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/BinaryEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete binary Laurent evaluation with unrestricted signed powers. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues

/-! Complete-field residue calculus with the original signed Laurent powers.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. Hahn operations: mathlib, Apache 2.0.
This is a formalized synthesis and application, with no literature novelty claim.
Consumed boundary helpers are not independent mathematical endpoints.
The unfinished whole-family information audit is covered by issue #20163. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockClearedTaylorReadout LatticeHalfFockABLocalResidue
open CollisionLaurentKernels.LaurentCollision
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.ContextualLaurentKernel
open LabelledRationalClearing.GlobalRationalCurry
open scoped BigOperators
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
noncomputable section

abbrev BinaryPolynomial := CoefficientPolynomial ℂ (1 : Fin 3)

abbrev BinaryExponent := Remaining (1 : Fin 3) → ℤ

def binaryRational (Q : BinaryPolynomial) (p : ℤ) : ABField :=
  algebraMap _ ABField Q * (y - LatticeHalfFockABLocalResidue.z) ^ p

private def binaryExpansion (reverse : Bool) : ABField →+* HahnSeries (Indices 2) ℂ :=
  coefficientHahn ℂ 1 1 (1 : Fin 3)
    (if reverse then (Equiv.swap 0 1).trans (finSuccAboveEquiv 1)
      else finSuccAboveEquiv 1)

def binaryModes (reverse : Bool) (F : ABField) (m k : ℤ) : ℂ :=
  (binaryExpansion reverse F).coeff (exponents 2 ![-m - 1, -k - 1])

private def binaryKernel (reverse : Bool) (p : ℤ) : HahnSeries (Indices 2) ℂ :=
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
  rw [ite_eq_left rfl, reverse_kernel, map_mul, constant, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul,
    ContextualKernelExtraction.contextual_kernel_coeff]
  rfl

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
    ContextualKernelExtraction.contextual_kernel_coeff, backward_kernel_coeff]
  change (if 0 ≤ -n - 1 - e ⟨2, by decide⟩ then
      if -1 - e ⟨0, by decide⟩ = p - (-n - 1 - e ⟨2, by decide⟩) then
        BinomialKernelDelta.chooseSign p (-n - 1 - e ⟨2, by decide⟩).toNat
      else 0 else 0) * c - _ = _
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

/- proof_shape: binary_laurent_jump: bind-only
   admission_basis: none (consumed bind-only helper, CLAUDE.md §3.2)
   escape_witness: none (no independent escape content)
   consumer: binary_complete_residue -/
/-- The complete binary Laurent jump, with unrestricted numerator and
diagonal exponents. The degree filter is exact, including empty fibers. -/
private theorem binary_laurent_jump (Q : BinaryPolynomial) (p n : ℤ) :
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

private theorem forward_readout (F : ABField) (q k : ℤ) :
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

private theorem reverse_readout (F : ABField) (q k : ℤ) :
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
  rw [ite_eq_left rfl, reverse_kernel, map_mul, constant, mul_assoc, HahnSeries.C_apply,
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

/- proof_shape: binary_complete_residue: bind-only
   admission_basis: none (consumed bind-only helper, CLAUDE.md §3.2)
   escape_witness: none (no independent escape content)
   consumer: binary_fractional_taylor -/
/-- Every complete ordinary residue of a finite binary Laurent rational is
an explicit finite signed-binomial sum. The fractional index only shifts
its Taylor order; the homogeneous degree filter stays fixed. -/
private theorem binary_complete_residue (Q : BinaryPolynomial) (p r n : ℤ) (ell : ℕ) :
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

/- proof_shape: binary_fractional_taylor: bind-only
   admission_basis: none (consumed bind-only helper, CLAUDE.md §3.2)
   escape_witness: none (no independent escape content)
   consumer: LatticeHalfFockABOuterTaylor.actual_ab_binary_taylor -/
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

