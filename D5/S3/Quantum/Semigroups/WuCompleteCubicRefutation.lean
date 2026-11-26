/- GID: D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCompleteCubicRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.claim; result=D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.result; claim=D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.claim
   digest: A faithful separable two-qubit state refutes the proposed fixed-marginal extension of Wu's tracial cubic inequality. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Recovery.BKMObservableRigidity
import D5.S3.Quantum.Semigroups.WuModularEdgeSpectral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
A faithful separable witness against the proposed fixed-marginal extension of
Wu, arXiv:2610.33686v1, (3.54), at the tracial cubic point of (3.55).
The embedded energy follows (2.4). The joint basis is ordered as 00, 01, 10, 11
and the trace is ordinary.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCompleteCubicRefutation

open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Recovery.BKMObservableRigidity (mpow_add)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (mpow_smul_of_nonneg)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
  (DensityState quantumRelativeEntropy)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Semigroups.WuModularEdgeSpectral (generatorTrace_eq_cosh pairedGenerator)

private abbrev Q := Fin 2
private abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

private def diagReal {n : Type*} [DecidableEq n] (v : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun i => (v i : ℂ))

private def productBasis : Q × Q ≃ Fin 4 := finProdFinEquiv

private theorem basis_symm_zero : productBasis.symm 0 = (0, 0) := rfl
private theorem basis_symm_one : productBasis.symm 1 = (0, 1) := rfl
private theorem basis_symm_two : productBasis.symm 2 = (1, 0) := rfl
private theorem basis_symm_three : productBasis.symm 3 = (1, 1) := rfl

private def flatten (X : Matrix (Q × Q) (Q × Q) ℂ) : Mat :=
  reindex productBasis productBasis X

/-- Read a computational-basis matrix as a matrix on system × ancilla. -/
private def unflatten (X : Mat) : Matrix (Q × Q) (Q × Q) ℂ :=
  reindex productBasis.symm productBasis.symm X

private def D : Matrix Q Q ℂ := diagReal ![1 / 2, 1 / 2]

private def sigma : Matrix Q Q ℂ := diagReal ![2 / 28, 26 / 28]

private def raw : Mat := !![2, 0, 0, 5; 0, 26, 0, 0; 0, 0, 2, 0; 5, 0, 0, 26]

/-- The displayed rational joint density in the computational basis. -/
private def rho : Mat := (1 / 56 : ℝ) • raw

/-- The reference is built from the actual ancillary partial trace. -/
private def reference (R : Mat) : Mat :=
  flatten (D ⊗ₖ partialTraceLeft (unflatten R))

private def jump : Mat := flatten ((!![0, 1; 0, 0] : Matrix Q Q ℂ) ⊗ₖ (1 : Matrix Q Q ℂ))

/-- The tracial one-mode generator amplified by the identity on the ancilla. -/
private def generator (X : Mat) : Mat := pairedGenerator (1 / 2) (1 / 2) jump X

private def embeddedPower (T R : Mat) (r : ℝ) : Mat :=
  mpow T (-r / 2) * mpow R r * mpow T (-r / 2)

/-- Wu's embedded energy with the actual fixed-marginal reference. -/
private def energy (R : Mat) (p : ℝ) : ℝ :=
  let T := reference R
  let q := 1 - p
  (mpow T (1 / 2) * embeddedPower T R q * mpow T (1 / 2) *
    generator (embeddedPower T R p)).trace.re / (4 * p * q)

private def relativeEntropy (R : Mat) : ℝ :=
  (R * (CFC.log R - CFC.log (reference R))).trace.re

/-- The proposed tracial cubic bound with fixed system and ancillary marginals. -/
def claim : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℂ,
    R.PosDef →
    partialTraceRight (unflatten R) = D →
    partialTraceLeft (unflatten R) = sigma →
    IsSeparable (unflatten R) →
    relativeEntropy R / 2 ≤ energy R (1 / 3)

private theorem rho_marginals :
    partialTraceRight (unflatten rho) = D ∧ partialTraceLeft (unflatten rho) = sigma := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, partialTraceLeft, Fin.sum_univ_two,
      unflatten, reindex_apply, productBasis, finProdFinEquiv, rho, raw,
      D, sigma, diagReal, Matrix.smul_apply, Complex.real_smul]

private def refValues : Fin 4 → ℝ := ![2 / 56, 26 / 56, 2 / 56, 26 / 56]

private theorem reference_value : reference rho = diagReal refValues := by
  rw [reference, rho_marginals.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flatten, reindex_apply, basis_symm_zero, basis_symm_one, basis_symm_two,
      basis_symm_three, D, sigma,
      diagReal, refValues, Matrix.kroneckerMap_apply]

private theorem trace_rho : rho.trace = 1 := by
  norm_num [Matrix.trace, Fin.sum_univ_four, rho, raw, Matrix.smul_apply, Complex.real_smul]

private theorem trace_reference : (reference rho).trace = 1 := by
  rw [reference_value]
  norm_num [Matrix.trace, Fin.sum_univ_four, diagReal, refValues]

private def frame (s : ℝ) : Mat :=
  !![(5 * s : ℝ), 0, 0, (s : ℂ);
      0, 1, 0, 0;
      0, 0, 1, 0;
      (-s : ℝ), 0, 0, (5 * s : ℝ)]

private def frameScale : ℝ := Real.sqrt (1 / 26)

private theorem frameScale_sq : (frameScale : ℂ) ^ 2 = 1 / 26 := by
  rw [pow_two]
  have h : frameScale * frameScale = 1 / 26 := by
    rw [← sq, frameScale, Real.sq_sqrt (by norm_num)]
  simpa using congrArg Complex.ofReal h

private def U : Matrix.unitaryGroup (Fin 4) ℂ := by
  refine ⟨frame frameScale, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [frame, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] <;>
    norm_num [Matrix.one_apply, Complex.star_def] <;>
    ring_nf <;> rw [frameScale_sq] <;> norm_num

private def spectral (v : Fin 4 → ℝ) : Mat := U.val * diagReal v * U.valᴴ

private def corner (a b c d t : ℝ) : Mat :=
  !![(a : ℂ), 0, 0, (t : ℂ);
      0, (b : ℂ), 0, 0;
      0, 0, (c : ℂ), 0;
      (t : ℂ), 0, 0, (d : ℂ)]

private theorem spectral_entries (v : Fin 4 → ℝ) :
    spectral v = corner ((25 * v 0 + v 3) / 26) (v 1) (v 2)
      ((v 0 + 25 * v 3) / 26) (5 * (v 3 - v 0) / 26) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [spectral, U, frame, corner, diagReal, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_four] <;>
    norm_num [Complex.star_def, Complex.ofReal_div] <;>
    ring_nf <;> rw [frameScale_sq] <;> ring


private def rawValues : Fin 4 → ℝ := ![1, 26, 2, 27]
private def stateValues : Fin 4 → ℝ := fun i => rawValues i / 56

private theorem raw_spectral : raw = spectral rawValues := by
  rw [spectral_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [raw, rawValues, corner]

private theorem rho_spectral : rho = spectral stateValues := by
  rw [spectral_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho, raw, stateValues, rawValues, corner, Matrix.smul_apply, Complex.real_smul]

private theorem diag_pos {v : Fin 4 → ℝ} (hv : ∀ i, 0 < v i) : (diagReal v).PosDef :=
  Matrix.PosDef.diagonal (fun i => by exact_mod_cast hv i)

private theorem spectral_pos {v : Fin 4 → ℝ} (hv : ∀ i, 0 < v i) : (spectral v).PosDef :=
  (Unitary.isUnit_coe (U := U)).posDef_star_right_conjugate_iff.mpr (diag_pos hv)

private theorem rho_pos : rho.PosDef := by
  rw [rho_spectral]
  apply spectral_pos
  intro i
  fin_cases i <;> norm_num [stateValues, rawValues]

private theorem reference_pos : (reference rho).PosDef := by
  rw [reference_value]
  apply diag_pos
  intro i
  fin_cases i <;> norm_num [refValues]

private def density (M : Mat) (hM : M.PosDef) (htr : M.trace = 1) : DensityState (Fin 4) :=
  ⟨CStarMatrix.ofMatrix M,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.posSemidef.nonneg, htr⟩

/-- Relative entropy of the witness against the product with its actual ancilla. -/
private def entropy : ℝ :=
  quantumRelativeEntropy (density rho rho_pos trace_rho)
    (density (reference rho) reference_pos trace_reference)

private theorem cfc_spectral {v : Fin 4 → ℝ} (hv : ∀ i, 0 < v i) (f : ℝ → ℝ) :
    cfc f (spectral v) = spectral (fun i => f (v i)) := by
  have h := (spectral_pos hv).isHermitian
  rw [h.cfc_eq]
  exact h.cfc_eq_any_unitary (U := U) (D := v) rfl f

private def scaledEnergy : ℝ :=
  let x := (2 : ℝ) ^ (1 / 3 : ℝ)
  let y := (26 : ℝ) ^ (1 / 3 : ℝ)
  9 / 8 * (56 - (14 * x ^ 2 + 17 * x + 38 * y ^ 2 + 113 * y) / 13)

private def scaledEntropy : ℝ :=
  27 * Real.log 27 - 2 * Real.log 2 - 26 * Real.log 26

private theorem cube_root_cube {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = a := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

private theorem scaled_energy_lt : scaledEnergy < 7 / 5 := by
  let x := (2 : ℝ) ^ (1 / 3 : ℝ)
  let y := (26 : ℝ) ^ (1 / 3 : ℝ)
  have hx : (12599 / 10000 : ℝ) < x := by
    have h : (12599 / 10000 : ℝ) ^ (3 : ℕ) < x ^ (3 : ℕ) := by
      rw [cube_root_cube (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    exact lt_of_not_ge fun hle => h.not_ge (pow_le_pow_left₀ (by dsimp [x]; positivity) hle _)
  have hy : (29624 / 10000 : ℝ) < y := by
    have h : (29624 / 10000 : ℝ) ^ (3 : ℕ) < y ^ (3 : ℕ) := by
      rw [cube_root_cube (by norm_num : 0 ≤ (26 : ℝ))]
      norm_num
    exact lt_of_not_ge fun hle => h.not_ge (pow_le_pow_left₀ (by dsimp [y]; positivity) hle _)
  have hx2 := pow_lt_pow_left₀ hx (by norm_num) (by decide : (2 : ℕ) ≠ 0)
  have hy2 := pow_lt_pow_left₀ hy (by norm_num) (by decide : (2 : ℕ) ≠ 0)
  change 9 / 8 * (56 - (14 * x ^ 2 + 17 * x + 38 * y ^ 2 + 113 * y) / 13) < 7 / 5
  linarith

private theorem scaled_entropy_half_gt : 7 / 5 < scaledEntropy / 2 := by
  have h₁ := Real.sum_range_le_log_div (x := 1 / 5) (by norm_num) (by norm_num) 1
  have h₂ := Real.sum_range_le_log_div (x := 1 / 3) (by norm_num) (by norm_num) 2
  have h₃ := Real.sum_range_le_log_div (x := 1 / 53) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h₁ h₂ h₃
  have hdiv₁ : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have hdiv₃ : Real.log (27 / 26) = Real.log 27 - Real.log 26 :=
    Real.log_div (by norm_num) (by norm_num)
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  unfold scaledEntropy
  linarith

private theorem jump_entries :
    jump = !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jump, flatten, reindex_apply, basis_symm_zero, basis_symm_one, basis_symm_two,
      basis_symm_three, Matrix.kroneckerMap_apply, Matrix.one_apply]

private theorem reference_commutes :
    reference rho * jump = jump * reference rho := by
  rw [reference_value, jump_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal_mul, Matrix.mul_diagonal, diagReal, refValues]

private theorem trace_embedded (A B G : Mat) :
    (G * A * G * B).trace = (A * (G * B * G)).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm G (A * (G * B))

-- With equal rates the same spectral sum computes the trace for both references.
private theorem cubic_trace_eq_identity :
    (mpow rho (2 / 3) * (mpow (reference rho) (1 / 6) *
      generator (embeddedPower (reference rho) rho (1 / 3)) *
      mpow (reference rho) (1 / 6))).trace.re =
    (mpow rho (2 / 3) * generator (mpow rho (1 / 3))).trace.re := by
  have hratio : ((1 / 2 : ℝ) / (1 / 2)) = 1 := by norm_num
  have hdet : IsUnit (reference rho).det :=
    (reference rho).isUnit_iff_isUnit_det.mp reference_pos.isUnit
  have hmodular :
      reference rho * jump * (reference rho)⁻¹ = ((1 / 2 : ℝ) / (1 / 2)) • jump := by
    rw [reference_commutes, Matrix.mul_nonsing_inv_cancel_right _ _ hdet, hratio, one_smul]
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hs : (1 : ℝ) < 3 := by norm_num
  have href := generatorTrace_eq_cosh reference_pos rho_pos.posSemidef
    (fun _ : Unit => 1 / 2) (fun _ : Unit => 1 / 2) (fun _ : Unit => jump)
    hs (fun _ => hpos) (fun _ => hpos) (fun _ => hmodular)
  have hone := generatorTrace_eq_cosh (D := (1 : Mat)) Matrix.PosDef.one rho_pos.posSemidef
    (fun _ : Unit => 1 / 2) (fun _ : Unit => 1 / 2) (fun _ : Unit => jump)
    hs (fun _ => hpos) (fun _ => hpos) (fun _ => by
      simp only [hratio, one_smul, Matrix.one_mul, inv_one, Matrix.mul_one])
  have htrace := Eq.trans href (Eq.symm hone)
  have hpow (p : ℝ) : mpow rho p = CFC.rpow rho p :=
    (CFC.rpow_eq_cfc_real rho_pos.posSemidef.nonneg).symm
  have hroot_nonneg : 0 ≤ CFC.rpow rho (1 / 3) := CFC.rpow_nonneg
  have hpower : mpow (mpow rho (1 / 3)) 2 = mpow rho (2 / 3) := by
    rw [hpow (1 / 3), hpow (2 / 3), mpow, ← CFC.rpow_eq_cfc_real hroot_nonneg]
    change (rho ^ (1 / 3 : ℝ)) ^ (2 : ℝ) = rho ^ (2 / 3 : ℝ)
    rw [CFC.rpow_rpow_of_exponent_nonneg rho (1 / 3) 2 (by norm_num) (by norm_num)
      rho_pos.posSemidef.nonneg, show (1 / 3 * 2 : ℝ) = 2 / 3 by norm_num]
  have hidentity (p : ℝ) : mpow (1 : Mat) p = 1 := by
    rw [mpow, ← CFC.rpow_eq_cfc_real (zero_le_one : (0 : Mat) ≤ 1)]
    exact CFC.one_rpow
  apply mul_left_cancel₀ (by norm_num : (1 / 4 : ℝ) ≠ 0)
  simpa only [Fintype.sum_unique, show (1 / (2 * 3) : ℝ) = 1 / 6 by norm_num,
    show (3 - 1 : ℝ) = 2 by norm_num, hpower, hidentity, Matrix.one_mul, Matrix.mul_one,
    generator, embeddedPower, show (-(1 / 3) / 2 : ℝ) = -(1 / 6) by norm_num] using htrace

private theorem cubic_identity_trace :
    (mpow rho (2 / 3) * generator (mpow rho (1 / 3))).trace.re =
      (rho * (jumpᴴ * jump)).trace.re + (rho * (jump * jumpᴴ)).trace.re -
        (mpow rho (2 / 3) * (jumpᴴ * mpow rho (1 / 3) * jump)).trace.re -
        (mpow rho (2 / 3) * (jump * mpow rho (1 / 3) * jumpᴴ)).trace.re := by
  let M := mpow rho (1 / 3)
  let N := mpow rho (2 / 3)
  have hNM : N * M = rho := by
    change mpow rho (2 / 3) * mpow rho (1 / 3) = rho
    rw [mpow_add rho_pos, show (2 / 3 + 1 / 3 : ℝ) = 1 by norm_num, mpow_one rho_pos.isHermitian]
  have hMN : M * N = rho := by
    change mpow rho (1 / 3) * mpow rho (2 / 3) = rho
    rw [mpow_add rho_pos, show (1 / 3 + 2 / 3 : ℝ) = 1 by norm_num, mpow_one rho_pos.isHermitian]
  have hLoss (P : Mat) :
      (N * ((1 / 2 : ℝ) • (P * M + M * P))).trace.re = (rho * P).trace.re := by
    have hLeft : (N * (P * M)).trace = (rho * P).trace := by
      rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc M N P, hMN]
    have hRight : (N * (M * P)).trace = (rho * P).trace := by
      rw [← Matrix.mul_assoc, hNM]
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
      Complex.smul_re, Complex.add_re, smul_eq_mul, hLeft, hRight]
    ring
  have hGenerator :
      generator M =
        ((1 / 2 : ℝ) • ((jumpᴴ * jump) * M + M * (jumpᴴ * jump)) - jumpᴴ * M * jump) +
        ((1 / 2 : ℝ) • (((jumpᴴ)ᴴ * jumpᴴ) * M + M * ((jumpᴴ)ᴴ * jumpᴴ)) -
          (jumpᴴ)ᴴ * M * jumpᴴ) := by
    simp only [generator, pairedGenerator, show (2 * (1 / 2) : ℝ) = 1 by norm_num, one_smul]
    rfl
  change (N * generator M).trace.re =
    (rho * (jumpᴴ * jump)).trace.re + (rho * (jump * jumpᴴ)).trace.re -
      (N * (jumpᴴ * M * jump)).trace.re - (N * (jump * M * jumpᴴ)).trace.re
  rw [hGenerator]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, hLoss]
  ring

private theorem cubic_embedded_trace :
    energy rho (1 / 3) =
      ((rho * (jumpᴴ * jump)).trace.re + (rho * (jump * jumpᴴ)).trace.re -
        (mpow rho (2 / 3) * (jumpᴴ * mpow rho (1 / 3) * jump)).trace.re -
        (mpow rho (2 / 3) * (jump * mpow rho (1 / 3) * jumpᴴ)).trace.re) /
        (4 * (1 / 3) * (1 - 1 / 3)) := by
  have hleft : mpow (reference rho) (1 / 2) * mpow (reference rho) (-(1 - 1 / 3) / 2) =
      mpow (reference rho) (1 / 6) := by
    rw [mpow_add reference_pos, show (1 / 2 + -(1 - 1 / 3) / 2 : ℝ) = 1 / 6 by norm_num]
  have hright : mpow (reference rho) (-(1 - 1 / 3) / 2) * mpow (reference rho) (1 / 2) =
      mpow (reference rho) (1 / 6) := by
    rw [mpow_add reference_pos, show (-(1 - 1 / 3) / 2 + 1 / 2 : ℝ) = 1 / 6 by norm_num]
  have hsandwich :
      mpow (reference rho) (1 / 2) * embeddedPower (reference rho) rho (1 - 1 / 3) *
        mpow (reference rho) (1 / 2) =
      mpow (reference rho) (1 / 6) * mpow rho (2 / 3) * mpow (reference rho) (1 / 6) := by
    unfold embeddedPower
    simp only [Matrix.mul_assoc, hright]
    rw [← Matrix.mul_assoc _ (mpow (reference rho) _) (mpow rho _ * _), hleft,
      show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num]
  unfold energy
  dsimp only
  rw [hsandwich, trace_embedded, cubic_trace_eq_identity, cubic_identity_trace]

private theorem jump_projections : jumpᴴ * jump + jump * jumpᴴ = 1 := by
  rw [jump_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
      Fin.sum_univ_four] <;>
    norm_num [Matrix.one_apply, Complex.star_def]

private theorem mixed_corner (a b c d t e f g h u : ℝ) :
    (corner a b c d t * (jumpᴴ * corner e f g h u * jump)).trace.re +
    (corner a b c d t * (jump * corner e f g h u * jumpᴴ)).trace.re =
      c * e + d * f + a * g + b * h := by
  rw [jump_entries]
  simp only [corner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four]
  norm_num [Complex.star_def, Complex.add_re, Complex.mul_re]
  ring

private theorem raw_pos : raw.PosDef := by
  rw [raw_spectral]
  apply spectral_pos
  intro i
  fin_cases i <;> norm_num [rawValues]

private theorem mpow_raw (r : ℝ) :
    mpow raw r = spectral (fun i => rawValues i ^ r) := by
  rw [raw_spectral, mpow, cfc_spectral (fun i => by fin_cases i <;> norm_num [rawValues])]

private theorem twentySeven_cuberoot : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
  rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) by norm_num,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private theorem two_thirds (a : ℝ) (ha : 0 ≤ a) :
    a ^ (2 / 3 : ℝ) = (a ^ (1 / 3 : ℝ)) ^ (2 : ℕ) := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

private theorem raw_cube_root :
    mpow raw (1 / 3) =
      corner (14 / 13) ((26 : ℝ) ^ (1 / 3 : ℝ)) ((2 : ℝ) ^ (1 / 3 : ℝ))
        (38 / 13) (5 / 13) := by
  rw [mpow_raw, spectral_entries]
  norm_num [rawValues, twentySeven_cuberoot]

private theorem raw_two_thirds :
    mpow raw (2 / 3) =
      corner (17 / 13) (((26 : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℕ))
        (((2 : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℕ)) (113 / 13) (20 / 13) := by
  rw [mpow_raw, spectral_entries]
  norm_num [rawValues, two_thirds, twentySeven_cuberoot]

private theorem normalization_power (r : ℝ) (hr : 0 ≤ r) :
    mpow rho r = (1 / 56 : ℝ) ^ r • mpow raw r :=
  mpow_smul_of_nonneg raw_pos.posSemidef.nonneg (by norm_num) hr

private theorem energy_exact : 56 * energy rho (1 / 3) = scaledEnergy := by
  rw [cubic_embedded_trace]
  have hproj : (rho * (jumpᴴ * jump)).trace.re + (rho * (jump * jumpᴴ)).trace.re = 1 := by
    rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add, jump_projections, mul_one,
      trace_rho, Complex.one_re]
  have hnorm : (1 / 56 : ℝ) ^ (2 / 3 : ℝ) * (1 / 56 : ℝ) ^ (1 / 3 : ℝ) = 1 / 56 := by
    rw [← Real.rpow_add (by norm_num : 0 < (1 / 56 : ℝ))]
    norm_num
  rw [hproj, normalization_power (1 / 3) (by norm_num),
    normalization_power (2 / 3) (by norm_num)]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul]
  rw [sub_sub, ← mul_add, mul_comm ((1 / 56 : ℝ) ^ (1 / 3 : ℝ)), hnorm,
    raw_cube_root, raw_two_thirds, mixed_corner]
  unfold scaledEnergy
  ring

private theorem spectral_trace_product (v w : Fin 4 → ℝ) :
    (spectral v * spectral w).trace.re = ∑ i, v i * w i := by
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  unfold spectral
  rw [show U.val * diagReal v * U.valᴴ * (U.val * diagReal w * U.valᴴ) =
      U.val * (diagReal v * diagReal w) * U.valᴴ by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.valᴴ U.val, hU, one_mul],
    Matrix.trace_mul_cycle, hU, one_mul]
  simp [diagReal, Matrix.diagonal_mul_diagonal, Matrix.trace, ← Complex.ofReal_mul, Complex.re_sum]

private theorem entropy_trace_rho :
    (rho * CFC.log rho).trace.re = ∑ i, stateValues i * Real.log (stateValues i) := by
  rw [rho_spectral, CFC.log,
    cfc_spectral (fun i => by fin_cases i <;> norm_num [stateValues, rawValues])]
  exact spectral_trace_product _ _

private theorem entropy_trace_reference :
    (rho * CFC.log (reference rho)).trace.re = ∑ i, refValues i * Real.log (refValues i) := by
  rw [reference_value, CFC.log]
  have hlog : cfc Real.log (diagReal refValues) =
      diagReal (fun i => Real.log (refValues i)) := by
    simpa only [diagReal, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) refValues Real.log
  rw [hlog]
  have hdiag (i : Fin 4) : rho i i = (refValues i : ℂ) := by
    fin_cases i <;> norm_num [rho, raw, refValues, Matrix.smul_apply, Complex.real_smul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, diagReal, hdiag,
    ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

private theorem entropy_exact : 56 * entropy = scaledEntropy := by
  change 56 * (rho * (CFC.log rho - CFC.log (reference rho))).trace.re = _
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, entropy_trace_rho,
    entropy_trace_reference]
  have h₂ : Real.log (1 / 28) = Real.log 2 - Real.log 56 := by
    calc
      _ = Real.log (2 / 56) := by norm_num
      _ = _ := Real.log_div (by norm_num) (by norm_num)
  have h₂₆ : Real.log (13 / 28) = Real.log 26 - Real.log 56 := by
    calc
      _ = Real.log (26 / 56) := by norm_num
      _ = _ := Real.log_div (by norm_num) (by norm_num)
  norm_num [Fin.sum_univ_four, stateValues, rawValues, refValues, scaledEntropy, h₂, h₂₆,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (56 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (56 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (26 : ℝ) ≠ 0) (by norm_num : (56 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (27 : ℝ) ≠ 0) (by norm_num : (56 : ℝ) ≠ 0)]
  ring

private theorem witness_separable :
    IsSeparable (unflatten rho) := by
  let z : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]
  let x : Fin 4 → Q → ℂ := fun k => ![1, z k]
  let y : Fin 4 → Q → ℂ := fun k => ![1, 5 * star (z k)]
  let mixed : Matrix Q Q ℂ := (1 / 2 : ℝ) • (1 : Matrix Q Q ℂ)
  let p : Fin 5 → ℝ := Fin.cons (4 / 56) (fun _ => 13 / 56)
  let A : Fin 5 → Matrix Q Q ℂ := Fin.cons mixed
    (fun k => (1 / 2 : ℝ) • Matrix.vecMulVec (x k) (star (x k)))
  let B : Fin 5 → Matrix Q Q ℂ := Fin.cons mixed
    (fun k => (1 / 26 : ℝ) • Matrix.vecMulVec (y k) (star (y k)))
  refine ⟨5, p, A, B, ?_, ?_, ?_, ?_⟩
  · intro t
    cases t using Fin.cases <;> norm_num [p]
  · rw [Fin.sum_univ_succ]
    simp only [p, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_four]
    norm_num
  · intro t
    cases t using Fin.cases with
    | zero =>
      have hm : mixed.PosSemidef ∧ mixed.trace = 1 := by
        refine ⟨Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2), ?_⟩
        norm_num [mixed, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
          Matrix.one_apply, Matrix.smul_apply, Complex.real_smul]
      simpa only [A, B, Fin.cons_zero] using And.intro hm hm
    | succ k =>
      simp only [A, B, Fin.cons_succ]
      refine ⟨⟨(Matrix.posSemidef_vecMulVec_self_star (x k)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2), ?_⟩,
        ⟨(Matrix.posSemidef_vecMulVec_self_star (y k)).smul
          (by norm_num : (0 : ℝ) ≤ 1 / 26), ?_⟩⟩ <;>
        simp only [Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct, Fin.sum_univ_two,
          Pi.star_apply] <;>
        fin_cases k <;>
        norm_num [x, y, z, Complex.star_def,
          Complex.real_smul, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
          Complex.div_re, Complex.div_im, Complex.normSq_apply]
  · apply Matrix.ext
    rintro ⟨i, a⟩ ⟨j, b⟩
    rw [Fin.sum_univ_succ, Fin.sum_univ_four]
    simp only [unflatten, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      rho, p, A, B, mixed, Fin.cons_zero, Fin.cons_succ, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.real_smul, smul_eq_mul]
    fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
      norm_num [productBasis, finProdFinEquiv, raw, x, y, z, Matrix.one_apply,
        Complex.star_def, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- The sharp one-mode coefficient fails on the faithful separable witness. -/
theorem result : ¬ claim := by
  intro h
  have hbound := h rho rho_pos rho_marginals.1 rho_marginals.2 witness_separable
  change entropy / 2 ≤ energy rho (1 / 3) at hbound
  have he := scaled_energy_lt
  have hh := scaled_entropy_half_gt
  rw [← energy_exact] at he
  rw [← entropy_exact] at hh
  linarith

end D5.S3.Quantum.Semigroups.WuCompleteCubicRefutation
