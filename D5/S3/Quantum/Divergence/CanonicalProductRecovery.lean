/- GID: D5/S3/Quantum/Divergence/CanonicalProductRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CanonicalProductRecovery
   mirror-E: none(waiver:general-operator-identity)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.HermitianFunctionalCalculus]
   utility: none
   digest: Actual marginal support cancels singular tensor logarithms in product recovery. -/

import D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.UnitaryGroup

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0; full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Authors of the adapted source: Alex Meiburg

Adapted substantive sources, at Physlib b9043cc548ef6d63a28454cf3a57fb12a0c2e142:
QuantumInfo/ForMathlib/Isometry.lean, cfc_eq_any_isometry;
QuantumInfo/ForMathlib/HermitianMat/LogExp.lean, log_kron_with_proj;
QuantumInfo/Entropy/Relative.lean, fixed_support_kron_right and its weighted cancellation.
The adaptation uses canonical receiving states and their existing actual partial traces.
Finite trace contractions and CFC transport are proof-local normalizations.
Retire the adapted portions when this repository's own pinned Mathlib supplies
equivalent declarations, replacing their uses directly with those declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.CanonicalProductRecovery

open scoped BigOperators Kronecker Matrix ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- Product-reference recovery on the actual joint density and its actual marginal.
The joint density and its marginal may be singular. Faithfulness is required only
of the two reference factors. No chosen eigenbasis alignment is an assumption. -/
theorem canonical_product_recovery_chain
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho : DensityState (a × b)) (gammaA : DensityState a) (gammaB : DensityState b)
    (hA : (CStarMatrix.ofMatrix.symm gammaA.1).PosDef)
    (hB : (CStarMatrix.ofMatrix.symm gammaB.1).PosDef) :
    let rhoA := fromLegacyDensityState (marginalRight (toLegacyDensityState rho))
    let recovered := fromLegacyDensityState
      (productState (toLegacyDensityState rhoA) (toLegacyDensityState gammaB))
    let reference := fromLegacyDensityState
      (productState (toLegacyDensityState gammaA) (toLegacyDensityState gammaB))
    SupportContained rho recovered ∧
    finiteTraceLogRelativeEntropy rho reference -
        finiteTraceLogRelativeEntropy rhoA gammaA =
      finiteTraceLogRelativeEntropy rho recovered ∧
    extendedQuantumRelativeEntropy rho reference =
      extendedQuantumRelativeEntropy rho recovered +
        extendedQuantumRelativeEntropy rhoA gammaA ∧
    extendedQuantumRelativeEntropy rho reference ≠ ⊤ ∧
    extendedQuantumRelativeEntropy rho recovered ≠ ⊤ ∧
    extendedQuantumRelativeEntropy rhoA gammaA ≠ ⊤ ∧
    extendedQuantumRelativeEntropy
      (fromLegacyDensityState (marginalLeft (toLegacyDensityState rho))) gammaB ≠ ⊤ ∧
    finiteTraceLogRelativeEntropy rho recovered =
      quantumMutualInformation (toLegacyDensityState rho) +
        finiteTraceLogRelativeEntropy
          (fromLegacyDensityState (marginalLeft (toLegacyDensityState rho))) gammaB := by
  classical
  -- Trace one discharges the impossible empty-density carrier.
  letI : Nonempty a := by
    rcases isEmpty_or_nonempty a with hn | hn
    · letI := hn
      have hz : Matrix.trace gammaA.1 = 0 := by simp [Matrix.trace]
      exact False.elim (one_ne_zero (gammaA.2.2.symm.trans hz))
    · exact hn
  letI : Nonempty b := by
    rcases isEmpty_or_nonempty b with hn | hn
    · letI := hn
      have hz : Matrix.trace gammaB.1 = 0 := by simp [Matrix.trace]
      exact False.elim (one_ne_zero (gammaB.2.2.symm.trans hz))
    · exact hn
  dsimp only
  let rhoA := fromLegacyDensityState (marginalRight (toLegacyDensityState rho))
  let recovered := fromLegacyDensityState
    (productState (toLegacyDensityState rhoA) (toLegacyDensityState gammaB))
  let reference := fromLegacyDensityState
    (productState (toLegacyDensityState gammaA) (toLegacyDensityState gammaB))
  let M : Matrix (a × b) (a × b) ℂ := CStarMatrix.ofMatrix.symm rho.1
  let R : Matrix a a ℂ := partialTraceRight M
  let C : Matrix a a ℂ := CStarMatrix.ofMatrix.symm gammaA.1
  let B : Matrix b b ℂ := CStarMatrix.ofMatrix.symm gammaB.1
  let chi : ℝ → ℝ := fun t => if t = 0 then 0 else 1
  have hM : M.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
  have hR : R.PosSemidef := partialTraceRight_posSemidef hM
  have hC : C.PosDef := hA
  have hBB : B.PosDef := hB
  -- Arbitrary diagonalization: intertwining handles repeated eigenvalues.
  -- The substantive intertwining proof is adapted from the exact donor source.
  have anyCFC : ∀ (X : Matrix (a × b) (a × b) ℂ) (hX : X.IsHermitian)
        (U : Matrix.unitaryGroup (a × b) ℂ) (d : (a × b) → ℝ),
      X = (U : Matrix (a × b) (a × b) ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
        star (U : Matrix (a × b) (a × b) ℂ) →
      ∀ f : ℝ → ℝ, cfc f X = (U : Matrix (a × b) (a × b) ℂ) *
        Matrix.diagonal (fun i => (f (d i) : ℂ)) * star (U : Matrix (a × b) (a × b) ℂ) := by
    intro X hX U d hXD f
    rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    let V : Matrix (a × b) (a × b) ℂ := hX.eigenvectorUnitary
    let W : Matrix (a × b) (a × b) ℂ := star (U : Matrix (a × b) (a × b) ℂ) * V
    have hVV : V * star V = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
    have hVsV : star V * V = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
    have hUU : (U : Matrix (a × b) (a × b) ℂ) * star (U : Matrix (a × b) (a × b) ℂ) = 1 :=
      Unitary.coe_mul_star_self U
    have hUsU : star (U : Matrix (a × b) (a × b) ℂ) * (U : Matrix (a × b) (a × b) ℂ) = 1 :=
      Unitary.coe_star_mul_self U
    have hEV : X = V * Matrix.diagonal (fun j => (hX.eigenvalues j : ℂ)) * star V := by
      simpa [V, Unitary.conjStarAlgAut_apply, Function.comp_def] using hX.spectral_theorem
    have hi : Matrix.diagonal (fun i => (d i : ℂ)) * W =
        W * Matrix.diagonal (fun j => (hX.eigenvalues j : ℂ)) := by
      have hh := congrArg (fun T : Matrix (a × b) (a × b) ℂ => star (U : Matrix (a × b) (a × b) ℂ) * T * V)
        (hXD.symm.trans hEV)
      simp only [← Matrix.mul_assoc, hUsU, Matrix.one_mul] at hh
      simp only [Matrix.mul_assoc, hVsV, Matrix.mul_one] at hh
      simpa only [W, Matrix.mul_assoc] using hh
    have hif : Matrix.diagonal (fun i => (f (d i) : ℂ)) * W =
        W * Matrix.diagonal (fun j => (f (hX.eigenvalues j) : ℂ)) := by
      ext i j
      have hij := congrFun (congrFun hi i) j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij ⊢
      by_cases hd : d i = hX.eigenvalues j
      · simp [hd, mul_comm]
      · have hn : (d i : ℂ) - (hX.eigenvalues j : ℂ) ≠ 0 := by
          exact sub_ne_zero.mpr (Complex.ofReal_injective.ne hd)
        have hz : ((d i : ℂ) - (hX.eigenvalues j : ℂ)) * W i j = 0 := by
          calc
            _ = (d i : ℂ) * W i j - W i j * (hX.eigenvalues j : ℂ) := by ring
            _ = 0 := sub_eq_zero.mpr hij
        have hw : W i j = 0 := (mul_eq_zero.mp hz).resolve_left hn
        simp [hw]
    have hUV : (U : Matrix (a × b) (a × b) ℂ) * W = V := by
      simp [W, ← Matrix.mul_assoc, hUU]
    have hWVs : W * star V = star (U : Matrix (a × b) (a × b) ℂ) := by
      simp [W, Matrix.mul_assoc, hVV]
    change V * Matrix.diagonal (fun j => (f (hX.eigenvalues j) : ℂ)) * star V = _
    calc
      _ = ((U : Matrix (a × b) (a × b) ℂ) * W) *
          Matrix.diagonal (fun j => (f (hX.eigenvalues j) : ℂ)) * star V := by rw [hUV]
      _ = (U : Matrix (a × b) (a × b) ℂ) *
          (W * Matrix.diagonal (fun j => (f (hX.eigenvalues j) : ℂ))) * star V := by
        simp only [Matrix.mul_assoc]
      _ = (U : Matrix (a × b) (a × b) ℂ) *
          (Matrix.diagonal (fun i => (f (d i) : ℂ)) * W) * star V := by rw [← hif]
      _ = ((U : Matrix (a × b) (a × b) ℂ) * Matrix.diagonal (fun i => (f (d i) : ℂ))) *
          (W * star V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWVs]
  have tensor_hermitian : ∀ {X : Matrix a a ℂ} {Y : Matrix b b ℂ},
      X.IsHermitian → Y.IsHermitian → (X ⊗ₖ Y).IsHermitian := by
    intro X Y hX hY
    exact D5.S3.Quantum.Information.PartialTraceMutualInformation.isHermitian_kronecker hX hY
  -- No tensor eigenvalue-list alignment: use the actual product unitary.
  have tensorCFC : ∀ (X : Matrix a a ℂ) (Y : Matrix b b ℂ)
      (hX : X.IsHermitian) (hY : Y.IsHermitian) (f : ℝ → ℝ),
      cfc f (X ⊗ₖ Y) =
        ((hX.eigenvectorUnitary : Matrix a a ℂ) ⊗ₖ
          (hY.eigenvectorUnitary : Matrix b b ℂ)) *
        Matrix.diagonal (fun p : a × b => (f (hX.eigenvalues p.1 * hY.eigenvalues p.2) : ℂ)) *
        star ((hX.eigenvectorUnitary : Matrix a a ℂ) ⊗ₖ
          (hY.eigenvectorUnitary : Matrix b b ℂ)) := by
    intro X Y hX hY f
    let U : Matrix.unitaryGroup (a × b) ℂ :=
      ⟨(hX.eigenvectorUnitary : Matrix a a ℂ) ⊗ₖ (hY.eigenvectorUnitary : Matrix b b ℂ),
        Matrix.kronecker_mem_unitary hX.eigenvectorUnitary.2 hY.eigenvectorUnitary.2⟩
    apply anyCFC (X ⊗ₖ Y) (tensor_hermitian hX hY) U
      (fun p => hX.eigenvalues p.1 * hY.eigenvalues p.2) _ f
    simpa [U, Complex.ofReal_mul] using
      D5.S3.Quantum.Information.PartialTraceMutualInformation.kronecker_eq_conj_diagonal_eigenvalues hX hY
  have logTensor : ∀ (X : Matrix a a ℂ) (Y : Matrix b b ℂ)
      (hX : X.IsHermitian) (hY : Y.IsHermitian),
      cfc Real.log (X ⊗ₖ Y) =
        cfc Real.log X ⊗ₖ cfc chi Y + cfc chi X ⊗ₖ cfc Real.log Y := by
    intro X Y hX hY
    rw [tensorCFC X Y hX hY Real.log, hX.cfc_eq Real.log, hY.cfc_eq Real.log,
      hX.cfc_eq chi, hY.cfc_eq chi]
    simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal]
    rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
    congr 2
    ext p q
    by_cases hpq : p = q
    · subst q
      simp only [Matrix.diagonal_apply, if_true]
      by_cases hx : hX.eigenvalues p.1 = 0
      · simp [chi, hx]
      by_cases hy : hY.eigenvalues p.2 = 0
      · simp [chi, hy]
      simp [chi, hx, hy, Real.log_mul hx hy]
    · simp [Matrix.diagonal_apply, hpq]
  have supportDefA : ∀ (X : Matrix a a ℂ) (hX : X.PosDef), cfc chi X = 1 := by
    intro X hX
    rw [hX.isHermitian.cfc_eq chi, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have hd : Matrix.diagonal (fun i => (chi (hX.isHermitian.eigenvalues i) : ℂ)) = 1 := by
      ext i j
      simp [chi, ne_of_gt (hX.eigenvalues_pos i), Matrix.diagonal_apply, Matrix.one_apply]
    rw [show Matrix.diagonal (RCLike.ofReal ∘ chi ∘ hX.isHermitian.eigenvalues) = 1 from hd]
    simp
  have supportDefB : ∀ (X : Matrix b b ℂ) (hX : X.PosDef), cfc chi X = 1 := by
    intro X hX
    rw [hX.isHermitian.cfc_eq chi, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have hd : Matrix.diagonal (fun i => (chi (hX.isHermitian.eigenvalues i) : ℂ)) = 1 := by
      ext i j
      simp [chi, ne_of_gt (hX.eigenvalues_pos i), Matrix.diagonal_apply, Matrix.one_apply]
    rw [show Matrix.diagonal (RCLike.ofReal ∘ chi ∘ hX.isHermitian.eigenvalues) = 1 from hd]
    simp
  have contraction : ∀ (T : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ),
      Matrix.trace (T * (X ⊗ₖ (1 : Matrix b b ℂ))) =
        Matrix.trace (partialTraceRight T * X) := by
    intro T X
    simp [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, partialTraceRight,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have contractionLeft : ∀ (T : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ),
      Matrix.trace (T * ((1 : Matrix a a ℂ) ⊗ₖ Y)) =
        Matrix.trace (partialTraceLeft T * Y) := by
    intro T Y
    simp [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, partialTraceLeft,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  -- The marginal zero directions really annihilate the same joint matrix.
  let U : Matrix a a ℂ := hR.isHermitian.eigenvectorUnitary
  let W : Matrix (a × b) (a × b) ℂ := U ⊗ₖ (1 : Matrix b b ℂ)
  let T : Matrix (a × b) (a × b) ℂ := star W * M * W
  let Q : Matrix (a × b) (a × b) ℂ := cfc chi R ⊗ₖ (1 : Matrix b b ℂ)
  have hUsU : star U * U = 1 := Unitary.coe_star_mul_self hR.isHermitian.eigenvectorUnitary
  have hUUs : U * star U = 1 := Unitary.coe_mul_star_self hR.isHermitian.eigenvectorUnitary
  let Uw : Matrix.unitaryGroup (a × b) ℂ :=
    ⟨W, Matrix.kronecker_mem_unitary hR.isHermitian.eigenvectorUnitary.2
      (Matrix.unitaryGroup b ℂ).one_mem⟩
  have hWsW : star W * W = 1 := Unitary.coe_star_mul_self Uw
  have hWWs : W * star W = 1 := Unitary.coe_mul_star_self Uw
  have hstarW : star W = star U ⊗ₖ (1 : Matrix b b ℂ) := by
    dsimp only [W]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
    rfl
  have hT : T.PosSemidef := by
    simpa [T, Matrix.star_eq_conjTranspose] using hM.conjTranspose_mul_mul_same W
  have hRotEntry : ∀ (i k : a) (j l : b), T (i,j) (k,l) =
      ∑ q : a, ∑ p : a, star U i p * M (p,j) (q,l) * U q k := by
    intro i k j l
    simp [T, W, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc, apply_ite, ite_mul]
    exact Finset.sum_comm
  have hMarginal : partialTraceRight T = star U * R * U := by
    ext i k
    simp only [partialTraceRight, hRotEntry, Matrix.mul_apply, R,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
  have hRotR : star U * R * U =
      Matrix.diagonal (fun i => (hR.isHermitian.eigenvalues i : ℂ)) := by
    have hs : R = U * Matrix.diagonal (fun i => (hR.isHermitian.eigenvalues i : ℂ)) *
        star U := by
      simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hR.isHermitian.spectral_theorem
    have hh := congrArg (fun X : Matrix a a ℂ => star U * X * U) hs
    simp only [← Matrix.mul_assoc, hUsU, Matrix.one_mul] at hh
    simp only [Matrix.mul_assoc, hUsU, Matrix.mul_one] at hh
    simpa only [Matrix.mul_assoc] using hh
  have hZeroColumn : ∀ i : a, hR.isHermitian.eigenvalues i = 0 →
      ∀ j : b, ∀ p : a × b, T p (i,j) = 0 := by
    intro i hi j p
    have hs : ∑ j : b, T (i,j) (i,j) = 0 := by
      have hh := congrFun (congrFun (hMarginal.trans hRotR) i) i
      simpa [partialTraceRight, hi] using hh
    have hd : T (i,j) (i,j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hT.diag_nonneg)).mp hs j (Finset.mem_univ j)
    have hquad : star (Pi.single (i,j) (1 : ℂ)) ⬝ᵥ
        T *ᵥ Pi.single (i,j) 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hd
    have hz := (hT.dotProduct_mulVec_zero_iff (Pi.single (i,j) 1)).mp hquad
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hz p
  let D : Matrix (a × b) (a × b) ℂ :=
    Matrix.diagonal (fun p => (chi (hR.isHermitian.eigenvalues p.1) : ℂ))
  have hTD : T * D = T := by
    ext p q
    simp only [D, Matrix.mul_diagonal]
    by_cases hi : hR.isHermitian.eigenvalues q.1 = 0
    · rw [hZeroColumn q.1 hi q.2 p]
      simp
    · simp [chi, hi]
  have hQ : Q = W * D * star W := by
    let DA : Matrix a a ℂ := Matrix.diagonal
      (fun i => (chi (hR.isHermitian.eigenvalues i) : ℂ))
    have hd : DA ⊗ₖ (1 : Matrix b b ℂ) = D := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
      simp only [DA, D, mul_one]
    dsimp only [Q]
    rw [hR.isHermitian.cfc_eq chi, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, hstarW]
    change (U * DA * star U) ⊗ₖ (1 : Matrix b b ℂ) =
      (U ⊗ₖ (1 : Matrix b b ℂ)) * D * (star U ⊗ₖ (1 : Matrix b b ℂ))
    rw [← hd, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul]
  have hMQ : M * Q = M := by
    rw [hQ]
    have hh := congrArg (fun X : Matrix (a × b) (a × b) ℂ => W * X * star W) hTD
    dsimp only [T] at hh
    simp only [← Matrix.mul_assoc, hWWs, Matrix.one_mul] at hh
    simp only [Matrix.mul_assoc, hWWs, Matrix.mul_one] at hh
    simpa only [Matrix.mul_assoc] using hh
  -- CFC support annihilates exactly the zero eigenvalue directions.
  have kernelSupport : ∀ (X : Matrix (a × b) (a × b) ℂ) (hX : X.IsHermitian) (v : (a × b) → ℂ),
      X *ᵥ v = 0 → cfc chi X *ᵥ v = 0 := by
    intro X hX v hv
    let V : Matrix (a × b) (a × b) ℂ := hX.eigenvectorUnitary
    let z := star V *ᵥ v
    have hVsV : star V * V = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
    have hs : X = V * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * star V := by
      simpa [V, Unitary.conjStarAlgAut_apply, Function.comp_def] using hX.spectral_theorem
    have hsV : star V * X = Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * star V := by
      have hh := congrArg (fun Y : Matrix (a × b) (a × b) ℂ => star V * Y) hs
      simp only [← Matrix.mul_assoc, hVsV, Matrix.one_mul] at hh
      exact hh
    have hz : Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) *ᵥ z = 0 := by
      have hh := congrArg (fun w : (a × b) → ℂ => star V *ᵥ w) hv
      rw [Matrix.mulVec_mulVec, hsV, ← Matrix.mulVec_mulVec] at hh
      simpa only [z, Matrix.mulVec_zero] using hh
    have hfz : Matrix.diagonal (fun i => (chi (hX.eigenvalues i) : ℂ)) *ᵥ z = 0 := by
      ext i
      have hh := congrFun hz i
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at hh ⊢
      by_cases hi : hX.eigenvalues i = 0
      · simp [chi, hi]
      · have hzi : z i = 0 := (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hi)
        simp [hzi]
    rw [hX.cfc_eq chi, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    change (V * Matrix.diagonal (fun i => (chi (hX.eigenvalues i) : ℂ)) * star V) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change V *ᵥ (Matrix.diagonal (fun i => (chi (hX.eigenvalues i) : ℂ)) *ᵥ z) = 0
    rw [hfz, Matrix.mulVec_zero]
  have hKronSupport : cfc chi (R ⊗ₖ B) = Q := by
    rw [tensorCFC R B hR.isHermitian hBB.isHermitian chi]
    dsimp [Q]
    rw [← supportDefB B hBB, hR.isHermitian.cfc_eq chi, hBB.isHermitian.cfc_eq chi]
    simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal]
    congr 2
    ext p q
    by_cases hpq : p = q
    · subst q
      simp only [Matrix.diagonal_apply, if_true]
      by_cases hr : hR.isHermitian.eigenvalues p.1 = 0 <;>
        by_cases hb : hBB.isHermitian.eigenvalues p.2 = 0 <;>
        simp [chi, hr, hb, mul_eq_zero]
    · simp [Matrix.diagonal_apply, hpq]
  have hsRecovered : SupportContained rho recovered := by
    intro v hv
    change (R ⊗ₖ B) *ᵥ v = 0 at hv
    change M *ᵥ v = 0
    have hqv : Q *ᵥ v = 0 := hKronSupport ▸
      kernelSupport (R ⊗ₖ B) (tensor_hermitian hR.isHermitian hBB.isHermitian) v hv
    rw [← hMQ, ← Matrix.mulVec_mulVec, hqv, Matrix.mulVec_zero]
  have supportInDefJoint : ∀ (s t : DensityState (a × b)), (CStarMatrix.ofMatrix.symm t.1).PosDef → SupportContained s t := by
    intro s t ht v hv
    change (CStarMatrix.ofMatrix.symm t.1) *ᵥ v = 0 at hv
    have hv0 : v = 0 := Matrix.mulVec_injective_of_isUnit ht.isUnit
      (by simpa using hv)
    change (CStarMatrix.ofMatrix.symm s.1) *ᵥ v = 0
    rw [hv0, Matrix.mulVec_zero]
  have supportInDefA : ∀ (s t : DensityState a), (CStarMatrix.ofMatrix.symm t.1).PosDef → SupportContained s t := by
    intro s t ht v hv
    change (CStarMatrix.ofMatrix.symm t.1) *ᵥ v = 0 at hv
    have hv0 : v = 0 := Matrix.mulVec_injective_of_isUnit ht.isUnit
      (by simpa using hv)
    change (CStarMatrix.ofMatrix.symm s.1) *ᵥ v = 0
    rw [hv0, Matrix.mulVec_zero]
  have supportInDefB : ∀ (s t : DensityState b), (CStarMatrix.ofMatrix.symm t.1).PosDef → SupportContained s t := by
    intro s t ht v hv
    change (CStarMatrix.ofMatrix.symm t.1) *ᵥ v = 0 at hv
    have hv0 : v = 0 := Matrix.mulVec_injective_of_isUnit ht.isUnit
      (by simpa using hv)
    change (CStarMatrix.ofMatrix.symm s.1) *ᵥ v = 0
    rw [hv0, Matrix.mulVec_zero]
  have hsReference : SupportContained rho reference :=
    supportInDefJoint rho reference (hC.kronecker hBB)
  have hsA : SupportContained rhoA gammaA := supportInDefA rhoA gammaA hC
  have hTransportJoint : ∀ (s : DensityState (a × b)),
      CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm s.1)) = CFC.log s.1 := by
    intro s
    let X : Matrix (a × b) (a × b) ℂ := CStarMatrix.ofMatrix.symm s.1
    have hX : X.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm s.2.1)).isHermitian
    exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log X
      (X.finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous hX (by exact hX)
  have hTransportA : ∀ (s : DensityState a),
      CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm s.1)) = CFC.log s.1 := by
    intro s
    let X : Matrix a a ℂ := CStarMatrix.ofMatrix.symm s.1
    have hX : X.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm s.2.1)).isHermitian
    exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log X
      (X.finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous hX (by exact hX)
  have hTransportB : ∀ (s : DensityState b),
      CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm s.1)) = CFC.log s.1 := by
    intro s
    let X : Matrix b b ℂ := CStarMatrix.ofMatrix.symm s.1
    have hX : X.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm s.2.1)).isHermitian
    exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log X
      (X.finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous hX (by exact hX)
  have hWeighted : Matrix.trace (M * cfc Real.log (R ⊗ₖ B)) =
      Matrix.trace (R * cfc Real.log R) +
        Matrix.trace (partialTraceLeft M * cfc Real.log B) := by
    rw [logTensor R B hR.isHermitian hBB.isHermitian, supportDefB B hBB,
      Matrix.mul_add, Matrix.trace_add, contraction]
    have hp : (cfc chi R ⊗ₖ cfc Real.log B) = Q *
        ((1 : Matrix a a ℂ) ⊗ₖ cfc Real.log B) := by
      simp [Q, ← Matrix.mul_kronecker_mul]
    rw [hp, ← Matrix.mul_assoc, hMQ, contractionLeft]
  have hCross : Matrix.trace (M * cfc Real.log (C ⊗ₖ B)) =
      Matrix.trace (R * cfc Real.log C) +
        Matrix.trace (partialTraceLeft M * cfc Real.log B) := by
    rw [logTensor C B hC.isHermitian hBB.isHermitian,
      supportDefA C hC, supportDefB B hBB,
      Matrix.mul_add, Matrix.trace_add, contraction, contractionLeft]
  have hFinite : finiteTraceLogRelativeEntropy rho reference -
      finiteTraceLogRelativeEntropy rhoA gammaA =
        finiteTraceLogRelativeEntropy rho recovered := by
    unfold finiteTraceLogRelativeEntropy
    rw [← hTransportJoint rho, ← hTransportJoint reference, ← hTransportA rhoA,
      ← hTransportA gammaA, ← hTransportJoint recovered]
    change (Matrix.trace (M * (cfc Real.log M - cfc Real.log (C ⊗ₖ B)))).re -
      (Matrix.trace (R * (cfc Real.log R - cfc Real.log C))).re =
      (Matrix.trace (M * (cfc Real.log M - cfc Real.log (R ⊗ₖ B)))).re
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [hWeighted, hCross, Complex.add_re, Complex.add_re]
    ring
  refine ⟨hsRecovered, hFinite, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [extendedQuantumRelativeEntropy_eq_coe_of_support hsReference,
      extendedQuantumRelativeEntropy_eq_coe_of_support hsRecovered,
      extendedQuantumRelativeEntropy_eq_coe_of_support hsA, ← WithTop.coe_add]
    exact congrArg (fun x : ℝ => (x : WithTop ℝ)) (by linarith [hFinite])
  · exact (extendedQuantumRelativeEntropy_ne_top_iff rho reference).mpr hsReference
  · exact (extendedQuantumRelativeEntropy_ne_top_iff rho recovered).mpr hsRecovered
  · exact (extendedQuantumRelativeEntropy_ne_top_iff rhoA gammaA).mpr hsA
  · exact (extendedQuantumRelativeEntropy_ne_top_iff _ gammaB).mpr
      (supportInDefB _ gammaB hBB)
  · let rhoB := fromLegacyDensityState (marginalLeft (toLegacyDensityState rho))
    have hEntropyA :
        D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
          (marginalRight (toLegacyDensityState rho)) =
        -(Matrix.trace (R * cfc Real.log R)).re := by
      unfold D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
      change -(Matrix.trace (R * CStarMatrix.ofMatrix.symm (CFC.log rhoA.1))).re = _
      rw [← hTransportA rhoA]
      rfl
    have hEntropyB :
        D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
          (marginalLeft (toLegacyDensityState rho)) =
        -(Matrix.trace (partialTraceLeft M * cfc Real.log (partialTraceLeft M))).re := by
      unfold D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
      change -(Matrix.trace (partialTraceLeft M *
        CStarMatrix.ofMatrix.symm (CFC.log rhoB.1))).re = _
      rw [← hTransportB rhoB]
      rfl
    have hEntropyJoint :
        D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
          (toLegacyDensityState rho) = -(Matrix.trace (M * cfc Real.log M)).re := by
      unfold D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
      change -(Matrix.trace (M * CStarMatrix.ofMatrix.symm (CFC.log rho.1))).re = _
      rw [← hTransportJoint rho]
      rfl
    unfold quantumMutualInformation
    rw [hEntropyA, hEntropyB, hEntropyJoint]
    unfold finiteTraceLogRelativeEntropy
    rw [← hTransportJoint rho, ← hTransportJoint recovered,
      ← hTransportB rhoB, ← hTransportB gammaB]
    change (Matrix.trace (M * (cfc Real.log M - cfc Real.log (R ⊗ₖ B)))).re =
      -(Matrix.trace (R * cfc Real.log R)).re +
        -(Matrix.trace (partialTraceLeft M * cfc Real.log (partialTraceLeft M))).re -
        -(Matrix.trace (M * cfc Real.log M)).re +
        (Matrix.trace (partialTraceLeft M *
          (cfc Real.log (partialTraceLeft M) - cfc Real.log B))).re
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [hWeighted, Complex.add_re]
    ring

end D5.S3.Quantum.Divergence.CanonicalProductRecovery
