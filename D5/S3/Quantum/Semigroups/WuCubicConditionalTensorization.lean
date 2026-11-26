/- GID: D5/S3/Quantum/Semigroups/WuCubicConditionalTensorization
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicConditionalTensorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wu's two-mode cubic bound for arbitrary positive semidefinite occupation blocks. -/

import D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization

open WuCubicOperatorBridge (D G GInv Mat dissipator generator)
open TwistedTwoModeOUComparison (modeJump)
open WuRepeatedMiddleCubic (alpha oneModeDeficit)
open private gibbsLow gibbsHigh gamma jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private def cubicRoot (t : ℝ) : ℝ := t ^ (1 / 3 : ℝ)

private theorem cubicRoot_cube {t : ℝ} (ht : 0 ≤ t) : cubicRoot t ^ 3 = t := by
  unfold cubicRoot
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

section MixedTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectral_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    A ^ k = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (hA.eigenvalues i : ℂ) ^ k) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  calc
    A ^ k = (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues))) ^ k :=
      congrArg (· ^ k) hA.spectral_theorem
    _ = _ := by
      rw [← map_pow, Unitary.conjStarAlgAut_apply, diagonal_pow]
      simp only [RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      congr 2

private theorem trace_cube {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 3).trace.re = ∑ i, hA.eigenvalues i ^ 3 := by
  rw [spectral_pow hA, Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem row_overlap (W : Matrix n n ℂ) (hW : W * Wᴴ = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ => (M i i).re) hW
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re]
    using h

private theorem column_overlap (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj,
    Matrix.conjTranspose_conjTranspose] using row_overlap Wᴴ
      (by rwa [Matrix.conjTranspose_conjTranspose]) j

theorem trace_diagonal_overlap (u v : n → ℝ) (W : Matrix n n ℂ) :
    (diagonal (fun i => (u i : ℂ)) * W *
      diagonal (fun i => (v i : ℂ)) * Wᴴ).trace.re =
      ∑ i, ∑ j, u i * v j * Complex.normSq (W i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum,
    Matrix.mul_apply (N := Wᴴ), Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Complex.star_def]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show (u i : ℂ) * W i j * (v j : ℂ) * (starRingEnd ℂ) (W i j) =
    ((u i : ℂ) * (v j : ℂ)) * (W i j * (starRingEnd ℂ) (W i j)) by ring,
    Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem cubic_holder {u v : n → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    {W : Matrix n n ℂ} (hrow : W * Wᴴ = 1) (hcol : Wᴴ * W = 1) :
    ∑ i, ∑ j, u i ^ 2 * v j * Complex.normSq (W i j) ≤
      cubicRoot (∑ i, u i ^ 3) ^ 2 * cubicRoot (∑ j, v j ^ 3) := by
  let c : n × n → ℝ := fun p => cubicRoot (Complex.normSq (W p.1 p.2))
  let x : n × n → ℝ := fun p => u p.1 * c p
  let y : n × n → ℝ := fun p => v p.2 * c p
  have hc (p : n × n) : 0 ≤ c p := Real.rpow_nonneg (Complex.normSq_nonneg _) _
  have hc3 (p : n × n) : c p ^ 3 = Complex.normSq (W p.1 p.2) :=
    cubicRoot_cube (Complex.normSq_nonneg _)
  have hx (p : n × n) : 0 ≤ x p := mul_nonneg (hu _) (hc p)
  have hy (p : n × n) : 0 ≤ y p := mul_nonneg (hv _) (hc p)
  have hp : (3 / 2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun p => x p ^ 2) (g := y) hp (fun p _ => sq_nonneg _) (fun p _ => hy p)
  have hpw (p : n × n) : (x p ^ 2) ^ (3 / 2 : ℝ) = x p ^ 3 := by
    rw [← Real.rpow_natCast_mul (hx p)]
    norm_num
  have hxy (p : n × n) :
      x p ^ 2 * y p = u p.1 ^ 2 * v p.2 * Complex.normSq (W p.1 p.2) := by
    rw [← hc3 p]
    dsimp only [x, y]
    ring
  have hleft : ∑ p, x p ^ 3 = ∑ i, u i ^ 3 := by
    simp only [x, mul_pow, hc3, Fintype.sum_prod_type, ← Finset.mul_sum, row_overlap W hrow,
      mul_one]
  have hright : ∑ p, y p ^ 3 = ∑ j, v j ^ 3 := by
    simp only [y, mul_pow, hc3, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, column_overlap W hcol, mul_one]
  simp_rw [hpw, hxy, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] at h
  rw [hleft, hright, Fintype.sum_prod_type] at h
  have hroot : cubicRoot (∑ i, u i ^ 3) ^ 2 = (∑ i, u i ^ 3) ^ (1 / (3 / 2) : ℝ) := by
    unfold cubicRoot
    rw [← Real.rpow_mul_natCast (Finset.sum_nonneg fun i _ => pow_nonneg (hu i) _)]
    congr 1
    norm_num
  rw [hroot]
  exact h

private theorem trace_sq_mul_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ^ 2 * B).trace.re ≤ cubicRoot (A ^ 3).trace.re ^ 2 * cubicRoot (B ^ 3).trace.re := by
  let U : Matrix n n ℂ := hA.1.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.1.eigenvectorUnitary
  let W : Matrix n n ℂ := Uᴴ * V
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self _
  have hV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self _
  have hW' : W * Wᴴ = 1 := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V Vᴴ U, hV', Matrix.one_mul, hU]
  have hW : Wᴴ * W = 1 := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ V, hU', Matrix.one_mul, hV]
  let P := diagonal (fun i => ((hA.1.eigenvalues i ^ 2 : ℝ) : ℂ))
  let Q := diagonal (fun j => (hB.1.eigenvalues j : ℂ))
  have h2 : A ^ 2 = U * P * Uᴴ := by simpa only [U, P, Complex.ofReal_pow] using spectral_pow hA.1 2
  have h1 : B = V * Q * Vᴴ := by simpa only [V, Q, pow_one] using spectral_pow hB.1 1
  have htrace : (A ^ 2 * B).trace = (P * W * Q * Wᴴ).trace := by
    rw [h2, h1]
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm U]
    simp only [Matrix.mul_assoc]
  rw [htrace, trace_diagonal_overlap, trace_cube hA.1, trace_cube hB.1]
  exact cubic_holder hA.eigenvalues_nonneg hB.eigenvalues_nonneg hW' hW

/-- Both cubic mixed-trace gaps are nonnegative for finite complex PSD blocks. -/
private theorem mixed_trace_gaps {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let x := cubicRoot (A ^ 3).trace.re
    let y := cubicRoot (B ^ 3).trace.re
    0 ≤ x ^ 2 * y - (A ^ 2 * B).trace.re ∧ 0 ≤ x * y ^ 2 - (A * B ^ 2).trace.re := by
  refine ⟨sub_nonneg.mpr (trace_sq_mul_le hA hB), sub_nonneg.mpr ?_⟩
  rw [Matrix.trace_mul_comm A (B ^ 2), mul_comm]
  exact trace_sq_mul_le hB hA

end MixedTrace

private abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

private def occupationBlocks (C : Fin 2 → Qubit) : Mat :=
  (Matrix.blockDiagonal C).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)

private theorem occupationBlocks_apply (C : Fin 2 → Qubit) (i j k l : Fin 2) :
    occupationBlocks C (i,k) (j,l) = if i = j then C i k l else 0 := by
  rfl

private def occupationBlocksHom : (Fin 2 → Qubit) →⋆ₐ[ℂ] Mat where
  toFun := occupationBlocks
  map_one' := by
    unfold occupationBlocks
    rw [Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  map_mul' C E := by
    unfold occupationBlocks
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    rfl
  map_zero' := by simp [occupationBlocks, Matrix.blockDiagonal_zero]
  map_add' C E := by simp [occupationBlocks, Matrix.blockDiagonal_add, Matrix.submatrix_add]
  commutes' c := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp only [occupationBlocks_apply, Algebra.algebraMap_eq_smul_one, Pi.smul_apply,
      Pi.one_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs <;> simp_all
  map_star' C := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Pi.star_apply,
      occupationBlocks_apply, apply_ite, star_zero]
    split_ifs <;> simp_all

private theorem occupationBlocks_mul (C E : Fin 2 → Qubit) :
    occupationBlocks C * occupationBlocks E = occupationBlocks (C * E) :=
  (map_mul occupationBlocksHom C E).symm

private theorem occupationBlocks_pow (C : Fin 2 → Qubit) (k : ℕ) :
    occupationBlocks C ^ k = occupationBlocks (C ^ k) :=
  (map_pow occupationBlocksHom C k).symm

private theorem occupationBlocks_trace (C : Fin 2 → Qubit) :
    (occupationBlocks C).trace = ∑ i, (C i).trace := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, occupationBlocks_apply]

private def jumpGenerator (r : ℝ) (k : Fin 2) (X : Mat) : Mat :=
  (2 * (gibbsLow r : ℂ)) • dissipator (modeJump k) X +
    (2 * (gibbsHigh r : ℂ)) • dissipator (modeJump k)ᴴ X

open private rootValue rootScale rootRatio rootScale_pos rootRatio_sq from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

set_option maxHeartbeats 6000000 in
private theorem spectator_transport {r : ℝ} (hr : 1 ≤ r) (A B : Qubit) :
    let M := occupationBlocks ![A,B]
    G r * jumpGenerator r 0 (GInv r * M * GInv r) * G r =
      occupationBlocks ![
        (2 * (gibbsHigh r : ℂ)) • A - (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) • B,
        (2 * (gibbsLow r : ℂ)) • B - (2 * (gibbsLow r : ℂ) * (r : ℂ)) • A] := by
  dsimp only
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hq : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr0).ne'
  have ht : rootScale r ≠ 0 := (rootScale_pos hr0.le).ne'
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast rootRatio_sq hr0.le
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [jumpGenerator, dissipator, G, GInv, jump_zero, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, rootValue, finProdFinEquiv, rootRatio,
      Matrix.smul_apply, smul_eq_mul, occupationBlocks_apply]
  all_goals
    field_simp [hq, ht, hr0.ne']
    all_goals try rw [hs]
    all_goals ring

/-- Exact ordinary-trace energy of the spectator jump `E₀₁ ⊗ I` (`modeJump 0`). -/
private theorem spectator_energy_split {r : ℝ} (hr : 1 ≤ r) (A B : Qubit) :
    let M := occupationBlocks ![A,B]
    let X := GInv r * M * GInv r
    let J := modeJump 0
    (9 / 8 : ℝ) * (M ^ 2 * (G r *
      ((2 * (gibbsLow r : ℂ)) • dissipator J X +
        (2 * (gibbsHigh r : ℂ)) • dissipator Jᴴ X) * G r)).trace.re =
      gamma r * (r ^ 3 * (A ^ 3).trace.re + (B ^ 3).trace.re -
        r ^ 2 * (A ^ 2 * B).trace.re - r * (A * B ^ 2).trace.re) := by
  change (9 / 8 : ℝ) * ((occupationBlocks ![A,B]) ^ 2 *
    (G r * jumpGenerator r 0 (GInv r * occupationBlocks ![A,B] * GInv r) * G r)).trace.re = _
  rw [spectator_transport hr A B, occupationBlocks_pow, occupationBlocks_mul,
    occupationBlocks_trace, Complex.re_sum, Fin.sum_univ_two]
  simp only [Pi.mul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    smul_eq_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← pow_succ A 2, ← pow_succ B 2, Matrix.trace_mul_comm (B ^ 2) A]
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hγ : gamma r = (9 / 4) * gibbsLow r := by
    unfold gamma gibbsLow
    have h : 0 < 1 + r ^ 3 := by positivity
    field_simp
  rw [hγ]
  unfold gibbsHigh
  field_simp [hr0.ne']
  ring

private def cubicMass {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℂ) : ℝ :=
  (C ^ 3).trace.re

private def cubicEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (rho C : Matrix n n ℂ) : ℝ :=
  (C ^ 3 * (cfc Real.log (C ^ 3) - cfc Real.log rho)).trace.re -
    cubicMass C * Real.log (cubicMass C)

open private gibbsOccupation energyKernel from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private def gibbsDensity (r : ℝ) : Qubit :=
  diagonal fun i => (gibbsOccupation r i : ℂ)

private def classicalEntropy (r T S : ℝ) : ℝ :=
  T * Real.log T + S * Real.log S - (T + S) * Real.log (T + S) -
    (T * Real.log (gibbsLow r) + S * Real.log (gibbsHigh r))

private theorem occupationBlocks_log (C : Fin 2 → Qubit)
    (hC : ∀ i, (C i).IsHermitian) :
    cfc Real.log (occupationBlocks C) = occupationBlocks fun i => cfc Real.log (C i) := by
  let : ContinuousFunctionalCalculus ℝ (Fin 2 → Qubit) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hC' : IsSelfAdjoint C := Pi.isSelfAdjoint.mpr hC
  have hc : ContinuousOn Real.log (spectrum ℝ C) := by
    rw [Pi.spectrum_eq]
    exact (Set.finite_iUnion (fun i => (C i).finite_real_spectrum)).continuousOn _
  have hmap := occupationBlocksHom.map_cfc Real.log C hc
    occupationBlocksHom.toLinearMap.continuous_of_finiteDimensional hC' (hC'.map _)
  rw [cfc_map_pi (S := ℂ) Real.log C (by rwa [Pi.spectrum_eq] at hc) hC' hC] at hmap
  exact hmap.symm

private theorem gibbs_occupation_pos {r : ℝ} (hr : 1 ≤ r) (i : Fin 2) :
    0 < gibbsOccupation r i := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  fin_cases i <;> simp [gibbsOccupation, gibbsHigh, gibbsLow] <;> positivity

private theorem gibbs_log_split {r : ℝ} (hr : 1 ≤ r) :
    cfc Real.log (D r) = occupationBlocks fun i =>
      cfc Real.log (gibbsDensity r) + (Real.log (gibbsOccupation r i) : ℂ) • 1 := by
  have hD : cfc Real.log (D r) = diagonal (fun o =>
      (Real.log (gibbsOccupation r o.1 * gibbsOccupation r o.2) : ℂ)) := by
    simpa only [D, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ)
        (fun o : Fin 2 × Fin 2 => gibbsOccupation r o.1 * gibbsOccupation r o.2) Real.log
  have hρ : cfc Real.log (gibbsDensity r) =
      diagonal (fun i => (Real.log (gibbsOccupation r i) : ℂ)) := by
    simpa only [gibbsDensity, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) (gibbsOccupation r) Real.log
  rw [hD, hρ]
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      simp [occupationBlocks_apply, Real.log_mul (gibbs_occupation_pos hr i).ne'
        (gibbs_occupation_pos hr k).ne', Matrix.smul_apply, add_comm]
    · simp [occupationBlocks_apply, Matrix.smul_apply, hkl]
  · simp [occupationBlocks_apply, hij]

/-- Conditional entropy chain rule for the unnormalized cubic mass in each occupation block. -/
private theorem conditional_entropy_split {r : ℝ} (hr : 1 ≤ r)
    {A B : Qubit} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cubicEntropy (D r) (occupationBlocks ![A,B]) =
      cubicEntropy (gibbsDensity r) A + cubicEntropy (gibbsDensity r) B +
        classicalEntropy r (cubicMass A) (cubicMass B) := by
  have hp (i : Fin 2) : (((![A,B] : Fin 2 → Qubit) ^ 3) i).IsHermitian := by
    fin_cases i
    · exact hA.1.pow 3
    · exact hB.1.pow 3
  have hsub (C E : Fin 2 → Qubit) :
      occupationBlocks C - occupationBlocks E = occupationBlocks (C - E) :=
    (map_sub occupationBlocksHom C E).symm
  unfold cubicEntropy cubicMass classicalEntropy
  rw [occupationBlocks_pow, occupationBlocks_log _ hp, gibbs_log_split hr,
    hsub, occupationBlocks_mul]
  simp only [occupationBlocks_trace, Fin.sum_univ_two, Pi.mul_apply,
    Pi.sub_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [gibbsOccupation, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_add_eq_sub_sub, mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  ring

/-- The exact energy correction to replacing the two spectator blocks by their cubic roots. -/
private theorem spectator_gap {r : ℝ} (hr : 1 ≤ r)
    {A B : Qubit} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let M := occupationBlocks ![A,B]
    let x := cubicRoot (cubicMass A)
    let y := cubicRoot (cubicMass B)
    (9 / 8 : ℝ) * (M ^ 2 * (G r *
      jumpGenerator r 0 (GInv r * M * GInv r) * G r)).trace.re =
      energyKernel r x y + gamma r * r ^ 2 * (x ^ 2 * y - (A ^ 2 * B).trace.re) +
        gamma r * r * (x * y ^ 2 - (A * B ^ 2).trace.re) := by
  have hmass {C : Qubit} (hC : C.PosSemidef) : 0 ≤ cubicMass C := by
    rw [cubicMass, trace_cube hC.1]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (hC.eigenvalues_nonneg i) _
  dsimp only
  rw [show (9 / 8 : ℝ) * ((occupationBlocks ![A,B]) ^ 2 *
    (G r * jumpGenerator r 0 (GInv r * occupationBlocks ![A,B] * GInv r) * G r)).trace.re = _
      from spectator_energy_split hr A B]
  unfold energyKernel
  rw [cubicRoot_cube (hmass hA), cubicRoot_cube (hmass hB)]
  unfold cubicMass
  ring

private def qubitJump : Qubit := !![0,1;0,0]

private theorem qubitJump_adjoint : qubitJumpᴴ = !![0,0;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitJump, Matrix.conjTranspose_apply]

private def modularJump {n : Type*} [Fintype n] (r : ℝ) (J C : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (gibbsLow r : ℂ) • ((Jᴴ * J) * C + C * (Jᴴ * J)) -
    (2 * (gibbsLow r : ℂ) * (r : ℂ)) • (Jᴴ * C * J) +
    (gibbsHigh r : ℂ) • ((J * Jᴴ) * C + C * (J * Jᴴ)) -
    (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) • (J * C * Jᴴ)

private def oneModeEnergy (r : ℝ) (C : Qubit) : ℝ :=
  (9 / 8 : ℝ) * (C ^ 2 * modularJump r qubitJump C).trace.re

private theorem spectator_modular (r : ℝ) (A B : Qubit) :
    modularJump r (modeJump 0) (occupationBlocks ![A,B]) =
      occupationBlocks ![
        (2 * (gibbsHigh r : ℂ)) • A - (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) • B,
        (2 * (gibbsLow r : ℂ)) • B - (2 * (gibbsLow r : ℂ) * (r : ℂ)) • A] := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [modularJump, jump_zero, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul, occupationBlocks_apply] <;> ring

private theorem active_modular (r : ℝ) (A B : Qubit) :
    modularJump r (modeJump 1) (occupationBlocks ![A,B]) =
      occupationBlocks ![modularJump r qubitJump A, modularJump r qubitJump B] := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [modularJump, qubitJump_adjoint]
  all_goals simp [jump_one, qubitJump, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, occupationBlocks_apply]

private def operatorEnergy (r : ℝ) (M : Mat) : ℝ :=
  (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)).trace.re

private theorem operator_energy_split {r : ℝ} (hr : 1 ≤ r) (A B : Qubit) :
    let M := occupationBlocks ![A,B]
    operatorEnergy r M = oneModeEnergy r A + oneModeEnergy r B +
      (9 / 8 : ℝ) * (M ^ 2 * (G r * jumpGenerator r 0 (GInv r * M * GInv r) * G r)).trace.re := by
  let M := occupationBlocks ![A,B]
  have hmod : G r * generator r (GInv r * M * GInv r) * G r =
      ∑ k, modularJump r (modeJump k) M :=
    WuCubicOperatorBridge.operator_trace_modular_identity hr M
  have hspec : modularJump r (modeJump 0) M =
      G r * jumpGenerator r 0 (GInv r * M * GInv r) * G r :=
    (spectator_modular r A B).trans (spectator_transport hr A B).symm
  change operatorEnergy r M = _
  rw [operatorEnergy, hmod, Fin.sum_univ_two, hspec, active_modular]
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, mul_add]
  rw [show M = occupationBlocks ![A,B] from rfl, occupationBlocks_pow, occupationBlocks_mul,
    occupationBlocks_trace, Complex.re_sum, Fin.sum_univ_two]
  simp only [Pi.mul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, oneModeEnergy]
  ring

private def oneModeOperatorDeficit (r : ℝ) (C : Qubit) : ℝ :=
  oneModeEnergy r C - alpha r * cubicEntropy (gibbsDensity r) C

/-- The conditional tensorization identity for Wu's actual operator deficit. -/
private theorem operator_deficit_split {r : ℝ} (hr : 1 ≤ r)
    {A B : Qubit} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let M := occupationBlocks ![A,B]
    let x := cubicRoot (cubicMass A)
    let y := cubicRoot (cubicMass B)
    operatorEnergy r M - alpha r * cubicEntropy (D r) M =
      oneModeOperatorDeficit r A + oneModeOperatorDeficit r B +
        (energyKernel r x y - alpha r * classicalEntropy r (cubicMass A) (cubicMass B)) +
        gamma r * r ^ 2 * (x ^ 2 * y - (A ^ 2 * B).trace.re) +
        gamma r * r * (x * y ^ 2 - (A * B ^ 2).trace.re) := by
  dsimp only
  rw [operator_energy_split hr A B, conditional_entropy_split hr hA hB, spectator_gap hr hA hB]
  unfold oneModeOperatorDeficit
  ring

open private h c e cutA cutB bias entropyPair beta centered_bias from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private theorem one_mode_deficit_unsorted {r v w z : ℝ} (hr : 1 ≤ r)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hz₁ : -1 ≤ z) (hz₂ : z ≤ 1) :
    0 ≤ oneModeDeficit r v w z := by
  rcases le_total v w with hvw | hwv
  · exact WuOneModeCubic.one_mode_bound hr v w z hv hvw hz₁ hz₂
  have hswap : oneModeDeficit r v w z = oneModeDeficit r w v (-z) := by
    simp only [oneModeDeficit, entropyPair, cutA, cutB, add_comm (w ^ 3) (v ^ 3)]
    ring
  rw [hswap]
  exact WuOneModeCubic.one_mode_bound hr w v (-z) hw hwv (by linarith) (by linarith)

private def moment (v w p : ℝ) (k : ℕ) : ℝ :=
  (1 - p) * v ^ k + p * w ^ k

private theorem one_mode_scalar_identity {r v w : ℝ} (hr : 1 ≤ r)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (p : ℝ) :
    gamma r * (r ^ 3 * moment v w p 3 + moment v w (1 - p) 3 -
      r ^ 2 * moment v w p 2 * moment v w (1 - p) 1 -
      r * moment v w (1 - p) 2 * moment v w p 1) -
      alpha r * (v ^ 3 * Real.log (v ^ 3) + w ^ 3 * Real.log (w ^ 3) -
        (v ^ 3 + w ^ 3) * Real.log (v ^ 3 + w ^ 3) -
        (moment v w p 3 * Real.log (gibbsLow r) +
          moment v w (1 - p) 3 * Real.log (gibbsHigh r))) =
      oneModeDeficit r v w (2 * p - 1) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ha : 0 < gibbsLow r := by unfold gibbsLow; positivity
  have hb : 0 < gibbsHigh r := by unfold gibbsHigh; positivity
  have hlogb : Real.log (gibbsHigh r) = Real.log (gibbsLow r) + beta r := by
    rw [gibbsHigh, Real.log_mul (pow_ne_zero _ hr0.ne') ha.ne', Real.log_pow, beta]
    ring
  have hlog4 : Real.log (4 * gibbsLow r * gibbsHigh r) =
      2 * Real.log 2 + Real.log (gibbsLow r) + Real.log (gibbsHigh r) := by
    rw [Real.log_mul (by positivity) hb.ne', Real.log_mul (by norm_num) ha.ne',
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hmass (t : ℝ) (ht : 0 ≤ t) :
      t * Real.log (t / 2) = t * Real.log t - t * Real.log 2 := by
    rcases ht.eq_or_lt with he | hp
    · simp [← he]
    · rw [Real.log_div hp.ne' (by norm_num), mul_sub]
  have hcenter := centered_bias hr
  unfold e at hcenter
  unfold oneModeDeficit h entropyPair cutA cutB c e moment
  rw [hmass _ (by positivity), hlog4, hlogb]
  linear_combination (-((w ^ 3 - v ^ 3) * (2 * p - 1) / 2)) * hcenter

private theorem classical_deficit_nonneg {r x y : ℝ} (hr : 1 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ energyKernel r x y - alpha r * classicalEntropy r (x ^ 3) (y ^ 3) := by
  have hxy := one_mode_scalar_identity hr hx hy 0
  have hsign : (2 : ℝ) * 0 - 1 = -1 := by norm_num
  rw [hsign] at hxy
  simp only [moment, sub_zero, sub_self, zero_mul, one_mul, add_zero, zero_add, pow_one] at hxy
  rw [show energyKernel r x y - alpha r * classicalEntropy r (x ^ 3) (y ^ 3) =
    oneModeDeficit r x y (-1) by
      rw [← hxy]
      unfold energyKernel classicalEntropy
      ring]
  exact one_mode_deficit_unsorted hr hx hy (by norm_num) (by norm_num)

private theorem one_mode_energy_diagonal {r : ℝ} (hr : 1 ≤ r) (C : Qubit) :
    oneModeEnergy r C = gamma r * (r ^ 3 * ((C ^ 3) 0 0).re + ((C ^ 3) 1 1).re -
      r ^ 2 * ((C ^ 2) 0 0 * C 1 1).re - r * ((C ^ 2) 1 1 * C 0 0).re) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrate : 2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹ = ((2 * gibbsLow r * r ^ 2 : ℝ) : ℂ) := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    push_cast
    simp only [gibbsHigh, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp
  have hγ : gamma r = (9 / 4) * gibbsLow r := by
    rw [gamma, gibbsLow, div_mul_div_comm, mul_one]
  rw [oneModeEnergy, modularJump, qubitJump_adjoint, hrate, hγ]
  norm_num [qubitJump, pow_succ, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, gibbsHigh, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.mul_im, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem qubit_diagonal_moments {C : Qubit} (hC : C.IsHermitian) :
    let U : Qubit := hC.eigenvectorUnitary
    let p := Complex.normSq (U 0 1)
    let v := hC.eigenvalues 0
    let w := hC.eigenvalues 1
    0 ≤ p ∧ p ≤ 1 ∧ ∀ k : ℕ,
      (C ^ k) 0 0 = (moment v w p k : ℂ) ∧ (C ^ k) 1 1 = (moment v w (1 - p) k : ℂ) := by
  let U : Qubit := hC.eigenvectorUnitary
  let p := Complex.normSq (U 0 1)
  let v := hC.eigenvalues 0
  let w := hC.eigenvalues 1
  have hr := row_overlap U (Unitary.coe_mul_star_self _) 0
  have hc := column_overlap U (Unitary.coe_star_mul_self _) 1
  have hr' := row_overlap U (Unitary.coe_mul_star_self _) 1
  simp only [Fin.sum_univ_two] at hr hc hr'
  have h00 : Complex.normSq (U 0 0) = 1 - p := by dsimp [p]; linarith only [hr]
  have h11 : Complex.normSq (U 1 1) = 1 - p := by dsimp [p]; linarith only [hc]
  have h10 : Complex.normSq (U 1 0) = p := by linarith only [hr', h11]
  change 0 ≤ p ∧ p ≤ 1 ∧ _
  refine ⟨Complex.normSq_nonneg _, ?_, ?_⟩
  · linarith only [h00, Complex.normSq_nonneg (U 0 0)]
  intro k
  have hd (i : Fin 2) :
      (C ^ k) i i =
        ∑ j : Fin 2, ((hC.eigenvalues j ^ k * Complex.normSq (U i j) : ℝ) : ℂ) := by
    rw [spectral_pow hC]
    change (U * diagonal (fun j => (hC.eigenvalues j : ℂ) ^ k) * Uᴴ) i i = _
    simp only [Matrix.mul_apply (N := Uᴴ), Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Complex.star_def]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_right_comm, Complex.mul_conj, Complex.ofReal_mul, Complex.ofReal_pow, mul_comm]
  constructor
  · rw [hd 0, Fin.sum_univ_two, h00, show Complex.normSq (U 0 1) = p from rfl]
    push_cast
    unfold moment
    push_cast
    change _ = ((1 : ℂ) - (p : ℂ)) * (v : ℂ) ^ k + (p : ℂ) * (w : ℂ) ^ k
    simp only [v, w]
    ring
  · rw [hd 1, Fin.sum_univ_two, h10, h11]
    push_cast
    unfold moment
    push_cast
    change _ = ((1 : ℂ) - (1 - (p : ℂ))) * (v : ℂ) ^ k +
      (1 - (p : ℂ)) * (w : ℂ) ^ k
    simp only [v, w]
    ring

private theorem trace_cube_log {C : Qubit} (hC : C.IsHermitian) :
    (C ^ 3 * cfc Real.log (C ^ 3)).trace.re =
      ∑ i, hC.eigenvalues i ^ 3 * Real.log (hC.eigenvalues i ^ 3) := by
  let U : Qubit := hC.eigenvectorUnitary
  let f : Fin 2 → ℝ := fun i => hC.eigenvalues i ^ 3
  let A : Qubit := diagonal fun i => (f i : ℂ)
  let B : Qubit := diagonal fun i => (Real.log (f i) : ℂ)
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hA : C ^ 3 = U * A * Uᴴ := by
    simpa only [U, A, f, Complex.ofReal_pow] using spectral_pow hC 3
  have hB : cfc Real.log A = B := by
    simpa only [A, B, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) f Real.log
  have hu : U.Isometry := hU
  have hu' : Uᴴ.Isometry := by simpa only [Matrix.Isometry, conjTranspose_conjTranspose] using hU'
  rw [hA, Matrix.cfc_conj_isometry Real.log hu hu', hB]
  have hmul : U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  rw [hmul, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp only [A, B, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum,
    f, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem one_mode_operator_nonneg {r : ℝ} (hr : 1 ≤ r) {C : Qubit}
    (hC : C.PosSemidef) : 0 ≤ oneModeOperatorDeficit r C := by
  let v := hC.1.eigenvalues 0
  let w := hC.1.eigenvalues 1
  let U : Qubit := hC.1.eigenvectorUnitary
  let p := Complex.normSq (U 0 1)
  have hv : 0 ≤ v := hC.eigenvalues_nonneg 0
  have hw : 0 ≤ w := hC.eigenvalues_nonneg 1
  have hdata : 0 ≤ p ∧ p ≤ 1 ∧ ∀ k : ℕ,
      (C ^ k) 0 0 = (moment v w p k : ℂ) ∧ (C ^ k) 1 1 = (moment v w (1 - p) k : ℂ) :=
    qubit_diagonal_moments hC.1
  obtain ⟨hp, hp', hm⟩ := hdata
  have hρ : cfc Real.log (gibbsDensity r) =
      diagonal (fun i => (Real.log (gibbsOccupation r i) : ℂ)) := by
    simpa only [gibbsDensity, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) (gibbsOccupation r) Real.log
  have hGibbs : (C ^ 3 * cfc Real.log (gibbsDensity r)).trace.re =
      moment v w p 3 * Real.log (gibbsLow r) + moment v w (1 - p) 3 * Real.log (gibbsHigh r) := by
    rw [hρ]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fin.sum_univ_two,
      (hm 3).1, (hm 3).2, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re,
      gibbsOccupation, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hm0 : C 0 0 = (moment v w p 1 : ℂ) := by simpa only [pow_one] using (hm 1).1
  have hm1 : C 1 1 = (moment v w (1 - p) 1 : ℂ) := by simpa only [pow_one] using (hm 1).2
  unfold oneModeOperatorDeficit cubicEntropy cubicMass
  rw [one_mode_energy_diagonal hr, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    trace_cube_log hC.1, trace_cube hC.1, hGibbs, (hm 3).1, (hm 3).2, (hm 2).1, (hm 2).2,
    hm0, hm1]
  simp only [Fin.sum_univ_two, ← Complex.ofReal_mul, Complex.ofReal_re]
  change 0 ≤ _ - alpha r * (_ - _ - _)
  rw [sub_right_comm ((v ^ 3 * Real.log (v ^ 3)) + (w ^ 3 * Real.log (w ^ 3)))]
  have hbound : 0 ≤ oneModeDeficit r v w (2 * p - 1) :=
    one_mode_deficit_unsorted hr hv hw (by linarith) (by linarith)
  rw [← one_mode_scalar_identity hr hv hw p] at hbound
  simpa only [v, w, mul_assoc] using hbound

/-- Wu v1 (3.54) at exponent three for arbitrary PSD blocks in the first occupation.
The blocks can have arbitrary spectra and independent eigenbases. -/
theorem occupation_conditional_bound {r : ℝ} (hr : 1 ≤ r) {A B : Qubit}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let M := (Matrix.blockDiagonal ![A,B]).submatrix Prod.swap Prod.swap
    let X := GInv r * M * GInv r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re := by
  change alpha r * cubicEntropy (D r) (occupationBlocks ![A,B]) ≤
    operatorEnergy r (occupationBlocks ![A,B])
  apply sub_nonneg.mp
  rw [operator_deficit_split hr hA hB]
  have hmass {C : Qubit} (hC : C.PosSemidef) : 0 ≤ cubicMass C := by
    rw [cubicMass, trace_cube hC.1]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (hC.eigenvalues_nonneg i) _
  have hclassical := classical_deficit_nonneg hr
    (Real.rpow_nonneg (hmass hA) (1 / 3 : ℝ)) (Real.rpow_nonneg (hmass hB) (1 / 3 : ℝ))
  change 0 ≤ energyKernel r (cubicRoot (cubicMass A)) (cubicRoot (cubicMass B)) -
    alpha r * classicalEntropy r (cubicRoot (cubicMass A) ^ 3) (cubicRoot (cubicMass B) ^ 3)
    at hclassical
  rw [cubicRoot_cube (hmass hA), cubicRoot_cube (hmass hB)] at hclassical
  obtain ⟨hgap₁, hgap₂⟩ := mixed_trace_gaps hA hB
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hγ : 0 ≤ gamma r := by unfold gamma; positivity
  exact add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (one_mode_operator_nonneg hr hA) (one_mode_operator_nonneg hr hB))
      hclassical)
    (mul_nonneg (mul_nonneg hγ (sq_nonneg r)) hgap₁))
    (mul_nonneg (mul_nonneg hγ hr0) hgap₂)

end D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
