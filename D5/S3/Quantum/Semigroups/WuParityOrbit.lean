/- GID: D5/S3/Quantum/Semigroups/WuParityOrbit
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuParityOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity orbit identity and the equal-cap two-mode cubic inequality. -/

import D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuParityOrbit

open D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)
open D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
  (D G GInv Mat Occupation generator operator_trace_modular_identity)
open private GInv_mul_G G_mul_GInv from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (alpha)
open private gibbsOccupation gibbsLow gibbsHigh jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private occupationBlocks occupationBlocksHom occupationBlocks_apply
  qubit_diagonal_moments moment trace_cube trace_cube_log from
  D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

private def xorBit (i j : Fin 2) : Fin 2 := if i = j then 0 else 1

/-- The two rows of this coordinate map are `[00,11]` and `[01,10]`. -/
private def parityIndex : Occupation ≃ Occupation where
  toFun p := (p.2, xorBit p.1 p.2)
  invFun p := (xorBit p.1 p.2, p.1)
  left_inv := by
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide
  right_inv := by
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide

def parityBlocks (C : Fin 2 → Qubit) : Mat :=
  (occupationBlocks C).submatrix parityIndex.symm parityIndex.symm

private theorem parityBlocks_apply (C : Fin 2 → Qubit) (i j k l : Fin 2) :
    parityBlocks C (i,j) (k,l) = if xorBit i j = xorBit k l then C (xorBit i j) i k else 0 :=
  occupationBlocks_apply _ _ _ _ _

private def parityBlocksHom : (Fin 2 → Qubit) →⋆ₐ[ℂ] Mat where
  toFun := parityBlocks
  map_one' := by
    change (occupationBlocksHom 1).submatrix _ _ = _
    rw [map_one, Matrix.submatrix_one_equiv]
  map_mul' C E := by
    change (occupationBlocksHom (C * E)).submatrix parityIndex.symm parityIndex.symm =
      (occupationBlocksHom C).submatrix parityIndex.symm parityIndex.symm *
        (occupationBlocksHom E).submatrix parityIndex.symm parityIndex.symm
    rw [map_mul, Matrix.submatrix_mul_equiv]
  map_zero' := by
    change (occupationBlocksHom 0).submatrix _ _ = _
    rw [map_zero]
    rfl
  map_add' C E := by
    change (occupationBlocksHom (C + E)).submatrix _ _ = _
    rw [map_add, Matrix.submatrix_add]
    rfl
  commutes' c := by
    change (occupationBlocksHom (algebraMap ℂ (Fin 2 → Qubit) c)).submatrix
      parityIndex.symm parityIndex.symm = algebraMap ℂ Mat c
    rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
    change c • (1 : Mat).submatrix parityIndex.symm parityIndex.symm = c • 1
    rw [Matrix.submatrix_one_equiv]
  map_star' C := by
    change (occupationBlocksHom (star C)).submatrix _ _ = _
    rw [map_star]
    rfl

private theorem parityBlocks_pow (C : Fin 2 → Qubit) (k : ℕ) :
    parityBlocks C ^ k = parityBlocks (C ^ k) :=
  (map_pow parityBlocksHom C k).symm

private theorem parityBlocks_mul (C E : Fin 2 → Qubit) :
    parityBlocks C * parityBlocks E = parityBlocks (C * E) :=
  (map_mul parityBlocksHom C E).symm

private theorem parityBlocks_trace (C : Fin 2 → Qubit) :
    (parityBlocks C).trace = (C 0).trace + (C 1).trace := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    parityBlocks_apply, xorBit]
  ac_rfl

/-- For parity blocks each signed jump has one entry in each ordered sector pair.
Their lower and upper mixed traces thus use only physical diagonal entries. -/
private theorem signed_mixed_traces (A B E F : Qubit) :
    let M := parityBlocks ![A,B]
    let N := parityBlocks ![E,F]
    (N * (∑ k : Fin 2, (modeJump k)ᴴ * M * modeJump k)).trace =
      (F 0 0 + F 1 1) * A 0 0 + E 1 1 * (B 0 0 + B 1 1) ∧
    (N * (∑ k : Fin 2, modeJump k * M * (modeJump k)ᴴ)).trace =
      E 0 0 * (B 0 0 + B 1 1) + (F 0 0 + F 1 1) * A 1 1 := by
  dsimp only
  constructor <;>
    norm_num [jump_zero, jump_one, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, parityBlocks_apply, xorBit] <;> ring

private theorem jump_projections :
    (∑ k : Fin 2, (modeJump k)ᴴ * modeJump k) =
      diagonal (fun i : Occupation => ![0,1,1,2] (finProdFinEquiv i)) ∧
    (∑ k : Fin 2, modeJump k * (modeJump k)ᴴ) =
      diagonal (fun i : Occupation => ![2,1,1,0] (finProdFinEquiv i)) := by
  constructor <;> ext ⟨i,j⟩ ⟨k,l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [jump_zero, jump_one, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, finProdFinEquiv]


private theorem parityBlocks_log (C : Fin 2 → Qubit)
    (hC : ∀ i, (C i).IsHermitian) :
    cfc Real.log (parityBlocks C) = parityBlocks fun i => cfc Real.log (C i) := by
  let : ContinuousFunctionalCalculus ℝ (Fin 2 → Qubit) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hC' : IsSelfAdjoint C := Pi.isSelfAdjoint.mpr hC
  have hc : ContinuousOn Real.log (spectrum ℝ C) := by
    rw [Pi.spectrum_eq]
    exact (Set.finite_iUnion (fun i => (C i).finite_real_spectrum)).continuousOn _
  have hmap := parityBlocksHom.map_cfc Real.log C hc
    parityBlocksHom.toLinearMap.continuous_of_finiteDimensional hC' (hC'.map _)
  rw [cfc_map_pi (S := ℂ) Real.log C (by rwa [Pi.spectrum_eq] at hc) hC' hC] at hmap
  exact hmap.symm

private def logGibbs (r : ℝ) (i j : Fin 2) : ℝ :=
  Real.log (gibbsOccupation r i * gibbsOccupation r j)

private theorem logGibbs_matrix (r : ℝ) :
    cfc Real.log (D r) = diagonal fun i : Occupation => (logGibbs r i.1 i.2 : ℂ) := by
  simpa only [D, logGibbs, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
    Matrix.cfc_diagonal_real (𝕜 := ℂ)
      (fun i : Occupation => gibbsOccupation r i.1 * gibbsOccupation r i.2) Real.log

private theorem trace_anticommutator (M Q : Mat) :
    (M ^ 2 * (Q * M + M * Q)).trace = 2 * (M ^ 3 * Q).trace := by
  have hLeft : (M ^ 2 * (Q * M)).trace = (M ^ 3 * Q).trace := by
    rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc, ← pow_succ']
  have hRight : (M ^ 2 * (M * Q)).trace = (M ^ 3 * Q).trace := by
    rw [← Matrix.mul_assoc, ← pow_succ]
  rw [Matrix.mul_add, Matrix.trace_add, hLeft, hRight, two_mul]

private def energy (r : ℝ) (M : Mat) : ℝ :=
  (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)).trace.re

/-- The ordinary cubic trace deficit with any real entropy coefficient. -/
def cubicDeficit (r c : ℝ) (M : Mat) : ℝ :=
  energy r M - c * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
    (M ^ 3).trace.re * Real.log (M ^ 3).trace.re)

private theorem energy_diagonal_terms {r : ℝ} (hr : 1 ≤ r) (A B : Qubit) :
    energy r (parityBlocks ![A,B]) =
      (9 / 4 : ℝ) *
        ((gibbsLow r : ℂ) *
          ((B ^ 3) 0 0 + (B ^ 3) 1 1 + 2 * (A ^ 3) 1 1 -
            (r : ℂ) * (((B ^ 2) 0 0 + (B ^ 2) 1 1) * A 0 0 +
              (A ^ 2) 1 1 * (B 0 0 + B 1 1))) +
         (gibbsHigh r : ℂ) *
          (2 * (A ^ 3) 0 0 + (B ^ 3) 0 0 + (B ^ 3) 1 1 -
            (r : ℂ)⁻¹ * ((A ^ 2) 0 0 * (B 0 0 + B 1 1) +
              ((B ^ 2) 0 0 + (B ^ 2) 1 1) * A 1 1))).re := by
  unfold energy
  rw [operator_trace_modular_identity hr]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    ← Matrix.sum_mul, ← Matrix.mul_sum]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hProjection (Q : Mat) :
      ((parityBlocks ![A,B]) ^ 2 * (Q * parityBlocks ![A,B])).trace +
        ((parityBlocks ![A,B]) ^ 2 * (parityBlocks ![A,B] * Q)).trace =
          2 * ((parityBlocks ![A,B]) ^ 3 * Q).trace := by
    rw [← Matrix.trace_add, ← Matrix.mul_add, trace_anticommutator]
  rw [hProjection, hProjection]
  rw [parityBlocks_pow ![A,B] 2]
  have h := signed_mixed_traces A B (A ^ 2) (B ^ 2)
  rw [show (![A,B] : Fin 2 → Qubit) ^ 2 = ![A ^ 2, B ^ 2] by
    funext i; fin_cases i <;> rfl, h.1, h.2]
  rw [jump_projections.1, jump_projections.2, parityBlocks_pow ![A,B] 3]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fintype.sum_prod_type,
    Fin.sum_univ_two, parityBlocks_apply, xorBit, finProdFinEquiv, Complex.add_re,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.inv_re, Complex.inv_im]
  ring

private theorem cubicEntropy_split (r : ℝ) (A B : Qubit)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let M := parityBlocks ![A,B]
    let mass := (A ^ 3).trace.re + (B ^ 3).trace.re
    (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re =
        (A ^ 3 * cfc Real.log (A ^ 3)).trace.re +
        (B ^ 3 * cfc Real.log (B ^ 3)).trace.re - mass * Real.log mass -
        (logGibbs r 0 0 * ((A ^ 3) 0 0).re + logGibbs r 1 1 * ((A ^ 3) 1 1).re +
          logGibbs r 0 1 * ((B ^ 3) 0 0).re + logGibbs r 1 0 * ((B ^ 3) 1 1).re) := by
  dsimp only
  rw [parityBlocks_pow, logGibbs_matrix]
  rw [parityBlocks_log _ (by intro i; fin_cases i; exacts [hA.pow 3, hB.pow 3])]
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, parityBlocks_mul, parityBlocks_trace,
    parityBlocks_trace]
  simp only [Pi.mul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fintype.sum_prod_type,
    Fin.sum_univ_two, parityBlocks_apply, xorBit, Complex.mul_re]
  ring


private def orbitMoment (v : Fin 2 → ℝ) (p : ℝ) (i : Fin 2) (k : ℕ) : ℝ :=
  ![moment (v 0) (v 1) p k, moment (v 0) (v 1) (1 - p) k] i

private def orbitValue (r c : ℝ) (v w : Fin 2 → ℝ) (p q : ℝ) : ℝ :=
  let a := orbitMoment v p
  let b := orbitMoment w q
  let mass := (v 0 ^ 3 + v 1 ^ 3) + (w 0 ^ 3 + w 1 ^ 3)
  let spectralLog := (v 0 ^ 3 * Real.log (v 0 ^ 3) + v 1 ^ 3 * Real.log (v 1 ^ 3)) +
    (w 0 ^ 3 * Real.log (w 0 ^ 3) + w 1 ^ 3 * Real.log (w 1 ^ 3))
  (9 / 4 : ℝ) *
    (gibbsLow r *
      (b 0 3 + b 1 3 + 2 * a 1 3 -
        r * ((b 0 2 + b 1 2) * a 0 1 + a 1 2 * (b 0 1 + b 1 1))) +
     gibbsHigh r *
      (2 * a 0 3 + b 0 3 + b 1 3 -
        r⁻¹ * (a 0 2 * (b 0 1 + b 1 1) + (b 0 2 + b 1 2) * a 1 1))) -
    c * (spectralLog - mass * Real.log mass -
      (logGibbs r 0 0 * a 0 3 + logGibbs r 1 1 * a 1 3 +
       logGibbs r 0 1 * b 0 3 + logGibbs r 1 0 * b 1 3))

private theorem cubicDeficit_eval {r : ℝ} (hr : 1 ≤ r) (c : ℝ) (A B : Qubit)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (v w : Fin 2 → ℝ) (p q : ℝ)
    (hmA : ∀ k, (A ^ k) 0 0 = (orbitMoment v p 0 k : ℂ) ∧
      (A ^ k) 1 1 = (orbitMoment v p 1 k : ℂ))
    (hmB : ∀ k, (B ^ k) 0 0 = (orbitMoment w q 0 k : ℂ) ∧
      (B ^ k) 1 1 = (orbitMoment w q 1 k : ℂ))
    (hMassA : (A ^ 3).trace.re = v 0 ^ 3 + v 1 ^ 3)
    (hMassB : (B ^ 3).trace.re = w 0 ^ 3 + w 1 ^ 3)
    (hLogA : (A ^ 3 * cfc Real.log (A ^ 3)).trace.re =
      v 0 ^ 3 * Real.log (v 0 ^ 3) + v 1 ^ 3 * Real.log (v 1 ^ 3))
    (hLogB : (B ^ 3 * cfc Real.log (B ^ 3)).trace.re =
      w 0 ^ 3 * Real.log (w 0 ^ 3) + w 1 ^ 3 * Real.log (w 1 ^ 3)) :
    cubicDeficit r c (parityBlocks ![A,B]) = orbitValue r c v w p q := by
  rw [cubicDeficit, energy_diagonal_terms hr, cubicEntropy_split r A B hA hB,
    hMassA, hMassB, hLogA, hLogB]
  have hA1 := hmA 1
  have hB1 := hmB 1
  simp only [pow_one] at hA1 hB1
  rw [(hmA 3).1, (hmA 3).2, (hmB 3).1, (hmB 3).2,
    (hmA 2).1, (hmA 2).2, (hmB 2).1, (hmB 2).2, hA1.1, hA1.2, hB1.1, hB1.2]
  simp only [orbitValue, ← Complex.ofReal_ofNat, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.ofReal_re]

private def qubitDiag (v : Fin 2 → ℝ) : Qubit :=
  diagonal fun i => (v i : ℂ)

private theorem qubitDiag_hermitian (v : Fin 2 → ℝ) : (qubitDiag v).IsHermitian := by
  simp [qubitDiag, Matrix.isHermitian_diagonal_iff, IsSelfAdjoint]

private theorem qubitDiag_pow (v : Fin 2 → ℝ) (k : ℕ) :
    qubitDiag v ^ k = qubitDiag fun i => v i ^ k := by
  simp [qubitDiag, diagonal_pow, Complex.ofReal_pow]

private theorem cubicDeficit_diag {r : ℝ} (hr : 1 ≤ r) (c : ℝ) (v w : Fin 2 → ℝ) :
    cubicDeficit r c (parityBlocks ![qubitDiag v, qubitDiag w]) = orbitValue r c v w 0 0 := by
  have hLog (x : Fin 2 → ℝ) :
      cfc Real.log (qubitDiag x) = qubitDiag fun i => Real.log (x i) := by
    simpa only [qubitDiag, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) x Real.log
  refine cubicDeficit_eval hr c _ _ (qubitDiag_hermitian v) (qubitDiag_hermitian w)
    _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [qubitDiag_pow, hLog]
    simp only [qubitDiag, Matrix.diagonal_apply_eq,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, orbitMoment, moment,
      Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, sub_self, zero_mul, one_mul,
      zero_add, add_zero, true_and, forall_const, Fin.sum_univ_two, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re]

private def swap (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![v 1, v 0]

/-- Assign the even and odd levels to the diagonal in physical occupation order. -/
def diagonalEndpoint (v w : Fin 2 → ℝ) : Mat :=
  diagonal fun i => ((![v 0, w 0, w 1, v 1] (finProdFinEquiv i) : ℝ) : ℂ)

private theorem parityBlocks_diagonal (v w : Fin 2 → ℝ) :
    parityBlocks ![qubitDiag v, qubitDiag w] = diagonalEndpoint v w := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [parityBlocks_apply, qubitDiag, xorBit, diagonalEndpoint, finProdFinEquiv]

private theorem orbitValue_average (r c : ℝ) (v w : Fin 2 → ℝ) (p q : ℝ) :
    orbitValue r c v w p q =
      ((1 - p) * (1 - q)) * orbitValue r c v w 0 0 +
      ((1 - p) * q) * orbitValue r c v (swap w) 0 0 +
      (p * (1 - q)) * orbitValue r c (swap v) w 0 0 +
      (p * q) * orbitValue r c (swap v) (swap w) 0 0 := by
  simp only [orbitValue, orbitMoment, moment, swap, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_zero, zero_mul, one_mul, add_zero]
  rw [add_comm (v 1 ^ 3) (v 0 ^ 3), add_comm (w 1 ^ 3) (w 0 ^ 3)]
  ring

/-- The parity deficit equals the average of its four physical diagonal assignments.
The two weights come from the chosen eigenframes of the respective blocks. -/
theorem cubicDeficit_parity_orbit {r : ℝ} (hr : 1 ≤ r) (c : ℝ) {A B : Qubit}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let v := hA.eigenvalues
    let w := hB.eigenvalues
    let p := Complex.normSq ((hA.eigenvectorUnitary : Qubit) 0 1)
    let q := Complex.normSq ((hB.eigenvectorUnitary : Qubit) 0 1)
    let endpoint (x y : Fin 2 → ℝ) := cubicDeficit r c (diagonalEndpoint x y)
    cubicDeficit r c (parityBlocks ![A,B]) =
      ((1 - p) * (1 - q)) * endpoint v w +
      ((1 - p) * q) * endpoint v ![w 1, w 0] +
      (p * (1 - q)) * endpoint ![v 1, v 0] w +
      (p * q) * endpoint ![v 1, v 0] ![w 1, w 0] := by
  dsimp only
  obtain ⟨_, _, hmA⟩ := qubit_diagonal_moments hA
  obtain ⟨_, _, hmB⟩ := qubit_diagonal_moments hB
  simp only [← parityBlocks_diagonal, cubicDeficit_diag hr]
  rw [cubicDeficit_eval hr c A B hA hB _ _ _ _ hmA hmB
    (by simpa only [Fin.sum_univ_two] using trace_cube hA)
    (by simpa only [Fin.sum_univ_two] using trace_cube hB)
    (by simpa only [Fin.sum_univ_two] using trace_cube_log hA)
    (by simpa only [Fin.sum_univ_two] using trace_cube_log hB)]
  exact orbitValue_average _ _ _ _ _ _

private theorem diagonalEndpoint_bound {r : ℝ} (hr : 1 ≤ r) (v w : Fin 2 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ cubicDeficit r (alpha r) (diagonalEndpoint v w) := by
  let A := qubitDiag ![v 0, w 0]
  let B := qubitDiag ![w 1, v 1]
  have hA : A.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr (hv 0)
    · exact Complex.zero_le_real.mpr (hw 0)
  have hB : B.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr (hw 1)
    · exact Complex.zero_le_real.mpr (hv 1)
  have hM : occupationBlocks ![A,B] = diagonalEndpoint v w := by
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [occupationBlocks_apply, A, B, qubitDiag, diagonalEndpoint, finProdFinEquiv]
  have h := WuCubicConditionalTensorization.occupation_conditional_bound hr hA hB
  have h' : 0 ≤ cubicDeficit r (alpha r) (occupationBlocks ![A,B]) := sub_nonneg.mpr h
  exact hM ▸ h'

/-- Wu's equal-cap cubic bound for arbitrary PSD blocks in the two physical
parity sectors, including zero and repeated eigenvalues. -/
private theorem parity_matrix_psd_bound {r : ℝ} (hr : 1 ≤ r) {A B : Qubit}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let M := parityBlocks ![A,B]
    let X := GInv r * M * GInv r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re := by
  apply sub_nonneg.mp
  change 0 ≤ cubicDeficit r (alpha r) (parityBlocks ![A,B])
  rw [cubicDeficit_parity_orbit hr (alpha r) hA.1 hB.1]
  obtain ⟨hp0, hp1, _⟩ := qubit_diagonal_moments hA.1
  obtain ⟨hq0, hq1, _⟩ := qubit_diagonal_moments hB.1
  have hv := hA.eigenvalues_nonneg
  have hw := hB.eigenvalues_nonneg
  have hvs : ∀ i, 0 ≤ (![hA.1.eigenvalues 1, hA.1.eigenvalues 0] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · exact hv 1
    · exact hv 0
  have hws : ∀ i, 0 ≤ (![hB.1.eigenvalues 1, hB.1.eigenvalues 0] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · exact hw 1
    · exact hw 0
  dsimp only
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1))
      (diagonalEndpoint_bound hr _ _ hv hw))
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) hq0)
      (diagonalEndpoint_bound hr _ _ hv hws)))
    (mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hq1))
      (diagonalEndpoint_bound hr _ _ hvs hw)))
    (mul_nonneg (mul_nonneg hp0 hq0)
      (diagonalEndpoint_bound hr _ _ hvs hws))


/-- The physical parity operator in the occupation basis `00,01,10,11`. -/
def parityOperator : Mat :=
  diagonal fun i => if xorBit i.1 i.2 = 0 then 1 else -1

private theorem parity_reconstruct (M : Mat) (h : Commute parityOperator M) :
    parityBlocks (fun b => M.submatrix (fun k => parityIndex (b,k))
      (fun k => parityIndex (b,k))) = M := by
  have hEntry (i j : Occupation) :
      (if xorBit i.1 i.2 = 0 then (1 : ℂ) else -1) * M i j =
        M i j * (if xorBit j.1 j.2 = 0 then (1 : ℂ) else -1) := by
    simpa only [parityOperator, Matrix.diagonal_mul, Matrix.mul_diagonal] using
      congrArg (fun N : Mat => N i j) h.eq
  ext ⟨i,j⟩ ⟨k,l⟩
  have he := hEntry (i,j) (k,l)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [parityBlocks_apply, parityIndex, xorBit, Matrix.submatrix_apply] at he ⊢
  all_goals first | linear_combination (1 / 2 : ℂ) * he | linear_combination -(1 / 2 : ℂ) * he

/-- Wu's equal-cap cubic inequality for a PSD observable commuting with the
physical parity operator. -/
theorem cubic_inequality_of_commute_parity {r : ℝ} (hr : 1 ≤ r) {X : Mat}
    (hX : X.PosSemidef) (hParity : Commute parityOperator X) :
    let M := G r * X * G r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re := by
  let M := G r * X * G r
  have hG : (G r).IsHermitian := by
    simp [G, Matrix.isHermitian_diagonal_iff, IsSelfAdjoint]
  have hM : M.PosSemidef := by
    simpa only [M, hG.eq] using hX.mul_mul_conjTranspose_same (G r)
  have hPG : Commute parityOperator (G r) := by
    change parityOperator * G r = G r * parityOperator
    simp only [parityOperator, G, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hPM : Commute parityOperator M := (hPG.mul_right hParity).mul_right hPG
  let A := M.submatrix (fun k => parityIndex (0,k)) (fun k => parityIndex (0,k))
  let B := M.submatrix (fun k => parityIndex (1,k)) (fun k => parityIndex (1,k))
  have hBlocks : parityBlocks ![A,B] = M := by
    rw [show (![A,B] : Fin 2 → Qubit) = fun b =>
      M.submatrix (fun k => parityIndex (b,k)) (fun k => parityIndex (b,k)) by
        funext b; fin_cases b <;> rfl]
    exact parity_reconstruct M hPM
  have hBound := parity_matrix_psd_bound hr (A := A) (B := B) (hM.submatrix _) (hM.submatrix _)
  dsimp only at hBound
  have hX' : GInv r * M * GInv r = X := by
    calc
      _ = (GInv r * G r) * X * (G r * GInv r) := by simp only [M, Matrix.mul_assoc]
      _ = X := by rw [GInv_mul_G hr, G_mul_GInv hr, Matrix.one_mul, Matrix.mul_one]
  rw [hBlocks, hX'] at hBound
  exact hBound

end D5.S3.Quantum.Semigroups.WuParityOrbit
