/- GID: D5/S3/Quantum/Semigroups/WuParityCoherence
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuParityCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed parity interference and the exact four-square defect at fixed occupation. -/

import D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The directed CAR jump traces across physical parity and the exact occupation-constrained
CAR trace for rank-two projections. All traces are unnormalized. -/

set_option autoImplicit false

noncomputable section

open Matrix Kronecker
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuParityCoherence

open WuPhysicalHighHigh (Occupation Mat phi psi)
open TwistedTwoModeOUComparison (modeJump)

private abbrev Block := Matrix (Fin 2) (Fin 2) ℂ

private def evenSites : Fin 2 → Occupation := ![(0, 0), (1, 1)]
private def oddSites : Fin 2 → Occupation := ![(0, 1), (1, 0)]

/-- The even-to-even block, with sites ordered as 00, 11. -/
def A (M : Mat) : Matrix (Fin 2) (Fin 2) ℂ := M.submatrix evenSites evenSites

/-- The even-row, odd-column block, with rows 00, 11 and columns 01, 10. -/
def B (M : Mat) : Matrix (Fin 2) (Fin 2) ℂ := M.submatrix evenSites oddSites

private def C (M : Mat) : Block := M.submatrix oddSites oddSites

/-- The determinant with first row `u` and second row `v`. -/
def rowDet (u v : Fin 2 → ℂ) : ℂ := u 0 * v 1 - u 1 * v 0

/-- Retain only opposite-parity entries in the physical occupation basis. -/
private def crossParity (X : Mat) : Mat :=
  Matrix.of fun i j => if (i.1 = i.2) ↔ (j.1 = j.2) then 0 else X i j

/-- The opposite-parity contribution from the lowering sandwiches. -/
def phiInterference (M : Mat) : ℝ := ((M ^ 2) * crossParity (phi M)).trace.re

/-- The opposite-parity contribution from the raising sandwiches. -/
def psiInterference (M : Mat) : ℝ := ((M ^ 2) * crossParity (psi M)).trace.re

private theorem jump_zero :
    modeJump 0 = (!![0,1;0,0] : Block) ⊗ₖ 1 := rfl

private theorem jump_one :
    modeJump 1 = diagonal (![-1,1] : Fin 2 → ℂ) ⊗ₖ (!![0,1;0,0] : Block) := rfl

set_option maxHeartbeats 2000000 in
private theorem signed_traces_aux (M N : Mat) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (N * crossParity (phi M)).trace.re = 2 * (rowDet (B N 0) (B M 1)).re ∧
    (N * crossParity (psi M)).trace.re = 2 * (rowDet (B M 0) (B N 1)).re := by
  -- Expand the jump sandwiches before substituting the conjugate entries.
  constructor <;>
    norm_num [crossParity, phi, psi, jump_zero, jump_one, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      rowDet, B, evenSites, oddSites] <;>
    simp [← hM.apply (0, 1) (0, 0), ← hM.apply (1, 0) (0, 0),
      ← hM.apply (0, 1) (1, 1), ← hM.apply (1, 0) (1, 1),
      ← hN.apply (0, 1) (0, 0), ← hN.apply (1, 0) (0, 0),
      ← hN.apply (0, 1) (1, 1), ← hN.apply (1, 0) (1, 1),
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re] <;> ring

/-- The two directed jump sandwiches give signed row determinants. Their physical
coefficients give the opposite-parity term of the two-mode cubic deficit. -/
theorem signed_interference (r : ℝ) (M : Mat) (hM : M.IsHermitian) :
    let γ : ℝ := 9 / (4 * (1 + r ^ 3))
    phiInterference M = 2 * (rowDet (B (M ^ 2) 0) (B M 1)).re ∧
    psiInterference M = 2 * (rowDet (B M 0) (B (M ^ 2) 1)).re ∧
    -γ * r ^ 2 * phiInterference M - γ * r * psiInterference M =
      -2 * γ * r *
        ((r : ℂ) * rowDet (B (M ^ 2) 0) (B M 1) + rowDet (B M 0) (B (M ^ 2) 1)).re := by
  intro γ
  have mixed :
      phiInterference M = 2 * (rowDet (B (M ^ 2) 0) (B M 1)).re ∧
      psiInterference M = 2 * (rowDet (B M 0) (B (M ^ 2) 1)).re :=
    signed_traces_aux M (M ^ 2) hM (hM.pow 2)
  obtain ⟨hphi, hpsi⟩ := mixed
  refine ⟨hphi, hpsi, ?_⟩
  rw [hphi, hpsi, Complex.add_re, Complex.re_ofReal_mul]
  ring

/-- The ordinary real trace pairing with the two signed CAR jump sums. -/
def carTrace (U V : Mat) : ℝ := (U * (phi V + psi V)).trace.re

private theorem hermitian_diag_im (M : Mat) (hM : M.IsHermitian) (i : Occupation) :
    (M i i).im = 0 := by
  have h := congrArg Complex.im (hM.apply i i)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith only [h]

set_option maxHeartbeats 2000000 in
private theorem trace_mul_phi_entries (M : Mat) :
    (M * phi M).trace =
      M (0, 0) (0, 0) * M (1, 0) (1, 0) + M (0, 1) (0, 1) * M (1, 1) (1, 1) +
      M (0, 0) (0, 1) * M (1, 1) (1, 0) + M (0, 1) (0, 0) * M (1, 0) (1, 1) +
      M (0, 0) (0, 0) * M (0, 1) (0, 1) + M (1, 0) (1, 0) * M (1, 1) (1, 1) -
      M (0, 0) (1, 0) * M (1, 1) (0, 1) - M (1, 0) (0, 0) * M (0, 1) (1, 1) := by
  norm_num [phi, jump_zero, jump_one, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

private theorem trace_mul_psi_eq_phi (M : Mat) : (M * psi M).trace = (M * phi M).trace := by
  have cycle (J : Mat) : (M * (Jᴴ * M * J)).trace = (M * (J * M * Jᴴ)).trace := by
    simpa only [← Matrix.mul_assoc] using Matrix.trace_mul_comm (M * Jᴴ) (M * J)
  simp only [phi, psi, Fin.sum_univ_two, Matrix.mul_add, Matrix.trace_add,
    cycle (modeJump 0), cycle (modeJump 1)]

/-- The literal CAR trace on any Hermitian matrix in the parity order
(00, 11 | 01, 10). The sign of the second jump gives the determinant of the cross block. -/
private theorem carTrace_self (M : Mat) (hM : M.IsHermitian) :
    carTrace M M = 2 * (A M).trace.re * (C M).trace.re + 4 * (B M).det.re := by
  rw [carTrace, Matrix.mul_add, Matrix.trace_add, trace_mul_psi_eq_phi, trace_mul_phi_entries]
  simp only [A, B, C, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.det_fin_two,
    Matrix.submatrix_apply]
  simp [evenSites, oddSites, ← hM.apply (0, 1) (0, 0), ← hM.apply (1, 0) (0, 0),
    ← hM.apply (0, 1) (1, 1), ← hM.apply (1, 0) (1, 1),
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.sub_re, Complex.mul_re,
    hermitian_diag_im M hM]
  ring

/-- The diagonal difference at the two even sites, with the sign of the occupation field. -/
def occupationDifference (M : Mat) : ℝ := (A M 1 1).re - (A M 0 0).re

/-- The even-site diagonal difference equals the occupation trace minus the ordinary trace.
The number operator is 1 - F, with diagonal (0, 1, 1, 2). -/
private theorem occupationDifference_eq_trace (M : Mat) :
    occupationDifference M =
      (((1 : Mat) - WuPhysicalHighHigh.F) * M).trace.re - M.trace.re := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  norm_num [occupationDifference, WuPhysicalHighHigh.F, A, evenSites, Matrix.diagonal_mul,
    Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.add_re, Complex.neg_re] <;> ring

private theorem trace_parity_blocks (M : Mat) : M.trace = (A M).trace + (C M).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    A, C, Matrix.submatrix_apply]
  simp [evenSites, oddSites]
  ring

private def blockNormSq (D : Block) : ℝ :=
  Complex.normSq (D 0 0) + Complex.normSq (D 0 1) +
    Complex.normSq (D 1 0) + Complex.normSq (D 1 1)

private theorem block_determinant_squares (D : Block) :
    Complex.normSq (D 0 0 - star (D 1 1)) + Complex.normSq (D 0 1 + star (D 1 0)) =
      blockNormSq D - 2 * D.det.re := by
  simp only [blockNormSq, Matrix.det_fin_two, Complex.normSq_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re]
  ring

private theorem normSq_mul_star_re (z : ℂ) : (z * star z).re = Complex.normSq z := by
  simpa only [Complex.star_def, Complex.ofReal_re] using congrArg Complex.re (Complex.mul_conj z)

private theorem projection_row_normSq (Q : Mat) (hQ : Q.IsHermitian) (hidem : Q * Q = Q)
    (i : Occupation) : (∑ j : Occupation, Complex.normSq (Q i j)) = (Q i i).re := by
  have hprod : Q * Qᴴ = Q := by rw [hQ.eq, hidem]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, normSq_mul_star_re]
    using congrArg (fun M : Mat => (M i i).re) hprod

private theorem projection_even_diagonal (Q : Mat) (hQ : Q.IsHermitian)
    (hidem : Q * Q = Q) :
    (A Q 0 0).re ^ 2 + (A Q 1 1).re ^ 2 + 2 * Complex.normSq (A Q 0 1) +
      blockNormSq (B Q) = (A Q 0 0).re + (A Q 1 1).re := by
  have diagNorm (i : Occupation) : Complex.normSq (Q i i) = (Q i i).re ^ 2 := by
    simp only [Complex.normSq_apply, hermitian_diag_im Q hQ i, mul_zero, add_zero, pow_two]
  have h00 := projection_row_normSq Q hQ hidem (0, 0)
  have h11 := projection_row_normSq Q hQ hidem (1, 1)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, diagNorm,
    ← hQ.apply (1, 1) (0, 0), Complex.star_def, Complex.normSq_conj] at h00 h11
  simp [A, B, evenSites, oddSites, blockNormSq] <;> linear_combination h00 + h11

/-- The exact four-square defect at fixed occupation for a Hermitian
projection of ordinary trace two. -/
theorem rankTwo_projection_defect (Q : Mat) (hQ : Q.IsHermitian)
    (hidem : Q * Q = Q) (htrace : Q.trace = 2) :
    3 - occupationDifference Q ^ 2 - carTrace Q Q =
      3 * ((A Q).trace.re - 1) ^ 2 + 4 * Complex.normSq (A Q 0 1) +
        2 * Complex.normSq (B Q 0 0 - star (B Q 1 1)) +
        2 * Complex.normSq (B Q 0 1 + star (B Q 1 0)) := by
  have hx : (A Q).trace.re = (A Q 0 0).re + (A Q 1 1).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Complex.add_re]
  have hC : (C Q).trace.re = 2 - (A Q).trace.re := by
    have h := congrArg Complex.re htrace
    rw [trace_parity_blocks, Complex.add_re] at h
    norm_num at h
    linarith only [h]
  rw [carTrace_self Q hQ, hC, hx, occupationDifference]
  linear_combination -2 * projection_even_diagonal Q hQ hidem -
    2 * block_determinant_squares (B Q)

/-- The bound is attained at each allowed occupation by the identity on the first
mode tensored with a real one-mode projection. -/
private theorem rankTwo_projection_attains (L : ℝ) (hlo : -1 ≤ L) (hhi : L ≤ 1) :
    ∃ Q : Mat, Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
      Commute Q (diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ (1 : Block)) ∧
      occupationDifference Q = L ∧ carTrace Q Q = 3 - L ^ 2 := by
  let p : ℝ := (1 - L) / 2
  let q : ℝ := (1 + L) / 2
  let t : ℝ := Real.sqrt (p * q)
  have hp : 0 ≤ p := by dsimp [p]; linarith only [hhi]
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hlo]
  have hpq : p + q = 1 := by dsimp [p, q]; ring
  have ht : t ^ 2 = p * q := Real.sq_sqrt (mul_nonneg hp hq)
  let P : Block := !![(p : ℂ), (t : ℂ); (t : ℂ), (q : ℂ)]
  have hP : P.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [P, Complex.star_def, Complex.conj_ofReal]
  have hPP : P * P = P := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_two, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im]
    all_goals
      first
      | linear_combination p * hpq + ht
      | linear_combination q * hpq + ht
      | linear_combination t * hpq
  have htraceP : P.trace = 1 := by
    simpa [P, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Complex.ofReal_add] using
      congrArg (fun x : ℝ => (x : ℂ)) hpq
  let Q : Mat := (1 : Block) ⊗ₖ P
  have hQ : Q.IsHermitian := by
    change ((1 : Block) ⊗ₖ P)ᴴ = (1 : Block) ⊗ₖ P
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hP.eq]
  have hQQ : Q * Q = Q := by
    simp only [Q, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hPP]
  have htraceQ : Q.trace = 2 := by
    norm_num [Q, Matrix.trace_kronecker, Matrix.trace_one, htraceP]
  have hcomm : Commute Q (diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ (1 : Block)) := by
    show Q * (diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ (1 : Block)) =
      (diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ (1 : Block)) * Q
    simp only [Q, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hL : occupationDifference Q = L := by
    norm_num [occupationDifference, A, evenSites, Q, P, Matrix.kroneckerMap_apply,
      Matrix.one_apply, p, q] <;> ring
  have hx : (A Q).trace.re = 1 := by
    simp only [A, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.submatrix_apply]
    simpa [evenSites, Q, P, Matrix.kroneckerMap_apply, Matrix.one_apply, Complex.add_re] using hpq
  have h := rankTwo_projection_defect Q hQ hQQ htraceQ
  rw [hx, hL] at h
  norm_num [A, B, evenSites, oddSites, Q, P, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Complex.star_def, Complex.conj_ofReal, Complex.normSq_apply] at h
  refine ⟨Q, hQ, hQQ, htraceQ, hcomm, hL, ?_⟩
  linarith only [h]

/-- At total occupation `2 + L` the exact maximum of the ordinary CAR trace is
`3 - L ^ 2`. An attaining projection at that occupation commutes with first-mode occupation. -/
theorem rankTwo_projection_isGreatest (L : ℝ) (hlo : -1 ≤ L) (hhi : L ≤ 1) :
    IsGreatest {g : ℝ | ∃ Q : Mat, Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
      (((1 : Mat) - WuPhysicalHighHigh.F) * Q).trace.re = 2 + L ∧
      carTrace Q Q = g} (3 - L ^ 2) ∧
    ∃ Q : Mat, Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
      Commute Q (diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (((1 : Mat) - WuPhysicalHighHigh.F) * Q).trace.re = 2 + L ∧
      carTrace Q Q = 3 - L ^ 2 := by
  have occupation_at (Q : Mat) (htrace : Q.trace = 2) :
      occupationDifference Q = L ↔
        (((1 : Mat) - WuPhysicalHighHigh.F) * Q).trace.re = 2 + L := by
    have hreal : Q.trace.re = 2 := by norm_num [htrace]
    rw [occupationDifference_eq_trace, hreal]
    constructor <;> intro h <;> linarith only [h]
  obtain ⟨P, hP, hPP, htraceP, hcomm, hL, hmax⟩ := rankTwo_projection_attains L hlo hhi
  have hoccP := (occupation_at P htraceP).mp hL
  refine ⟨⟨?_, ?_⟩, ⟨P, hP, hPP, htraceP, hcomm, hoccP, hmax⟩⟩
  · exact ⟨P, hP, hPP, htraceP, hoccP, hmax⟩
  · rintro g ⟨Q, hQ, hQQ, htrace, hocc, hg⟩
    have h := rankTwo_projection_defect Q hQ hQQ htrace
    rw [(occupation_at Q htrace).mpr hocc, hg] at h
    linarith only [h, sq_nonneg ((A Q).trace.re - 1), Complex.normSq_nonneg (A Q 0 1),
      Complex.normSq_nonneg (B Q 0 0 - star (B Q 1 1)),
      Complex.normSq_nonneg (B Q 0 1 + star (B Q 1 0))]

end D5.S3.Quantum.Semigroups.WuParityCoherence
