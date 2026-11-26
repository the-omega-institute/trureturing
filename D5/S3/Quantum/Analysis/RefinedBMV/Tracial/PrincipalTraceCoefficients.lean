/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/PrincipalTraceCoefficients
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed principal minors imply coefficient positivity of matrix power traces. -/

import D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Complex.Order

namespace RefinedBMV.Tracial

open Matrix
open scoped ComplexOrder

open private detSeries pencil liftMat traceSeries detSeries_mul_traceSeries
  coeff_logderiv_of_one_sub from
  D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion

noncomputable section

private theorem trace_pow_eq_log_coeff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (hm : 0 < m) :
    trace (M ^ m) = (m : ℂ) *
      ∑ j ∈ Finset.Icc 1 m, ((1 - M.charpolyRev) ^ j).coeff m / (j : ℂ) := by
  let f : Polynomial ℂ →+* PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom
  have hdet : detSeries M = (M.charpolyRev : PowerSeries ℂ) := by
    unfold detSeries pencil liftMat Matrix.charpolyRev
    change _ = f _
    rw [f.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    by_cases hij : i = j <;>
      simp [f, hij, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] <;>
        ac_rfl
  let F : PowerSeries ℂ := 1 - detSeries M
  have hzero : PowerSeries.coeff 0 F = 0 := by
    rw [show F = 1 - (M.charpolyRev : PowerSeries ℂ) by simp [F, hdet]]
    have hc : M.charpolyRev.coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    simp [hc]
  have hrel : (1 - F) * traceSeries M = PowerSeries.derivative F := by
    simpa [F] using detSeries_mul_traceSeries M
  have h := coeff_logderiv_of_one_sub F (traceSeries M) hzero hrel m hm
  simpa only [traceSeries, PowerSeries.coeff_mk, Nat.sub_add_cancel (Nat.succ_le_of_lt hm),
    F, hdet, ← Polynomial.coe_one, ← Polynomial.coe_sub, ← Polynomial.coe_pow,
    Polynomial.coeff_coe] using h

private theorem complex_sum_nonneg {α : Type*} (s : Finset α) (f : α → ℂ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i := by
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg fun i hi ↦ (Complex.nonneg_iff.mp (hf i hi)).1
  · rw [Complex.im_sum]
    symm
    exact Finset.sum_eq_zero fun i hi ↦ (Complex.nonneg_iff.mp (hf i hi)).2.symm

private theorem complex_mul_nonneg {x y : ℂ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x * y := by
  obtain ⟨hx', hxi⟩ := Complex.nonneg_iff.mp hx
  obtain ⟨hy', hyi⟩ := Complex.nonneg_iff.mp hy
  rw [Complex.nonneg_iff, Complex.mul_re, Complex.mul_im, ← hxi, ← hyi]
  simpa using mul_nonneg hx' hy'

private theorem coeffMul_nonneg {σ : Type*} {P Q : MvPolynomial σ ℂ}
    (hP : ∀ d, 0 ≤ P.coeff d) (hQ : ∀ d, 0 ≤ Q.coeff d) :
    ∀ d, 0 ≤ (P * Q).coeff d := by
  intro d
  classical
  rw [MvPolynomial.coeff_mul]
  exact complex_sum_nonneg _ _ fun ab _ ↦ complex_mul_nonneg (hP ab.1) (hQ ab.2)

private theorem coeffPower_bounded {σ : Type*}
    (F : Polynomial (MvPolynomial σ ℂ)) (m : ℕ)
    (hF : ∀ k ≤ m, ∀ d, 0 ≤ (F.coeff k).coeff d) (j : ℕ) :
    ∀ k ≤ m, ∀ d, 0 ≤ ((F ^ j).coeff k).coeff d := by
  classical
  induction j with
  | zero =>
    intro k hk d
    by_cases h : k = 0 <;> by_cases hd : (0 : σ →₀ ℕ) = d <;>
      simp [pow_zero, Polynomial.coeff_one, h, hd, MvPolynomial.coeff_one,
        Complex.nonneg_iff]
  | succ j ih =>
    intro k hk d
    rw [pow_succ, Polynomial.coeff_mul, MvPolynomial.coeff_sum]
    refine complex_sum_nonneg _ _ fun ab hab ↦ ?_
    have hsum := Finset.mem_antidiagonal.mp hab
    exact coeffMul_nonneg (ih ab.1 (by omega)) (hF ab.2 (by omega)) d

private theorem map_charpolyRev_eval {σ : Type*} {n : ℕ} (z : σ → ℂ)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
    M.charpolyRev.map (MvPolynomial.eval z) = (M.map (MvPolynomial.eval z)).charpolyRev := by
  let f := (Polynomial.mapRingHom (MvPolynomial.eval z))
  unfold Matrix.charpolyRev
  change f _ = _
  rw [f.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  by_cases hij : i = j <;>
    simp [f, hij, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]

/-- If the reversed characteristic polynomial is one minus a polynomial
with nonnegative coefficients through order m, then the m-th power trace
has nonnegative coefficients in the original variables. -/
theorem trace_pow_coeff_nonneg_of_charpolyRev {σ : Type*} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (m : ℕ) (hm : 0 < m)
    (hM : ∀ k ≤ m, ∀ d, 0 ≤ ((1 - M.charpolyRev).coeff k).coeff d) (d : σ →₀ ℕ) :
    0 ≤ (trace (M ^ m)).coeff d := by
  let : Infinite ℂ := Infinite.of_injective _ Complex.ofReal_injective
  let F := 1 - M.charpolyRev
  have htrace : trace (M ^ m) =
      MvPolynomial.C (m : ℂ) * ∑ j ∈ Finset.Icc 1 m,
        (F ^ j).coeff m * MvPolynomial.C ((j : ℂ)⁻¹) := by
    apply MvPolynomial.funext
    intro z
    let f := MvPolynomial.eval z
    have heval (j : ℕ) :
        f ((F ^ j).coeff m) =
          ((1 - (M.map f).charpolyRev) ^ j).coeff m := by
      rw [← Polynomial.coeff_map, Polynomial.map_pow]
      have hMap : F.map f = 1 - (M.map f).charpolyRev := by
        change (Polynomial.mapRingHom f) (1 - M.charpolyRev) = _
        rw [map_sub, map_one]
        exact congrArg (1 - ·) (map_charpolyRev_eval z M)
      rw [hMap]
    rw [AddMonoidHom.map_trace f, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
    rw [trace_pow_eq_log_coeff _ _ hm]
    simp only [f, map_mul, map_sum, MvPolynomial.eval_C, heval, div_eq_mul_inv]
  rw [htrace, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum]
  have hm' : (0 : ℂ) ≤ (m : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.zero_le_real]
    positivity
  refine complex_mul_nonneg hm' (complex_sum_nonneg _ _ fun j _ ↦ ?_)
  rw [mul_comm, MvPolynomial.coeff_C_mul]
  have hj : (0 : ℂ) ≤ ((j : ℂ)⁻¹) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.zero_le_real]
    positivity
  exact complex_mul_nonneg hj (coeffPower_bounded F m hM j m le_rfl d)

/-- The sign criterion requires only the principal minors through the
desired power. Labels may identify coordinates in a common eigenspace. -/
theorem trace_pow_coeff_nonneg_of_signed_minors {σ : Type*} {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (label : Fin n → σ) (m : ℕ) (hm : 0 < m)
    (hB : ∀ s : Finset (Fin n), 0 < s.card → s.card ≤ m →
      0 ≤ (-1 : ℂ) ^ (s.card + 1) *
        (B.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det)
    (d : σ →₀ ℕ) :
    0 ≤ (trace ((diagonal (fun i ↦ MvPolynomial.X (label i)) *
      B.map MvPolynomial.C) ^ m)).coeff d := by
  classical
  let V := MvPolynomial σ ℂ
  let M : Matrix (Fin n) (Fin n) V :=
    diagonal (fun i ↦ MvPolynomial.X (label i)) * B.map MvPolynomial.C
  change 0 ≤ (trace (M ^ m)).coeff d
  apply trace_pow_coeff_nonneg_of_charpolyRev M m hm
  intro k hk a
  by_cases hz : k = 0
  · subst k
    have hc : M.charpolyRev.coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    simp [hc]
  have hpencil : M.charpolyRev =
      det (1 + (Polynomial.X : Polynomial V) • (-M).map Polynomial.C) := by
    rw [Matrix.charpolyRev, sub_eq_add_neg, Matrix.map_neg Polynomial.C (map_neg Polynomial.C),
      smul_neg]
  rw [Polynomial.coeff_sub, Polynomial.coeff_one, ite_eq_right hz, zero_sub, hpencil,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors, ← Finset.sum_neg_distrib,
    MvPolynomial.coeff_sum]
  refine complex_sum_nonneg _ _ fun s hs ↦ ?_
  let e : s → Fin n := Subtype.val
  have hsCard := (Finset.mem_powersetCard.mp hs).2
  have hsign : 0 ≤ -(((-B).submatrix e e).det) := by
    rw [Matrix.submatrix_neg]
    change 0 ≤ -((-(B.submatrix e e)).det)
    rw [Matrix.det_neg, Fintype.card_coe]
    convert hB s (by omega) (by omega) using 1
    rw [pow_succ]
    ring
  have hrestrict : (-M).submatrix e e =
      diagonal (fun i ↦ MvPolynomial.X (label (e i))) *
        (((-B).submatrix e e).map MvPolynomial.C) := by
    ext i j
    simp only [M, Matrix.submatrix_apply, Matrix.neg_apply, Matrix.diagonal_mul,
      Matrix.map_apply, map_neg, mul_neg]
  change 0 ≤ (-(((-M).submatrix e e).det)).coeff a
  rw [hrestrict, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← mul_neg, ← map_neg, mul_comm]
  rw [show (∏ i : s, MvPolynomial.X (label (e i)) : V) =
      MvPolynomial.monomial (∑ i : s, Finsupp.single (label (e i)) 1) 1 by
    rw [MvPolynomial.monomial_sum_one]
    rfl]
  rw [MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
  split
  · exact hsign
  · exact le_rfl

#print axioms trace_pow_coeff_nonneg_of_charpolyRev
#print axioms trace_pow_coeff_nonneg_of_signed_minors

end
end RefinedBMV.Tracial
