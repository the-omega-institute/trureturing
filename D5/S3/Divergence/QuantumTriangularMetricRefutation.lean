/- GID: D5/S3/Divergence/QuantumTriangularMetricRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/QuantumTriangularMetricRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/QuantumTriangularMetricRefutation.claim; result=D5/S3/Divergence/QuantumTriangularMetricRefutation.result; claim=D5/S3/Divergence/QuantumTriangularMetricRefutation.claim
   digest: The square root of quantum triangular discrimination has no quasi-triangle bound. -/

/- admission_basis: open-problem-resolution (#31661; Refuted)
   escape_witness: bind-only. The external assertion is refuted by pure qubit endpoints
   with coherence t^3 and a diagonal intermediate state with noise t^4.
   Direct frozen dependencies:
     D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.QTD
     D5/S3/Divergence/CoherenceL1RelativeEntropyBound.IsState
     D5/S3/Quantum/Matrix/AlternativeMeanLinearization.half_eq_sqrt
     D5/S3/Quantum/Matrix/AlternativeMeanLinearization.half_inverse
     D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
     D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two
     D5/S3/Quantum/CommutingMidpoint/Fidelity.sqrt_trace_square_two
     D5/S3/Quantum/CommutingMidpoint/Fidelity.sqrt_times_trace_two
   Definitions and live consumers:
     claim: definition; consumer=result
     rho: definition; consumers=rho_state, long_value, short_bound, no_quasi_triangle
     tau: definition; consumers=tau_pos, tau_state, short_value, short_bound, no_quasi_triangle
   Per-declaration proof_shape and live consumers:
     rho_state: bind-only; consumers=short_bound, no_quasi_triangle
     tau_pos: bind-only; consumers=tau_state, short_value
     tau_state: bind-only; consumer=no_quasi_triangle
     inverse_root: bind-only; consumer=short_value
     short_value: bind-only; consumer=short_bound
     short_scalar_bound: bind-only; consumer=short_bound
     long_value: bind-only; consumer=no_quasi_triangle
     qtd_symm: bind-only; consumer=no_quasi_triangle
     short_bound: bind-only; consumer=no_quasi_triangle
     no_quasi_triangle: bind-only; consumer=result
     result: bind-only; designated external open-problem refutation. -/

import D5.S3.Divergence.QuantumTriangularJensenShannonRefutation
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Divergence.QuantumTriangularMetricRefutation

open D5.S3.Divergence.CoherenceL1RelativeEntropyBound (IsState)
open D5.S3.Divergence.QuantumTriangularJensenShannonRefutation (QTD)
open D5.S3.Quantum.Matrix.AlternativeMeanLinearization (half_eq_sqrt half_inverse)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)

/-- The triangle assertion in Liu's Open Problem 8.16, with every finite dimension. -/
def claim : Prop :=
  ∀ (n : ℕ) (ρ₀ ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℂ),
    IsState ρ₀ → IsState ρ₁ → IsState ρ₂ →
      Real.sqrt (QTD ρ₀ ρ₂) ≤ Real.sqrt (QTD ρ₀ ρ₁) + Real.sqrt (QTD ρ₁ ρ₂)

private def rho (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 / (1 + r ^ 2) : ℝ) : ℂ), ((r / (1 + r ^ 2) : ℝ) : ℂ);
    ((r / (1 + r ^ 2) : ℝ) : ℂ), ((r ^ 2 / (1 + r ^ 2) : ℝ) : ℂ)]

private def tau (b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![((1 - b : ℝ) : ℂ), (b : ℂ)]

private lemma rho_state (r : ℝ) : IsState (rho r) := by
  have hn : 0 < 1 + r ^ 2 := by positivity
  constructor
  · have he : rho r = (1 / (1 + r ^ 2) : ℝ) •
        vecMulVec (![1, (r : ℂ)]) (star ![1, (r : ℂ)]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rho, vecMulVec, div_eq_mul_inv] <;> ring
    rw [he]
    exact (posSemidef_vecMulVec_self_star _).smul (by positivity)
  · simp [rho, trace_fin_two, ← Complex.ofReal_add]
    norm_cast
    field_simp

private lemma tau_pos (b : ℝ) (hb : 0 < b) (hb1 : b < 1) : (tau b).PosDef := by
  apply PosDef.diagonal
  intro i
  fin_cases i
  · change (0 : ℂ) < ((1 - b : ℝ) : ℂ)
    exact_mod_cast sub_pos.mpr hb1
  · change (0 : ℂ) < (b : ℂ)
    exact_mod_cast hb

private lemma tau_state (b : ℝ) (hb : 0 < b) (hb1 : b < 1) : IsState (tau b) := by
  exact ⟨(tau_pos b hb hb1).posSemidef, by simp [tau, trace_fin_two]⟩

private lemma inverse_root (x c d : ℝ) (hd : 0 < d)
    (hd2 : d ^ 2 = x * (2 - x) - c ^ 2)
    (hS : (!![((2 - x : ℝ) : ℂ), (c : ℂ);
      (c : ℂ), (x : ℂ)]).PosDef) :
    cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ)))
        !![((2 - x : ℝ) : ℂ), (c : ℂ); (c : ℂ), (x : ℂ)] =
      ((d * Real.sqrt (2 + 2 * d))⁻¹ : ℝ) •
        (((2 + d : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) -
          !![((2 - x : ℝ) : ℂ), (c : ℂ); (c : ℂ), (x : ℂ)]) := by
  let S : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((2 - x : ℝ) : ℂ), (c : ℂ); (c : ℂ), (x : ℂ)]
  let s := Real.sqrt (2 + 2 * d)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 2 + 2 * d := Real.sq_sqrt (by linarith)
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hd2c : (d : ℂ) ^ 2 = (x : ℂ) * (2 - x) - (c : ℂ) ^ 2 := by
    exact_mod_cast hd2
  have hs2c : (s : ℂ) ^ 2 = 2 + 2 * (d : ℂ) := by exact_mod_cast hs2
  let T : Matrix (Fin 2) (Fin 2) ℂ := (s⁻¹ : ℝ) • (S + d • 1)
  have hdet : S.det.re = d ^ 2 := by
    simp [S, Matrix.det_fin_two, Complex.mul_re]
    nlinarith only [hd2]
  have hdetroot : Real.sqrt S.det.re = d := by
    rw [hdet, Real.sqrt_sq hd.le]
  have htrace : (trace (CFC.sqrt S)).re = s := by
    have h := D5.S3.Quantum.CommutingMidpoint.sqrt_trace_square_two S hS.posSemidef
    rw [hdetroot] at h
    have hn := (Complex.nonneg_iff.mp (CFC.sqrt_nonneg S).posSemidef.trace_nonneg).1
    have ht : (trace S).re = 2 := by simp [S, trace_fin_two]
    rw [ht] at h
    nlinarith only [h, hs2, hn, hs]
  have hroot : CFC.sqrt S = T := by
    have h := D5.S3.Quantum.CommutingMidpoint.sqrt_times_trace_two S hS.posSemidef
    rw [hdetroot, htrace] at h
    have hr : s • CFC.sqrt S = S + d • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      simpa [Complex.real_smul, smul_eq_mul] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) h
    simpa only [T, smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using
      congrArg (fun M => (s⁻¹ : ℝ) • M) hr
  have hTR : T * cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) S = 1 := by
    rw [← hroot,
      ← D5.S3.Quantum.Matrix.AlternativeMeanLinearization.half_eq_sqrt hS]
    exact (D5.S3.Quantum.Matrix.AlternativeMeanLinearization.half_inverse hS).1
  let U : Matrix (Fin 2) (Fin 2) ℂ :=
    ((d * s)⁻¹ : ℝ) • (((2 + d : ℝ) • 1) - S)
  have hUT : U * T = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [U, T, S, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
      push_cast
      field_simp [hd0, hs0]
    · linear_combination -hd2c - (d : ℂ) * hs2c
    · ring
    · ring
    · linear_combination -hd2c - (d : ℂ) * hs2c
  change cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) S = U
  calc
    cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) S =
        (U * T) * cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) S := by
          rw [hUT, one_mul]
    _ = U := by rw [mul_assoc, hTR, mul_one]


private lemma short_value (a b c d : ℝ) (hc : c ^ 2 = a * (1 - a))
    (hb : 0 < b) (hb1 : b < 1) (hd : 0 < d)
    (hd2 : d ^ 2 = b * (2 - b) + (1 - 2 * b) * a)
    (hA : (!![((1 - a : ℝ) : ℂ), (c : ℂ);
      (c : ℂ), (a : ℂ)]).PosSemidef) :
    QTD !![((1 - a : ℝ) : ℂ), (c : ℂ); (c : ℂ), (a : ℂ)] (tau b) =
      (b ^ 2 + (1 - 2 * b) * a) / d +
        (b * (1 - b)) ^ 2 / (d ^ 2 * (1 + d)) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((1 - a : ℝ) : ℂ), (c : ℂ); (c : ℂ), (a : ℂ)]
  let S : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((2 - (a + b) : ℝ) : ℂ), (c : ℂ); (c : ℂ), ((a + b : ℝ) : ℂ)]
  let s := Real.sqrt (2 + 2 * d)
  let R : Matrix (Fin 2) (Fin 2) ℂ :=
    ((d * s)⁻¹ : ℝ) • (((2 + d : ℝ) • 1) - S)
  have hsum : A + tau b = S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, S, tau] <;> push_cast <;> ring
  have hS : S.PosDef := hsum ▸ Matrix.PosDef.posSemidef_add hA (tau_pos b hb hb1)
  have hc' : (c : ℂ) ^ 2 = (a : ℂ) * (1 - a) := by exact_mod_cast hc
  have hd' : (d : ℂ) ^ 2 = (b : ℂ) * (2 - b) + (1 - 2 * b) * a := by
    exact_mod_cast hd2
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : (s : ℂ) ^ 2 = 2 + 2 * (d : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (show 0 ≤ 2 + 2 * d by linarith))
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hr : cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) (A + tau b) = R := by
    rw [hsum]
    exact inverse_root (a + b) c d hd (by nlinarith [hc]) hS
  have ht : trace ((A - tau b) * R) =
      (((-2 * b * (1 - b) / (d * s) : ℝ)) : ℂ) := by
    simp [A, R, S, tau, trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.real_smul]
    push_cast
    field_simp
    linear_combination -2 * hc'
  have hdetA : det (A - tau b) =
      ((-(b ^ 2 + (1 - 2 * b) * a) : ℝ) : ℂ) := by
    simp [A, tau, det_fin_two]
    push_cast
    linear_combination -hc'
  have hdetR : det R = ((1 / d : ℝ) : ℂ) := by
    simp [R, S, det_fin_two, Complex.real_smul]
    push_cast
    field_simp
    linear_combination -hd' - (d : ℂ) * hs2 - hc'
  have htr := D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two
    ((A - tau b) * R) 0
  simp only [zero_add, pow_one, pow_zero, trace_one, Fintype.card_fin,
    Nat.cast_ofNat, ht, det_mul, hdetA, hdetR] at htr
  change (1 / 2 : ℝ) * (trace ((A - tau b) *
    cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) (A + tau b) * (A - tau b) *
    cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) (A + tau b))).re = _
  rw [hr]
  have he : (A - tau b) * R * (A - tau b) * R = ((A - tau b) * R) ^ 2 := by
    simp only [pow_two, mul_assoc]
  rw [he, htr]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, sub_zero]
  norm_num only
  have hs2r : s ^ 2 = 2 + 2 * d := Real.sq_sqrt (by linarith)
  field_simp [hd.ne', hs.ne']
  rw [hs2r]
  ring

private lemma short_scalar_bound (t a d : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4)
    (ha0 : 0 ≤ a) (ha1 : a ≤ t ^ 6) (hd : 0 < d)
    (hd2 : d ^ 2 = t ^ 4 * (2 - t ^ 4) + (1 - 2 * t ^ 4) * a) :
    (t ^ 8 + (1 - 2 * t ^ 4) * a) / d +
        (t ^ 4 * (1 - t ^ 4)) ^ 2 / (d ^ 2 * (1 + d)) ≤
      (83 / 48 : ℝ) * t ^ 4 := by
  have ht2 : t ^ 2 ≤ (1 / 16 : ℝ) := by
    have h := pow_le_pow_left₀ ht.le ht1 2
    norm_num at h
    exact h
  have ht4 : t ^ 4 ≤ (1 / 256 : ℝ) := by
    have h := pow_le_pow_left₀ ht.le ht1 4
    norm_num at h
    exact h
  have ht8 : t ^ 8 ≤ t ^ 6 / 16 := by
    nlinarith [mul_nonneg (pow_nonneg ht.le 6) (sub_nonneg.mpr ht2)]
  have hcoeff : 0 ≤ 1 - 2 * t ^ 4 := by linarith
  have hbase : (3 / 2 : ℝ) * t ^ 4 ≤ t ^ 4 * (2 - t ^ 4) := by
    nlinarith [mul_nonneg (pow_nonneg ht.le 4)
      (show 0 ≤ 1 / 2 - t ^ 4 by linarith)]
  have hdet : (3 / 2 : ℝ) * t ^ 4 ≤ d ^ 2 := by
    linarith [mul_nonneg hcoeff ha0]
  have hdt : t ^ 2 ≤ d := by
    apply (sq_le_sq₀ (sq_nonneg t) hd.le).mp
    nlinarith [pow_nonneg ht.le 4]
  have hu : t ^ 8 + (1 - 2 * t ^ 4) * a ≤ (17 / 16 : ℝ) * t ^ 6 := by
    nlinarith [mul_nonneg (pow_nonneg ht.le 4) ha0]
  have huq : (t ^ 8 + (1 - 2 * t ^ 4) * a) / d ≤
      (17 / 16 : ℝ) * t ^ 4 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (pow_nonneg ht.le 4) (sub_nonneg.mpr hdt)]
  have hfactor : (1 - t ^ 4) ^ 2 ≤ 1 := by
    nlinarith [pow_nonneg ht.le 4,
      mul_nonneg (pow_nonneg ht.le 4)
        (show 0 ≤ 1 - t ^ 4 by linarith)]
  have hv : (t ^ 4 * (1 - t ^ 4)) ^ 2 ≤ t ^ 8 := by
    calc
      (t ^ 4 * (1 - t ^ 4)) ^ 2 = t ^ 8 * (1 - t ^ 4) ^ 2 := by ring
      _ ≤ t ^ 8 * 1 :=
        mul_le_mul_of_nonneg_left hfactor (pow_nonneg ht.le 8)
      _ = t ^ 8 := mul_one _
  have htmp : t ^ 8 ≤ ((2 / 3 : ℝ) * t ^ 4) * d ^ 2 := by
    nlinarith [mul_nonneg (pow_nonneg ht.le 4) (sub_nonneg.mpr hdet)]
  have hvq : (t ^ 4 * (1 - t ^ 4)) ^ 2 / (d ^ 2 * (1 + d)) ≤
      (2 / 3 : ℝ) * t ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < d ^ 2 * (1 + d))).mpr
    have hp : 0 ≤ ((2 / 3 : ℝ) * t ^ 4) * d ^ 2 := by positivity
    nlinarith [mul_nonneg hp hd.le]
  linarith

private lemma long_value (r : ℝ) (hr : 0 < r) :
    QTD (rho r) (rho (-r)) = 2 * r / (1 + r ^ 2) := by
  let h := 1 + r ^ 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hx : 0 < 2 / h := by positivity
  have hy : 0 < 2 * r ^ 2 / h := by positivity
  have hsum : rho r + rho (-r) =
      diagonal (fun i : Fin 2 => (![2 / h, 2 * r ^ 2 / h] i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho, h, diagonal] <;> push_cast <;> ring
  have hp (x : ℝ) (hx : 0 ≤ x) :
      x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]
  have hsx : 0 < Real.sqrt (2 / h) := Real.sqrt_pos.mpr hx
  have hsy : 0 < Real.sqrt (2 * r ^ 2 / h) := Real.sqrt_pos.mpr hy
  have hprod : Real.sqrt (2 / h) * Real.sqrt (2 * r ^ 2 / h) = 2 * r / h := by
    rw [← Real.sqrt_mul hx.le]
    have he : 2 / h * (2 * r ^ 2 / h) = (2 * r / h) ^ 2 := by ring
    rw [he, Real.sqrt_sq (by positivity)]
  have hcf : cfc (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) (rho r + rho (-r)) =
      diagonal ![(((Real.sqrt (2 / h))⁻¹ : ℝ) : ℂ),
        (((Real.sqrt (2 * r ^ 2 / h))⁻¹ : ℝ) : ℂ)] := by
    rw [hsum, cfc_diagonal]
    congr 1
    funext i
    fin_cases i
    · simpa using congrArg Complex.ofReal (hp (2 / h) hx.le)
    · simpa using congrArg Complex.ofReal (hp (2 * r ^ 2 / h) hy.le)
  have hdiff : rho r - rho (-r) =
      !![0, ((2 * r / h : ℝ) : ℂ); ((2 * r / h : ℝ) : ℂ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho, h] <;> push_cast <;> ring
  rw [QTD, hcf, hdiff]
  simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    diagonal_apply, cons_val_zero, cons_val_one, cons_val_fin_one, Fin.reduceEq,
    ↓reduceIte, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
    Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  change _ = 2 * r / h
  calc
    _ = 4 * (r / h) ^ 2 /
        (Real.sqrt (2 / h) * Real.sqrt (2 * r ^ 2 / h)) := by
      field_simp
      ring
    _ = 2 * r / h := by rw [hprod]; field_simp; ring

private lemma qtd_symm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    QTD A B = QTD B A := by
  rw [QTD, QTD, add_comm B A, show B - A = -(A - B) by abel]
  simp only [neg_mul, mul_neg, neg_neg]

private lemma short_bound (t r : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 4)
    (hr : r ^ 2 = t ^ 6) : QTD (rho r) (tau (t ^ 4)) < (7 / 4 : ℝ) * t ^ 4 := by
  let a := r ^ 2 / (1 + r ^ 2)
  let b := t ^ 4
  let c := r / (1 + r ^ 2)
  let d := Real.sqrt (b * (2 - b) + (1 - 2 * b) * a)
  have hn : 0 < 1 + r ^ 2 := by positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hat : a ≤ t ^ 6 := by
    dsimp [a]
    rw [div_le_iff₀ hn, ← hr]
    nlinarith [sq_nonneg (r ^ 2)]
  have hb : 0 < b := pow_pos ht 4
  have hbsmall : b ≤ (1 / 256 : ℝ) := by
    dsimp [b]
    calc
      t ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ ht.le ht1 4
      _ = 1 / 256 := by norm_num
  have hb1 : b < 1 := by linarith
  have hdet : 0 < b * (2 - b) + (1 - 2 * b) * a := by
    have : 0 ≤ (1 - 2 * b) * a := mul_nonneg (by linarith) ha
    have : 0 < b * (2 - b) := mul_pos hb (by linarith)
    linarith
  have hd : 0 < d := Real.sqrt_pos.mpr hdet
  have hd2 : d ^ 2 = b * (2 - b) + (1 - 2 * b) * a := Real.sq_sqrt hdet.le
  have hc : c ^ 2 = a * (1 - a) := by
    dsimp [a, c]
    field_simp
    ring
  have he : rho r = !![((1 - a : ℝ) : ℂ), (c : ℂ); (c : ℂ), (a : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [rho, a, c, cons_val_zero, cons_val_one, cons_val_fin_one]
    all_goals congr 1 <;> field_simp [hn.ne'] <;> ring
  have hval := short_value a b c d hc hb hb1 hd hd2 (he ▸ (rho_state r).1)
  rw [← he] at hval
  rw [hval]
  have hs := short_scalar_bound t a d ht ht1 ha hat hd hd2
  have hp : b ^ 2 = t ^ 8 := by dsimp [b]; ring
  rw [hp]
  exact hs.trans_lt (by nlinarith [pow_pos ht 4])

/-- No finite real constant gives a uniform quasi-triangle inequality, even on qubits. -/
theorem no_quasi_triangle : ∀ K : ℝ,
    ∃ ρ₀ ρ₁ ρ₂ : Matrix (Fin 2) (Fin 2) ℂ,
      IsState ρ₀ ∧ IsState ρ₁ ∧ IsState ρ₂ ∧
        K * (Real.sqrt (QTD ρ₀ ρ₁) + Real.sqrt (QTD ρ₁ ρ₂)) <
          Real.sqrt (QTD ρ₀ ρ₂) := by
  intro K
  let M := max K 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  let t := 1 / (8 * M ^ 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 4 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 8 * M ^ 2)).mpr
    nlinarith [sq_nonneg (M - 1)]
  have ht4 : t ^ 4 < 1 := by
    have h := pow_le_pow_left₀ ht.le ht1 4
    norm_num at h
    linarith
  have hshort0 := short_bound t (t ^ 3) ht ht1 (by ring)
  have hshort1 := short_bound t (-(t ^ 3)) ht ht1 (by ring)
  rw [qtd_symm (rho (-(t ^ 3))) (tau (t ^ 4))] at hshort1
  have hlong := long_value (t ^ 3) (pow_pos ht 3)
  have ht6 : t ^ 6 ≤ 1 := by
    calc
      t ^ 6 ≤ (1 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ ht.le ht1 6
      _ ≤ 1 := by norm_num
  have hlower : t ^ 3 ≤ QTD (rho (t ^ 3)) (rho (-(t ^ 3))) := by
    rw [hlong]
    apply (le_div_iff₀ (by positivity : 0 < 1 + (t ^ 3) ^ 2)).mpr
    nlinarith [mul_nonneg (pow_nonneg ht.le 3) (sub_nonneg.mpr ht6)]
  let B := Real.sqrt ((7 / 4 : ℝ) * t ^ 4)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B ^ 2 = (7 / 4 : ℝ) * t ^ 4 := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (QTD (rho (t ^ 3)) (tau (t ^ 4))) ≤ B :=
    Real.sqrt_le_sqrt hshort0.le
  have hs1 : Real.sqrt (QTD (tau (t ^ 4)) (rho (-(t ^ 3)))) ≤ B :=
    Real.sqrt_le_sqrt hshort1.le
  have hscale : 7 * M ^ 2 * t ^ 4 = (7 / 8 : ℝ) * t ^ 3 := by
    dsimp [t]
    field_simp
  have hsq : (M * (2 * B)) ^ 2 < QTD (rho (t ^ 3)) (rho (-(t ^ 3))) := by
    have he : (M * (2 * B)) ^ 2 = 7 * M ^ 2 * t ^ 4 := by
      calc
        (M * (2 * B)) ^ 2 = 4 * M ^ 2 * B ^ 2 := by ring
        _ = 7 * M ^ 2 * t ^ 4 := by rw [hB2]; ring
    rw [he, hscale]
    nlinarith [pow_pos ht 3]
  have hstrict : M * (2 * B) <
      Real.sqrt (QTD (rho (t ^ 3)) (rho (-(t ^ 3)))) := by
    apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt ((pow_nonneg ht.le 3).trans hlower)]
    exact hsq
  refine ⟨rho (t ^ 3), tau (t ^ 4), rho (-(t ^ 3)), rho_state _,
    tau_state _ (pow_pos ht 4) ht4, rho_state _, ?_⟩
  calc
    K * _ ≤ M * _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ ≤ M * (2 * B) := mul_le_mul_of_nonneg_left (by linarith) hM.le
    _ < _ := hstrict

/-- The universal triangle assertion in Open Problem 8.16 is false. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨A, B, C, hA, hB, hC, hlt⟩ := no_quasi_triangle 1
  have hle := h 2 A B C hA hB hC
  exact (not_lt_of_ge hle) (by simpa only [one_mul] using hlt)

end D5.S3.Divergence.QuantumTriangularMetricRefutation
