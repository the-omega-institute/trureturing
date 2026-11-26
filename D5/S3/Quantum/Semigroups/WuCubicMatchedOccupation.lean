/- GID: D5/S3/Quantum/Semigroups/WuCubicMatchedOccupation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicMatchedOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic paired modular energy controls the Hellinger distance between endpoint laws. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Semigroups.WuModularEdgeSpectral

/-!
A quantitative comparison with the matched-occupation product energy at exponent three
for Wu, arXiv:2610.33686v1, Remark 3.15. The two normalized endpoint laws use the
same physical jump entries in the density eigenframe.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation

open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open WuCubicConditionalTensorization (trace_diagonal_overlap)
open WuModularEdgeSpectral (coshEdgeKernel edgeKernel_eq_cosh edgeWeight
  generatorTrace_eq_cosh pairedGenerator)

/-- The pointwise weighted arithmetic-geometric mean deficit. -/
private def youngDeficit (p P Q : ℝ) : ℝ :=
  p * P + (1 - p) * Q - P ^ p * Q ^ (1 - p)

/-- Coefficient of the squared Hellinger distance, normalized as one minus affinity. -/
def hellingerCoefficient (u v : ℝ) : ℝ :=
  4 * (u + v) / 9 + 16 * u * v / (9 * (u + v))

set_option maxHeartbeats 400000 in
-- The sum-of-squares identity expands a degree-six polynomial in the endpoint roots.
private theorem sixthRoot_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (u v : ℝ) :
    (2 * (u + v)^2 + 8 * u * v) * (x^3 - y^3)^2 ≤
      3 * (u + v) * (u * (x^6 + 2 * y^6 - 3 * x^2 * y^4) +
        v * (2 * x^6 + y^6 - 3 * x^4 * y^2)) := by
  let S := x + y
  let V := x - y
  let s := u + v
  let d := v - u
  have hSV : S^2 - V^2 = 4 * x * y := by
    dsimp only [S, V]
    ring
  apply sub_nonneg.mp
  calc
    0 ≤ (x - y)^2 * ((s * S * V + (3 / 2 : ℝ) * d * S^2)^2 / 2 +
        s^2 * V^2 * (S^2 - V^2) / 4 + d^2 * (6 * S^2 * V^2 + V^4) / 8) := by
      rw [hSV]
      positivity
    _ = _ := by
      dsimp only [S, V, s, d]
      ring

private theorem sixthRoot_pow {t r : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (hk : (1 / 6 : ℝ) * (k : ℝ) = r) :
    (t ^ (1 / 6 : ℝ)) ^ k = t ^ r := by
  rw [← Real.rpow_mul_natCast ht, hk]

/-- The weighted cubic deficits control the half-power deficit, including at zero endpoints. -/
private theorem youngDeficit_comparison {P Q u v : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hu : 0 < u) (hv : 0 < v) :
    hellingerCoefficient u v * youngDeficit (1 / 2) P Q ≤
      u * youngDeficit (1 / 3) P Q + v * youngDeficit (2 / 3) P Q := by
  let x := P ^ (1 / 6 : ℝ)
  let y := Q ^ (1 / 6 : ℝ)
  have hP2 : x^2 = P ^ (1 / 3 : ℝ) := sixthRoot_pow hP 2 (by norm_num)
  have hP3 : x^3 = P ^ (1 / 2 : ℝ) := sixthRoot_pow hP 3 (by norm_num)
  have hP4 : x^4 = P ^ (2 / 3 : ℝ) := sixthRoot_pow hP 4 (by norm_num)
  have hP6 : x^6 = P :=
    (sixthRoot_pow hP 6 (by norm_num : (1 / 6 : ℝ) * ((6 : ℕ) : ℝ) = 1)).trans
      (Real.rpow_one P)
  have hQ2 : y^2 = Q ^ (1 / 3 : ℝ) := sixthRoot_pow hQ 2 (by norm_num)
  have hQ3 : y^3 = Q ^ (1 / 2 : ℝ) := sixthRoot_pow hQ 3 (by norm_num)
  have hQ4 : y^4 = Q ^ (2 / 3 : ℝ) := sixthRoot_pow hQ 4 (by norm_num)
  have hQ6 : y^6 = Q :=
    (sixthRoot_pow hQ 6 (by norm_num : (1 / 6 : ℝ) * ((6 : ℕ) : ℝ) = 1)).trans
      (Real.rpow_one Q)
  have hhalf : (x^3 - y^3)^2 = 2 * youngDeficit (1 / 2) P Q := by
    calc
      _ = x^6 + y^6 - 2 * (x^3 * y^3) := by ring
      _ = _ := by
        rw [hP6, hQ6, hP3, hQ3, youngDeficit, show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
        ring
  have hs : 0 < u + v := add_pos hu hv
  have hscale : 0 < 9 * (u + v) := by positivity
  have hcoef : (9 * (u + v)) * hellingerCoefficient u v = 4 * (u + v)^2 + 16 * u * v := by
    unfold hellingerCoefficient
    field_simp [hs.ne']
  apply (mul_le_mul_iff_right₀ hscale).mp
  calc
    _ = (2 * (u + v)^2 + 8 * u * v) * (x^3 - y^3)^2 := by
      rw [← mul_assoc, hcoef, hhalf]
      ring
    _ ≤ 3 * (u + v) * (u * (x^6 + 2 * y^6 - 3 * x^2 * y^4) +
          v * (2 * x^6 + y^6 - 3 * x^4 * y^2)) :=
      sixthRoot_bound (Real.rpow_nonneg hP _) (Real.rpow_nonneg hQ _) u v
    _ = _ := by
      rw [hP6, hQ6, hP2, hQ4, hP4, hQ2]
      unfold youngDeficit
      rw [show 1 - (1 / 3 : ℝ) = 2 / 3 by norm_num, show 1 - (2 / 3 : ℝ) = 1 / 3 by norm_num]
      ring

/-- Summing the pointwise estimate over two probability laws on the same finite set. -/
theorem finite_probability_comparison {ι : Type*} [Fintype ι]
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hPsum : (∑ i, P i) = 1) (hQsum : (∑ i, Q i) = 1)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    hellingerCoefficient u v * (1 - ∑ i, Real.sqrt (P i * Q i)) ≤
      u * (1 - ∑ i, P i ^ (1 / 3 : ℝ) * Q i ^ (2 / 3 : ℝ)) +
        v * (1 - ∑ i, P i ^ (2 / 3 : ℝ) * Q i ^ (1 / 3 : ℝ)) := by
  have hsum (p : ℝ) :
      (∑ i, youngDeficit p (P i) (Q i)) = 1 - ∑ i, P i ^ p * Q i ^ (1 - p) := by
    simp only [youngDeficit, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      hPsum, hQsum, mul_one]
    ring
  have hroot (i : ι) :
      P i ^ (1 / 2 : ℝ) * Q i ^ (1 - (1 / 2 : ℝ)) = Real.sqrt (P i * Q i) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (hP i) (hQ i), show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  have h : (∑ i, hellingerCoefficient u v * youngDeficit (1 / 2) (P i) (Q i)) ≤
      ∑ i, (u * youngDeficit (1 / 3) (P i) (Q i) + v * youngDeficit (2 / 3) (P i) (Q i)) :=
    Finset.sum_le_sum fun i _ => youngDeficit_comparison (hP i) (hQ i) hu hv
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hroot,
    show 1 - (1 / 3 : ℝ) = 2 / 3 by norm_num, show 1 - (2 / 3 : ℝ) = 1 / 3 by norm_num] using h

/-- The symmetric cubic edge cost, twice the modular edge kernel at exponent one third. -/
def cubicKernel (X Y : ℝ) : ℝ :=
  X + Y - X ^ (1 / 3 : ℝ) * Y ^ (2 / 3 : ℝ) - X ^ (2 / 3 : ℝ) * Y ^ (1 / 3 : ℝ)

private theorem cubicKernel_scale {t X Y : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    cubicKernel (t * X) (t * Y) = t * cubicKernel X Y := by
  have htPow : t ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ) = t := by
    rw [← Real.rpow_add' ht (by norm_num : (1 / 3 : ℝ) + 2 / 3 ≠ 0),
      show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
  simp only [cubicKernel, Real.mul_rpow ht hX, Real.mul_rpow ht hY]
  calc
    _ = t * (X + Y) - (t ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ)) *
        (X ^ (1 / 3 : ℝ) * Y ^ (2 / 3 : ℝ) + X ^ (2 / 3 : ℝ) * Y ^ (1 / 3 : ℝ)) := by ring
    _ = _ := by rw [htPow]; ring

set_option maxHeartbeats 500000 in
-- The normalization rewrites nested finite sums of real powers.
/-- The cubic excess over the cost of the two weighted endpoint totals. -/
private theorem weighted_edge_energy_excess {n : Type*} [Fintype n]
    (w : n → n → ℝ) (lam : n → ℝ) {a b : ℝ}
    (hw : ∀ i j, 0 ≤ w i j) (hlam : ∀ i, 0 ≤ lam i) (ha : 0 < a) (hb : 0 < b)
    (hA : 0 < ∑ i, ∑ j, w i j * lam i) (hB : 0 < ∑ i, ∑ j, w i j * lam j) :
    let A := ∑ i, ∑ j, w i j * lam i
    let B := ∑ i, ∑ j, w i j * lam j
    let P (i j : n) := w i j * lam i / A
    let Q (i j : n) := w i j * lam j / B
    let u := (b * A) ^ (1 / 3 : ℝ) * (a * B) ^ (2 / 3 : ℝ)
    let v := (b * A) ^ (2 / 3 : ℝ) * (a * B) ^ (1 / 3 : ℝ)
    (9 / 4 : ℝ) * hellingerCoefficient u v * (1 - ∑ i, ∑ j, Real.sqrt (P i j * Q i j)) ≤
      (9 / 4 : ℝ) * ((∑ i, ∑ j, w i j * cubicKernel (b * lam i) (a * lam j)) -
        cubicKernel (b * A) (a * B)) := by
  intro A B P Q u v
  change 0 < A at hA
  change 0 < B at hB
  let p : n × n → ℝ := fun e => P e.1 e.2
  let q : n × n → ℝ := fun e => Q e.1 e.2
  let X := b * A
  let Y := a * B
  have hX : 0 < X := mul_pos hb hA
  have hY : 0 < Y := mul_pos ha hB
  have hp (e : n × n) : 0 ≤ p e := div_nonneg (mul_nonneg (hw e.1 e.2) (hlam e.1)) hA.le
  have hq (e : n × n) : 0 ≤ q e := div_nonneg (mul_nonneg (hw e.1 e.2) (hlam e.2)) hB.le
  have hpSum : (∑ e, p e) = 1 := by
    calc
      _ = A / A := by simp only [p, P, Fintype.sum_prod_type, ← Finset.sum_div, A]
      _ = 1 := div_self hA.ne'
  have hqSum : (∑ e, q e) = 1 := by
    calc
      _ = B / B := by simp only [q, Q, Fintype.sum_prod_type, ← Finset.sum_div, B]
      _ = 1 := div_self hB.ne'
  have hu : 0 < u :=
    mul_pos (Real.rpow_pos_of_pos hX _) (Real.rpow_pos_of_pos hY _)
  have hv : 0 < v :=
    mul_pos (Real.rpow_pos_of_pos hX _) (Real.rpow_pos_of_pos hY _)
  have hterm (e : n × n) :
      cubicKernel (X * p e) (Y * q e) = X * p e + Y * q e -
        u * (p e ^ (1 / 3 : ℝ) * q e ^ (2 / 3 : ℝ)) -
        v * (p e ^ (2 / 3 : ℝ) * q e ^ (1 / 3 : ℝ)) := by
    simp only [cubicKernel, Real.mul_rpow hX.le (hp e), Real.mul_rpow hY.le (hq e)]
    change _ = X * p e + Y * q e -
      (X ^ (1 / 3 : ℝ) * Y ^ (2 / 3 : ℝ)) * (p e ^ (1 / 3 : ℝ) * q e ^ (2 / 3 : ℝ)) -
      (X ^ (2 / 3 : ℝ) * Y ^ (1 / 3 : ℝ)) * (p e ^ (2 / 3 : ℝ) * q e ^ (1 / 3 : ℝ))
    ring
  have hgap :
      (∑ e, cubicKernel (X * p e) (Y * q e)) - cubicKernel X Y =
        u * (1 - ∑ e, p e ^ (1 / 3 : ℝ) * q e ^ (2 / 3 : ℝ)) +
          v * (1 - ∑ e, p e ^ (2 / 3 : ℝ) * q e ^ (1 / 3 : ℝ)) := by
    simp only [hterm]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      hpSum, hqSum, mul_one, cubicKernel]
    change X + Y - u * (∑ e, p e ^ (1 / 3 : ℝ) * q e ^ (2 / 3 : ℝ)) -
      v * (∑ e, p e ^ (2 / 3 : ℝ) * q e ^ (1 / 3 : ℝ)) - (X + Y - u - v) = _
    ring
  have hsum : (∑ e, cubicKernel (X * p e) (Y * q e)) =
      ∑ i, ∑ j, w i j * cubicKernel (b * lam i) (a * lam j) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hrow : X * p (i, j) = w i j * (b * lam i) := by
      calc
        _ = b * ((w i j * lam i / A) * A) := by
          change (b * A) * (w i j * lam i / A) = _
          ring
        _ = _ := by rw [div_mul_cancel₀ _ hA.ne']; ring
    have hcol : Y * q (i, j) = w i j * (a * lam j) := by
      calc
        _ = a * ((w i j * lam j / B) * B) := by
          change (a * B) * (w i j * lam j / B) = _
          ring
        _ = _ := by rw [div_mul_cancel₀ _ hB.ne']; ring
    rw [hrow, hcol, cubicKernel_scale (hw i j) (mul_nonneg hb.le (hlam i))
      (mul_nonneg ha.le (hlam j))]
  have h := finite_probability_comparison p q hp hq hpSum hqSum hu hv
  rw [← hgap, hsum] at h
  have hnormalized :
      hellingerCoefficient u v * (1 - ∑ i, ∑ j, Real.sqrt (P i j * Q i j)) ≤
        (∑ i, ∑ j, w i j * cubicKernel (b * lam i) (a * lam j)) -
          cubicKernel (b * A) (a * B) := by
    simpa only [Fintype.sum_prod_type, p, q, X, Y] using h
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hnormalized (by norm_num : (0 : ℝ) ≤ 9 / 4)

private theorem coshEdgeKernel_cubic {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    coshEdgeKernel (1 / 3) X Y = cubicKernel X Y / 2 := by
  have h := edgeKernel_eq_cosh (p := (1 / 3 : ℝ)) (by norm_num) (by norm_num) hX hY
  change (X + Y - (Y ^ (1 - (1 / 3 : ℝ)) * X ^ (1 / 3 : ℝ) +
    X ^ (1 - (1 / 3 : ℝ)) * Y ^ (1 / 3 : ℝ))) / 2 = coshEdgeKernel (1 / 3) X Y at h
  rw [← h, show 1 - (1 / 3 : ℝ) = 2 / 3 by norm_num, cubicKernel]
  ring

private theorem trace_edge_marginals {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (J : Matrix n n ℂ) :
    (ρ * (J * Jᴴ)).trace.re = (∑ i, ∑ j, edgeWeight hρ J i j * hρ.eigenvalues i) ∧
      (ρ * (Jᴴ * J)).trace.re = (∑ i, ∑ j, edgeWeight hρ J i j * hρ.eigenvalues j) := by
  let frame := (Unitary.conjStarAlgAut ℂ _ hρ.eigenvectorUnitary).symm
  let K := frame J
  have htrace (W : Matrix n n ℂ) : (frame W).trace = W.trace := by
    dsimp only [frame]
    rw [Unitary.conjStarAlgAut_symm_apply, Matrix.trace_mul_cycle,
      ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have hdiag : frame ρ = diagonal (fun i => (hρ.eigenvalues i : ℂ)) := by
    dsimp only [frame]
    rw [Unitary.conjStarAlgAut_symm, hρ.conjStarAlgAut_star_eigenvectorUnitary]
    rfl
  have hadj : frame Jᴴ = Kᴴ := map_star frame J
  constructor
  · rw [← htrace (ρ * (J * Jᴴ)), map_mul, map_mul, hdiag, hadj]
    change (diagonal (fun i => (hρ.eigenvalues i : ℂ)) * (K * Kᴴ)).trace.re =
      ∑ i, ∑ j, Complex.normSq (K i j) * hρ.eigenvalues i
    simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_assoc,
      mul_one, one_mul, mul_comm] using trace_diagonal_overlap hρ.eigenvalues (fun _ => 1) K
  · rw [← htrace (ρ * (Jᴴ * J)), map_mul, map_mul, hdiag, hadj, Matrix.trace_mul_cycle']
    change (K * (diagonal (fun i => (hρ.eigenvalues i : ℂ)) * Kᴴ)).trace.re =
      ∑ i, ∑ j, Complex.normSq (K i j) * hρ.eigenvalues j
    simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.one_mul, Matrix.mul_assoc,
      one_mul, mul_comm] using trace_diagonal_overlap (fun _ => 1) hρ.eigenvalues K

set_option maxHeartbeats 600000 in
-- The physical trace uses three matrix powers and nested sums over jumps and entries.
/-- The ordinary cubic energy of actual paired modular jumps exceeds the collapsed
endpoint energy by the sum of the Hellinger bounds. For signed lowering letters,
`A k` is the empty-mode mass and `B k` is the occupied-mode mass. In the matched
diagonal product, the two masses on a spectator configuration are scaled by its
common probability, so homogeneity of the cubic kernel gives the collapsed term. -/
theorem generator_energy_sub_matched_occupation_ge {n ι : Type*}
    [Fintype n] [DecidableEq n] [Fintype ι]
    {D ρ : Matrix n n ℂ} (hD : D.PosDef) (hρ : ρ.PosSemidef)
    (a b : ι → ℝ) (J : ι → Matrix n n ℂ)
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (hJ : ∀ k, D * J k * D⁻¹ = (a k / b k) • J k)
    (hA : ∀ k, 0 < (ρ * (J k * (J k)ᴴ)).trace.re)
    (hB : ∀ k, 0 < (ρ * ((J k)ᴴ * J k)).trace.re) :
    let lam := hρ.isHermitian.eigenvalues
    let w (k : ι) := edgeWeight hρ.isHermitian (J k)
    let A (k : ι) := (ρ * (J k * (J k)ᴴ)).trace.re
    let B (k : ι) := (ρ * ((J k)ᴴ * J k)).trace.re
    let P (k : ι) (i j : n) := w k i j * lam i / A k
    let Q (k : ι) (i j : n) := w k i j * lam j / B k
    let u (k : ι) := (b k * A k) ^ (1 / 3 : ℝ) * (a k * B k) ^ (2 / 3 : ℝ)
    let v (k : ι) := (b k * A k) ^ (2 / 3 : ℝ) * (a k * B k) ^ (1 / 3 : ℝ)
    let G := mpow D (1 / (2 * 3))
    let H := mpow D (-(1 / (2 * 3)))
    let M := mpow ρ (1 / 3)
    let X := H * M * H
    (∑ k, (9 / 4 : ℝ) * hellingerCoefficient (u k) (v k) *
      (1 - ∑ i, ∑ j, Real.sqrt (P k i j * Q k i j))) ≤
      (9 / 8 : ℝ) * (mpow M 2 *
        (G * (∑ k, pairedGenerator (a k) (b k) (J k) X) * G)).trace.re -
        (9 / 4 : ℝ) * (∑ k, cubicKernel (b k * A k) (a k * B k)) := by
  intro lam w A B P Q u v G H M X
  let T := (mpow M 2 * (G * (∑ k, pairedGenerator (a k) (b k) (J k) X) * G)).trace.re
  let E (k : ι) := ∑ i, ∑ j, w k i j * cubicKernel (b k * lam i) (a k * lam j)
  let C (k : ι) := cubicKernel (b k * A k) (a k * B k)
  have hAeq (k : ι) : A k = ∑ i, ∑ j, w k i j * lam i := by
    exact (trace_edge_marginals hρ.isHermitian (J k)).1
  have hBeq (k : ι) : B k = ∑ i, ∑ j, w k i j * lam j := by
    exact (trace_edge_marginals hρ.isHermitian (J k)).2
  have hlam (i : n) : 0 ≤ lam i := hρ.eigenvalues_nonneg i
  have hw (k : ι) (i j : n) : 0 ≤ w k i j := by
    change 0 ≤ edgeWeight hρ.isHermitian (J k) i j
    unfold edgeWeight
    exact Complex.normSq_nonneg _
  have hcosh (k : ι) (i j : n) :
      coshEdgeKernel (1 / 3) (b k * lam i) (a k * lam j) =
        cubicKernel (b k * lam i) (a k * lam j) / 2 :=
    coshEdgeKernel_cubic (mul_nonneg (hb k).le (hlam i)) (mul_nonneg (ha k).le (hlam j))
  have htrace : (1 / 4 : ℝ) * T =
      ∑ k, ∑ i, ∑ j, w k i j * coshEdgeKernel (1 / 3) (b k * lam i) (a k * lam j) := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
      generatorTrace_eq_cosh hD hρ a b J (s := (3 : ℝ)) (by norm_num) ha hb hJ
  simp only [hcosh, ← mul_div_assoc, ← Finset.sum_div] at htrace
  change (1 / 4 : ℝ) * T = (∑ k, E k) / 2 at htrace
  have henergy : (9 / 4 : ℝ) * (∑ k, E k) = (9 / 8 : ℝ) * T := by
    calc
      _ = (9 / 2 : ℝ) * ((∑ k, E k) / 2) := by ring
      _ = _ := by rw [← htrace]; ring
  change _ ≤ (9 / 8 : ℝ) * T - (9 / 4 : ℝ) * (∑ k, C k)
  calc
    _ ≤ ∑ k, (9 / 4 : ℝ) * (E k - C k) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hApos : 0 < ∑ i, ∑ j, w k i j * lam i := by
        rw [← hAeq k]
        exact hA k
      have hBpos : 0 < ∑ i, ∑ j, w k i j * lam j := by
        rw [← hBeq k]
        exact hB k
      simpa only [← hAeq k, ← hBeq k, P, Q, u, v, E, C] using
        weighted_edge_energy_excess (w k) lam (hw k) hlam (ha k) (hb k) hApos hBpos
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, henergy]

#print axioms finite_probability_comparison
#print axioms generator_energy_sub_matched_occupation_ge

end D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation
