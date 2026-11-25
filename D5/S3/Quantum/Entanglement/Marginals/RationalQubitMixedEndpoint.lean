/- GID: D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Quadratic witnesses for a mixed qubit and a rational Bloch length. -/

import D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector
import Mathlib.NumberTheory.SumFourSquares

/-! A four-squares construction of the rational projector witness for a mixed endpoint. -/

open Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension (RationalEntry)
open D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint

private abbrev Bloch := Fin 3 → ℚ

private theorem four_rational_squares (q : ℚ) (hq : 0 ≤ q) :
    ∃ p r s t : ℚ, p ^ 2 + r ^ 2 + s ^ 2 + t ^ 2 = q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨p, r, s, t, h⟩ := Nat.sum_four_squares (q.num.toNat * q.den)
  have hnat : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hcast : (p : ℚ) ^ 2 + (r : ℚ) ^ 2 + (s : ℚ) ^ 2 + (t : ℚ) ^ 2 =
      (q.num : ℚ) * (q.den : ℚ) := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at hc
    rw [hnat] at hc
    exact hc
  have hqeq : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden).mp q.num_div_den
  rw [hqeq] at hcast
  refine ⟨p / (q.den : ℚ), r / (q.den : ℚ), s / (q.den : ℚ),
    t / (q.den : ℚ), ?_⟩
  field_simp
  linear_combination hcast

private theorem axis_witness (q : ℚ) (hq : 0 < q) :
    ∃ (y v : Bloch), 0 < y ⬝ᵥ y ∧ v 2 = 0 ∧ y ⬝ᵥ y = q * (v ⬝ᵥ v) := by
  obtain ⟨p, r, s, t, h⟩ := four_rational_squares q hq.le
  have construct (a b c d : ℚ) (hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = q)
      (hpair : 0 < a ^ 2 + b ^ 2) :
      ∃ (y v : Bloch), 0 < y ⬝ᵥ y ∧ v 2 = 0 ∧ y ⬝ᵥ y = q * (v ⬝ᵥ v) := by
    refine ⟨![a ^ 2 + b ^ 2, a * c - b * d, a * d + b * c], ![a, b, 0], ?_, rfl, ?_⟩
    · simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]
      nlinarith [pow_pos hpair 2, sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c)]
    · simp [dotProduct, Fin.sum_univ_three]
      have hmul := sq_add_sq_mul_sq_add_sq (x₁ := a) (x₂ := b) (y₁ := c) (y₂ := d)
      linear_combination (-hmul + hsum * (a ^ 2 + b ^ 2))
  by_cases hs : 0 < p ^ 2 + r ^ 2
  · exact construct p r s t h hs
  · exact construct s t p r (by linarith) (by linarith)

/-- A rational Bloch vector of positive rational length can use a rational
rotation of the four-squares witness in the coordinate plane. -/
private theorem mixed_endpoint_witness (c : Bloch) (r : ℚ)
    (hr : 0 < r) (hunit : r < 1) (hlen : c ⬝ᵥ c = r ^ 2) :
    ∃ y v : Bloch, 0 < y ⬝ᵥ y ∧ c ⬝ᵥ v = 0 ∧
      y ⬝ᵥ y = (1 - c ⬝ᵥ c) * (v ⬝ᵥ v) := by
  have hd : 0 < 1 - r ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hunit) (by linarith : 0 < 1 + r)]
  obtain ⟨y, v, hy, hv, hlenv⟩ := axis_witness (1 - r ^ 2) hd
  let n : Bloch := r⁻¹ • c
  let e : Bloch := ![0, 0, 1]
  have hn : n ⬝ᵥ n = 1 := by
    dsimp only [n]
    rw [smul_dotProduct, dotProduct_smul, hlen]
    simp only [smul_eq_mul]
    field_simp
  have hcn : c = r • n := by simp [n, smul_smul, hr.ne']
  have he : e ⬝ᵥ e = 1 := by norm_num [e, dotProduct, Fin.sum_univ_three]
  have hev : e ⬝ᵥ v = 0 := by simpa [e, dotProduct, Fin.sum_univ_three] using hv
  by_cases hne : e = n
  · have hcv : c ⬝ᵥ v = 0 := by rw [hcn, ← hne, smul_dotProduct, hev, smul_zero]
    exact ⟨y, v, hy, hcv, by simpa only [hlen] using hlenv⟩
  let w := e - n
  have hw : w ⬝ᵥ w ≠ 0 :=
    fun h => hne (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))
  let f := 2 * (w ⬝ᵥ v) / (w ⬝ᵥ w)
  let v' := v - f • w
  have hnw : n ⬝ᵥ w = -(w ⬝ᵥ w) / 2 := by
    dsimp only [w]
    rw [dotProduct_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      hn, he, dotProduct_comm e n]
    ring
  have hv' : n ⬝ᵥ v' = 0 := by
    have hwv : w ⬝ᵥ v = -(n ⬝ᵥ v) := by simp [w, sub_dotProduct, hev]
    dsimp only [v', f]
    rw [dotProduct_sub, dotProduct_smul, hnw, hwv, smul_eq_mul]
    field_simp
    ring
  have hnorm : v' ⬝ᵥ v' = v ⬝ᵥ v := by
    dsimp only [v']
    rw [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, dotProduct_comm v w]
    simp only [smul_eq_mul, f]
    field_simp
    <;> ring
  refine ⟨y, v', hy, ?_, ?_⟩
  · rw [hcn, smul_dotProduct, hv', smul_zero]
  · rw [hlen, hnorm, hlenv]

/-- A maximally mixed endpoint and a full-rank endpoint with positive rational
Bloch length have a rational joint state of rank exactly two. -/
theorem rational_rank_two_of_maximally_mixed_endpoint (c : Fin 3 → ℚ) (r : ℚ)
    (hr : 0 < r) (hunit : r < 1) (hlen : c ⬝ᵥ c = r ^ 2) :
    ∃ T : Matrix (Bool × Bool) (Bool × Bool) ℂ, T.PosSemidef ∧ T.rank = 2 ∧
      (∀ i j, RationalEntry (T i j)) ∧
      partialTraceRight T = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) ∧
      partialTraceLeft T = (1 / 2 : ℂ) • (1 + rationalBlochMatrix c) := by
  obtain ⟨y, v, hy, hcv, hq⟩ := mixed_endpoint_witness c r hr hunit hlen
  have hstrict : (0 : Bloch) ⬝ᵥ 0 < c ⬝ᵥ c := by rw [zero_dotProduct, hlen]; positivity
  have hzero : rationalBlochMatrix 0 = 0 := by
    unfold rationalBlochMatrix
    have heq : (WithLp.toLp 2 fun _ : Fin 3 => (0 : ℝ)) =
        (0 : EuclideanSpace ℝ (Fin 3)) := by
      apply (WithLp.equiv 2 _).injective
      funext i
      simp
    simp [heq]
  simpa only [hzero, add_zero] using
    rational_rank_two_of_quadratic_witness 0 c y v hstrict hy
      (by simp only [zero_dotProduct, hcv]) (by simpa only [hcv, zero_pow (by decide : 2 ≠ 0),
        add_zero] using hq)

end D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
