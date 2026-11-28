/- GID: D5/S3/Geometry/UnitQuaternions/Holonomy/SU2RankOneOverlap
   generality: G
   mirror-B: none(waiver:covered-by-chordal-su2-sharp-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rank-one update of a two-dimensional quadratic form gives the scalar overlap obstruction used in the rational interval certificate. -/

import D5.S3.Geometry.UnitQuaternions.SphericalCaps.SU2ChordalIntervals
import D5.S3.Geometry.QuaternionicHermitian.QuaternionicRayleigh

/-!
Omega original.

A rank-one update of a two-dimensional quadratic form gives the scalar
overlap obstruction used in the rational interval certificate.
-/

open Real

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

/-- A two-coordinate vector satisfying the support inequality must obey
the rank-one update discriminant bound. -/
theorem rank_one_update_discriminant {s γ p q x y w : ℝ}
    (hs : 0 < s) (hw : 0 < w)
    (hp : p ^ 2 + q ^ 2 = 1) (hx : x ^ 2 + y ^ 2 = 1)
    (h : (2 + w) * (1 + s) / 2 ≤
      (1 - γ) * x ^ 2 + (1 + γ) * y ^ 2 + w * (p * x + q * y) ^ 2) :
    s ^ 2 * (2 + w) ^ 2 ≤ (2 * γ + w) ^ 2 - 8 * γ * w * p ^ 2 := by
  let A := 1 - γ + w * p ^ 2
  let B := w * p * q
  let C := 1 + γ + w * q ^ 2
  let T := (2 + w) * (1 + s) / 2
  have hsum : A + C = 2 + w := by
    dsimp [A, C]
    nlinarith only [congrArg (fun a : ℝ => w * a) hp]
  have hd : 0 ≤ 2 * T - (A + C) := by
    rw [hsum]
    dsimp [T]
    nlinarith only [mul_nonneg hs.le (show 0 ≤ 2 + w by linarith)]
  have hform : T ≤ A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
    dsimp [T, A, B, C]
    nlinarith only [h]
  have hlin : 2 * T - (A + C) ≤ (A - C) * (x ^ 2 - y ^ 2) + (2 * B) * (2 * x * y) := by
    nlinarith only [hform, congrArg (fun a : ℝ => (A + C) * a) hx]
  have hsquare := pow_le_pow_left₀ hd hlin 2
  have hvec : (x ^ 2 - y ^ 2) ^ 2 + (2 * x * y) ^ 2 = 1 := by
    nlinarith only [congrArg (fun a : ℝ => a ^ 2) hx]
  have hCS : ((A - C) * (x ^ 2 - y ^ 2) + (2 * B) * (2 * x * y)) ^ 2 ≤
      (A - C) ^ 2 + (2 * B) ^ 2 := by
    nlinarith only [sq_nonneg ((A - C) * (2 * x * y) - (2 * B) * (x ^ 2 - y ^ 2)),
      congrArg (fun a : ℝ => a * ((A - C) ^ 2 + (2 * B) ^ 2)) hvec]
  have hright : (A - C) ^ 2 + (2 * B) ^ 2 = (2 * γ + w) ^ 2 - 8 * γ * w * p ^ 2 := by
    have hq : q ^ 2 = 1 - p ^ 2 := by linarith
    dsimp [A, B, C]
    rw [show (2 * (w * p * q)) ^ 2 = 4 * w ^ 2 * p ^ 2 * q ^ 2 by ring, hq]
    ring
  have hleft : (2 * T - (A + C)) ^ 2 = s ^ 2 * (2 + w) ^ 2 := by
    rw [hsum]
    dsimp [T]
    ring
  exact hleft ▸ hright ▸ hsquare.trans hCS

/-- Optimizing the rank-one weight yields the necessary asymmetric overlap
inequality in polynomial form. -/
theorem rank_one_overlap_discriminant {s γ pSq : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hγ : s ≤ γ)
    (h : ∀ w : ℝ, 0 < w →
      s ^ 2 * (2 + w) ^ 2 ≤ (2 * γ + w) ^ 2 - 8 * γ * w * pSq) :
    2 * γ * pSq - γ + s ^ 2 ≤ √((1 - s ^ 2) * (γ ^ 2 - s ^ 2)) := by
  let l := 2 * γ * pSq - γ + s ^ 2
  let A := 1 - s ^ 2
  have hA : 0 < A := by dsimp [A]; nlinarith only [mul_pos (sub_pos.mpr hs') (show 0 < 1 + s by linarith)]
  have hB : 0 ≤ γ ^ 2 - s ^ 2 := by nlinarith only [pow_le_pow_left₀ hs.le hγ 2]
  by_cases hl : 0 < l
  · let w := 2 * l / A
    have hw : 0 < w := by dsimp [w]; positivity
    have hq := h w hw
    have hwa : w * A = 2 * l := div_mul_cancel₀ _ hA.ne'
    have hwa' := congrArg (fun z : ℝ => w * z) hwa
    have hh : 0 ≤ A * w ^ 2 - 4 * l * w + 4 * (γ ^ 2 - s ^ 2) := by
      dsimp [A, l]
      nlinarith only [hq]
    have hh' := mul_nonneg hA.le hh
    have hwa₂ := congrArg (fun z : ℝ => (A * w + 2 * l) * z) hwa
    have hwa₃ := congrArg (fun z : ℝ => l * z) hwa
    apply le_sqrt_of_sq_le
    change l ^ 2 ≤ A * (γ ^ 2 - s ^ 2)
    nlinarith only [hh', hwa₂, hwa₃]
  · exact (le_of_not_gt hl).trans (sqrt_nonneg _)


open scoped Quaternion InnerProductSpace

variable {ι : Type*} [Fintype ι]

private theorem norm_smul_add_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (r s : ℝ) :
    ‖r • a + s • b‖ ^ 2 = r ^ 2 * ‖a‖ ^ 2 + s ^ 2 * ‖b‖ ^ 2 + 2 * (r * s) * ⟪a,b⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm b a, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, sq_abs, mul_pow]
  ring

/-- The weighted rank-one argument for the three simultaneous overlap
constraints. The constant `7/8` fixes the lower eigendirection. -/
theorem asymmetric_overlap {a b d z : Columns ι} {s α : ℝ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (hz : ‖z‖ = 1)
    (hs : 0 < s) (hs' : s < 1) (hsa : s ≤ α) (hαρ : α < 7 / 8)
    (hab : pairing a b = (α : ℍ[ℝ]))
    (hza : (1 + s) / 2 ≤ ‖pairing a z‖ ^ 2) (hzb : (1 + s) / 2 ≤ ‖pairing b z‖ ^ 2)
    (hzd : (1 + s) / 2 ≤ ‖pairing d z‖ ^ 2) :
    let ρ : ℝ := 7 / 8
    let N := 1 + ρ ^ 2 - 2 * ρ * α
    let D := 2 * ρ - (1 + ρ ^ 2) * α
    let γ := α * N / D
    2 * γ * (‖pairing b d - ρ • pairing a d‖ ^ 2 / N) - γ + s ^ 2 ≤
      √((1 - s ^ 2) * (γ ^ 2 - s ^ 2)) := by
  let ρ : ℝ := 7 / 8
  let N := 1 + ρ ^ 2 - 2 * ρ * α
  let D := 2 * ρ - (1 + ρ ^ 2) * α
  let γ := α * N / D
  let A := 2 * ρ * (1 - ρ * α) / D
  let B := 2 * (ρ - α) / D
  have hα : 0 < α := hs.trans_le hsa
  have hα₁ : α < 1 := by linarith
  have hN : 0 < N := by dsimp [N, ρ]; linarith
  have hD : 0 < D := by dsimp [D, ρ]; linarith
  have hA : 0 < A := by
    have hp : 0 < 1 - ρ * α := by dsimp [ρ]; linarith
    exact div_pos (mul_pos (by norm_num [ρ]) hp) hD
  have hB : 0 < B := div_pos (by dsimp [ρ]; linarith) hD
  have hAB : A + B = 2 := by
    dsimp only [A, B]
    field_simp [hD.ne']
    dsimp [D]
    ring
  have hγ₀ : α ≤ γ := by
    change α ≤ α * N / D
    rw [le_div_iff₀ hD]
    apply mul_le_mul_of_nonneg_left _ hα.le
    dsimp [N, D, ρ]
    linarith
  have hγ₁ : γ < 1 := by
    change α * N / D < 1
    rw [div_lt_iff₀ hD, one_mul]
    have hp := mul_pos (show 0 < ρ - α by dsimp [ρ]; linarith)
      (show 0 < 1 - ρ * α by dsimp [ρ]; linarith)
    dsimp [N, D]
    nlinarith only [hp]
  have hα₂ : 0 < 1 - α ^ 2 := by nlinarith only [mul_pos (sub_pos.mpr hα₁) (by linarith : 0 < 1 + α)]
  let n := √N
  let m := √((1 - α ^ 2) * N)
  have hn : 0 < n := sqrt_pos.mpr hN
  have hm : 0 < m := sqrt_pos.mpr (mul_pos hα₂ hN)
  have hn₂ : n ^ 2 = N := sq_sqrt hN.le
  have hm₂ : m ^ 2 = (1 - α ^ 2) * N := sq_sqrt (mul_nonneg hα₂.le hN.le)
  let e := n⁻¹ • (b - ρ • a)
  let f := m⁻¹ • ((1 - ρ * α) • a + (ρ - α) • b)
  have hReal : ⟪a,b⟫_ℝ = α := by rw [real_inner_eq_re_pairing, hab]; rfl
  have heN : ‖b - ρ • a‖ ^ 2 = N := by
    have h := norm_smul_add_sq b a 1 (-ρ)
    simp only [one_smul, one_pow, one_mul, ha, hb] at h
    rw [show ⟪b, a⟫_ℝ = α from (real_inner_comm _ _).trans hReal] at h
    rw [sub_eq_add_neg, ← neg_smul, h]
    dsimp [N]
    ring
  have hfN : ‖(1 - ρ * α) • a + (ρ - α) • b‖ ^ 2 = (1 - α ^ 2) * N := by
    rw [norm_smul_add_sq, ha, hb, hReal]
    dsimp [N]
    ring
  have he : ‖e‖ = 1 := by
    have H : ‖b - ρ • a‖ = n := by
      apply (pow_left_inj₀ (norm_nonneg _) hn.le two_ne_zero).mp
      rw [heN, hn₂]
    dsimp only [e]
    rw [norm_smul, H]
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg hn.le, inv_mul_cancel₀ hn.ne']
  have hf : ‖f‖ = 1 := by
    have H : ‖(1 - ρ * α) • a + (ρ - α) • b‖ = m := by
      apply (pow_left_inj₀ (norm_nonneg _) hm.le two_ne_zero).mp
      rw [hfN, hm₂]
    dsimp only [f]
    rw [norm_smul, H]
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg hm.le, inv_mul_cancel₀ hm.ne']
  have hab' : pairing b a = (α : ℍ[ℝ]) := by rw [← pairing_star, hab]; simp
  have ha₀ : pairing a a = 1 := by rw [pairing_self, ha, one_pow, Quaternion.coe_one]
  have hb₀ : pairing b b = 1 := by rw [pairing_self, hb, one_pow, Quaternion.coe_one]
  have hef : pairing e f = 0 := by
    simp only [e, f, pairing_smul_left, pairing_smul_right, pairing_sub_left,
      pairing_add_right, hab, hab', ha₀, hb₀]
    ext <;> simp
    ring
  let X := pairing a z
  let Y := pairing b z
  have heZ : ‖pairing e z‖ ^ 2 =
      (ρ ^ 2 * ‖X‖ ^ 2 + ‖Y‖ ^ 2 - 2 * ρ * ⟪X,Y⟫_ℝ) / N := by
    simp only [e, pairing_smul_left, pairing_sub_left]
    change ‖n⁻¹ • (Y - ρ • X)‖ ^ 2 = _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, hn₂, ← div_eq_inv_mul,
      sub_eq_add_neg, ← neg_smul]
    have h := norm_smul_add_sq Y X 1 (-ρ)
    simp only [one_smul, one_pow, one_mul] at h
    rw [show ⟪Y, X⟫_ℝ = ⟪X, Y⟫_ℝ from real_inner_comm _ _] at h
    rw [h]
    ring
  have hfZ : ‖pairing f z‖ ^ 2 =
      ((1 - ρ * α) ^ 2 * ‖X‖ ^ 2 + (ρ - α) ^ 2 * ‖Y‖ ^ 2 +
        2 * ((1 - ρ * α) * (ρ - α)) * ⟪X,Y⟫_ℝ) / ((1 - α ^ 2) * N) := by
    simp only [f, pairing_smul_left, pairing_add_left]
    change ‖m⁻¹ • ((1 - ρ * α) • X + (ρ - α) • Y)‖ ^ 2 = _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, hm₂, ← div_eq_inv_mul, norm_smul_add_sq]
  have hdiag : A * ‖X‖ ^ 2 + B * ‖Y‖ ^ 2 =
      (1 - γ) * ‖pairing e z‖ ^ 2 + (1 + γ) * ‖pairing f z‖ ^ 2 := by
    rw [heZ, hfZ]
    dsimp only [A, B, γ]
    field_simp [hD.ne', hN.ne', hα₂.ne']
    dsimp [N, D]
    ring
  let p := ‖pairing e d‖
  let x := ‖pairing e z‖
  let q := √(1 - p ^ 2)
  let y := √(1 - x ^ 2)
  have hp : p ≤ 1 := by
    change ‖pairing e d‖ ≤ 1
    simpa [he, hd] using (quaternion_cauchy (x := e) (y := d))
  have hx : x ≤ 1 := by
    change ‖pairing e z‖ ≤ 1
    simpa [he, hz] using (quaternion_cauchy (x := e) (y := z))
  have hq : q ^ 2 = 1 - p ^ 2 :=
    sq_sqrt (sub_nonneg.mpr ((pow_le_pow_left₀ (show 0 ≤ p from norm_nonneg _) hp 2).trans_eq (one_pow 2)))
  have hy : y ^ 2 = 1 - x ^ 2 :=
    sq_sqrt (sub_nonneg.mpr ((pow_le_pow_left₀ (show 0 ≤ x from norm_nonneg _) hx 2).trans_eq (one_pow 2)))
  have hbess := pair_orthogonal_bessel (d := z) he hf hef
  rw [hz, one_pow] at hbess
  have hfbound : ‖pairing f z‖ ^ 2 ≤ y ^ 2 := by
    rw [hy]
    change x ^ 2 + ‖pairing f z‖ ^ 2 ≤ 1 at hbess
    linarith only [hbess]
  have hzalt : ‖pairing d z‖ ≤ p * x + q * y := overlap_le_projection e d z he hd hz
  have hdisc (w : ℝ) (hw : 0 < w) :
      s ^ 2 * (2 + w) ^ 2 ≤ (2 * γ + w) ^ 2 - 8 * γ * w * p ^ 2 := by
    apply rank_one_update_discriminant (q := q) (x := x) (y := y) hs hw
      (by linarith only [hq]) (by linarith only [hy])
    have h₁ := mul_le_mul_of_nonneg_left hza hA.le
    have h₂ := mul_le_mul_of_nonneg_left hzb hB.le
    have h₃ := mul_le_mul_of_nonneg_left hzd hw.le
    have h₄ := mul_le_mul_of_nonneg_left hfbound (by linarith : 0 ≤ 1 + γ)
    have h₅ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzalt 2) hw.le
    have hsum := congrArg (fun t : ℝ => t * ((1 + s) / 2)) hAB
    change A * ((1 + s) / 2) ≤ A * ‖X‖ ^ 2 at h₁
    change B * ((1 + s) / 2) ≤ B * ‖Y‖ ^ 2 at h₂
    change A * ‖X‖ ^ 2 + B * ‖Y‖ ^ 2 = (1 - γ) * x ^ 2 +
      (1 + γ) * ‖pairing f z‖ ^ 2 at hdiag
    linarith only [h₁, h₂, h₃, h₄, h₅, hsum, hdiag]
  have h := rank_one_overlap_discriminant hs hs' (hsa.trans hγ₀) hdisc
  have hpSq : p ^ 2 = ‖pairing b d - ρ • pairing a d‖ ^ 2 / N := by
    dsimp [p,e]
    rw [pairing_smul_left, pairing_sub_left, pairing_smul_left, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, inv_pow, hn₂, div_eq_inv_mul]
  rwa [hpSq] at h


/-- The quartic excludes the simultaneous support bounds once the affine
overlap has the certified squared lower bound. -/
theorem asymmetric_overlap_excluded {a b d z : Columns ι} {s α G : ℝ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (hz : ‖z‖ = 1)
    (hs : 0 < s) (hs' : s < 1) (hsa : s ≤ α) (hαρ : α < 7 / 8)
    (hab : pairing a b = (α : ℍ[ℝ]))
    (hza : (1 + s) / 2 ≤ ‖pairing a z‖ ^ 2) (hzb : (1 + s) / 2 ≤ ‖pairing b z‖ ^ 2)
    (hzd : (1 + s) / 2 ≤ ‖pairing d z‖ ^ 2)
    (hG : G ≤ ‖pairing b d - (7 / 8 : ℝ) • pairing a d‖ ^ 2)
    (hcert : SU2ChordalIntervals.QuarticCertificate s G) : False := by
  let ρ : ℝ := 7 / 8
  let n := 1 + ρ ^ 2
  let N := n - 2 * ρ * α
  let D := 2 * ρ - n * α
  let γ := α * N / D
  let v := ‖pairing b d - ρ • pairing a d‖ ^ 2
  have hN : 0 < N := by dsimp [N, n, ρ]; linarith
  have hD : 0 < D := by dsimp [D, n, ρ]; linarith
  have hα : 0 < α := hs.trans_le hsa
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have h := asymmetric_overlap ha hb hd hz hs hs' hsa hαρ hab hza hzb hzd
  change 2 * γ * (v / N) - γ + s ^ 2 ≤ √((1 - s ^ 2) * (γ ^ 2 - s ^ 2)) at h
  have hV : G / N ≤ v / N := div_le_div_of_nonneg_right hG hN.le
  have hh := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * γ by positivity)
  have hJ : 2 * γ * (G / N) - γ + s ^ 2 ≤ √((1 - s ^ 2) * (γ ^ 2 - s ^ 2)) := by
    linarith only [h, hh]
  let J := 2 * ρ * α ^ 2 + (2 * G - n * (1 + s ^ 2)) * α + 2 * ρ * s ^ 2
  let T := (1 - s ^ 2) * (α ^ 2 * N ^ 2 - s ^ 2 * D ^ 2)
  have hl : (2 * γ * (G / N) - γ + s ^ 2) * D = J := by
    dsimp only [J, γ]
    field_simp [hN.ne', hD.ne']
    dsimp [N, D]
    ring
  have he : D ^ 2 * ((1 - s ^ 2) * (γ ^ 2 - s ^ 2)) = T := by
    dsimp only [T, γ]
    field_simp [hD.ne']
  have hr : √((1 - s ^ 2) * (γ ^ 2 - s ^ 2)) * D = √T := by
    rw [← he, sqrt_mul (sq_nonneg D), sqrt_sq hD.le, mul_comm]
  have hmul := mul_le_mul_of_nonneg_right hJ hD.le
  rw [hl, hr] at hmul
  exact (not_lt_of_ge hmul) (SU2ChordalIntervals.quartic_obstruction hcert hsa)

end Omega.Geometry.HolonomySpectrum
