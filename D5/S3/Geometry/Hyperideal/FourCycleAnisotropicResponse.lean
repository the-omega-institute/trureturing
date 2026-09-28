/- GID: D5/S3/Geometry/Hyperideal/FourCycleAnisotropicResponse
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FourCycleAnisotropicResponse
   mirror-E: none(waiver:unbounded-genuine-angle-response)
   anchors: []
   utility: none
   digest: Signed half-difference response for paired transverse lengths. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/- The six entries are in the fixed order (12,13,14,34,24,23). -/
set_option maxHeartbeats 3000000 in
-- The two radical factorizations and the signed branch need this local budget.
theorem paired_angle_half_difference
    (r a b o : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (ht : -1 < cosine r a b o a b ∧ cosine r a b o a b < 1)
    (hbeta : -1 < cosine a b r a b o ∧ cosine a b r a b o < 1)
    (hdelta : -1 < cosine b a r b a o ∧ cosine b a r b a o < 1) :
    (Real.arccos (cosine a b r a b o) -
        Real.arccos (cosine b a r b a o)) / 2 =
      Real.arctan (((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) / (a + b)) *
        Real.sqrt ((r - 1) / (r + 1)) *
          Real.cot (Real.arccos (cosine r a b o a b) / 2)) := by
  let ct : ℝ := cosine r a b o a b
  let ca : ℝ := cosine a b r a b o
  let cb : ℝ := cosine b a r b a o
  let theta : ℝ := Real.arccos ct
  let beta : ℝ := Real.arccos ca
  let delta : ℝ := Real.arccos cb
  let k : ℝ := a + b
  let L : ℝ := k^2 - (r - 1) * (o - 1)
  let M : ℝ := (r + 1) * (o + 1) - (a - b)^2
  let Dr : ℝ := rad r a b
  let Do : ℝ := rad o a b
  have hrad : ∀ x y z : ℝ, 1 < x → 1 < y → 1 < z → 0 < rad x y z := by
    intro x y z hx hy hz
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x - 1)]
    have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y - 1)]
    have hz2 : 1 ≤ z^2 := by nlinarith [sq_nonneg (z - 1)]
    have hp : 0 ≤ 2 * x * y * z := by positivity
    unfold rad
    linarith
  have hDr : 0 < Dr := by dsimp [Dr]; exact hrad r a b hr ha hb
  have hDo : 0 < Do := by dsimp [Do]; exact hrad o a b ho ha hb
  have hQ : 0 < Dr * Do := mul_pos hDr hDo
  have hQs : 0 < Real.sqrt (Dr * Do) := Real.sqrt_pos.2 hQ
  have hsqQ : (Real.sqrt (Dr * Do))^2 = Dr * Do := Real.sq_sqrt hQ.le
  have hsqrt_mul : Real.sqrt (Dr * Do) = Real.sqrt Dr * Real.sqrt Do := by
    rw [Real.sqrt_mul (le_of_lt hDr)]
  have hct_den : ct * Dr = numerator r a b o a b := by
    have hrad_swap : rad r b a = rad r a b := by unfold rad; ring
    have hct0 : ct = numerator r a b o a b / Real.sqrt (rad r a b) /
        Real.sqrt (rad r b a) := by
      dsimp [ct]
      rfl
    rw [hct0, hrad_swap, div_div]
    rw [← pow_two, Real.sq_sqrt hDr.le]
    field_simp [hDr.ne']
  have hplus_poly : Dr + numerator r a b o a b = (r + 1) * L := by
    dsimp [Dr, L, k]
    unfold rad numerator
    ring
  have hminus_poly : Dr - numerator r a b o a b = (r - 1) * M := by
    dsimp [Dr, M]
    unfold rad numerator
    ring
  have hplus : Dr * (1 + ct) = (r + 1) * L := by
    nlinarith [hct_den, hplus_poly]
  have hminus : Dr * (1 - ct) = (r - 1) * M := by
    nlinarith [hct_den, hminus_poly]
  have hL : 0 < L := by
    have : 0 < 1 + ct := by linarith [ht.1]
    have : 0 < r + 1 := by linarith
    nlinarith [hplus]
  have hM : 0 < M := by
    have : 0 < 1 - ct := by linarith [ht.2]
    have : 0 < r - 1 := by linarith
    nlinarith [hminus]
  have hP : 0 < L * M := mul_pos hL hM
  have hPs : 0 < Real.sqrt (L * M) := Real.sqrt_pos.2 hP
  have hsqP : (Real.sqrt (L * M))^2 = L * M := Real.sq_sqrt hP.le
  have hca_exact : ca * Real.sqrt (Dr * Do) = numerator a b r a b o := by
    dsimp [ca]
    unfold cosine
    have hrad1 : rad a b o = Do := by dsimp [Do]; unfold rad; ring
    have hrad2 : rad a r b = Dr := by dsimp [Dr]; unfold rad; ring
    rw [hrad1, hrad2, div_div, hsqrt_mul]
    field_simp [(Real.sqrt_pos.2 hDr).ne', (Real.sqrt_pos.2 hDo).ne']
  have hcb_exact : cb * Real.sqrt (Dr * Do) = numerator b a r b a o := by
    dsimp [cb]
    unfold cosine
    have hrad1 : rad b a o = Do := by dsimp [Do]; unfold rad; ring
    have hrad2 : rad b r a = Dr := by dsimp [Dr]; unfold rad; ring
    rw [hrad1, hrad2, div_div, hsqrt_mul]
    field_simp [(Real.sqrt_pos.2 hDr).ne', (Real.sqrt_pos.2 hDo).ne']
  have hca_sq : ca^2 * (Dr * Do) = numerator a b r a b o ^ 2 := by
    calc
      ca^2 * (Dr * Do) = (ca * Real.sqrt (Dr * Do))^2 := by rw [mul_pow, hsqQ]
      _ = numerator a b r a b o ^ 2 := by rw [hca_exact]
  have hcb_sq : cb^2 * (Dr * Do) = numerator b a r b a o ^ 2 := by
    calc
      cb^2 * (Dr * Do) = (cb * Real.sqrt (Dr * Do))^2 := by rw [mul_pow, hsqQ]
      _ = numerator b a r b a o ^ 2 := by rw [hcb_exact]
  have hfactor_a : Dr * Do - numerator a b r a b o ^ 2 =
      (a^2 - 1) * L * M := by
    dsimp [Dr, Do, L, M, k]
    unfold rad numerator
    ring
  have hfactor_b : Dr * Do - numerator b a r b a o ^ 2 =
      (b^2 - 1) * L * M := by
    dsimp [Dr, Do, L, M, k]
    unfold rad numerator
    ring
  have hsum_num : numerator a b r a b o + numerator b a r b a o = k * M := by
    dsimp [k, M]
    unfold numerator
    ring
  have hcos_sum : (ca + cb) * Real.sqrt (Dr * Do) = k * M := by
    calc
      (ca + cb) * Real.sqrt (Dr * Do) =
          ca * Real.sqrt (Dr * Do) + cb * Real.sqrt (Dr * Do) := by ring
      _ = numerator a b r a b o + numerator b a r b a o := by
        rw [hca_exact, hcb_exact]
      _ = k * M := hsum_num
  have hk : 0 < k := by dsimp [k]; linarith
  have hcos_sum_pos : 0 < ca + cb := by
    have hprod : 0 < (ca + cb) * Real.sqrt (Dr * Do) := by
      rw [hcos_sum]
      exact mul_pos hk hM
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.1
    · linarith [h.2, hQs]
  have hcos_theta : Real.cos theta = ct := by
    dsimp [theta]
    exact Real.cos_arccos ht.1.le ht.2.le
  have hcos_beta : Real.cos beta = ca := by
    dsimp [beta]
    exact Real.cos_arccos hbeta.1.le hbeta.2.le
  have hcos_delta : Real.cos delta = cb := by
    dsimp [delta]
    exact Real.cos_arccos hdelta.1.le hdelta.2.le
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    exact Real.arccos_pos.2 ht.2
  have htheta_lt_pi : theta < Real.pi := by
    dsimp [theta]
    exact Real.arccos_lt_pi.2 ht.1
  have hbeta_pos : 0 < beta := by
    dsimp [beta]
    exact Real.arccos_pos.2 hbeta.2
  have hbeta_lt_pi : beta < Real.pi := by
    dsimp [beta]
    exact Real.arccos_lt_pi.2 hbeta.1
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact Real.arccos_pos.2 hdelta.2
  have hdelta_lt_pi : delta < Real.pi := by
    dsimp [delta]
    exact Real.arccos_lt_pi.2 hdelta.1
  have hsin_beta : 0 < Real.sin beta :=
    Real.sin_pos_of_pos_of_lt_pi hbeta_pos hbeta_lt_pi
  have hsin_delta : 0 < Real.sin delta :=
    Real.sin_pos_of_pos_of_lt_pi hdelta_pos hdelta_lt_pi
  have hsin_beta_sq : (Real.sin beta)^2 * (Dr * Do) =
      (a^2 - 1) * L * M := by
    have htrig := Real.sin_sq_add_cos_sq beta
    rw [hcos_beta] at htrig
    have hsin_beta_cos : (Real.sin beta)^2 = 1 - ca^2 := by linarith [htrig]
    calc
      (Real.sin beta)^2 * (Dr * Do) = (1 - ca^2) * (Dr * Do) := by
        rw [hsin_beta_cos]
      _ = Dr * Do - ca^2 * (Dr * Do) := by ring
      _ = Dr * Do - numerator a b r a b o ^ 2 := by rw [hca_sq]
      _ = (a^2 - 1) * L * M := hfactor_a
  have hsin_delta_sq : (Real.sin delta)^2 * (Dr * Do) =
      (b^2 - 1) * L * M := by
    have htrig := Real.sin_sq_add_cos_sq delta
    rw [hcos_delta] at htrig
    have hsin_delta_cos : (Real.sin delta)^2 = 1 - cb^2 := by linarith [htrig]
    calc
      (Real.sin delta)^2 * (Dr * Do) = (1 - cb^2) * (Dr * Do) := by
        rw [hsin_delta_cos]
      _ = Dr * Do - cb^2 * (Dr * Do) := by ring
      _ = Dr * Do - numerator b a r b a o ^ 2 := by rw [hcb_sq]
      _ = (b^2 - 1) * L * M := hfactor_b
  have hsin_beta_exact : Real.sin beta * Real.sqrt (Dr * Do) =
      Real.sqrt (a^2 - 1) * Real.sqrt (L * M) := by
    apply (sq_eq_sq₀ (mul_nonneg hsin_beta.le hQs.le)
      (mul_nonneg (Real.sqrt_nonneg _) hPs.le)).mp
    have hsqA : (Real.sqrt (a^2 - 1))^2 = a^2 - 1 :=
      Real.sq_sqrt (by nlinarith only [ha, sq_nonneg (a - 1)])
    rw [mul_pow, hsqQ, mul_pow, hsqP, hsqA]
    simpa [mul_assoc] using hsin_beta_sq
  have hsin_delta_exact : Real.sin delta * Real.sqrt (Dr * Do) =
      Real.sqrt (b^2 - 1) * Real.sqrt (L * M) := by
    apply (sq_eq_sq₀ (mul_nonneg hsin_delta.le hQs.le)
      (mul_nonneg (Real.sqrt_nonneg _) hPs.le)).mp
    have hsqB : (Real.sqrt (b^2 - 1))^2 = b^2 - 1 :=
      Real.sq_sqrt (by nlinarith only [hb, sq_nonneg (b - 1)])
    rw [mul_pow, hsqQ, mul_pow, hsqP, hsqB]
    simpa [mul_assoc] using hsin_delta_sq
  have hsigned_sine : (Real.sin beta - Real.sin delta) * Real.sqrt (Dr * Do) =
      (Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) * Real.sqrt (L * M) := by
    calc
      (Real.sin beta - Real.sin delta) * Real.sqrt (Dr * Do) =
          Real.sin beta * Real.sqrt (Dr * Do) -
            Real.sin delta * Real.sqrt (Dr * Do) := by ring
      _ = Real.sqrt (a^2 - 1) * Real.sqrt (L * M) -
          Real.sqrt (b^2 - 1) * Real.sqrt (L * M) := by
        rw [hsin_beta_exact, hsin_delta_exact]
      _ = (Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) *
          Real.sqrt (L * M) := by ring
  let eta : ℝ := (beta + delta) / 2
  let phi : ℝ := (beta - delta) / 2
  have hphi_bounds : -(Real.pi / 2) < phi ∧ phi < Real.pi / 2 := by
    dsimp [phi]
    constructor <;> linarith [hbeta_lt_pi, hdelta_lt_pi, hbeta_pos, hdelta_pos]
  have hcos_phi : 0 < Real.cos phi :=
    Real.cos_pos_of_mem_Ioo ⟨hphi_bounds.1, hphi_bounds.2⟩
  have hcos_sum_trig : Real.cos beta + Real.cos delta =
      2 * Real.cos eta * Real.cos phi := by
    have hbde : beta = eta + phi := by dsimp [eta, phi]; ring
    have hdde : delta = eta - phi := by dsimp [eta, phi]; ring
    rw [hbde, hdde, Real.cos_add, Real.cos_sub]
    ring
  have hcos_eta : 0 < Real.cos eta := by
    have hpos : 0 < 2 * Real.cos eta * Real.cos phi := by
      rw [← hcos_sum_trig, hcos_beta, hcos_delta]
      exact hcos_sum_pos
    rcases (mul_pos_iff.mp hpos) with h | h
    · nlinarith only [h.1]
    · linarith only [h.2, hcos_phi]
  have hsin_diff_trig : Real.sin beta - Real.sin delta =
      2 * Real.cos eta * Real.sin phi := by
    have hbde : beta = eta + phi := by dsimp [eta, phi]; ring
    have hdde : delta = eta - phi := by dsimp [eta, phi]; ring
    rw [hbde, hdde, Real.sin_add, Real.sin_sub]
    ring
  have htan_phi : Real.tan phi =
      (Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) * Real.sqrt (L * M) /
        (k * M) := by
    have hcos_sum_ne : Real.cos beta + Real.cos delta ≠ 0 := by
      rw [hcos_beta, hcos_delta]
      exact ne_of_gt hcos_sum_pos
    have hkM : 0 < k * M := mul_pos hk hM
    calc
      Real.tan phi = Real.sin phi / Real.cos phi := by
        rw [Real.tan_eq_sin_div_cos]
      _ = (Real.sin beta - Real.sin delta) /
          (Real.cos beta + Real.cos delta) := by
        calc
          Real.sin phi / Real.cos phi =
              (2 * Real.cos eta * Real.sin phi) /
                (2 * Real.cos eta * Real.cos phi) := by
            field_simp [hcos_eta.ne', hcos_phi.ne']
          _ = (Real.sin beta - Real.sin delta) /
              (Real.cos beta + Real.cos delta) := by
            rw [← hsin_diff_trig, ← hcos_sum_trig]
      _ = (Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) *
          Real.sqrt (L * M) / (k * M) := by
        apply (div_eq_div_iff hcos_sum_ne (ne_of_gt hkM)).2
        calc
          (Real.sin beta - Real.sin delta) * (k * M) =
              (Real.sin beta - Real.sin delta) *
                ((ca + cb) * Real.sqrt (Dr * Do)) := by rw [hcos_sum]
          _ = ((Real.sin beta - Real.sin delta) *
              Real.sqrt (Dr * Do)) * (ca + cb) := by ring
          _ = ((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) *
              Real.sqrt (L * M)) * (ca + cb) := by rw [hsigned_sine]
          _ = ((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) *
              Real.sqrt (L * M)) * (Real.cos beta + Real.cos delta) := by
            rw [hcos_beta, hcos_delta]
  have hhalf_sin : 0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [htheta_pos])
      (by linarith [htheta_lt_pi, Real.pi_pos])
  have hhalf_cos : 0 < Real.cos (theta / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [htheta_lt_pi]⟩
  have hhalf_tan : 0 < Real.tan (theta / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hhalf_sin hhalf_cos
  have hhalf_cot : Real.cot (theta / 2) = 1 / Real.tan (theta / 2) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    field_simp [hhalf_sin.ne', hhalf_cos.ne']
  have htan_half : (Real.tan (theta / 2))^2 * (1 + ct) = 1 - ct := by
    have harg : 2 * (theta / 2) = theta := by ring
    have hdouble : Real.cos theta =
        2 * Real.cos (theta / 2)^2 - 1 := by
      calc
        Real.cos theta = Real.cos (2 * (theta / 2)) := congrArg Real.cos harg.symm
        _ = 2 * Real.cos (theta / 2)^2 - 1 := Real.cos_two_mul _
    have htrig := Real.sin_sq_add_cos_sq (theta / 2)
    have hcos_sq : 2 * Real.cos (theta / 2)^2 = 1 + ct := by
      rw [hcos_theta] at hdouble
      linarith only [hdouble]
    have hsin_sq : 2 * Real.sin (theta / 2)^2 = 1 - ct := by
      have hsin_cos : Real.sin (theta / 2)^2 =
          1 - Real.cos (theta / 2)^2 := eq_sub_of_add_eq htrig
      calc
        2 * Real.sin (theta / 2)^2 =
            2 * (1 - Real.cos (theta / 2)^2) := by rw [hsin_cos]
        _ = 2 - 2 * Real.cos (theta / 2)^2 := by ring
        _ = 1 - ct := by rw [hcos_sq]; ring
    calc
      (Real.tan (theta / 2))^2 * (1 + ct) =
          ((Real.sin (theta / 2))^2 / (Real.cos (theta / 2))^2) *
            (2 * Real.cos (theta / 2)^2) := by
        rw [Real.tan_eq_sin_div_cos, div_pow, hcos_sq]
      _ = 2 * Real.sin (theta / 2)^2 := by
        field_simp [hhalf_cos.ne']
      _ = 1 - ct := hsin_sq
  have htan_relation : (Real.tan (theta / 2))^2 * ((r + 1) * L) =
      (r - 1) * M := by
    calc
      _ = (Real.tan (theta / 2))^2 * (Dr * (1 + ct)) := by rw [hplus]
      _ = Dr * ((Real.tan (theta / 2))^2 * (1 + ct)) := by ring
      _ = Dr * (1 - ct) := by rw [htan_half]
      _ = (r - 1) * M := hminus
  have hratio_nonneg : 0 ≤ (r - 1) / (r + 1) := by positivity
  have hscale_sq :
      ((Real.sqrt (L * M) / M) * Real.tan (theta / 2))^2 =
        (Real.sqrt ((r - 1) / (r + 1)))^2 := by
    rw [Real.sq_sqrt hratio_nonneg, mul_pow, div_pow, hsqP]
    have hrne : r + 1 ≠ 0 := by linarith
    have hMne : M ≠ 0 := ne_of_gt hM
    field_simp [hMne, hrne]
    nlinarith only [htan_relation]
  have hscale_tan :
      (Real.sqrt (L * M) / M) * Real.tan (theta / 2) =
        Real.sqrt ((r - 1) / (r + 1)) := by
    apply (sq_eq_sq₀ (mul_nonneg (div_nonneg hPs.le hM.le) hhalf_tan.le)
      (Real.sqrt_nonneg _)).mp
    exact hscale_sq
  have hscale : Real.sqrt (L * M) / M =
      Real.sqrt ((r - 1) / (r + 1)) * Real.cot (theta / 2) := by
    rw [hhalf_cot]
    rw [mul_one_div]
    apply (eq_div_iff hhalf_tan.ne').2
    exact hscale_tan
  have htan_phi_lambda : Real.tan phi =
      ((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) / k) *
        Real.sqrt ((r - 1) / (r + 1)) * Real.cot (theta / 2) := by
    calc
      Real.tan phi =
          (Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) *
            Real.sqrt (L * M) / (k * M) := htan_phi
      _ = ((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) / k) *
          (Real.sqrt (L * M) / M) := by
            field_simp [hk.ne', hM.ne']
      _ = ((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) / k) *
          Real.sqrt ((r - 1) / (r + 1)) * Real.cot (theta / 2) := by
            rw [hscale]
            ring
  have hbranch := Real.arctan_eq_of_tan_eq htan_phi_lambda
    ⟨hphi_bounds.1, hphi_bounds.2⟩
  dsimp [phi, theta, beta, delta, k] at hbranch
  exact hbranch.symm

#print axioms paired_angle_half_difference

end D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse
