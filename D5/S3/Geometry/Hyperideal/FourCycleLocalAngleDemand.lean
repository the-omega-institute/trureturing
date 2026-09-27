/- GID: D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand
   mirror-E: none(waiver:unbounded-genuine-angle-demand)
   anchors: []
   utility: none
   digest: Paired local angle demand and a flat transverse length gap. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/- The six entries are in the fixed order (12,13,14,34,24,23). -/
set_option maxHeartbeats 3000000 in
-- The coupled radical identities and strict angle comparison need this local budget.
theorem paired_angle_demand
    (r a b o : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hdom : 1 + a + b ≤ r)
    (ht : -1 < cosine r a b o a b ∧ cosine r a b o a b < 1)
    (hbeta : -1 < cosine a b r a b o ∧ cosine a b r a b o < 1)
    (hdelta : -1 < cosine b a r b a o ∧ cosine b a r b a o < 1) :
    2 * Real.arccos (cosine r a b o a b) +
        Real.arccos (cosine a b r a b o) +
          Real.arccos (cosine b a r b a o) > Real.pi := by
  let ct : ℝ := cosine r a b o a b
  let ca : ℝ := cosine a b r a b o
  let cb : ℝ := cosine b a r b a o
  let theta : ℝ := Real.arccos ct
  let beta : ℝ := Real.arccos ca
  let delta : ℝ := Real.arccos cb
  let k : ℝ := a + b
  let j : ℝ := a - b
  let L : ℝ := (a + b)^2 - (r - 1) * (o - 1)
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
  have hDrs : 0 < Real.sqrt Dr := Real.sqrt_pos.2 hDr
  have hDos : 0 < Real.sqrt Do := Real.sqrt_pos.2 hDo
  have hQ : 0 < Dr * Do := mul_pos hDr hDo
  have hQs : 0 < Real.sqrt (Dr * Do) := Real.sqrt_pos.2 hQ
  have hsqQ : (Real.sqrt (Dr * Do))^2 = Dr * Do := Real.sq_sqrt hQ.le
  have hsqDr : (Real.sqrt Dr)^2 = Dr := Real.sq_sqrt hDr.le
  have hsqDo : (Real.sqrt Do)^2 = Do := Real.sq_sqrt hDo.le
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
    dsimp [Dr, L]
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
    field_simp [hDrs.ne', hDos.ne']
  have hca_sq : ca^2 * (Dr * Do) = numerator a b r a b o ^ 2 := by
    calc
      ca^2 * (Dr * Do) = (ca * Real.sqrt (Dr * Do))^2 := by
        rw [mul_pow, hsqQ]
      _ = numerator a b r a b o ^ 2 := by rw [hca_exact]
  have hcb_exact : cb * Real.sqrt (Dr * Do) = numerator b a r b a o := by
    dsimp [cb]
    unfold cosine
    have hrad1 : rad b a o = Do := by dsimp [Do]; unfold rad; ring
    have hrad2 : rad b r a = Dr := by dsimp [Dr]; unfold rad; ring
    rw [hrad1, hrad2, div_div, hsqrt_mul]
    field_simp [hDrs.ne', hDos.ne']
  have hcb_sq : cb^2 * (Dr * Do) = numerator b a r b a o ^ 2 := by
    calc
      cb^2 * (Dr * Do) = (cb * Real.sqrt (Dr * Do))^2 := by
        rw [mul_pow, hsqQ]
      _ = numerator b a r b a o ^ 2 := by rw [hcb_exact]
  have hfactor_a : Dr * Do - numerator a b r a b o ^ 2 =
      (a^2 - 1) * L * M := by
    dsimp [Dr, Do, L, M]
    unfold rad numerator
    ring
  have hfactor_b : Dr * Do - numerator b a r b a o ^ 2 =
      (b^2 - 1) * L * M := by
    dsimp [Dr, Do, L, M]
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
  have hcos_sum_pos : 0 < ca + cb := by
    have hk : 0 < k := by dsimp [k]; linarith
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
    have hsin_beta_cos : (Real.sin beta)^2 = 1 - ca^2 := by
      linarith [htrig]
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
    have hsin_delta_cos : (Real.sin delta)^2 = 1 - cb^2 := by
      linarith [htrig]
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
    rw [mul_pow, hsqQ, mul_pow, hsqP]
    rw [hsqA]
    simpa [mul_assoc] using hsin_beta_sq
  have hsin_delta_exact : Real.sin delta * Real.sqrt (Dr * Do) =
      Real.sqrt (b^2 - 1) * Real.sqrt (L * M) := by
    apply (sq_eq_sq₀ (mul_nonneg hsin_delta.le hQs.le)
      (mul_nonneg (Real.sqrt_nonneg _) hPs.le)).mp
    have hsqB : (Real.sqrt (b^2 - 1))^2 = b^2 - 1 :=
      Real.sq_sqrt (by nlinarith only [hb, sq_nonneg (b - 1)])
    rw [mul_pow, hsqQ, mul_pow, hsqP]
    rw [hsqB]
    simpa [mul_assoc] using hsin_delta_sq
  have hsin_sum : (Real.sin beta + Real.sin delta) * Real.sqrt (Dr * Do) =
      (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1)) * Real.sqrt (L * M) := by
    calc
      (Real.sin beta + Real.sin delta) * Real.sqrt (Dr * Do) =
          Real.sin beta * Real.sqrt (Dr * Do) +
            Real.sin delta * Real.sqrt (Dr * Do) := by ring
      _ = Real.sqrt (a^2 - 1) * Real.sqrt (L * M) +
          Real.sqrt (b^2 - 1) * Real.sqrt (L * M) := by
        rw [hsin_beta_exact, hsin_delta_exact]
      _ = (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1)) *
          Real.sqrt (L * M) := by ring
  let eta : ℝ := (beta + delta) / 2
  let phi : ℝ := (beta - delta) / 2
  have hphi_bounds : -(Real.pi / 2) < phi ∧ phi < Real.pi / 2 := by
    dsimp [phi]
    constructor <;> linarith [hbeta_lt_pi, hdelta_lt_pi, hbeta_pos, hdelta_pos]
  have hcos_phi : 0 < Real.cos phi :=
    Real.cos_pos_of_mem_Ioo ⟨hphi_bounds.1, hphi_bounds.2⟩
  have heta_pos : 0 < eta := by dsimp [eta]; linarith
  have heta_lt_pi : eta < Real.pi := by dsimp [eta]; linarith
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
  have heta_lt_half_pi : eta < Real.pi / 2 := by
    by_contra hn
    have hnon := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hn)
      (by linarith [heta_lt_pi, Real.pi_pos])
    linarith
  have htan_eta : Real.tan eta =
      (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1)) * Real.sqrt (L * M) /
        (k * M) := by
    have hsin_sum_trig : Real.sin beta + Real.sin delta =
        2 * Real.sin eta * Real.cos phi := by
      have hbde : beta = eta + phi := by dsimp [eta, phi]; ring
      have hdde : delta = eta - phi := by dsimp [eta, phi]; ring
      rw [hbde, hdde, Real.sin_add, Real.sin_sub]
      ring
    have hcos_sum_trig' : Real.cos beta + Real.cos delta =
        2 * Real.cos eta * Real.cos phi := hcos_sum_trig
    have hcos_eta_ne : Real.cos eta ≠ 0 := ne_of_gt hcos_eta
    have hcos_phi_ne : Real.cos phi ≠ 0 := ne_of_gt hcos_phi
    have hcos_sum_ne : Real.cos beta + Real.cos delta ≠ 0 := by
      rw [hcos_beta, hcos_delta]
      exact ne_of_gt hcos_sum_pos
    have hk_local : 0 < k := by dsimp [k]; linarith
    have hkM : 0 < k * M := mul_pos hk_local hM
    calc
      Real.tan eta = Real.sin eta / Real.cos eta := by
        rw [Real.tan_eq_sin_div_cos]
      _ = (Real.sin beta + Real.sin delta) /
          (Real.cos beta + Real.cos delta) := by
        calc
          Real.sin eta / Real.cos eta =
              (2 * Real.sin eta * Real.cos phi) /
                (2 * Real.cos eta * Real.cos phi) := by
            field_simp [hcos_eta_ne, hcos_phi_ne]
          _ = (Real.sin beta + Real.sin delta) /
              (Real.cos beta + Real.cos delta) := by
            rw [← hsin_sum_trig, ← hcos_sum_trig']
      _ = (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1)) *
          Real.sqrt (L * M) / (k * M) := by
        apply (div_eq_div_iff hcos_sum_ne (ne_of_gt hkM)).2
        calc
          (Real.sin beta + Real.sin delta) * (k * M) =
              (Real.sin beta + Real.sin delta) *
                ((ca + cb) * Real.sqrt (Dr * Do)) := by
            rw [hcos_sum]
          _ = ((Real.sin beta + Real.sin delta) *
              Real.sqrt (Dr * Do)) * (ca + cb) := by ring
          _ = ((Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1)) *
              Real.sqrt (L * M)) * (ca + cb) := by rw [hsin_sum]
          _ = ((Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1)) *
              Real.sqrt (L * M)) * (Real.cos beta + Real.cos delta) := by
            rw [hcos_beta, hcos_delta]
  let T : ℝ := (Real.tan eta)^2
  let t : ℝ := (Real.tan (theta / 2))^2
  let q : ℝ :=
    ((Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1))^2 / k^2) *
      ((r - 1) / (r + 1))
  have ht_pos : 0 < t := by
    dsimp [t]
    have hhalf : 0 < theta / 2 := by linarith
    have hhalf_lt : theta / 2 < Real.pi / 2 := by linarith
    have hsin_half : 0 < Real.sin (theta / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hhalf (by linarith [Real.pi_pos])
    have hcos_half : 0 < Real.cos (theta / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf_lt⟩
    exact sq_pos_of_pos (by
      rw [Real.tan_eq_sin_div_cos]
      exact div_pos hsin_half hcos_half)
  have htan_half : t * (1 + ct) = 1 - ct := by
    dsimp [t]
    have hhalf_cos : 0 < Real.cos (theta / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    have hdouble : Real.cos theta =
        2 * Real.cos (theta / 2)^2 - 1 := by
      have harg : 2 * (theta / 2) = theta := by ring
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
  have htan_relation : t * ((r + 1) * L) = (r - 1) * M := by
    calc
      t * ((r + 1) * L) = t * (Dr * (1 + ct)) := by rw [hplus]
      _ = Dr * (t * (1 + ct)) := by ring
      _ = Dr * (1 - ct) := by rw [htan_half]
      _ = (r - 1) * M := hminus
  have htan_relation_eq : t = (r - 1) * M / ((r + 1) * L) := by
    apply (eq_div_iff (mul_ne_zero (by linarith : r + 1 ≠ 0) (ne_of_gt hL))).2
    exact htan_relation
  have hk : 0 < k := by dsimp [k]; linarith
  have hk2 : 0 < k + 2 := by linarith
  have hksq : 0 < k^2 := sq_pos_of_pos hk
  have hroot_a : 0 < Real.sqrt (a^2 - 1) :=
    Real.sqrt_pos.2 (by nlinarith [ha])
  have hroot_b : 0 < Real.sqrt (b^2 - 1) :=
    Real.sqrt_pos.2 (by nlinarith [hb])
  have hA : 0 ≤ a^2 - 1 := by nlinarith only [ha, sq_nonneg (a - 1)]
  have hB : 0 ≤ b^2 - 1 := by nlinarith only [hb, sq_nonneg (b - 1)]
  have hroot_prod : (a - 1) * (b - 1) <
      Real.sqrt ((a^2 - 1) * (b^2 - 1)) := by
    apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg hA hB)]
    calc
      ((a - 1) * (b - 1))^2 <
          ((a - 1) * (b - 1))^2 + 2 * (a - 1) * (b - 1) * (a + b) := by
        have hp : 0 < 2 * (a - 1) * (b - 1) * (a + b) := by positivity
        linarith only [hp]
      _ = (a^2 - 1) * (b^2 - 1) := by ring
  have hroot_sum_sq : k * (k - 2) <
      (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1))^2 := by
    have hsa := Real.sq_sqrt hA
    have hsb := Real.sq_sqrt hB
    have hprod : Real.sqrt (a^2 - 1) * Real.sqrt (b^2 - 1) =
        Real.sqrt ((a^2 - 1) * (b^2 - 1)) := by
      rw [Real.sqrt_mul hA]
    calc
      k * (k - 2) =
          (a^2 - 1) + (b^2 - 1) + 2 * (a - 1) * (b - 1) := by
        dsimp [k]
        ring
      _ < (a^2 - 1) + (b^2 - 1) +
          2 * Real.sqrt ((a^2 - 1) * (b^2 - 1)) := by
        linarith only [hroot_prod]
      _ = (a^2 - 1) + (b^2 - 1) +
          2 * (Real.sqrt (a^2 - 1) * Real.sqrt (b^2 - 1)) := by
        rw [hprod]
      _ = (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1))^2 := by
        rw [add_sq, hsa, hsb]
        ring
  have hratio_r : k / (k + 2) ≤ (r - 1) / (r + 1) := by
    have hdom_k : k + 1 ≤ r := by dsimp [k]; linarith only [hdom]
    apply (div_le_div_iff₀ hk2 (by linarith only [hr])).2
    nlinarith only [hdom_k]
  have hratio_a : (k - 2) / k <
      (Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1))^2 / k^2 := by
    apply (div_lt_div_iff₀ hk hksq).2
    have hmul := mul_lt_mul_of_pos_left hroot_sum_sq hk
    nlinarith only [hmul]
  have hq_lower : (k - 2) / (k + 2) < q := by
    dsimp [q]
    have hnonneg : 0 ≤ (r - 1) / (r + 1) := by positivity
    have hkp : 0 < k / (k + 2) := div_pos hk hk2
    calc
      (k - 2) / (k + 2) = ((k - 2) / k) * (k / (k + 2)) := by
        field_simp
      _ < ((Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1))^2 / k^2) *
          (k / (k + 2)) := mul_lt_mul_of_pos_right hratio_a hkp
      _ ≤ ((Real.sqrt (a^2 - 1) + Real.sqrt (b^2 - 1))^2 / k^2) *
          ((r - 1) / (r + 1)) :=
        mul_le_mul_of_nonneg_left hratio_r (by positivity)
  let F : ℝ := (r - 1) * (2 * (r + 1) - j^2) / ((r + 1) * k^2)
  have hslack : 0 < t - F := by
    have hden : 0 < (r + 1) * L * k^2 := by positivity
    have heq : t - F =
        (2 * (r - 1) * (o - 1) * Dr) / ((r + 1) * L * k^2) := by
      rw [htan_relation_eq]
      dsimp [F]
      field_simp [hL.ne', (by linarith : r + 1 ≠ 0), hk.ne']
      dsimp [L, M, Dr, k, j]
      unfold rad
      ring
    rw [heq]
    positivity
  have hjbound : j^2 < (k - 2)^2 := by
    have hp : 0 < 4 * (a - 1) * (b - 1) := by positivity
    calc
      j^2 < j^2 + 4 * (a - 1) * (b - 1) := by linarith only [hp]
      _ = (k - 2)^2 := by dsimp [j, k]; ring
  have hFmono :
      ((k + 1 - 1) * (2 * (k + 1 + 1) - j^2) /
        ((k + 1 + 1) * k^2)) ≤ F := by
    have hxy : 0 < (r + 1) * (k + 2) - j^2 := by
      have hdom_k : k + 1 ≤ r := by dsimp [k]; linarith only [hdom]
      have hsq : j^2 < (k + 2)^2 := by
        have heq : (k + 2)^2 = (k - 2)^2 + 8 * k := by ring
        linarith only [hjbound, heq, hk]
      have hmul : (k + 2)^2 ≤ (r + 1) * (k + 2) := by
        have h := mul_le_mul_of_nonneg_right hdom_k hk2.le
        nlinarith only [h]
      linarith only [hsq, hmul]
    have heq : F - ((k + 1 - 1) * (2 * (k + 1 + 1) - j^2) /
        ((k + 1 + 1) * k^2)) =
        (2 * (r - k - 1) * ((r + 1) * (k + 2) - j^2)) /
          ((r + 1) * (k + 2) * k^2) := by
      dsimp [F]
      field_simp [(by linarith : r + 1 ≠ 0), hk.ne', hk2.ne']
      ring
    rw [← sub_nonneg]
    rw [heq]
    have hdom_k : 0 ≤ r - k - 1 := by dsimp [k]; linarith only [hdom]
    exact div_nonneg (by positivity) (by positivity)
  have hFbase : (6 - k) / (k + 2) <
      ((k + 1 - 1) * (2 * (k + 1 + 1) - j^2) /
        ((k + 1 + 1) * k^2)) := by
    have heq : ((k + 1 - 1) * (2 * (k + 1 + 1) - j^2) /
        ((k + 1 + 1) * k^2)) - (6 - k) / (k + 2) =
        ((k - 2)^2 - j^2) / ((k + 2) * k) := by
      field_simp [hk.ne', hk2.ne']
      ring
    rw [← sub_pos, heq]
    exact div_pos (sub_pos.mpr hjbound) (mul_pos hk2 hk)
  have ht_lower : (6 - k) / (k + 2) < t := by
    have hFb := hFmono
    have hFs : F < t := sub_pos.mp hslack
    linarith
  have hbase_sum : (6 - k) / (k + 2) + 2 * ((k - 2) / (k + 2)) = 1 := by
    field_simp
    ring
  have hkey : 1 < t + 2 * q := by
    linarith only [ht_lower, hq_lower, hbase_sum]
  have htan_eta_sq : T * t = q := by
    dsimp [T, q]
    rw [htan_eta, htan_relation_eq]
    field_simp [hL.ne', (by linarith : r + 1 ≠ 0), hk.ne', hM.ne']
    rw [hsqP]
  have hcos_eta_sq : Real.cos eta ^ 2 = 1 / (1 + T) := by
    have hone := Real.one_add_tan_sq_mul_cos_sq_eq_one (ne_of_gt hcos_eta)
    dsimp [T] at hone ⊢
    apply (eq_div_iff (by positivity : 1 + Real.tan eta ^ 2 ≠ 0)).2
    nlinarith only [hone]
  have hcos_sq_bound : Real.cos eta ^ 2 < 2 * t / (1 + t) := by
    have hden1 : 0 < 1 + t := by linarith [ht_pos]
    have hden2 : 0 < 1 + T := by dsimp [T]; positivity
    have heq : 2 * t / (1 + t) - Real.cos eta ^ 2 =
        (t + 2 * q - 1) / ((1 + t) * (1 + T)) := by
      rw [hcos_eta_sq]
      field_simp [hden1.ne', hden2.ne']
      nlinarith only [htan_eta_sq]
    rw [← sub_pos, heq]
    exact div_pos (by linarith only [hkey]) (mul_pos hden1 hden2)
  by_cases htheta : Real.pi / 2 ≤ theta
  · change 2 * theta + beta + delta > Real.pi
    linarith only [htheta, hbeta_pos, hdelta_pos]
  · have htheta_lt_half : theta < Real.pi / 2 := lt_of_not_ge htheta
    have htheta_cos_pos : 0 < Real.cos theta :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta_lt_half⟩
    have htheta_cos_lt_one : Real.cos theta < 1 := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith)
        (by linarith [htheta_lt_pi, Real.pi_pos]) htheta_pos
      simpa using h
    have hhalf_ratio : 2 * t / (1 + t) = 1 - ct := by
      have hden : 0 < 1 + t := by linarith only [ht_pos]
      apply (div_eq_iff hden.ne').2
      nlinarith only [htan_half]
    have hsin_sq_bound : 1 - ct < Real.sin theta ^ 2 := by
      have htrig := Real.sin_sq_add_cos_sq theta
      rw [hcos_theta] at htrig
      have hctpos : 0 < ct := by rw [← hcos_theta]; exact htheta_cos_pos
      have hctlt : ct < 1 := by rw [← hcos_theta]; exact htheta_cos_lt_one
      have hprod : 0 < ct * (1 - ct) :=
        mul_pos hctpos (by linarith only [hctlt])
      nlinarith only [htrig, hprod]
    have hcos_eta_lt_sin : Real.cos eta < Real.sin theta := by
      have hsintheta : 0 < Real.sin theta :=
        Real.sin_pos_of_pos_of_lt_pi htheta_pos htheta_lt_pi
      apply (sq_lt_sq₀ hcos_eta.le hsintheta.le).mp
      calc
        Real.cos eta ^ 2 < 2 * t / (1 + t) := hcos_sq_bound
        _ = 1 - ct := hhalf_ratio
        _ < Real.sin theta ^ 2 := hsin_sq_bound
    have htarget : Real.pi / 2 - theta < eta := by
      by_contra hn
      have hle : eta ≤ Real.pi / 2 - theta := le_of_not_gt hn
      have hcosle : Real.cos (Real.pi / 2 - theta) ≤ Real.cos eta := by
        exact Real.strictAntiOn_cos.antitoneOn
          ⟨by linarith [htheta_lt_half], by linarith [htheta_pos, Real.pi_pos]⟩
          ⟨by linarith [heta_pos], by linarith [heta_lt_half_pi, Real.pi_pos]⟩ hle
      rw [Real.cos_pi_div_two_sub] at hcosle
      linarith
    dsimp [eta] at htarget
    change 2 * theta + beta + delta > Real.pi
    linarith only [htarget]

/-- For the same paired tuple, a transverse flat choice has a unique longer
label and a gap set by the two positive axial lengths. This uses raw cosines,
without moving the genuine-angle formulas into a flat branch. -/
theorem flat_transverse_gap
    (r a b o : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (haxis : 1 ≤ cosine r a b o a b)
    (hchosen : cosine a b r a b o ≤ -1)
    (hother : 1 ≤ cosine b a r b a o) :
    a > b ∧ Real.sqrt ((r + 1) * (o + 1)) ≤ a - b := by
  let Dr : ℝ := rad r a b
  let Do : ℝ := rad o a b
  let L : ℝ := (a + b)^2 - (r - 1) * (o - 1)
  let M : ℝ := (r + 1) * (o + 1) - (a - b)^2
  have hrad : ∀ x y z : ℝ, 1 < x → 1 < y → 1 < z → 0 < rad x y z := by
    intro x y z hx hy hz
    have hx2 : 1 ≤ x^2 := by nlinarith only [hx, sq_nonneg (x - 1)]
    have hy2 : 1 ≤ y^2 := by nlinarith only [hy, sq_nonneg (y - 1)]
    have hz2 : 1 ≤ z^2 := by nlinarith only [hz, sq_nonneg (z - 1)]
    have hp : 0 ≤ 2 * x * y * z := by positivity
    unfold rad
    linarith
  have hDr : 0 < Dr := hrad r a b hr ha hb
  have hDo : 0 < Do := hrad o a b ho ha hb
  have hQ : 0 < Dr * Do := mul_pos hDr hDo
  have hQs : 0 < Real.sqrt (Dr * Do) := Real.sqrt_pos.2 hQ
  have hsqrt_mul : Real.sqrt (Dr * Do) = Real.sqrt Dr * Real.sqrt Do := by
    rw [Real.sqrt_mul (le_of_lt hDr)]
  have haxis_exact : cosine r a b o a b * Dr = numerator r a b o a b := by
    have hrad_swap : rad r b a = Dr := by dsimp [Dr]; unfold rad; ring
    rw [cosine, hrad_swap, div_div, ← pow_two, Real.sq_sqrt hDr.le]
    field_simp [hDr.ne']
  have hminus_poly : Dr - numerator r a b o a b = (r - 1) * M := by
    dsimp [Dr, M]
    unfold rad numerator
    ring
  have hminus : Dr * (1 - cosine r a b o a b) = (r - 1) * M := by
    nlinarith only [haxis_exact, hminus_poly]
  have hM : M ≤ 0 := by
    have hleft : Dr * (1 - cosine r a b o a b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hDr.le (by linarith)
    have hright : (r - 1) * M ≤ 0 := by rw [← hminus]; exact hleft
    by_contra h
    have hMpos : 0 < M := lt_of_not_ge h
    exact (not_lt_of_ge hright) (mul_pos (by linarith) hMpos)
  have hgap_sq : (r + 1) * (o + 1) ≤ (a - b)^2 := by
    dsimp [M] at hM
    linarith
  have hprod : 0 < (r + 1) * (o + 1) := mul_pos (by linarith) (by linarith)
  have hL : 0 < L := by
    have hab : 0 < a * b := mul_pos (by linarith) (by linarith)
    dsimp [L]
    nlinarith only [hgap_sq, hab, hr, ho]
  have hca_exact : cosine a b r a b o * Real.sqrt (Dr * Do) =
      numerator a b r a b o := by
    unfold cosine
    have hrad1 : rad a b o = Do := by dsimp [Do]; unfold rad; ring
    have hrad2 : rad a r b = Dr := by dsimp [Dr]; unfold rad; ring
    rw [hrad1, hrad2, div_div, hsqrt_mul]
    field_simp [(Real.sqrt_pos.2 hDr).ne', (Real.sqrt_pos.2 hDo).ne']
  have hcb_exact : cosine b a r b a o * Real.sqrt (Dr * Do) =
      numerator b a r b a o := by
    unfold cosine
    have hrad1 : rad b a o = Do := by dsimp [Do]; unfold rad; ring
    have hrad2 : rad b r a = Dr := by dsimp [Dr]; unfold rad; ring
    rw [hrad1, hrad2, div_div, hsqrt_mul]
    field_simp [(Real.sqrt_pos.2 hDr).ne', (Real.sqrt_pos.2 hDo).ne']
  have hnum_diff : numerator a b r a b o - numerator b a r b a o =
      -(a - b) * L := by
    dsimp [L]
    unfold numerator
    ring
  have hnum_order : numerator a b r a b o < numerator b a r b a o := by
    rw [← hca_exact, ← hcb_exact]
    exact mul_lt_mul_of_pos_right (by linarith : cosine a b r a b o <
      cosine b a r b a o) hQs
  have hab : 0 < a - b := by
    have hnegative : -(a - b) * L < 0 := by rw [← hnum_diff]; linarith
    nlinarith only [hnegative, hL]
  have hsqrt_sq : (Real.sqrt ((r + 1) * (o + 1)))^2 =
      (r + 1) * (o + 1) := Real.sq_sqrt hprod.le
  constructor
  · linarith
  · nlinarith only [hgap_sq, hab, hsqrt_sq,
      Real.sqrt_nonneg ((r + 1) * (o + 1))]

/-- The selected transverse raw cosine alone forces the flat length gap,
without axial or opposite transverse branch inequalities. -/
theorem flat_transverse_gap_of_chosen
    (r a b o : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hchosen : cosine a b r a b o ≤ -1) :
    a > b ∧ Real.sqrt ((r + 1) * (o + 1)) ≤ a - b := by
  let Dr : ℝ := rad r a b
  let Do : ℝ := rad o a b
  let L : ℝ := (a + b)^2 - (r - 1) * (o - 1)
  let M : ℝ := (r + 1) * (o + 1) - (a - b)^2
  have hrad : ∀ x y z : ℝ, 1 < x → 1 < y → 1 < z → 0 < rad x y z := by
    intro x y z hx hy hz
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x - 1)]
    have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y - 1)]
    have hz2 : 1 ≤ z^2 := by nlinarith [sq_nonneg (z - 1)]
    have hp : 0 ≤ 2 * x * y * z := by positivity
    unfold rad
    linarith
  have hDr : 0 < Dr := hrad r a b hr ha hb
  have hDo : 0 < Do := hrad o a b ho ha hb
  have hQ : 0 < Dr * Do := mul_pos hDr hDo
  have hQs : 0 < Real.sqrt (Dr * Do) := Real.sqrt_pos.2 hQ
  have hsqrt_mul : Real.sqrt (Dr * Do) = Real.sqrt Dr * Real.sqrt Do := by
    rw [Real.sqrt_mul (le_of_lt hDr)]
  have hca_exact : cosine a b r a b o * Real.sqrt (Dr * Do) =
      numerator a b r a b o := by
    unfold cosine
    have hrad1 : rad a b o = Do := by dsimp [Do]; unfold rad; ring
    have hrad2 : rad a r b = Dr := by dsimp [Dr]; unfold rad; ring
    rw [hrad1, hrad2, div_div, hsqrt_mul]
    field_simp [(Real.sqrt_pos.2 hDr).ne', (Real.sqrt_pos.2 hDo).ne']
  have hnum_neg : numerator a b r a b o < 0 := by
    rw [← hca_exact]
    nlinarith only [hchosen, hQs]
  have hab : b < a := by
    by_contra h
    have hab' : a ≤ b := le_of_not_gt h
    have hsq : a^2 ≤ b^2 := by nlinarith only [hab', ha, hb]
    have hro : 0 < r * o := mul_pos (by linarith) (by linarith)
    have hterm : 0 < r * o + b^2 - a^2 + 1 := by linarith
    have hpos : 0 < b * (r + o) + a * (r * o + b^2 - a^2 + 1) := by
      positivity
    have hpoly : numerator a b r a b o =
        b * (r + o) + a * (r * o + b^2 - a^2 + 1) := by
      unfold numerator
      ring
    linarith
  have hL : 0 < L := by
    by_contra h
    have hbound : (a + b)^2 ≤ (r - 1) * (o - 1) := by
      dsimp [L] at h
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbound (by linarith : 0 ≤ a)
    have hpoly : numerator a b r a b o =
        b * (r + o) + a * (r * o + b^2 - a^2 + 1) := by
      unfold numerator
      ring
    have hsum : 0 < (a + b) * (r + o) + 2 * a * b * (a + b) := by
      positivity
    rw [hpoly] at hnum_neg
    nlinarith only [hmul, hsum, hnum_neg]
  have hca_sq : (cosine a b r a b o)^2 * (Dr * Do) =
      numerator a b r a b o ^ 2 := by
    calc
      (cosine a b r a b o)^2 * (Dr * Do) =
          (cosine a b r a b o * Real.sqrt (Dr * Do))^2 := by
        rw [mul_pow, Real.sq_sqrt hQ.le]
      _ = numerator a b r a b o ^ 2 := by rw [hca_exact]
  have hfactor : Dr * Do - numerator a b r a b o ^ 2 =
      (a^2 - 1) * L * M := by
    dsimp [Dr, Do, L, M]
    unfold rad numerator
    ring
  have hca_bound : 1 ≤ (cosine a b r a b o)^2 := by
    nlinarith only [hchosen, sq_nonneg (cosine a b r a b o + 1)]
  have hfactor_nonpos : (a^2 - 1) * L * M ≤ 0 := by
    have hnonneg : 0 ≤ ((cosine a b r a b o)^2 - 1) * (Dr * Do) :=
      mul_nonneg (by linarith) hQ.le
    nlinarith only [hfactor, hca_sq, hnonneg]
  have hM : M ≤ 0 := by
    by_contra h
    have hMpos : 0 < M := lt_of_not_ge h
    have hapos : 0 < a^2 - 1 := by nlinarith only [ha]
    have hpos := mul_pos (mul_pos hapos hL) hMpos
    nlinarith only [hpos, hfactor_nonpos]
  have hgap_sq : (r + 1) * (o + 1) ≤ (a - b)^2 := by
    dsimp [M] at hM
    linarith
  have hprod : 0 ≤ (r + 1) * (o + 1) := by positivity
  have hsqrt_sq : (Real.sqrt ((r + 1) * (o + 1)))^2 =
      (r + 1) * (o + 1) := Real.sq_sqrt hprod
  constructor
  · exact hab
  · nlinarith only [hgap_sq, hab, hsqrt_sq,
      Real.sqrt_nonneg ((r + 1) * (o + 1))]

#print axioms paired_angle_demand
#print axioms flat_transverse_gap
#print axioms flat_transverse_gap_of_chosen

end D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
