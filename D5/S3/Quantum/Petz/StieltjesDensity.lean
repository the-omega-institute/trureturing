/- GID: D5/S3/Quantum/Petz/StieltjesDensity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boundary density of the symmetric logarithmic kernel and its explicit confluent limit. -/

import D5.S3.Quantum.PositiveResolvent.LogarithmicIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

namespace D5.S3.Quantum.Petz.StieltjesDensity

open Set MeasureTheory Filter
open scoped Topology

noncomputable def rP (y z t : ℝ) : ℝ :=
  ((t + y) / ((t + z) * ((Real.log (t / y)) ^ 2 + Real.pi ^ 2))
    - (t + z) / ((t + y) * ((Real.log (t / z)) ^ 2 + Real.pi ^ 2))) / (y - z)

noncomputable def rQ (y z t : ℝ) : ℝ :=
  ((t + z) / (t * z * ((Real.log (t / z)) ^ 2 + Real.pi ^ 2))
    - (t + y) / (t * y * ((Real.log (t / y)) ^ 2 + Real.pi ^ 2))) / Real.log (y / z)

/-- The diagonal branch is the confluent boundary value, written in the original variables. -/
noncomputable def rho (y z t : ℝ) : ℝ :=
  if y = z then
    (t ^ 2 * ((Real.log (t / y)) ^ 2 + Real.pi ^ 2 - 3 * Real.log (t / y))
      - 5 * Real.log (t / y) * t * y - 2 * Real.log (t / y) * y ^ 2) /
      (3 * t * y * (t + y) * ((Real.log (t / y)) ^ 2 + Real.pi ^ 2) ^ 2)
  else (2 * rQ y z t - rP y z t) / 6

private noncomputable def K (u t : ℝ) : ℝ :=
  1 / ((Real.log (t / u)) ^ 2 + Real.pi ^ 2)

private lemma K_deriv {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    HasDerivAt (fun v => K v t)
      (2 * Real.log (t / u) / (u * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2) ^ 2)) u := by
  have hlog : HasDerivAt (fun v : ℝ => Real.log (t / v)) (-1 / u) u := by
    have h := ((hasDerivAt_const u t).div (hasDerivAt_id u) hu.ne').log (div_ne_zero ht.ne' hu.ne')
    convert h using 1 <;> dsimp <;> field_simp <;> ring
  have hd : ((Real.log (t / u)) ^ 2 + Real.pi ^ 2) ≠ 0 := by positivity
  have h := (((hlog.pow 2).add_const (Real.pi ^ 2)).inv hd)
  convert! h using 1
  · ext v
    simp [K, add_comm]
  · dsimp
    field_simp [hu.ne', hd]
    <;> ring

private lemma phi_deriv {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    HasDerivAt (fun v => (t + v) / (t * v) * K v t)
      (-1 / u ^ 2 * K u t + (t + u) / (t * u) *
        (2 * Real.log (t / u) / (u * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2) ^ 2))) u := by
  have h := (((hasDerivAt_id u).const_add t).div
    ((hasDerivAt_id u).const_mul t) (mul_ne_zero ht.ne' hu.ne')).mul (K_deriv hu ht)
  convert! h using 1 <;> (try rfl) <;> (try dsimp) <;>
    (try field_simp [hu.ne', ht.ne']) <;> ring

private lemma rP_split {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 < t)
    (hne : y ≠ z) :
    rP y z t = slope (fun u => K u t) y z + K y t / (t + z) + K z t / (t + y) := by
  have hD (u : ℝ) : (Real.log (t / u)) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  rw [slope_def_field]
  dsimp [rP, K]
  field_simp [hD y, hD z, (add_pos ht hy).ne', (add_pos ht hz).ne',
    sub_ne_zero.mpr hne, sub_ne_zero.mpr hne.symm]
  <;> ring

private lemma rQ_split {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 < t)
    (hne : y ≠ z) :
    rQ y z t = -slope (fun u => (t + u) / (t * u) * K u t) y z /
      slope Real.log y z := by
  rw [slope_def_field, slope_def_field]
  dsimp [rQ, K]
  rw [Real.log_div hy.ne' hz.ne']
  have hlog : Real.log y - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (Real.log_injOn_pos hy hz h))
  have hlog2 : Real.log z - Real.log y ≠ 0 := sub_ne_zero.mpr
    (fun h => hne (Real.log_injOn_pos hy hz h.symm))
  field_simp [hy.ne', hz.ne', ht.ne', hlog, hlog2, sub_ne_zero.mpr hne,
    sub_ne_zero.mpr hne.symm]
  <;> ring

/-- Continuity at the confluent parameter for each positive boundary argument. -/
theorem rho_tendsto {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    Tendsto (fun z => rho y z t) (𝓝[≠] y) (𝓝 (rho y y t)) := by
  let a := Real.log (t / y)
  let D := a ^ 2 + Real.pi ^ 2
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hK := K_deriv hy ht
  have hφ := phi_deriv hy ht
  have hQ := hφ.tendsto_slope.neg.div (Real.hasDerivAt_log hy.ne').tendsto_slope
    (inv_ne_zero hy.ne')
  have hc : Tendsto (fun _ : ℝ => K y t) (𝓝[≠] y) (𝓝 (K y t)) := tendsto_const_nhds
  have hP := (hK.tendsto_slope.add
    (hc.div
      (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds))
      (add_pos ht hy).ne')).add
    (hK.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.div_const (t + y))
  have he : ∀ᶠ z in 𝓝[≠] y, 0 < z ∧ y ≠ z := by
    filter_upwards [(eventually_gt_nhds hy).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hne
    exact ⟨hz, by simpa [mem_compl_iff, mem_singleton_iff, ne_comm] using hne⟩
  have h := ((hQ.const_mul 2).sub hP).div_const 6
  have heq : (2 * (-(-1 / y ^ 2 * K y t + (t + y) / (t * y) *
      (2 * a / (y * D ^ 2))) / y⁻¹) -
      (2 * a / (y * D ^ 2) + K y t / (t + y) + K y t / (t + y))) / 6 =
      rho y y t := by
    simp only [rho, if_pos rfl]
    dsimp [K, a, D]
    field_simp [hy.ne', ht.ne', (add_pos ht hy).ne', hD]
    <;> ring
  rw [← heq]
  apply h.congr'
  filter_upwards [he] with z hz
  simp only [rho, if_neg hz.2]
  rw [rP_split hy hz.1 ht hz.2, rQ_split hy hz.1 ht hz.2]
  rfl

/-- Bounded logarithmic multiplier used by StieltjesRepresentation.rho_integrable. -/
lemma log_factor_bound (a : ℝ) :
    |a / (a ^ 2 + Real.pi ^ 2)| ≤ 1 + 1 / Real.pi ^ 2 := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  rw [abs_div, abs_of_pos (by positivity : 0 < a ^ 2 + Real.pi ^ 2),
    div_le_iff₀ (by positivity : 0 < a ^ 2 + Real.pi ^ 2)]
  have ha : |a| ≤ a ^ 2 + 1 := by nlinarith [sq_nonneg (|a| - 1 / 2), sq_abs a]
  have hh : a ^ 2 + 1 ≤ (1 + 1 / Real.pi ^ 2) * (a ^ 2 + Real.pi ^ 2) := by
    field_simp
    nlinarith [sq_nonneg a]
  exact ha.trans hh

private lemma K_compare {y u t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (hu : u ∈ Icc (y / 2) (2 * y)) :
    K u t ≤ (2 + 2 * (Real.log 2) ^ 2 / Real.pi ^ 2) * K y t := by
  have hup : 0 < u := lt_of_lt_of_le (by positivity) hu.1
  have hlo := Real.log_le_log (show 0 < y / 2 by positivity) hu.1
  have hhi := Real.log_le_log hup hu.2
  rw [Real.log_div hy.ne' (by norm_num)] at hlo
  rw [Real.log_mul (by norm_num) hy.ne'] at hhi
  have hab : |Real.log u - Real.log y| ≤ Real.log 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hs : (Real.log (t / y)) ^ 2 ≤
      2 * (Real.log (t / u)) ^ 2 + 2 * (Real.log 2) ^ 2 := by
    rw [Real.log_div ht.ne' hy.ne', Real.log_div ht.ne' hup.ne']
    have hsq := sq_le_sq₀ (abs_nonneg _) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) |>.mpr hab
    rw [sq_abs] at hsq
    nlinarith [sq_nonneg (Real.log t - Real.log u - (Real.log u - Real.log y))]
  dsimp [K]
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hD : 0 < (Real.log (t / u)) ^ 2 + Real.pi ^ 2 := by positivity
  have hE : 0 < (Real.log (t / y)) ^ 2 + Real.pi ^ 2 := by positivity
  rw [mul_one_div, div_le_div_iff₀ hD hE]
  have hR : 0 ≤ (2 * (Real.log 2) ^ 2 / Real.pi ^ 2) * (Real.log (t / u)) ^ 2 := by positivity
  have he : (2 + 2 * (Real.log 2) ^ 2 / Real.pi ^ 2) *
      ((Real.log (t / u)) ^ 2 + Real.pi ^ 2) =
      2 * (Real.log (t / u)) ^ 2 + 2 * Real.pi ^ 2 + 2 * (Real.log 2) ^ 2 +
        (2 * (Real.log 2) ^ 2 / Real.pi ^ 2) * (Real.log (t / u)) ^ 2 := by
    field_simp
    <;> ring
  rw [he]
  nlinarith

private lemma slope_bound {f df : ℝ → ℝ} {y z M : ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (hy : y ∈ S) (hz : z ∈ S) (hne : y ≠ z)
    (hf : ∀ u ∈ S, HasDerivAt f (df u) u) (hb : ∀ u ∈ S, ‖df u‖ ≤ M) :
    ‖slope f y z‖ ≤ M := by
  rw [slope_def_field, norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))]
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hf u hu).hasDerivWithinAt) hb hS hy hz

private lemma uniform_derivatives {y t u : ℝ} (hy : 0 < y) (ht : 0 < t)
    (hu : u ∈ Icc (y / 2) (2 * y)) :
    let R := 2 + 2 * (Real.log 2) ^ 2 / Real.pi ^ 2
    let M := 2 / y
    let k := 2 * (1 + 1 / Real.pi ^ 2) * M * R
    let f := M ^ 2 * R + (M + 1) * k
    ‖2 * Real.log (t / u) / (u * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2) ^ 2)‖ ≤
      k * K y t ∧
    ‖-1 / u ^ 2 * K u t + (t + u) / (t * u) *
      (2 * Real.log (t / u) / (u * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2) ^ 2))‖ ≤
      f * (1 + 1 / t) * K y t := by
  let R := 2 + 2 * (Real.log 2) ^ 2 / Real.pi ^ 2
  let M := 2 / y
  let c := 1 + 1 / Real.pi ^ 2
  let k := 2 * c * M * R
  let f := M ^ 2 * R + (M + 1) * k
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  have hup : 0 < u := lt_of_lt_of_le (by positivity) hu.1
  have hK : 0 < K u t := by dsimp [K]; positivity
  have hKy : 0 < K y t := by dsimp [K]; positivity
  have hKu : K u t ≤ R * K y t := K_compare hy ht hu
  have hmu : 1 / u ≤ M := by
    dsimp [M]
    rw [div_le_div_iff₀ hup hy]
    linarith [hu.1]
  let a := Real.log (t / u)
  let D := a ^ 2 + Real.pi ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : ‖2 * a / (u * D ^ 2)‖ = 2 * (|a| / D) * (1 / u) * K u t := by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (mul_pos hup (sq_pos_of_pos hD))]
    dsimp [K, D, a]
    field_simp
    <;> ring
  have hdb : ‖2 * a / (u * D ^ 2)‖ ≤ k * K y t := by
    rw [hd]
    calc
      2 * (|a| / D) * (1 / u) * K u t ≤ 2 * c * M * (R * K y t) := by
        gcongr
        simpa only [abs_div, abs_of_pos (show 0 < a ^ 2 + Real.pi ^ 2 from hD)] using log_factor_bound a
      _ = k * K y t := by dsimp [k]; ring
  refine ⟨hdb, ?_⟩
  have hp : (t + u) / (t * u) = 1 / u + 1 / t := by field_simp <;> ring
  have hn : ‖-1 / u ^ 2 * K u t‖ = (1 / u) ^ 2 * K u t := by
    rw [norm_mul, Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos (sq_pos_of_pos hup),
      Real.norm_eq_abs, abs_of_pos hK]
    field_simp
  have hs : 1 / u + 1 / t ≤ (M + 1) * (1 + 1 / t) := by
    have hi : 0 < 1 / t := one_div_pos.mpr ht
    nlinarith [mul_nonneg hM.le hi.le]
  calc
    ‖-1 / u ^ 2 * K u t + (t + u) / (t * u) * (2 * a / (u * D ^ 2))‖ ≤
        ‖-1 / u ^ 2 * K u t‖ + ‖(t + u) / (t * u) * (2 * a / (u * D ^ 2))‖ := norm_add_le _ _
    _ = (1 / u) ^ 2 * K u t + (1 / u + 1 / t) * ‖2 * a / (u * D ^ 2)‖ := by
      rw [hn, norm_mul, hp, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ M ^ 2 * (R * K y t) + ((M + 1) * (1 + 1 / t)) * (k * K y t) := by
      gcongr
    _ ≤ f * (1 + 1 / t) * K y t := by
      dsimp [f]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg M) hR.le)
        (mul_nonneg (one_div_pos.mpr ht).le hKy.le)]

/-- A local common majorant for confluence; the StieltjesRepresentation module consumes it. -/
theorem rho_uniform_bound {y : ℝ} (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] y, ∀ t : ℝ, 0 < t →
      ‖rho y z t‖ ≤ C * (1 + 1 / t) /
        ((Real.log (t / y)) ^ 2 + Real.pi ^ 2) := by
  let R := 2 + 2 * (Real.log 2) ^ 2 / Real.pi ^ 2
  let M := 2 / y
  let k := 2 * (1 + 1 / Real.pi ^ 2) * M * R
  let f := M ^ 2 * R + (M + 1) * k
  let p := k + M + R / y
  let C := (4 * y * f + p) / 6
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog := (Real.hasDerivAt_log hy.ne').tendsto_slope.eventually
    (eventually_gt_nhds (show 1 / (2 * y) < y⁻¹ by
      rw [one_div, mul_inv]
      nlinarith [inv_pos.mpr hy]))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlog, self_mem_nhdsWithin,
    (eventually_gt_nhds (show y / 2 < y by linarith)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show y < 2 * y by linarith)).filter_mono nhdsWithin_le_nhds]
    with z hlog hne hzlo hzhi
  have hyz : y ≠ z := by simpa [mem_compl_iff, mem_singleton_iff, ne_comm] using hne
  have hz : 0 < z := by linarith
  have hys : y ∈ Icc (y / 2) (2 * y) := ⟨by linarith, by linarith⟩
  have hzs : z ∈ Icc (y / 2) (2 * y) := ⟨hzlo.le, hzhi.le⟩
  intro t ht
  have hKy : 0 < K y t := by dsimp [K]; positivity
  have hKz : 0 < K z t := by dsimp [K]; positivity
  have hH : 1 ≤ 1 + 1 / t := le_add_of_nonneg_right (one_div_pos.mpr ht).le
  have hsK : ‖slope (fun u => K u t) y z‖ ≤ k * K y t :=
    slope_bound (convex_Icc _ _) hys hzs hyz
      (fun u hu => K_deriv (lt_of_lt_of_le (by positivity) hu.1) ht)
      (fun u hu => (uniform_derivatives hy ht hu).1)
  have hsF : ‖slope (fun u => (t + u) / (t * u) * K u t) y z‖ ≤
      f * (1 + 1 / t) * K y t :=
    slope_bound (convex_Icc _ _) hys hzs hyz
      (fun u hu => phi_deriv (lt_of_lt_of_le (by positivity) hu.1) ht)
      (fun u hu => (uniform_derivatives hy ht hu).2)
  have hP : ‖rP y z t‖ ≤ p * K y t := by
    rw [rP_split hy hz ht hyz]
    have h1 : ‖K y t / (t + z)‖ ≤ M * K y t := by
      rw [norm_div, Real.norm_eq_abs (K y t), abs_of_pos hKy,
        Real.norm_eq_abs (t + z), abs_of_pos (add_pos ht hz)]
      have hh : 1 / (t + z) ≤ M := by
        dsimp [M]
        rw [div_le_div_iff₀ (add_pos ht hz) hy]
        linarith
      simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hh hKy.le
    have h2 : ‖K z t / (t + y)‖ ≤ R / y * K y t := by
      rw [norm_div, Real.norm_eq_abs (K z t), abs_of_pos hKz,
        Real.norm_eq_abs (t + y), abs_of_pos (add_pos ht hy)]
      calc
        K z t / (t + y) ≤ (R * K y t) / y := by
          gcongr
          · exact K_compare hy ht hzs
          · linarith
        _ = R / y * K y t := by ring
    have hh := (norm_add_le (slope (fun u => K u t) y z + K y t / (t + z))
      (K z t / (t + y))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    calc
      ‖slope (fun u => K u t) y z + K y t / (t + z) + K z t / (t + y)‖ ≤
          ‖slope (fun u => K u t) y z‖ + ‖K y t / (t + z)‖ + ‖K z t / (t + y)‖ := hh
      _ ≤ k * K y t + M * K y t + R / y * K y t :=
        add_le_add (add_le_add hsK h1) h2
      _ = p * K y t := by dsimp [p]; ring
  have hQ : ‖rQ y z t‖ ≤ (2 * y * f) * (1 + 1 / t) * K y t := by
    rw [rQ_split hy hz ht hyz, norm_div, norm_neg,
      Real.norm_eq_abs (slope Real.log y z), abs_of_pos (lt_trans (by positivity) hlog)]
    calc
      ‖slope (fun u => (t + u) / (t * u) * K u t) y z‖ / slope Real.log y z ≤
          (f * (1 + 1 / t) * K y t) / (1 / (2 * y)) := by gcongr
      _ = (2 * y * f) * (1 + 1 / t) * K y t := by field_simp <;> ring
  simp only [rho, if_neg hyz]
  rw [norm_div, Real.norm_eq_abs (6 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hh : ‖2 * rQ y z t - rP y z t‖ ≤
      2 * ((2 * y * f) * (1 + 1 / t) * K y t) + p * K y t := by
    calc
      ‖2 * rQ y z t - rP y z t‖ ≤ ‖2 * rQ y z t‖ + ‖rP y z t‖ := norm_sub_le _ _
      _ = 2 * ‖rQ y z t‖ + ‖rP y z t‖ := by rw [norm_mul]; norm_num
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hQ (by norm_num)) hP
  have heq : C * (1 + 1 / t) / ((Real.log (t / y)) ^ 2 + Real.pi ^ 2) =
      C * (1 + 1 / t) * K y t := by dsimp [K]; ring
  rw [heq]

  dsimp [C]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
  calc
    ‖2 * rQ y z t - rP y z t‖ ≤
        2 * ((2 * y * f) * (1 + 1 / t) * K y t) + p * K y t := hh
    _ ≤ (4 * y * f + p) / 6 * (1 + 1 / t) * K y t * 6 := by
      nlinarith only [mul_le_mul_of_nonneg_left hH (mul_nonneg hp.le hKy.le)]

end D5.S3.Quantum.Petz.StieltjesDensity
