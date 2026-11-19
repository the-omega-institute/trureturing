/- GID: D5/S3/Arith/Robin/GronwallAbundant/Asymptotic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GronwallAbundant/Asymptotic
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The prime-code entropy inherits an exponential power-logarithm saving. -/

import D5.S3.Arith.Robin.GronwallAbundant.Budget

/-! Elementary real inequalities absorb the finite code overhead and missing-set entropy. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.GronwallAbundant
open Real Filter Asymptotics
open scoped Topology

/-- The logarithmic cost of the three integer-code coordinates. -/
def codeCost (X B : ℝ) : ℝ :=
  Real.log 2 + Real.log (codeM X) + (codeL X : ℝ) * Real.log (codeA X + 1) +
    (codeK X B : ℝ) * (1 + Real.log ((codeM X : ℝ) / codeK X B))

private theorem log_eventually_le_eighth :
    ∀ᶠ X : ℝ in atTop, Real.log X ≤ X ^ (1 / 8 : ℝ) := by
  have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh, eventually_gt_atTop (1 : ℝ)] with X hX hlarge
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.log_pos hlarge),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul] using hX

private theorem power_times_exp_absorb (c u : ℝ) (hc : 0 < c) :
    u * Real.exp (-c * u) ≤ (2 / c) * Real.exp (-(c / 2) * u) := by
  have hh : (c / 2) * u ≤ Real.exp ((c / 2) * u) := by
    linarith [Real.add_one_le_exp ((c / 2) * u)]
  have hm := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-c * u))
  have he : Real.exp ((c / 2) * u) * Real.exp (-c * u) =
      Real.exp (-(c / 2) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  have hc2 : 0 < c / 2 := by positivity
  calc
    _ ≤ Real.exp (-(c / 2) * u) / (c / 2) := (le_div_iff₀ hc2).mpr (by nlinarith)
    _ = _ := by field_simp

private theorem code_rounding_bounds {X : ℝ} (hX : 4 ≤ X) :
    (0 : ℝ) < codeM X ∧ (codeM X : ℝ) ≤ 2 * X ∧
    (codeL X : ℝ) ≤ 3 * Real.sqrt X ∧
    Real.log (codeA X + 1) ≤ 3 * Real.log X ∧
    Real.log 2 + Real.log (codeM X) ≤ 3 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hM0 : (0 : ℝ) < codeM X := by dsimp [codeM]; positivity
  have hM : (codeM X : ℝ) ≤ X + 1 := by
    dsimp [codeM]
    push_cast
    linarith [Nat.floor_le hX0.le]
  have hroot : (codeL X : ℝ) ≤ 3 * Real.sqrt X := by
    have hh : (codeL X : ℝ) ≤ Real.sqrt (2 * X) + 1 := by
      dsimp [codeL]
      push_cast
      linarith [Nat.floor_le (Real.sqrt_nonneg (2 * X))]
    have hsqrt : Real.sqrt (2 * X) ≤ 2 * Real.sqrt X := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have htwo : Real.sqrt 2 ≤ (2 : ℝ) := by
        apply (Real.sqrt_le_iff).mpr
        norm_num
      exact mul_le_mul_of_nonneg_right htwo
        (Real.sqrt_nonneg X)
    have hone : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by nlinarith)
    linarith
  have hA : (codeA X : ℝ) + 1 ≤ 4 * X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * X by positivity)
    dsimp [codeA]
    push_cast
    linarith
  have hA0 : (0 : ℝ) < (codeA X : ℝ) + 1 := by positivity
  have hlog4 : Real.log 4 ≤ 2 * Real.log X := by
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hX
    linarith
  have hlogA : Real.log (codeA X + 1) ≤ 3 * Real.log X := by
    have hh := Real.log_le_log hA0 hA
    rw [Real.log_mul (by norm_num) hX0.ne'] at hh
    linarith
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hlogM : Real.log (codeM X) ≤ Real.log 2 + Real.log X := by
    have hh := Real.log_le_log hM0 (show (codeM X : ℝ) ≤ 2 * X by linarith)
    simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] using hh
  exact ⟨hM0, by linarith, hroot, hlogA, by linarith⟩

private theorem code_overhead_eventually (a : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      Real.log 2 + Real.log (codeM X) + (codeL X : ℝ) * Real.log (codeA X + 1) ≤
        12 * (X / Real.log X) * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ), log_eventually_le_eighth,
    rpow_eventually_le_pnt_envelope a (3 / 4) (by norm_num)] with X hX hlogpow hsave
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  obtain ⟨hM0, hM, hL, hA, hlogM⟩ := code_rounding_bounds hX
  have hlogA0 : 0 ≤ Real.log (codeA X + 1) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ codeA X + 1 by omega))
  have hroot : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by nlinarith)
  have hmul : (codeL X : ℝ) * Real.log (codeA X + 1) ≤
      9 * Real.sqrt X * Real.log X := by
    have hh := mul_le_mul hL hA hlogA0 (by positivity : 0 ≤ 3 * Real.sqrt X)
    nlinarith only [hh]
  have hcost : Real.log 2 + Real.log (codeM X) +
      (codeL X : ℝ) * Real.log (codeA X + 1) ≤ 12 * Real.sqrt X * Real.log X := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hlog.le]
  have hpowers : Real.sqrt X * Real.log X ^ 2 ≤ X ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.sqrt X * (X ^ (1 / 8 : ℝ)) ^ 2 := by gcongr
      _ = X ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hX0.le,
          ← Real.rpow_add hX0]
        norm_num
  apply (mul_le_mul_iff_left₀ hlog).mp
  calc
    _ ≤ 12 * Real.sqrt X * Real.log X * Real.log X :=
      mul_le_mul_of_nonneg_right hcost hlog.le
    _ = 12 * (Real.sqrt X * Real.log X ^ 2) := by ring
    _ ≤ 12 * X ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hpowers (by norm_num)
    _ ≤ 12 * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) :=
      mul_le_mul_of_nonneg_left hsave (by norm_num)
    _ = (12 * (X / Real.log X) *
        Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) * Real.log X := by
      field_simp [hlog.ne']

private theorem code_entropy_bound {X c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hX : 4 ≤ X) (hloglarge : 2 * C + 2 ≤ Real.log X)
    (hH : 1 ≤ (X / Real.log X) * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)))
    (hu : 1 ≤ (Real.log X) ^ ((1 : ℝ) / 10)) :
    let B := C * (X * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)))
    codeK X B ≤ codeM X ∧
    (codeK X B : ℝ) * (1 + Real.log ((codeM X : ℝ) / codeK X B)) ≤
      ((2 * C + 2) * (11 + c + |Real.log C|) * (2 / c)) *
        (X / Real.log X) * Real.exp (-(c / 2) * (Real.log X) ^ ((1 : ℝ) / 10)) := by
  dsimp only
  let u := (Real.log X) ^ ((1 : ℝ) / 10)
  let H := (X / Real.log X) * Real.exp (-c * u)
  let B := C * (X * Real.exp (-c * u))
  let K : ℝ := codeK X B
  let M : ℝ := codeM X
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hH0 : 0 < H := by dsimp [H]; positivity
  have hbase : 2 * B / Real.log X = 2 * C * H := by dsimp [B, H]; ring
  have hlo : 2 * C * H ≤ K := by
    simpa only [hbase] using codeK_lower X B
  have hhi : K ≤ (2 * C + 2) * H := by
    have hh := codeK_upper (by linarith : 1 < X) (show 0 ≤ B by dsimp [B]; positivity)
    rw [hbase] at hh
    change 1 ≤ H at hH
    nlinarith
  have hK0 : 0 < K := by dsimp [K, codeK]; positivity
  have hM0 : 0 < M := by dsimp [M, codeM]; positivity
  have hexp : Real.exp (-c * u) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    nlinarith
  have hKX : K ≤ X := by
    calc
      K ≤ (2 * C + 2) * H := hhi
      _ ≤ (2 * C + 2) * (X / Real.log X) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        dsimp [H]
        exact mul_le_of_le_one_right (by positivity) hexp
      _ ≤ X := by
        apply (mul_le_mul_iff_left₀ hlog).mp
        have hh := mul_le_mul_of_nonneg_right hloglarge hX0.le
        field_simp [hlog.ne']
        nlinarith
  have hXM : X ≤ M := by
    dsimp [M, codeM]
    push_cast
    exact (Nat.lt_floor_add_one X).le
  have hKM : codeK X B ≤ codeM X := by
    have hh : (codeK X B : ℝ) ≤ (codeM X : ℝ) := hKX.trans hXM
    exact_mod_cast hh
  have hM : M ≤ 2 * X := (code_rounding_bounds hX).2.1
  have hlogM : Real.log M ≤ Real.log 2 + Real.log X := by
    have hh := Real.log_le_log hM0 hM
    simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] using hh
  have hlogK : Real.log 2 + Real.log C + Real.log X - c * u -
      Real.log (Real.log X) ≤ Real.log K := by
    have hh := Real.log_le_log (mul_pos (mul_pos (by norm_num) hC) hH0) hlo
    dsimp [H] at hh
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 2) hC).ne'
      (mul_pos (div_pos hX0 hlog) (Real.exp_pos _)).ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hC.ne',
      Real.log_mul (div_pos hX0 hlog).ne' (Real.exp_pos _).ne',
      Real.log_div hX0.ne' hlog.ne', Real.log_exp] at hh
    linarith
  have hloglog : Real.log (Real.log X) ≤ 10 * u := by
    have hh := Real.log_le_rpow_div hlog.le (by norm_num : (0 : ℝ) < 1 / 10)
    dsimp [u]
    convert hh using 1 <;> ring
  let R := 10 + c + |Real.log C|
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlogratio : Real.log (M / K) ≤ R * u := by
    rw [Real.log_div hM0.ne' hK0.ne']
    have habs : -Real.log C ≤ |Real.log C| := neg_le_abs _
    have hscale : |Real.log C| ≤ |Real.log C| * u :=
      le_mul_of_one_le_right (abs_nonneg _) hu
    dsimp [R]
    nlinarith
  have hterm : K * (1 + Real.log (M / K)) ≤
      (2 * C + 2) * (1 + R) * (X / Real.log X) *
        (u * Real.exp (-c * u)) := by
    calc
      _ ≤ K * ((1 + R) * u) := by
        apply mul_le_mul_of_nonneg_left _ hK0.le
        have hu' : 1 ≤ u := hu
        nlinarith
      _ ≤ ((2 * C + 2) * H) * ((1 + R) * u) :=
        mul_le_mul_of_nonneg_right hhi (by dsimp [u]; positivity)
      _ = _ := by dsimp [H]; ring
  have hfinal := hterm.trans (mul_le_mul_of_nonneg_left (power_times_exp_absorb c u hc)
    (show 0 ≤ (2 * C + 2) * (1 + R) * (X / Real.log X) by positivity))
  refine ⟨hKM, ?_⟩
  dsimp only [B, K, M, R, u] at hfinal ⊢
  convert hfinal using 1 <;> ring

/-- The complete integer-code cost retains a uniform exponential saving. -/
theorem code_cost_eventually (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ a > 0, ∃ D > 0, ∀ᶠ X : ℝ in atTop,
      let B := C * (X * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)))
      codeK X B ≤ codeM X ∧
      codeCost X B ≤ D * (X / Real.log X) *
        Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
  let D := 12 + (2 * C + 2) * (11 + c + |Real.log C|) * (2 / c)
  refine ⟨c / 2, by positivity, D, by dsimp [D]; positivity, ?_⟩
  have hloglarge : ∀ᶠ X : ℝ in atTop, 2 * C + 2 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  have hu : ∀ᶠ X : ℝ in atTop, 1 ≤ (Real.log X) ^ ((1 : ℝ) / 10) := by
    have hh : Tendsto (fun X : ℝ => (Real.log X) ^ ((1 : ℝ) / 10)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
    exact hh.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (4 : ℝ), hloglarge, hu,
    pnt_count_scale_eventually_ge_one c, code_overhead_eventually (c / 2)]
      with X hX hlog hu hscale hover
  obtain ⟨hKM, hentropy⟩ := code_entropy_bound hc hC hX hlog hscale hu
  refine ⟨hKM, ?_⟩
  dsimp only [codeCost, D]
  nlinarith only [hover, hentropy]

end D5.S3.Arith.Robin.GronwallAbundant
