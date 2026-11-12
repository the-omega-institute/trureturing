/- GID: D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Conditional uniform logarithmic denominator separation for actual mixed cutoffs. -/
import D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder

/-! Quantitative denominator separation for actual mixed cutoffs.
All roots below are the actual clamped cutoffs. The paid-growth and clock
suppliers remain external hypotheses. No theta approximation is used.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator
open Real Filter
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
open D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder

/-- The two leading coefficients and the fixed-logarithm fourth-order gap.
The proof consumes the original actual-root quartic remainder, rather than
assuming an expansion of U, V, or their gap. -/
theorem actual_mixed_denominator_expansions :
    Tendsto (fun X : ℝ => log X ^ 3 * U X) atTop (𝓝 (2 * log 2 ^ 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 3 * V X) atTop
      (𝓝 (2 * log 2 * (log 3 - log 2))) ∧
    Tendsto (fun X : ℝ => log X ^ 4 *
      ((log 3 - log 2) * U X - log 2 * V X)) atTop
      (𝓝 (3 * log 2 ^ 2 * log 3 * (log 3 - log 2))) := by
  let a : ℝ := log 2
  let b : ℝ := log 3
  let z := fun X : ℝ => 1 / log X
  let p := fun (j : ℕ) (X : ℝ) => (P (log j)).eval (z X)
  let pu := fun X => 3 * p 4 X - p 8 X - 3 * p 2 X
  let pv := fun X => p 2 X - 2 * p 4 X + p 8 X - p 3 X +
    2 * p 6 X - p 12 X
  have ha : 0 < a := log_pos (by norm_num : (1 : ℝ) < 2)
  have hz : Tendsto z atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hd : Tendsto (d 2) atTop (𝓝 a) :=
    fixed_layer_root_offset_tendsto (by norm_num)
  have hlog4 : log (4 : ℝ) = 2 * a := by
    simpa only [a, Nat.cast_ofNat, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
      log_pow (2 : ℝ) 2
  have hlog8 : log (8 : ℝ) = 3 * a := by
    simpa only [a, Nat.cast_ofNat, show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num] using
      log_pow (2 : ℝ) 3
  have hlog6 : log (6 : ℝ) = a + b := by
    simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
  have hlog12 : log (12 : ℝ) = 2 * a + b := by
    simpa only [show (4 : ℝ) * 3 = 12 by norm_num, hlog4] using
      log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
  -- Only finite polynomial algebra is new here; the analytic remainder is reused.
  have hpu (X : ℝ) : pu X = 2 * a ^ 3 * z X ^ 3 -
      (11 * a ^ 3 + 9 * a ^ 4) * z X ^ 4 := by
    dsimp [pu, p]
    simp only [hlog4, hlog8]
    simp only [P, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    dsimp [a]
    ring
  have hpv (X : ℝ) : pv X = 2 * a ^ 2 * (b - a) * z X ^ 3 -
      a ^ 2 * (b - a) * (11 + 9 * a + 3 * b) * z X ^ 4 := by
    dsimp [pv, p]
    simp only [hlog4, hlog8, hlog6, hlog12]
    simp only [P, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    dsimp [a, b]
    ring
  have hpf (X : ℝ) : (b - a) * pu X - a * pv X =
      3 * a ^ 3 * b * (b - a) * z X ^ 4 := by
    rw [hpu, hpv]
    ring
  have herr (j : ℕ) (hj : 2 ≤ j) :
      Tendsto (fun X => log X ^ 4 * (d j X - p j X)) atTop (𝓝 0) :=
    actual_quartic_error hj
  have hNU4 : Tendsto (fun X => log X ^ 4 * (NU X - pu X)) atTop (𝓝 0) := by
    have hh := ((herr 4 (by norm_num)).const_mul 3).sub (herr 8 (by norm_num))
      |>.sub ((herr 2 (by norm_num)).const_mul 3)
    simp only [mul_zero, sub_zero] at hh
    convert hh using 1
    funext X
    dsimp [NU, pu]
    ring
  have hNV4 : Tendsto (fun X => log X ^ 4 * (NV X - pv X)) atTop (𝓝 0) := by
    have hh := (herr 2 (by norm_num)).sub ((herr 4 (by norm_num)).const_mul 2)
      |>.add (herr 8 (by norm_num)) |>.sub (herr 3 (by norm_num))
      |>.add ((herr 6 (by norm_num)).const_mul 2) |>.sub (herr 12 (by norm_num))
    simp only [mul_zero, sub_zero, add_zero] at hh
    convert hh using 1
    funext X
    dsimp [NV, pv]
    ring
  have lower_error {f : ℝ → ℝ}
      (hf : Tendsto (fun X => log X ^ 4 * f X) atTop (𝓝 0)) :
      Tendsto (fun X => log X ^ 3 * f X) atTop (𝓝 0) := by
    have hh := hf.div_atTop tendsto_log_atTop
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    field_simp [(log_pos hX).ne']
    <;> ring
  have hpu3 : Tendsto (fun X => log X ^ 3 * pu X) atTop (𝓝 (2 * a ^ 3)) := by
    have hh := (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => 2 * a ^ 3) atTop (𝓝 (2 * a ^ 3))).sub
      (hz.const_mul (11 * a ^ 3 + 9 * a ^ 4))
    simp only [mul_zero, sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [hpu]
    dsimp [z]
    field_simp [(log_pos hX).ne']
    <;> ring
  have hpv3 : Tendsto (fun X => log X ^ 3 * pv X) atTop
      (𝓝 (2 * a ^ 2 * (b - a))) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2 * a ^ 2 * (b - a))
      atTop (𝓝 (2 * a ^ 2 * (b - a)))).sub
      (hz.const_mul (a ^ 2 * (b - a) * (11 + 9 * a + 3 * b)))
    simp only [mul_zero, sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [hpv]
    dsimp [z]
    field_simp [(log_pos hX).ne']
    <;> ring
  have hNU3 : Tendsto (fun X => log X ^ 3 * NU X) atTop (𝓝 (2 * a ^ 3)) := by
    have hh := hpu3.add (lower_error hNU4)
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    ring
  have hNV3 : Tendsto (fun X => log X ^ 3 * NV X) atTop
      (𝓝 (2 * a ^ 2 * (b - a))) := by
    have hh := hpv3.add (lower_error hNV4)
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    ring
  have hferr : Tendsto (fun X => log X ^ 4 *
      (((b - a) * NU X - a * NV X) - ((b - a) * pu X - a * pv X)))
      atTop (𝓝 0) := by
    have hh := (hNU4.const_mul (b - a)).sub (hNV4.const_mul a)
    simp only [mul_zero, sub_zero] at hh
    convert hh using 1
    funext X
    ring
  have hpoly4 : Tendsto (fun X => log X ^ 4 * ((b - a) * pu X - a * pv X))
      atTop (𝓝 (3 * a ^ 3 * b * (b - a))) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => 3 * a ^ 3 * b * (b - a))
      atTop (𝓝 (3 * a ^ 3 * b * (b - a)))).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [hpf]
    dsimp [z]
    field_simp [(log_pos hX).ne']
    <;> ring
  have hnum4 : Tendsto (fun X => log X ^ 4 * ((b - a) * NU X - a * NV X))
      atTop (𝓝 (3 * a ^ 3 * b * (b - a))) := by
    have hh := hpoly4.add hferr
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hh := hNU3.div hd ha.ne'
    have hc : 2 * a ^ 3 / a = 2 * a ^ 2 := by
      field_simp [ha.ne']
      <;> ring
    rw [hc] at hh
    apply hh.congr'
    filter_upwards [] with X
    dsimp [U, Pi.div_apply, a]
    simp only [div_eq_mul_inv]
    ring
  · have hh := hNV3.div hd ha.ne'
    have hc : 2 * a ^ 2 * (b - a) / a = 2 * a * (b - a) := by
      field_simp [ha.ne']
      <;> ring
    rw [hc] at hh
    apply hh.congr'
    filter_upwards [] with X
    dsimp [V, Pi.div_apply, a, b]
    simp only [div_eq_mul_inv]
    ring
  · have hh := hnum4.div hd ha.ne'
    have hc : 3 * a ^ 3 * b * (b - a) / a = 3 * a ^ 2 * b * (b - a) := by
      field_simp [ha.ne']
      <;> ring
    rw [hc] at hh
    apply hh.congr'
    filter_upwards [] with X
    dsimp [U, V, Pi.div_apply, a, b]
    simp only [div_eq_mul_inv]
    ring

/-- Positive logarithmic separation of two actual integer powers gives a
quantitative gap. This uses no irrationality theorem or determinant premise. -/
private theorem integer_power_log_gap {u v : ℤ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : 0 < (log 3 - log 2) * (u : ℝ) - log 2 * (v : ℝ)) :
    exp (-log 3 * (u : ℝ)) ≤ (log 3 - log 2) * (u : ℝ) - log 2 * (v : ℝ) := by
  let N : ℕ := 3 ^ u.toNat
  let M : ℕ := 2 ^ (u.toNat + v.toNat)
  have huc : ((u.toNat : ℕ) : ℝ) = (u : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ u)
  have hvc : ((v.toNat : ℕ) : ℝ) = (v : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ v)
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hlN : log (N : ℝ) = log 3 * (u : ℝ) := by
    simp only [N, Nat.cast_pow, Nat.cast_ofNat, log_pow, huc]
    ring
  have hlM : log (M : ℝ) = log 2 * ((u : ℝ) + v) := by
    simp only [M, Nat.cast_pow, Nat.cast_ofNat, log_pow, Nat.cast_add, huc, hvc]
    ring
  have htlog : (log 3 - log 2) * (u : ℝ) - log 2 * (v : ℝ) =
      log (N : ℝ) - log (M : ℝ) := by rw [hlN, hlM]; ring
  have hMN : M < N := by
    have hlog : log (M : ℝ) < log (N : ℝ) := by rw [← sub_pos, ← htlog]; exact ht
    have hreal := (log_lt_log_iff hM hN).mp hlog
    exact_mod_cast hreal
  have hunit : (M : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast (show M + 1 ≤ N by omega)
  have hbasic := log_le_sub_one_of_pos (div_pos hM hN)
  rw [log_div hM.ne' hN.ne'] at hbasic
  have hgap : 1 / (N : ℝ) ≤ 1 - (M : ℝ) / N := by
    apply (div_le_iff₀ hN).mpr
    have hid : (1 - (M : ℝ) / N) * N = (N : ℝ) - M := by
      field_simp [hN.ne']
      <;> ring
    rw [hid]
    linarith
  have hfinal : 1 / (N : ℝ) ≤ log (N : ℝ) - log (M : ℝ) := by linarith
  rw [htlog, show -log 3 * (u : ℝ) = -(log 3 * (u : ℝ)) by ring,
    ← hlN, exp_neg, exp_log hN]
  simpa only [one_div] using hfinal

/-- A consumed asymptotic/integer-gap lemma. The hypotheses are genuine
expansions and error limits; the denominator conclusion is not a premise. -/
private theorem eventual_two_resonance_denominator
    (w z eU eV : ℝ → ℝ)
    (hw : Tendsto (fun X : ℝ => log X ^ 3 * w X) atTop (𝓝 (2 * log 2 ^ 2)))
    (hz : Tendsto (fun X : ℝ => log X ^ 3 * z X) atTop
      (𝓝 (2 * log 2 * (log 3 - log 2))))
    (hf : Tendsto (fun X : ℝ => log X ^ 4 *
      ((log 3 - log 2) * w X - log 2 * z X)) atTop
      (𝓝 (3 * log 2 ^ 2 * log 3 * (log 3 - log 2))))
    (heU : Tendsto (fun X : ℝ => log X ^ 4 * eU X) atTop (𝓝 0))
    (heV : Tendsto (fun X : ℝ => log X ^ 4 * eV X) atTop (𝓝 0))
    (he : ∀ᶠ X : ℝ in atTop, 0 ≤ eU X ∧ 0 ≤ eV X)
    (C : ℝ) (hC : 0 < C) (hC' : C < 1 / (2 * log 2 ^ 2 * log 3)) :
    ∀ᶠ X : ℝ in atTop, ∀ h u v : ℤ, 1 ≤ h →
      |(h : ℝ) * w X - u| ≤ eU X →
      |(h : ℝ) * z X - v| ≤ eV X →
      C * log X ^ 3 * log (log X) < (h : ℝ) := by
  let a : ℝ := log 2
  let b : ℝ := log 3
  let c : ℝ := 2 * a ^ 2 * b
  let K : ℝ := 3 * a ^ 2 * b * (b - a)
  let f := fun X => (b - a) * w X - a * z X
  let E := fun X => (b - a) * eU X + a * eV X
  let R := fun X : ℝ => |log X ^ 4 * f X - K| + log X ^ 4 * E X
  let cX := fun X : ℝ => b * (log X ^ 3 * w X)
  let T := fun X : ℝ => log (log X)
  let G := fun X : ℝ => C * cX X +
    (b * eU X + log (K + R X) + log C) / T X + log (T X) / T X
  have ha : 0 < a := log_pos (by norm_num : (1 : ℝ) < 2)
  have hb : 0 < b := log_pos (by norm_num : (1 : ℝ) < 3)
  have hba : 0 < b - a := sub_pos.mpr
    (log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3))
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hCc : C * c < 1 := (lt_div_iff₀ hc).mp hC'
  have hi : Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have lower_error {e : ℝ → ℝ}
      (hh : Tendsto (fun X : ℝ => log X ^ 4 * e X) atTop (𝓝 0)) :
      Tendsto (fun X : ℝ => log X ^ 3 * e X) atTop (𝓝 0) := by
    have hh' := hh.div_atTop tendsto_log_atTop
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    field_simp [(log_pos hX).ne']
    <;> ring
  have heU3 := lower_error heU
  have heV3 := lower_error heV
  have heU0 : Tendsto eU atTop (𝓝 0) := by
    have hh := heU3.mul (hi.pow 3)
    norm_num only [zero_pow (by norm_num : 3 ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    field_simp [(log_pos hX).ne']
    <;> ring
  have hsignU := (hw.sub heU3).eventually
    (eventually_gt_nhds (show (0 : ℝ) < 2 * log 2 ^ 2 - 0 by
      change 0 < 2 * a ^ 2 - 0
      simpa only [sub_zero] using mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos ha 2)))
  have hsignV := (hz.sub heV3).eventually
    (eventually_gt_nhds (show (0 : ℝ) < 2 * log 2 * (log 3 - log 2) - 0 by
      change 0 < 2 * a * (b - a) - 0
      simpa only [sub_zero] using
        mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ha) hba))
  have hE : Tendsto (fun X : ℝ => log X ^ 4 * E X) atTop (𝓝 0) := by
    have hh := (heU.const_mul (b - a)).add (heV.const_mul a)
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    funext X
    dsimp [E]
    ring
  have hR : Tendsto R atTop (𝓝 0) := by
    have hf' : Tendsto (fun X : ℝ => log X ^ 4 * f X) atTop (𝓝 K) := hf
    have hh := (hf'.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => K) atTop (𝓝 K))).abs.add hE
    simpa only [sub_self, abs_zero, zero_add] using hh
  have hcX : Tendsto cX atTop (𝓝 c) := by
    have hh := hw.const_mul b
    have heq : b * (2 * log 2 ^ 2) = c := by dsimp [c, a]; ring
    simpa only [heq] using hh
  have hKR : Tendsto (fun X => K + R X) atTop (𝓝 K) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => K) atTop (𝓝 K)).add hR
  have hT : Tendsto T atTop atTop := tendsto_log_atTop.comp tendsto_log_atTop
  have hlogT : Tendsto (fun X => log (T X) / T X) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hT
  have hfinite : Tendsto (fun X => b * eU X + log (K + R X) + log C) atTop
      (𝓝 (log K + log C)) := by
    simpa only [mul_zero, zero_add] using
      ((heU0.const_mul b).add (hKR.log hK.ne')).add
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => log C) atTop (𝓝 (log C)))
  have hG : Tendsto G atTop (𝓝 (C * c)) := by
    have hh := ((hcX.const_mul C).add (hfinite.div_atTop hT)).add hlogT
    simpa only [add_zero] using hh
  -- Every event below depends on X and the supplied functions, before labels.
  filter_upwards [eventually_gt_atTop (1 : ℝ), he, hsignU, hsignV,
    hR.eventually (eventually_lt_nhds hK),
    hcX.eventually (eventually_gt_nhds hc), hT.eventually_gt_atTop 0,
    hG.eventually (eventually_lt_nhds hCc)]
      with X hX heX hUXpos hVXpos hRX hcxpos hTX hGX
  have hL : 0 < log X := log_pos hX
  have hL3 : 0 < log X ^ 3 := pow_pos hL 3
  have hL4 : 0 < log X ^ 4 := pow_pos hL 4
  have hwgt : eU X < w X := by
    have hs : log X ^ 3 * eU X < log X ^ 3 * w X := by linarith only [hUXpos]
    exact (mul_lt_mul_iff_right₀ hL3).mp hs
  have hzgt : eV X < z X := by
    have hs : log X ^ 3 * eV X < log X ^ 3 * z X := by linarith only [hVXpos]
    exact (mul_lt_mul_iff_right₀ hL3).mp hs
  have hw0 : 0 < w X := lt_of_le_of_lt heX.1 hwgt
  have hz0 : 0 < z X := lt_of_le_of_lt heX.2 hzgt
  have hE0 : 0 ≤ E X :=
    add_nonneg (mul_nonneg hba.le heX.1) (mul_nonneg ha.le heX.2)
  have hR0 : 0 ≤ R X := add_nonneg (abs_nonneg _) (mul_nonneg hL4.le hE0)
  have hKR0 : 0 < K + R X := by linarith
  intro h u v hh hUX hVX
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hUabs := abs_le.mp hUX
  have hVabs := abs_le.mp hVX
  -- The integer signs are uniform even when h = 1.
  have hu0 : (0 : ℝ) < u := by
    have hmul := mul_le_mul_of_nonneg_right hhR hw0.le
    linarith only [hmul, hwgt, hUabs.2]
  have hv0 : (0 : ℝ) < v := by
    have hmul := mul_le_mul_of_nonneg_right hhR hz0.le
    linarith only [hmul, hzgt, hVabs.2]
  have hu : 1 ≤ u := by
    have : (0 : ℤ) < u := by exact_mod_cast hu0
    omega
  have hv : 1 ≤ v := by
    have : (0 : ℤ) < v := by exact_mod_cast hv0
    omega
  let x : ℝ := (h : ℝ) / log X ^ 3
  let t : ℝ := (b - a) * (u : ℝ) - a * (v : ℝ)
  have hx : 0 < x := div_pos hh0 hL3
  have hterror : |t - (h : ℝ) * f X| ≤ E X := by
    have hid : t - (h : ℝ) * f X =
        (b - a) * ((u : ℝ) - h * w X) - a * ((v : ℝ) - h * z X) := by
      dsimp [t, f]
      ring
    rw [hid]
    calc
      _ ≤ |(b - a) * ((u : ℝ) - h * w X)| +
          |a * ((v : ℝ) - h * z X)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le ((b - a) * ((u : ℝ) - h * w X)) (-(a * ((v : ℝ) - h * z X)))
      _ = (b - a) * |(h : ℝ) * w X - u| + a * |(h : ℝ) * z X - v| := by
        rw [abs_mul, abs_mul, abs_of_pos hba, abs_of_pos ha,
          abs_sub_comm (u : ℝ), abs_sub_comm (v : ℝ)]
      _ ≤ E X := add_le_add (mul_le_mul_of_nonneg_left hUX hba.le)
        (mul_le_mul_of_nonneg_left hVX ha.le)
  have hscaled : |log X ^ 4 * t - (h : ℝ) * K| ≤ (h : ℝ) * R X := by
    calc
      _ = |log X ^ 4 * (t - (h : ℝ) * f X) +
          (h : ℝ) * (log X ^ 4 * f X - K)| := by congr 1; ring
      _ ≤ |log X ^ 4 * (t - (h : ℝ) * f X)| +
          |(h : ℝ) * (log X ^ 4 * f X - K)| := abs_add_le _ _
      _ = log X ^ 4 * |t - (h : ℝ) * f X| +
          (h : ℝ) * |log X ^ 4 * f X - K| := by
        rw [abs_mul, abs_mul, abs_of_pos hL4, abs_of_pos hh0]
      _ ≤ log X ^ 4 * E X + (h : ℝ) * |log X ^ 4 * f X - K| := by
        exact add_le_add (mul_le_mul_of_nonneg_left hterror hL4.le) le_rfl
      _ ≤ (h : ℝ) * (log X ^ 4 * E X) + (h : ℝ) * |log X ^ 4 * f X - K| := by
        have hhE := le_mul_of_one_le_left (mul_nonneg hL4.le hE0) hhR
        linarith only [hhE]
      _ = (h : ℝ) * R X := by dsimp [R]; ring
  have htbounds : (K - R X) * x / log X ≤ t ∧ t ≤ (K + R X) * x / log X := by
    have hs := abs_le.mp hscaled
    have hlow : log X ^ 4 * ((K - R X) * x / log X) = (h : ℝ) * (K - R X) := by
      dsimp [x]
      field_simp [hL.ne']
      <;> ring
    have hupp : log X ^ 4 * ((K + R X) * x / log X) = (h : ℝ) * (K + R X) := by
      dsimp [x]
      field_simp [hL.ne']
      <;> ring
    constructor
    · apply (mul_le_mul_iff_right₀ hL4).mp
      rw [hlow]
      nlinarith only [hs.1]
    · apply (mul_le_mul_iff_right₀ hL4).mp
      rw [hupp]
      nlinarith only [hs.2]
  have ht : 0 < t := lt_of_lt_of_le (div_pos (mul_pos (sub_pos.mpr hRX) hx) hL) htbounds.1
  have hgap : exp (-b * (u : ℝ)) ≤ t := integer_power_log_gap hu hv ht
  have hloggap := log_le_log (exp_pos (-b * (u : ℝ))) (hgap.trans htbounds.2)
  rw [log_exp, log_div (mul_pos hKR0 hx).ne' hL.ne', log_mul hKR0.ne' hx.ne'] at hloggap
  have htlog : T X ≤ b * (u : ℝ) + log (K + R X) + log x := by
    dsimp [T]
    linarith only [hloggap]
  have hcxid : cX X * x = b * (h : ℝ) * w X := by
    dsimp [cX, x]
    field_simp [hL.ne']
    <;> ring
  have hub : b * (u : ℝ) ≤ cX X * x + b * eU X := by
    have hleu : (u : ℝ) ≤ (h : ℝ) * w X + eU X := by linarith only [hUabs.1]
    have hmul := mul_le_mul_of_nonneg_left hleu hb.le
    rw [hcxid]
    simpa only [mul_add, mul_assoc] using hmul
  by_contra hn
  have hsmall : (h : ℝ) ≤ C * log X ^ 3 * T X := le_of_not_gt hn
  have hxsmall : x ≤ C * T X := by
    apply (div_le_iff₀ hL3).mpr
    nlinarith only [hsmall]
  have hlogx : log x ≤ log C + log (T X) := by
    have hh' := log_le_log hx hxsmall
    rwa [log_mul hC.ne' hTX.ne'] at hh'
  have hcsmall := mul_le_mul_of_nonneg_left hxsmall hcxpos.le
  have htotal : T X ≤ cX X * C * T X + b * eU X +
      log (K + R X) + log C + log (T X) := by
    nlinarith only [htlog, hub, hlogx, hcsmall]
  have hGid : G X * T X = cX X * C * T X + b * eU X +
      log (K + R X) + log C + log (T X) := by
    dsimp [G]
    field_simp [hTX.ne']
    <;> ring
  have hless := mul_lt_mul_of_pos_right hGX hTX
  rw [hGid] at hless
  linarith only [htotal, hless]

/-- Actual two-resonance denominator exclusion with the original mode-8 and
mode-12 paid suppliers. C is fixed before the common X threshold; all three
integer labels occur after that threshold. This does not produce a supplier. -/
theorem eventual_actual_mixed_denominator
    (beta C0 rho8 rho12 : ℝ) (barL : ℝ → ℝ) (M N : ℝ → ℕ)
    (hbeta : 37 / 50 ≤ beta) (hbeta' : beta < 3 / 4) (hC0 : 0 ≤ C0)
    (hrho8 : 0 < rho8) (hrho12 : 0 < rho12)
    (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0))
    (hpaid8 : ∀ᶠ X : ℝ in atTop,
      rho8 * exp (((1 - beta) / 8 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (M X : ℝ) + 1)
    (hpaid12 : ∀ᶠ X : ℝ in atTop,
      rho12 * exp (((1 - beta) / 12 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (N X : ℝ) + 1) :
    ∀ C : ℝ, 0 < C → C < 1 / (2 * log 2 ^ 2 * log 3) →
      ∀ᶠ X : ℝ in atTop, ∀ h u v : ℤ, 1 ≤ h →
        |(h : ℝ) * U X - u| ≤ C0 / ((M X : ℝ) + 1) →
        |(h : ℝ) * V X - v| ≤ C0 / ((N X : ℝ) + 1) →
        C * log X ^ 3 * log (log X) < (h : ℝ) := by
  have hl8 : 1 / 80 ≤ (1 - beta) / 8 - (3 / 2 - 2 * beta) := by linarith
  have hl12 : 1 / 600 ≤ (1 - beta) / 12 - (3 / 2 - 2 * beta) := by linarith
  obtain ⟨_, hr8⟩ := paid_range_rate hrho8 (by linarith :
    0 < (1 - beta) / 8 - (3 / 2 - 2 * beta)) hclose hpaid8
  obtain ⟨_, hr12⟩ := paid_range_rate hrho12 (by linarith :
    0 < (1 - beta) / 12 - (3 / 2 - 2 * beta)) hclose hpaid12
  let eU := fun X => C0 / ((M X : ℝ) + 1)
  let eV := fun X => C0 / ((N X : ℝ) + 1)
  have heU : Tendsto (fun X : ℝ => log X ^ 4 * eU X) atTop (𝓝 0) := by
    simpa [eU, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr8.const_mul C0
  have heV : Tendsto (fun X : ℝ => log X ^ 4 * eV X) atTop (𝓝 0) := by
    simpa [eV, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr12.const_mul C0
  have he : ∀ᶠ X : ℝ in atTop, 0 ≤ eU X ∧ 0 ≤ eV X := by
    filter_upwards [] with X
    exact ⟨div_nonneg hC0 (by positivity), div_nonneg hC0 (by positivity)⟩
  obtain ⟨hU, hV, hF⟩ := actual_mixed_denominator_expansions
  intro C hC hC'
  exact eventual_two_resonance_denominator U V eU eV hU hV hF heU heV he C hC hC'

#print axioms actual_mixed_denominator_expansions
#print axioms integer_power_log_gap
#print axioms eventual_two_resonance_denominator
#print axioms eventual_actual_mixed_denominator

end D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator
