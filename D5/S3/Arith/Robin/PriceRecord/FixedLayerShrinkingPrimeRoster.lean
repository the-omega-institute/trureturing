/- GID: D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster
   mirror-E: none(waiver:quantitative-prime-number-theorem)
   anchors: []
   utility: none
   digest: Logarithmically shrinking prime rosters at the actual fixed-layer roots. -/
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. Uses fixed N=6 quantitative PNT at both MOVING
endpoints. No fixed-relative-interval theorem is substituted for this result. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

theorem root_ratio {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun X : ℝ => cutoff j (referencePrice X) / X ^ ((j : ℝ)⁻¹))
      atTop (𝓝 ((j : ℝ) ^ ((j : ℝ)⁻¹))) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have h := ((fixed_layer_root_offset_tendsto hj).div_const (j : ℝ)).exp
  have hlim : exp (log (j : ℝ) / j) = (j : ℝ) ^ ((j : ℝ)⁻¹) := by
    rw [rpow_def_of_pos hj0]
    congr 1
  rw [← Real.exp_eq_exp_ℝ, hlim] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hLambda : 0 < referencePrice X := by
    dsimp [referencePrice]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))
  have hr := (cutoff_spec hj hLambda).1
  have he : ((j : ℝ) * log (cutoff j (referencePrice X)) - log X) / j =
      log (cutoff j (referencePrice X) / X ^ ((j : ℝ)⁻¹)) := by
    rw [log_div (by linarith : cutoff j (referencePrice X) ≠ 0)
      (rpow_pos_of_pos (by linarith : 0 < X) _).ne',
      log_rpow (by linarith : 0 < X)]
    field_simp <;> ring
  rw [he, exp_log (div_pos (by linarith) (rpow_pos_of_pos (by linarith) _))]

theorem root_atTop {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun X : ℝ => cutoff j (referencePrice X)) atTop atTop := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have h := (root_ratio hj).pos_mul_atTop (rpow_pos_of_pos hj0 _)
    (tendsto_rpow_atTop (inv_pos.mpr hj0))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact div_mul_cancel₀ _ (rpow_pos_of_pos hX _).ne'

theorem root_log_ratio {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun X : ℝ => log (cutoff j (referencePrice X)) / log X)
      atTop (𝓝 ((j : ℝ)⁻¹)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hz := (fixed_layer_root_offset_tendsto hj).div_atTop tendsto_log_atTop
  have h := (hz.add_const 1).div_const (j : ℝ)
  simp only [zero_add, one_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  field_simp [(log_pos hX).ne', hj0.ne'] <;> ring

/- A fixed w+2 powers of log pay w powers in the actual moving window width. This lemma includes the moving-clock conversion. -/
private theorem moving_theta_error (w : ℕ) {y : ℝ → ℝ} {c : ℝ}
    (hy : Tendsto y atTop atTop) (hc : 0 < c)
    (hlog : Tendsto (fun X : ℝ => log (y X) / log X) atTop (𝓝 c)) :
    Tendsto (fun X : ℝ => (Chebyshev.theta (y X) - y X) /
      (y X / log X ^ w)) atTop (𝓝 0) := by
  have hpnt := (theta_error_log_power (w + 2)).tendsto_div_nhds_zero.comp hy
  have hratio := hlog.inv₀ hc.ne'
  have hratio' : Tendsto (fun X : ℝ => log X / log (y X)) atTop (𝓝 c⁻¹) := by
    simpa only [inv_div] using hratio
  have hlast : Tendsto (fun X : ℝ => 1 / log (y X) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
      (tendsto_log_atTop.comp hy))
  have h := (hpnt.mul (hratio'.pow w)).mul hlast
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hy.eventually_gt_atTop 1] with X hX hyX
  dsimp only [Function.comp_def, Pi.mul_apply, Pi.div_apply]
  simp only [pow_add, div_pow]
  field_simp [(log_pos hX).ne', (log_pos hyX).ne', (by linarith : y X ≠ 0)]
  <;> ring

private theorem theta_interval_sum {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    let S := Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊
    (∀ p ∈ S, p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ z) ∧
    Chebyshev.theta z - Chebyshev.theta y = ∑ p ∈ S, log p := by
  classical
  dsimp only
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    obtain ⟨hp, hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp.trans (Nat.floor_mono hyz), hprime⟩
  constructor
  · intro p hp
    obtain ⟨hpz, hpy⟩ := mem_sdiff.mp hp
    obtain ⟨hpz, hprime⟩ := Nat.mem_primesLE.mp hpz
    refine ⟨hprime, ?_, (Nat.le_floor_iff (hy.trans hyz)).mp hpz⟩
    by_contra! h
    exact hpy (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hy).mpr h, hprime⟩)
  · rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    have hs := sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ))
    linarith only [hs]

/-- A genuine shrinking-window supply at the actual root. The threshold is
before X, and card(S) exceeds any fixed multiple of a fixed power of log X. Each member is a distinct natural prime. -/
theorem fixed_layer_shrinking_prime_roster_power {j : ℕ} (hj : 2 ≤ j)
    (w d : ℕ) (hw : 0 < w) :
    ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ X : ℝ, T ≤ X →
      ∃ S : Finset ℕ,
        C * log X ^ d ≤ (S.card : ℝ) ∧
        (∀ p ∈ S, p.Prime ∧ cutoff j (referencePrice X) < (p : ℝ) ∧
          (p : ℝ) ≤ cutoff j (referencePrice X) * (1 + 1 / log X ^ w)) ∧
        cutoff j (referencePrice X) / (2 * log X ^ w) ≤
          ∑ p ∈ S, log p := by
  intro C hC
  classical
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  let y := fun X : ℝ => cutoff j (referencePrice X)
  let κ := fun X : ℝ => 1 / log X ^ w
  let z := fun X : ℝ => y X * (1 + κ X)
  have hy : Tendsto y atTop atTop := root_atTop hj
  have hk : Tendsto κ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega : w ≠ 0)).comp tendsto_log_atTop)
  have hz : Tendsto z atTop atTop := by
    exact hy.atTop_mul_pos (by norm_num : (0 : ℝ) < 1)
      (by simpa only [add_zero] using (tendsto_const_nhds.add hk))
  have hlogy : Tendsto (fun X : ℝ => log (y X) / log X) atTop (𝓝 ((j : ℝ)⁻¹)) :=
    root_log_ratio hj
  have hlogz : Tendsto (fun X : ℝ => log (z X) / log X) atTop (𝓝 ((j : ℝ)⁻¹)) := by
    have hh := ((tendsto_const_nhds.add hk).log (by norm_num : (1 : ℝ) + 0 ≠ 0)).div_atTop
      tendsto_log_atTop
    have h := hlogy.add hh
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hy.eventually_gt_atTop 0] with X hX hyX
    have hLX : 0 < log X := log_pos hX
    dsimp [z]
    rw [log_mul hyX.ne' (by dsimp [κ]; positivity), add_div]
  have hey := moving_theta_error w hy (inv_pos.mpr hj0) hlogy
  have hez := moving_theta_error w hz (inv_pos.mpr hj0) hlogz
  have hzy : Tendsto (fun X : ℝ => z X / y X) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hk
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [hy.eventually_gt_atTop 0] with X hX
    dsimp [z]
    field_simp <;> ring
  have hmass : Tendsto (fun X : ℝ => (Chebyshev.theta (z X) - Chebyshev.theta (y X)) /
      (y X / log X ^ w)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add (hez.mul hzy)).sub hey
    simp only [zero_mul, add_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hy.eventually_gt_atTop 0,
      hz.eventually_gt_atTop 0] with X hX hyX hzX
    have hwidth : (z X - y X) * log X ^ w = y X := by
      dsimp [z, κ]
      field_simp [(log_pos hX).ne'] <;> ring
    have hcancel :
        (Chebyshev.theta (z X) - z X) / (z X / log X ^ w) * (z X / y X) =
          (Chebyshev.theta (z X) - z X) / (y X / log X ^ w) := by
      rw [div_div_eq_mul_div, div_mul_div_cancel₀ hzX.ne', div_div_eq_mul_div]
    have hone : (1 : ℝ) = (z X - y X) / (y X / log X ^ w) := by
      rw [div_div_eq_mul_div, hwidth, div_self hyX.ne']
    rw [hcancel, hone, ← add_div, ← sub_div]
    congr 1 <;> ring
  have hsmall : Tendsto (fun X : ℝ => log X ^ (w + d + 1) / y X) atTop (𝓝 0) := by
    have hl := (isLittleO_log_rpow_rpow_atTop (w + d + 1 : ℕ)
      (inv_pos.mpr hj0)).tendsto_div_nhds_zero
    simp only [rpow_natCast] at hl
    have h := hl.div (root_ratio hj) (rpow_pos_of_pos hj0 _).ne'
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hy.eventually_gt_atTop 0] with X hX hyX
    dsimp only [Pi.div_apply, y]
    field_simp [(rpow_pos_of_pos hX ((j : ℝ)⁻¹)).ne', hyX.ne'] <;> ring
  have hclt : (j : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hj0]
    linarith
  have hevent : ∀ᶠ X : ℝ in atTop,
      1 < X ∧ 0 < y X ∧ 0 < z X ∧ log (z X) < log X ∧
      1 / 2 ≤ (Chebyshev.theta (z X) - Chebyshev.theta (y X)) / (y X / log X ^ w) ∧
      log X ^ (w + d + 1) / y X < 1 / (2 * C) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hy.eventually_gt_atTop 0,
      hz.eventually_gt_atTop 0,
      hlogz.eventually (eventually_lt_nhds hclt),
      hmass.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hsmall.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (2 * C)))]
      with X hX hyX hzX hlog hm hs
    refine ⟨hX, hyX, hzX, ?_, hm.le, hs⟩
    have hh := (div_lt_iff₀ (log_pos hX)).mp hlog
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hXT
  obtain ⟨hX, hyX, hzX, hlog, hm, hs⟩ := hT X ((le_max_left T 2).trans hXT)
  have hL : 0 < log X := log_pos hX
  have hyz : y X ≤ z X := by
    dsimp [z, κ]
    nlinarith [mul_nonneg hyX.le (show (0 : ℝ) ≤ 1 / log X ^ w by positivity)]
  let S := Nat.primesLE ⌊z X⌋₊ \ Nat.primesLE ⌊y X⌋₊
  obtain ⟨hS, hsum⟩ := theta_interval_sum hyX.le hyz
  have hmasslower : y X / (2 * log X ^ w) ≤ ∑ p ∈ S, log p := by
    have hh := (le_div_iff₀ (by positivity : 0 < y X / log X ^ w)).mp hm
    rw [hsum] at hh
    change _ ≤ _ at hh
    convert hh using 1 <;> ring
  have hupper : (∑ p ∈ S, log p) ≤ (S.card : ℝ) * log X := by
    calc
      _ ≤ ∑ _p ∈ S, log X := by
        apply sum_le_sum
        intro p hp
        exact (log_le_log (by exact_mod_cast (hS p hp).1.pos) (hS p hp).2.2).trans hlog.le
      _ = _ := by simp
  have hlarge : C * log X ^ (d + 1) < y X / (2 * log X ^ w) := by
    have hineq : 2 * C * log X ^ (w + d + 1) < y X := by
      have hh := (div_lt_div_iff₀ hyX (by positivity : 0 < 2 * C)).mp hs
      nlinarith only [hh]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * log X ^ w)).mpr
    simpa only [pow_add, pow_one, mul_assoc, mul_left_comm, mul_comm] using hineq
  refine ⟨S, ?_, ?_, hmasslower⟩
  · have hh : C * log X ^ (d + 1) < (S.card : ℝ) * log X := hlarge.trans_le (hmasslower.trans hupper)
    apply le_of_mul_le_mul_right ?_ hL
    simpa only [pow_succ, mul_assoc] using hh.le
  · exact hS

#print axioms fixed_layer_shrinking_prime_roster_power
end D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
