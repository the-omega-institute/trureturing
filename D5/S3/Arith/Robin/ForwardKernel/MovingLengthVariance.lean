/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform band variance controls comparable lengths and all shorter increments. -/

import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
import D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance

/-! Uniform variance estimates at comparable lengths and below a fixed comparison length. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer

noncomputable section

variable {E : ℝ → ℝ} {α θ β : ℝ}

/-- One threshold controls the cumulative variance at every comparable length. -/
theorem comparable_length_variance_bound (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β) (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {A B d : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (A * X ^ θ) (B * X ^ θ),
        cumulativeVariance E (d * X) u ≤ C * X * X ^ θ * Real.log X := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hBpos : 0 < B := hA.trans_le hAB
  have hY : Tendsto (fun X : ℝ => d * X) atTop atTop :=
    tendsto_id.const_mul_atTop hd
  have hlo := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ
    (c := A) (d := d) (q := 1) (r := 0) hA hd zero_lt_one le_rfl
  have hhi := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ
    (c := B) (d := d) (q := 1) (r := 0) (hA.trans_le hAB) hd zero_lt_one le_rfl
  refine ⟨2 * d * B * (1 + |Real.log d|), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hY.eventually (eventually_gt_atTop (1 : ℝ)), hlo, hhi,
    hY.eventually (hV 1 zero_lt_one)] with X hX hY1 hlo hhi hV'
  simp only [fixedLength, one_mul, zero_mul, add_zero] at hlo hhi
  intro u hu
  have hX0 : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hband : (d * X) ^ α ≤ u ∧ u ≤ (d * X) ^ β :=
    ⟨hlo.1.trans hu.1, hu.2.trans hhi.2⟩
  have hu1 : 1 ≤ u :=
    (Real.one_le_rpow hY1.le hB.1.le).trans hband.1
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have huY : u < d * X := by
    calc
      u ≤ (d * X) ^ β := hband.2
      _ < (d * X) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hY1 hB.2.2.2
      _ = _ := Real.rpow_one _
  have hlogpos : 0 < Real.log (d * X / u) :=
    Real.log_pos ((one_lt_div hu0).mpr huY)
  have hlog : Real.log (d * X / u) ≤ (1 + |Real.log d|) * Real.log X := by
    calc
      _ ≤ Real.log (d * X) := Real.log_le_log (by positivity)
        (div_le_self (by positivity) hu1)
      _ = Real.log d + Real.log X := Real.log_mul hd.ne' hX0.ne'
      _ ≤ _ := by nlinarith [le_abs_self (Real.log d), abs_nonneg (Real.log d)]
  have hv := (abs_sub_le_iff.mp (hV' u hband.1 hband.2)).1
  have hv' : cumulativeVariance E (d * X) u ≤
      2 * ((d * X) * u * Real.log (d * X / u)) := by
    apply (div_le_iff₀ (by positivity : 0 < (d * X) * u * Real.log (d * X / u))).mp
    linarith
  calc
    _ ≤ 2 * ((d * X) * u * Real.log (d * X / u)) := hv'
    _ ≤ 2 * ((d * X) * (B * X ^ θ) * ((1 + |Real.log d|) * Real.log X)) := by
      gcongr
      exact hu.2
    _ = _ := by ring

/-- Every shorter increment has a square integral bounded at the comparison-length scale. -/
theorem shorter_increment_square_bound (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β) (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (0 : ℝ) (fixedLength θ c X),
        (∫ x in X..(2 * X), increment E u x ^ 2) ≤
          C * X * fixedLength θ c X * lengthLog θ c X := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨K, hK, hKv⟩ := comparable_length_variance_bound hE hB hV
    (A := c) (B := 3 * c) (d := 3) hc (by linarith) (by norm_num)
  have hband := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ
    (c := c) (d := 1) (q := 1) (r := 0) hc zero_lt_one zero_lt_one le_rfl
  refine ⟨12 * K / (c * (1 - θ)), by positivity, ?_⟩
  filter_upwards [hKv, hband, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * Real.log c / (1 - θ)))]
    with X hKv hband hX hlog
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hh : 0 < fixedLength θ c X := by unfold fixedLength; positivity
  have hhX : fixedLength θ c X ≤ X := by
    simp only [one_mul, zero_mul, add_zero] at hband
    exact hband.2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX hB.2.2.2.le)
  have hell : (1 - θ) / 2 * Real.log X ≤ lengthLog θ c X := by
    rw [lengthLog, Real.log_div hX0.ne' hh.ne', fixedLength,
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0]
    have := (div_le_iff₀ (sub_pos.mpr hθ)).mp hlog
    linarith
  intro u hu
  have hb := MovingEndpointVariance.two_endpoint_increment_square_le
    (p := fun x => x) (q := fun x => x + u)
    (p' := fun _ => 1) (q' := fun _ => 1)
    (l := X) (r := 2 * X) (Y := 3 * X) (R := fixedLength θ c X) (C₀ := 1) (m := 1)
    (K := K * X * X ^ θ * Real.log X)
    hE (by linarith) hh (by norm_num) zero_lt_one
    (by positivity [Real.log_nonneg hX])
    continuous_id.continuousOn (continuous_id.add continuous_const).continuousOn
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
    (fun x _ => ((hasDerivAt_id x).add_const u).hasDerivWithinAt)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (by
      intro x hx
      exact ⟨⟨hX.trans hx.1, by linarith [hx.2]⟩,
        ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hu.2]⟩⟩)
    (by intro x _; simpa only [add_sub_cancel_left, one_mul] using hu)
    (by
      intro v hv
      apply hKv v
      dsimp [fixedLength] at *
      constructor <;> nlinarith [hv.1, hv.2])
  have hb' : (∫ x in X..(2 * X), increment E u x ^ 2) ≤
      6 * K * X * X ^ θ * Real.log X := by
    simpa only [increment, show (2 * (1 + 2) / 1 : ℝ) = 6 by norm_num,
      mul_assoc] using hb
  calc
    _ ≤ 6 * K * X * X ^ θ * Real.log X := hb'
    _ ≤ _ := by
      have hscale := mul_le_mul_of_nonneg_left hell
        (show 0 ≤ 12 * K * X * X ^ θ / (1 - θ) by positivity)
      dsimp [fixedLength]
      field_simp at hscale ⊢
      nlinarith

private lemma band_range_variance_bound_of_constants
    {E : ℝ → ℝ} {α a b β d L U : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α a β) (hab : a < b) (hbβ : b < β)
    (hd : 0 < d) (hL : 0 < L) (hU : 0 < U)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (L * X ^ a) (U * X ^ b),
        cumulativeVariance E (d * X) u ≤ C * X * u * Real.log X := by
  have hαa : α < a := hBa.2.1
  have haβ : a < β := hBa.2.2.1
  have hβ1 : β < 1 := hBa.2.2.2
  have hY : Tendsto (fun X : ℝ => d * X) atTop atTop :=
    tendsto_id.const_mul_atTop hd
  have hlo : Tendsto (fun X : ℝ => (d * X) ^ α / (L * X ^ a)) atTop (𝓝 0) := by
    have hp : Tendsto (fun X : ℝ => X ^ (α - a)) atTop (𝓝 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hαa)
    have hc : Tendsto (fun _ : ℝ => d ^ α / L) atTop (𝓝 (d ^ α / L)) :=
      tendsto_const_nhds
    have h := hc.mul hp
    simpa only [mul_zero] using h.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      rw [Real.mul_rpow (le_of_lt hd) hX.le, Real.rpow_sub hX]
      field_simp
      )
  have hhi : Tendsto (fun X : ℝ => (U * X ^ b) / (d * X) ^ β) atTop (𝓝 0) := by
    have hp : Tendsto (fun X : ℝ => X ^ (b - β)) atTop (𝓝 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hbβ)
    have hc : Tendsto (fun _ : ℝ => U / d ^ β) atTop (𝓝 (U / d ^ β)) :=
      tendsto_const_nhds
    have h := hc.mul hp
    simpa only [mul_zero] using h.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      rw [Real.mul_rpow (le_of_lt hd) hX.le]
      field_simp
      rw [← Real.rpow_add hX]
      ring)
  refine ⟨2 * d * (1 + |Real.log d|), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hY.eventually (eventually_gt_atTop (1 : ℝ)),
    hlo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hhi.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hY.eventually (hV 1 zero_lt_one)] with X hX hY1 hlo hhi hV'
  have hX0 : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  intro u hu
  have hband : (d * X) ^ α ≤ u ∧ u ≤ (d * X) ^ β := by
    constructor
    · have hlow : (d * X) ^ α ≤ L * X ^ a := by
        exact (div_le_one (by positivity)).mp hlo.le
      exact hlow.trans hu.1
    · have hhigh : U * X ^ b ≤ (d * X) ^ β := by
        exact (div_le_one (by positivity)).mp hhi.le
      exact hu.2.trans hhigh
  have hu1 : 1 ≤ u := by
    exact (Real.one_le_rpow hY1.le hBa.1.le).trans hband.1
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have huY : u < d * X := by
    calc
      u ≤ (d * X) ^ β := hband.2
      _ < (d * X) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hY1 hβ1
      _ = _ := Real.rpow_one _
  have hlogpos : 0 < Real.log (d * X / u) :=
    Real.log_pos ((one_lt_div hu0).mpr huY)
  have hlog : Real.log (d * X / u) ≤ (1 + |Real.log d|) * Real.log X := by
    calc
      _ ≤ Real.log (d * X) := Real.log_le_log (by positivity)
        (div_le_self (by positivity) hu1)
      _ = Real.log d + Real.log X := Real.log_mul hd.ne' hX0.ne'
      _ ≤ _ := by nlinarith [le_abs_self (Real.log d), abs_nonneg (Real.log d)]
  have hv := (abs_sub_le_iff.mp (hV' u hband.1 hband.2)).1
  have hv' : cumulativeVariance E (d * X) u ≤
      2 * ((d * X) * u * Real.log (d * X / u)) := by
    apply (div_le_iff₀ (by positivity : 0 < (d * X) * u * Real.log (d * X / u))).mp
    linarith
  calc
    _ ≤ 2 * ((d * X) * u * Real.log (d * X / u)) := hv'
    _ ≤ 2 * ((d * X) * u * ((1 + |Real.log d|) * Real.log X)) := by
      gcongr
    _ = 2 * d * (1 + |Real.log d|) * X * u * Real.log X := by ring

theorem band_range_variance_bound
    {E : ℝ → ℝ} {α a b β d : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β) (hd : 0 < d)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (X ^ a) (8 * X ^ b),
        cumulativeVariance E (d * X) u ≤ C * X * u * Real.log X := by
  simpa only [one_mul] using
    (band_range_variance_bound_of_constants hE hBa hab hbβ hd
      (L := 1) (U := 8) (by norm_num) (by norm_num) hV)

theorem band_increment_square_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (0 : ℝ) (8 * X ^ b),
        (∫ x in (X / 2)..(4 * X), increment E u x ^ 2) ≤
          C * X * max u (X ^ a) * Real.log X := by
  obtain ⟨K, hK, hKv⟩ := band_range_variance_bound_of_constants hE hBa hab hbβ
    (d := 16) (L := (1 / 2 : ℝ)) (U := 16) (by norm_num) (by norm_num) (by norm_num) hV
  refine ⟨18 * K, by positivity, ?_⟩
  filter_upwards [hKv, eventually_ge_atTop (2 : ℝ)] with X hKv hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hXa : 0 < X ^ a := Real.rpow_pos_of_pos hX0 _
  have hXb : 0 < X ^ b := Real.rpow_pos_of_pos hX0 _
  have hpow_a : X ^ a ≤ X ^ b := by
    exact Real.rpow_le_rpow_of_exponent_le hX1 hab.le
  have hpow_b : X ^ b ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX1 (hbβ.trans hBa.2.2.2).le
  intro u hu
  have hbase : ∀ x ∈ Icc (X / 2) (4 * X),
      x ∈ Icc (1 : ℝ) (16 * X) ∧ x + u ∈ Icc (1 : ℝ) (16 * X) := by
    intro x hx
    constructor
    · constructor <;> linarith [hx.1, hx.2, hX]
    · constructor
      · linarith [hx.1, hu.1]
      · nlinarith [hx.2, hu.2, hpow_b]
  by_cases hsmall : u ≤ X ^ a
  · have hR : 0 < X ^ a := hXa
    have hb := MovingEndpointVariance.two_endpoint_increment_square_le
      (p := fun x => x) (q := fun x => x + u)
      (p' := fun _ => 1) (q' := fun _ => 1)
      (l := X / 2) (r := 4 * X) (Y := 16 * X) (R := X ^ a) (C₀ := 1) (m := 1)
      (K := 3 * K * X * X ^ a * Real.log X)
      hE (by linarith) hR (by norm_num) zero_lt_one
      (by positivity [hK.le, hX0, hlog])
      continuous_id.continuousOn (continuous_id.add continuous_const).continuousOn
      (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
      (fun x _ => ((hasDerivAt_id x).add_const u).hasDerivWithinAt)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) hbase
      (by
        intro x hx
        exact ⟨by linarith [hu.1], by simpa only [add_sub_cancel_left, one_mul] using hsmall⟩)
      (by
        intro v hv
        have hv' := hKv v ⟨by nlinarith [hv.1, hXa], by nlinarith [hv.2, hpow_a]⟩
        calc
          _ ≤ K * X * v * Real.log X := hv'
          _ ≤ 3 * K * X * X ^ a * Real.log X := by
            have hfac : 0 ≤ K * X * Real.log X := by positivity
            have hvle : v ≤ 3 * X ^ a := by nlinarith [hv.2]
            calc
              K * X * v * Real.log X = (K * X * Real.log X) * v := by ring
              _ ≤ (K * X * Real.log X) * (3 * X ^ a) :=
                mul_le_mul_of_nonneg_left hvle hfac
              _ = 3 * K * X * X ^ a * Real.log X := by ring)
    have hb' : (∫ x in (X / 2)..(4 * X), increment E u x ^ 2) ≤
        18 * K * X * X ^ a * Real.log X := by
      have hI : (∫ x in (X / 2)..(4 * X), increment E u x ^ 2) =
          ∫ x in (X / 2)..(4 * X), (E (x + u) - E x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rfl
      rw [hI]
      calc
        _ ≤ 2 * (1 + 2) / 1 * (3 * K * X * X ^ a * Real.log X) := hb
        _ = _ := by ring
    rw [max_eq_right hsmall]
    exact hb'
  · have hlarge : X ^ a ≤ u := le_of_lt (lt_of_not_ge hsmall)
    have hR : 0 < u / 2 := div_pos (hXa.trans_le hlarge) (by norm_num)
    have hb := MovingEndpointVariance.two_endpoint_increment_square_le
      (p := fun x => x) (q := fun x => x + u)
      (p' := fun _ => 1) (q' := fun _ => 1)
      (l := X / 2) (r := 4 * X) (Y := 16 * X) (R := u / 2) (C₀ := 2) (m := 1)
      (K := 2 * K * X * u * Real.log X)
      hE (by linarith) hR (by norm_num) zero_lt_one
      (by positivity [hK.le, hX0, hu.1, hlog])
      continuous_id.continuousOn (continuous_id.add continuous_const).continuousOn
      (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
      (fun x _ => ((hasDerivAt_id x).add_const u).hasDerivWithinAt)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) hbase
      (by
        intro x hx
        have hhalf : 2 * (u / 2) = u := by ring
        exact ⟨by linarith [hu.1], by
          rw [show x + u - x = u by ring, hhalf]
          ⟩)
      (by
        intro v hv
        have hv' := hKv v ⟨by nlinarith [hlarge, hv.1], by nlinarith [hv.2, hu.2]⟩
        calc
          _ ≤ K * X * v * Real.log X := hv'
          _ ≤ 2 * K * X * u * Real.log X := by
            have hfac : 0 ≤ K * X * Real.log X := by positivity
            have hvle : v ≤ 2 * u := by nlinarith [hv.2]
            calc
              K * X * v * Real.log X = (K * X * Real.log X) * v := by ring
              _ ≤ (K * X * Real.log X) * (2 * u) :=
                mul_le_mul_of_nonneg_left hvle hfac
              _ = 2 * K * X * u * Real.log X := by ring)
    have hb' : (∫ x in (X / 2)..(4 * X), increment E u x ^ 2) ≤
        16 * K * X * u * Real.log X := by
      have hI : (∫ x in (X / 2)..(4 * X), increment E u x ^ 2) =
          ∫ x in (X / 2)..(4 * X), (E (x + u) - E x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rfl
      rw [hI]
      calc
        _ ≤ 2 * (2 + 2) / 1 * (2 * K * X * u * Real.log X) := hb
        _ = _ := by ring
    rw [max_eq_left hlarge]
    have hu0 : 0 ≤ u := hu.1
    have hfac : 0 ≤ K * X * u * Real.log X := by positivity
    exact hb'.trans (by nlinarith [hfac])

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
