/- GID: D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CommonBandSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed signed sparse perturbation preserves variance and forces near-optimal cross energy. -/

import D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpnessTransport
import D5.S3.Arith.Robin.ForwardKernel.SparseLogSpikeBounds
import D5.S3.Arith.Robin.ForwardKernel.VariancePerturbation
import Mathlib.Order.Filter.Finite

/-! Quadratic response identities and fixed-sign common-band sharpness. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open VarianceTransferDefs ProfileKernelDefs
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The three perturbation signs. -/
def signChoices : Finset ℝ := {-1, 0, 1}

private lemma lbm_affine {E F : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hF : LocallyBoundedMeasurable F) (t : ℝ) :
    LocallyBoundedMeasurable (fun x => E x + t * F x) := by
  refine ⟨hE.1.add (hF.1.const_mul t), fun a b => ?_⟩
  obtain ⟨M, hM, hm⟩ := hE.2 a b
  obtain ⟨N, hN, hn⟩ := hF.2 a b
  refine ⟨M + |t| * N, by positivity, fun x hx => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hm x hx)
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hn x hx) (abs_nonneg t)))

/-- The actual price-weighted profile response is linear in its error function. -/
theorem profileResponse_affine {E F g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hF : LocallyBoundedMeasurable F)
    (hg : ProfileIntegrable g) (θ t : ℝ) {x : ℝ} (hx : 3 ≤ x) :
    profileResponse (fun y => E y + t * F y) θ g x =
      profileResponse E θ g x + t * profileResponse F θ g x := by
  have hx0 : 0 < x := by linarith
  have hq := Real.rpow_pos_of_pos hx0 θ
  have hi (H : ℝ → ℝ) (hH : LocallyBoundedMeasurable H) :
      Integrable (fun s => g s * increment H (s * x ^ θ) x * priceRatio x (s * x ^ θ))
        unitMeasure := by
    have hm : Measurable (fun s => priceRatio x (s * x ^ θ)) :=
      WeightRemoval.price_measurable.comp
        (measurable_const.prodMk (measurable_id.mul_const _))
    apply (VarianceTransfer.unit_increment_integrable hH hg.2 (x ^ θ) x).mul_bdd
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    obtain ⟨h0, h1⟩ := WeightControl.price_bounds hx (mul_nonneg hs.1.le hq.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  apply (div_left_inj' (Real.sqrt_pos.mpr hx0).ne').mp
  rw [WeightRemoval.normalized_eq hx0, add_div, mul_div_assoc,
    WeightRemoval.normalized_eq hx0, WeightRemoval.normalized_eq hx0]
  have he : (fun s => g s * increment (fun y => E y + t * F y) (s * x ^ θ) x *
      priceRatio x (s * x ^ θ)) =
      (fun s => g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ) +
        t * (g s * increment F (s * x ^ θ) x * priceRatio x (s * x ^ θ))) := by
    funext s; dsimp [increment]; ring
  rw [he, integral_add (hi E hE) ((hi F hF).const_mul t), integral_const_mul]
  ring

/-- The cross energy expands as a quadratic polynomial; both mixed terms
occur separately, with no symmetry assumption. -/
theorem profileCross_affine {E F : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hF : LocallyBoundedMeasurable F)
    (a b t : ℝ) {X : ℝ} (hX : 3 ≤ X) :
    profileCross (fun x => E x + t * F x) a b X =
      profileCross E a b X +
        t * ((∫ x in X..(2 * X),
            profileResponse E a (fun _ => 1) x * profileResponse F b (fun _ => 1) x / x) +
          (∫ x in X..(2 * X),
            profileResponse F a (fun _ => 1) x * profileResponse E b (fun _ => 1) x / x)) +
        t ^ 2 * profileCross F a b X := by
  have hg : ProfileIntegrable (fun _ : ℝ => (1 : ℝ)) :=
    ⟨measurable_const, integrable_const _⟩
  have hiEE := profileCross_integrable hE hE a b hX (by linarith : X ≤ 2 * X)
  have hiEF := profileCross_integrable hE hF a b hX (by linarith : X ≤ 2 * X)
  have hiFE := profileCross_integrable hF hE a b hX (by linarith : X ≤ 2 * X)
  have hiFF := profileCross_integrable hF hF a b hX (by linarith : X ≤ 2 * X)
  unfold profileCross
  calc
    _ = ∫ x in X..(2 * X),
        profileResponse E a (fun _ => 1) x * profileResponse E b (fun _ => 1) x / x +
          t * (profileResponse E a (fun _ => 1) x * profileResponse F b (fun _ => 1) x / x +
            profileResponse F a (fun _ => 1) x * profileResponse E b (fun _ => 1) x / x) +
          t ^ 2 * (profileResponse F a (fun _ => 1) x * profileResponse F b (fun _ => 1) x / x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
      dsimp only
      rw [profileResponse_affine hE hF hg a t (hX.trans hx.1),
        profileResponse_affine hE hF hg b t (hX.trans hx.1)]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hiEE.add ((hiEF.add hiFE).const_mul t))
          (hiFF.const_mul (t ^ 2)),
        intervalIntegral.integral_add hiEE ((hiEF.add hiFE).const_mul t),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hiEF hiFE]

/-- The sum of the plus and minus cross energies eliminates both mixed terms. -/
theorem profileCross_quadratic_identity {E F : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hF : LocallyBoundedMeasurable F)
    (a b : ℝ) {X : ℝ} (hX : 3 ≤ X) :
    profileCross (fun x => E x + F x) a b X +
        profileCross (fun x => E x - F x) a b X - 2 * profileCross E a b X =
      2 * profileCross F a b X := by
  have hp := profileCross_affine hE hF a b 1 hX
  have hm := profileCross_affine hE hF a b (-1) hX
  simp only [one_mul, one_pow, neg_one_mul, neg_one_sq, ← sub_eq_add_neg] at hp hm
  linarith

/-- A single sign works on a frequent set of centers independently of any
later lower-bound constant. -/
theorem profileCross_fixed_sign {E F : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hF : LocallyBoundedMeasurable F) (a b : ℝ) :
    ∃ ε ∈ signChoices, ∃ᶠ n : ℕ in atTop,
      |profileCross F a b (center n)| / 2 ≤
        |profileCross (fun x => E x + ε * F x) a b (center n)| := by
  apply (Filter.frequently_exists_finset signChoices).mp
  apply Filter.Eventually.frequently
  filter_upwards [center_tendsto.eventually (eventually_ge_atTop (3 : ℝ))] with n hn
  have H := profileCross_quadratic_identity hE hF a b hn
  by_contra! hc
  have hp := hc 1 (by simp [signChoices])
  have hm := hc (-1) (by simp [signChoices])
  have hz := hc 0 (by simp [signChoices])
  simp only [one_mul, zero_mul, add_zero, neg_one_mul, ← sub_eq_add_neg] at hp hm hz
  have Habs : |2 * profileCross F a b (center n)| ≤
      |profileCross (fun x => E x + F x) a b (center n)| +
        |profileCross (fun x => E x - F x) a b (center n)| +
        2 * |profileCross E a b (center n)| := by
    rw [← H]
    exact (abs_sub _ _).trans (by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_add_le (profileCross (fun x => E x + F x) a b (center n))
        (profileCross (fun x => E x - F x) a b (center n))])
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at Habs
  linarith

/-- Sparse cusp perturbations preserve a von Koch pointwise bound. -/
theorem vonKoch_affine_spikes {E₀ : ℝ → ℝ} {a b : ℝ} {n₀ : ℕ}
    (hab : a < b) (hs : AdmissibleStart b n₀)
    (hVK : WeightRemoval.VonKochBoundFor E₀) (t : ℝ) :
    WeightRemoval.VonKochBoundFor (fun x => E₀ x + t * perturbation a b n₀ x) := by
  obtain ⟨C, hF⟩ := (perturbation_pointwise_bound hab hs).bound
  obtain ⟨C₀, T₀, hC₀, hT₀, hE⟩ := hVK
  have hbound : ∀ᶠ x : ℝ in atTop,
      |perturbation a b n₀ x| ≤ |C| * Real.sqrt x * (Real.log x) ^ 2 := by
    filter_upwards [hF, eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx hlarge
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hlarge
    have hlog : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hlarge
    have hlog₁ : 1 ≤ Real.log x := (Real.add_one_le_exp 1 |>.trans' (by norm_num)).trans hlog
    have hll : 1 ≤ Real.log (Real.log x) :=
      (Real.le_log_iff_exp_le (by linarith : 0 < Real.log x)).2 hlog
    have hden : 1 ≤ Real.sqrt (Real.log (Real.log x)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hll
    have hscale : 0 ≤ spikePointScale x := by unfold spikePointScale; positivity
    have hp : spikePointScale x ≤ Real.sqrt x * (Real.log x) ^ 2 := by
      unfold spikePointScale
      apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (Real.log (Real.log x)))).2
      have hpow : (Real.log x) ^ (3 / 2 : ℝ) ≤ (Real.log x) ^ 2 := by
        convert Real.rpow_le_rpow_of_exponent_le hlog₁ (by norm_num : (3 / 2 : ℝ) ≤ 2) using 1
        norm_cast
      exact (mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg x)).trans
        (le_mul_of_one_le_right (by positivity) hden)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale] at hx
    exact hx.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) hscale).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (abs_nonneg C)))
  obtain ⟨T, hT⟩ := eventually_atTop.1 hbound
  refine ⟨C₀ + |t| * |C|, max T₀ T, by positivity, le_max_of_le_left hT₀, ?_⟩
  intro x hx
  have hEx := hE x ((le_max_left _ _).trans hx)
  have hFx := hT x ((le_max_right _ _).trans hx)
  calc
    _ ≤ |E₀ x| + |t| * |perturbation a b n₀ x| := by simpa only [abs_mul] using abs_add_le (E₀ x) (t * perturbation a b n₀ x)
    _ ≤ _ := add_le_add hEx (mul_le_mul_of_nonneg_left hFx (abs_nonneg t))
    _ = _ := by ring

private lemma reducedLogScale_div_nearOptScale {b η : ℝ} (hη : 0 < η) :
    Tendsto (fun X : ℝ => reducedLogScale b η X / nearOptScale b X)
      atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_atTop hη).tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop
  apply H.congr'
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with X hX
  have hx : 0 < X := (Real.exp_pos 1).trans hX
  have hl₁ : 1 < Real.log X := (Real.lt_log_iff_exp_lt hx).2 hX
  have hl : 0 < Real.log X := by linarith
  have hll := Real.log_pos hl₁
  have hp : (Real.log X) ^ (3 - η) = (Real.log X) ^ 3 / (Real.log X) ^ η := by
    rw [Real.rpow_sub hl]
    norm_cast
  dsimp [Function.comp_def, reducedLogScale, nearOptScale]
  rw [hp]
  have hZ := (Real.rpow_pos_of_pos hx (1 - b)).ne'
  have hQ := (Real.rpow_pos_of_pos hl η).ne'
  generalize X ^ (1 - b) = Z at *
  field_simp [hl.ne', hll.ne', hZ, hQ]

/-- A fixed signed perturbation preserves the common variance band and forces
cross energy at the near-optimal scale for every smaller constant, excluding
every fixed positive saving in the logarithmic exponent. -/
theorem common_band_near_optimality
    {E₀ : ℝ → ℝ} {α a b β : ℝ}
    (hE₀ : LocallyBoundedMeasurable E₀)
    (hBa : ValidBand α a β) (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E₀ α β) :
    ∃ n₀ : ℕ, AdmissibleStart b n₀ ∧ ∃ ε ∈ signChoices,
      let E := fun x => E₀ x + ε * perturbation a b n₀ x
      LocallyBoundedMeasurable E ∧
      CumulativeVarianceBandAsymptoticFor E α β ∧
      (∀ c : ℝ, c < (b - a) ^ 2 / 8 →
        ∃ᶠ X : ℝ in atTop, c * nearOptScale b X ≤ |profileCross E a b X|) ∧
      (∀ η : ℝ, 0 < η →
        ¬ Asymptotics.IsBigO atTop (profileCross E a b) (reducedLogScale b η)) ∧
      (WeightRemoval.VonKochBoundFor E₀ → WeightRemoval.VonKochBoundFor E) := by
  have ha := hBa.1.trans hBa.2.1
  have hb := hbβ.trans hBa.2.2.2
  obtain ⟨n₀, hs⟩ := exists_admissibleStart hb
  refine ⟨n₀, hs, ?_⟩
  have hF := perturbation_locallyBoundedMeasurable (a := a) hs
  obtain ⟨ε, hε, hfreq⟩ := profileCross_fixed_sign hE₀ hF a b
  let E := fun x => E₀ x + ε * perturbation a b n₀ x
  have hlower : ∀ c : ℝ, c < (b - a) ^ 2 / 8 →
      ∃ᶠ X : ℝ in atTop, c * nearOptScale b X ≤ |profileCross E a b X| := by
    intro c hc
    have hlim := profileCross_spike_asymptotic ha hab hb hs
    have hlim' := hlim.eventually (eventually_gt_nhds
      (by linarith : 2 * c < (b - a) ^ 2 / 4))
    apply center_tendsto.frequently
    apply (hfreq.and_eventually (hlim'.and
      (center_tendsto.eventually (eventually_gt_atTop (Real.exp 1))))).mono
    intro n hn
    obtain ⟨hfn, hcn, hX⟩ := hn
    have hx := center_pos n
    have hl₁ : 1 < Real.log (center n) := (Real.lt_log_iff_exp_lt hx).2 hX
    have hR : 0 < nearOptScale b (center n) := by
      unfold nearOptScale
      positivity [Real.log_pos hl₁]
    have hmain := (lt_div_iff₀ hR).1 hcn
    have habs := le_abs_self (profileCross (perturbation a b n₀) a b (center n))
    change _ ≤ |profileCross E a b (center n)| at hfn
    linarith
  refine ⟨ε, hε, lbm_affine hE₀ hF ε,
    band_asymptotic_affine hBa.1 (hBa.2.1.trans hBa.2.2.1) hBa.2.2.2 hE₀ hF hV
      (perturbation_band_negligible hBa hab hbβ hs) ε, hlower, ?_, ?_⟩
  · intro η hη hO
    obtain ⟨C, hC⟩ := hO.bound
    let c : ℝ := (b - a) ^ 2 / 16
    have hc0 : 0 < c := by dsimp [c]; positivity
    have hc : c < (b - a) ^ 2 / 8 := by dsimp [c]; nlinarith [sq_pos_of_pos (sub_pos.mpr hab)]
    have hratio := (reducedLogScale_div_nearOptScale (b := b) hη).const_mul C
    have hsmall := hratio.eventually (eventually_lt_nhds (by simpa using hc0))
    obtain ⟨X, hlow, hlarge, hCX, hsm⟩ :=
      ((hlower c hc).and_eventually
        ((eventually_gt_atTop (Real.exp 1)).and (hC.and hsmall))).exists
    have hx : 0 < X := (Real.exp_pos _).trans hlarge
    have hl₁ : 1 < Real.log X := (Real.lt_log_iff_exp_lt hx).2 hlarge
    have hl : 0 < Real.log X := by linarith
    have hR : 0 < nearOptScale b X := by unfold nearOptScale; positivity [Real.log_pos hl₁]
    have hS : 0 ≤ reducedLogScale b η X := by unfold reducedLogScale; positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS] at hCX
    have hsm' : C * reducedLogScale b η X < c * nearOptScale b X := by
      apply (div_lt_iff₀ hR).1
      simpa only [mul_div_assoc] using hsm
    linarith
  · intro hVK
    exact vonKoch_affine_spikes hab hs hVK ε

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
