/- GID: D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.claim; result=D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.result; claim=D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.claim
   digest: A two-block density refutes the general annealed Potts moment lower bound. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay

/-! The functions use Lebesgue integration against a density on the real line.
The standing curvature and uniqueness conditions are part of the claim. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation

open MeasureTheory Set Filter
open scoped Topology

/-- Moments with respect to a density on the real line. -/
def moment (f : ℝ → ℝ) (n : ℕ) : ℝ := ∫ w, w ^ n * f w

/-- The size-biased order parameter in Section 1, equation (1). -/
def F0 (f : ℝ → ℝ) (q t : ℝ) : ℝ :=
  (∫ w, w * ((Real.exp (t * w) - 1) / (Real.exp (t * w) + q - 1)) * f w) /
    moment f 1

/-- The criticality function in Section 1, equation (6). -/
def K (f : ℝ → ℝ) (q t : ℝ) : ℝ :=
  (∫ w, Real.log ((Real.exp (t * w) + q - 1) / q) * f w) / moment f 1 -
    (q - 1) / (2 * q) * t * F0 f q t - t / q

/-- The general lower inequality in equation (84), with uniqueness and the standing assumption
"Assume that 𝓕₀''(t) is first positive and then negative, so that 𝓕₀(t) has a unique inflection
point t_* > 0" from Section 1 explicit. -/
def claim : Prop :=
  ∀ (q : ℝ), 2 < q → ∀ f : ℝ → ℝ,
    Integrable f →
    (∀ w, 0 ≤ f w) →
    (∀ w, w ≤ 0 → f w = 0) →
    (∫ w, f w) = 1 →
    Integrable (fun w => w ^ 4 * f w) →
    (∃ s : ℝ, 0 < s ∧
      (∀ t, 0 < t → t < s → 0 < iteratedDeriv 2 (F0 f q) t) ∧
      (∀ t, s < t → iteratedDeriv 2 (F0 f q) t < 0)) →
    (∃! t : ℝ, 0 < t ∧ K f q t = 0) →
    ∀ t : ℝ, 0 < t → K f q t = 0 →
      2 * (moment f 3 / moment f 4) * Real.log (q - 1) < t

private def block (a : ℝ) : ℝ → ℝ :=
  (Icc (a - 1 / 1000) (a + 1 / 1000)).indicator (fun _ => 500)

/-- The mixture of uniform blocks of half-width 1/1000 centered at 1 and 11. -/
def density (w : ℝ) : ℝ := 1331 / 1340 * block 1 w + 9 / 1340 * block 11 w

private lemma block_nonneg (a w : ℝ) : 0 ≤ block a w := by
  unfold block Set.indicator
  split_ifs <;> norm_num

private lemma density_nonneg (w : ℝ) : 0 ≤ density w := by
  exact add_nonneg (mul_nonneg (by norm_num) (block_nonneg 1 w))
    (mul_nonneg (by norm_num) (block_nonneg 11 w))

private lemma density_zero (w : ℝ) (hw : w ≤ 0) : density w = 0 := by
  have h1 : w ∉ Icc (1 - 1 / 1000 : ℝ) (1 + 1 / 1000) := by
    intro h; linarith [h.1]
  have h11 : w ∉ Icc (11 - 1 / 1000 : ℝ) (11 + 1 / 1000) := by
    intro h; linarith [h.1]
  simp only [density, block, indicator_of_notMem h1, indicator_of_notMem h11,
    mul_zero, add_zero]

private lemma weighted_block_integrable (h : ℝ → ℝ) (hh : Continuous h) (a : ℝ) :
    Integrable (fun w => h w * block a w) := by
  have hi := (hh.mul (continuous_const (y := (500 : ℝ)))).integrableOn_Icc
    (a := a - 1 / 1000) (b := a + 1 / 1000) (μ := volume)
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext w
  by_cases hw : w ∈ Icc (a - 1 / 1000) (a + 1 / 1000)
  · simp only [block, indicator_of_mem hw, Pi.mul_apply]
  · simp only [block, indicator_of_notMem hw, mul_zero]

private lemma weighted_density_integrable (h : ℝ → ℝ) (hh : Continuous h) :
    Integrable (fun w => h w * density w) := by
  convert ((weighted_block_integrable h hh 1).const_mul (1331 / 1340)).add
    ((weighted_block_integrable h hh 11).const_mul (9 / 1340)) using 1
  ext w
  simp only [density, Pi.add_apply]
  ring

private lemma integral_weighted_block (h : ℝ → ℝ) (_hh : Continuous h) (a : ℝ) :
    (∫ w, h w * block a w) = 500 * ∫ w in (a - 1 / 1000)..(a + 1 / 1000), h w := by
  have heq : (fun w => h w * block a w) =
      (Icc (a - 1 / 1000) (a + 1 / 1000)).indicator (fun w => 500 * h w) := by
    ext w
    by_cases hw : w ∈ Icc (a - 1 / 1000) (a + 1 / 1000)
    · simp only [block, indicator_of_mem hw, mul_comm]
    · simp only [block, indicator_of_notMem hw, mul_zero]
  rw [heq, integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

private lemma integral_weighted_density (h : ℝ → ℝ) (hh : Continuous h) :
    (∫ w, h w * density w) =
      1331 / 1340 * (500 * ∫ w in (999 / 1000 : ℝ)..(1001 / 1000), h w) +
      9 / 1340 * (500 * ∫ w in (10999 / 1000 : ℝ)..(11001 / 1000), h w) := by
  have heq : (fun w => h w * density w) =
      fun w => (1331 / 1340) * (h w * block 1 w) +
        (9 / 1340) * (h w * block 11 w) := by
    ext w; simp only [density]; ring
  rw [heq, integral_add
    ((weighted_block_integrable h hh 1).const_mul _)
    ((weighted_block_integrable h hh 11).const_mul _), integral_const_mul,
    integral_const_mul, integral_weighted_block h hh 1, integral_weighted_block h hh 11]
  norm_num

private lemma density_integrable : Integrable density := by
  simpa using weighted_density_integrable (fun _ => 1) continuous_const

private lemma density_mass : (∫ w, density w) = 1 := by
  have h := integral_weighted_density (fun _ => 1) continuous_const
  norm_num at h ⊢
  exact h

private lemma density_moment_formula (n : ℕ) :
    moment density n =
      (1331 / 1340 : ℝ) * 500 *
        (((1001 / 1000) ^ (n + 1) - (999 / 1000) ^ (n + 1)) / (n + 1)) +
      9 / 1340 * 500 *
        (((11001 / 1000) ^ (n + 1) - (10999 / 1000) ^ (n + 1)) / (n + 1)) := by
  rw [moment, integral_weighted_density (fun w => w ^ n) (continuous_id.pow n),
    integral_pow, integral_pow]
  ring

private lemma density_moments :
    moment density 1 = 143 / 134 ∧
    moment density 3 = 1331000143 / 134000000 ∧
    moment density 4 = 33275001210000067 / 335000000000000 := by
  rw [density_moment_formula 1, density_moment_formula 3, density_moment_formula 4]
  norm_num

private lemma density_fourth_integrable : Integrable (fun w => w ^ 4 * density w) :=
  weighted_density_integrable _ (continuous_id.pow 4)

private def g (x : ℝ) : ℝ := (Real.exp x - 1) / (Real.exp x + 2)
private def g1 (x : ℝ) : ℝ := 3 * Real.exp x / (Real.exp x + 2) ^ 2
private def g2 (x : ℝ) : ℝ :=
  3 * Real.exp x * (2 - Real.exp x) / (Real.exp x + 2) ^ 3
private def g3 (x : ℝ) : ℝ :=
  3 * Real.exp x * ((Real.exp x) ^ 2 - 8 * Real.exp x + 4) / (Real.exp x + 2) ^ 4

private lemma g_deriv (x : ℝ) : HasDerivAt g (g1 x) x := by
  have hd : Real.exp x + 2 ≠ 0 := ne_of_gt (by positivity)
  apply (((Real.hasDerivAt_exp x).sub_const 1).div
    ((Real.hasDerivAt_exp x).add_const 2) hd).congr_deriv
  dsimp [g1]
  field_simp
  ring

private lemma g1_deriv (x : ℝ) : HasDerivAt g1 (g2 x) x := by
  have hd : (Real.exp x + 2) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
  apply (((Real.hasDerivAt_exp x).const_mul 3).div
    (((Real.hasDerivAt_exp x).add_const 2).pow 2) hd).congr_deriv
  dsimp [g2]
  field_simp
  ring

private lemma g2_deriv (x : ℝ) : HasDerivAt g2 (g3 x) x := by
  have hd : (Real.exp x + 2) ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
  apply ((((Real.hasDerivAt_exp x).const_mul 3).mul
    ((Real.hasDerivAt_exp x).const_sub 2)).div
    (((Real.hasDerivAt_exp x).add_const 2).pow 3) hd).congr_deriv
  dsimp [g3]
  field_simp
  ring

private lemma g2_negative {x : ℝ} (hx : Real.log 2 < x) : g2 x < 0 := by
  have he : 2 < Real.exp x := (Real.log_lt_iff_lt_exp (by norm_num)).1 hx
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Real.exp_pos _)) (sub_neg.mpr he))
    (by positivity)

private lemma positive_zeros_unique (k kp kpp : ℝ → ℝ)
    (hk : ∀ t, HasDerivAt k (kp t) t) (hkp : ∀ t, HasDerivAt kp (kpp t) t)
    (hk0 : k 0 = 0) (hkp0 : kp 0 = 0)
    (hsecond : ∀ x y : ℝ, 0 < x → 0 < y → kpp x = 0 → kpp y = 0 → x = y)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx0 : k x = 0) (hy0 : k y = 0) :
    x = y := by
  have hc : Continuous k := continuous_iff_continuousAt.2 (fun t => (hk t).continuousAt)
  have hpc : Continuous kp := continuous_iff_continuousAt.2 (fun t => (hkp t).continuousAt)
  have no_ordered_zeros : ∀ a b : ℝ, 0 < a → a < b → k a = 0 → k b = 0 → False := by
    intro a b ha hab hka hkb
    obtain ⟨u, hu, hpu⟩ := exists_hasDerivAt_eq_zero ha hc.continuousOn
      (hk0.trans hka.symm) (fun t _ => hk t)
    obtain ⟨v, hv, hpv⟩ := exists_hasDerivAt_eq_zero hab hc.continuousOn
      (hka.trans hkb.symm) (fun t _ => hk t)
    obtain ⟨r, hr, hpr⟩ := exists_hasDerivAt_eq_zero hu.1 hpc.continuousOn
      (hkp0.trans hpu.symm) (fun t _ => hkp t)
    obtain ⟨s, hs, hps⟩ := exists_hasDerivAt_eq_zero (hu.2.trans hv.1) hpc.continuousOn
      (hpu.trans hpv.symm) (fun t _ => hkp t)
    have hrs := hsecond r s hr.1 (hu.1.trans hs.1) hpr hps
    linarith [hr.2, hs.1]
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim (no_ordered_zeros x y hx hxy hx0 hy0)
  · exact hxy
  · exact False.elim (no_ordered_zeros y x hy hyx hy0 hx0)

private lemma expectation_deriv (F H : ℝ → ℝ → ℝ)
    (hF : Continuous F.uncurry) (hH : Continuous H.uncurry)
    (hd : ∀ t w, HasDerivAt (fun s => F s w) (H t w) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ w, F s w * density w) (∫ w, H t w * density w) t := by
  have hf (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hh (s : ℝ) : Continuous (H s) := hH.comp (continuous_const.prodMk continuous_id)
  have hi (a b : ℝ) (hab : a ≤ b) :
      HasDerivAt (fun s => ∫ w in a..b, F s w) (∫ w in a..b, H t w) t :=
    D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.deriv_integral_compact
      hab (by norm_num : (0 : ℝ) < 1) hF.continuousOn hH.continuousOn
      (fun s _ w _ => hd s w)
  have heq : (fun s => ∫ w, F s w * density w) = fun s =>
      1331 / 1340 * (500 * ∫ w in (999 / 1000 : ℝ)..(1001 / 1000), F s w) +
      9 / 1340 * (500 * ∫ w in (10999 / 1000 : ℝ)..(11001 / 1000), F s w) :=
    funext (fun s => integral_weighted_density _ (hf s))
  rw [heq, integral_weighted_density _ (hh t)]
  exact ((hi _ _ (by norm_num)).const_mul 500 |>.const_mul (1331 / 1340)).add
    ((hi _ _ (by norm_num)).const_mul 500 |>.const_mul (9 / 1340))

private def averaged (h : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (∫ w, w ^ n * h (t * w) * density w) / moment density 1

private lemma averaged_deriv (h h' : ℝ → ℝ) (hh : Continuous h) (hh' : Continuous h')
    (hd : ∀ x, HasDerivAt h (h' x) x) (n : ℕ) (t : ℝ) :
    HasDerivAt (averaged h n) (averaged h' (n + 1) t) t := by
  have hc : Continuous (fun z : ℝ × ℝ => z.2 ^ n * h (z.1 * z.2)) := by fun_prop
  have hc' : Continuous (fun z : ℝ × ℝ => z.2 ^ (n + 1) * h' (z.1 * z.2)) := by
    fun_prop
  apply (expectation_deriv (fun s w => w ^ n * h (s * w))
    (fun s w => w ^ (n + 1) * h' (s * w)) hc hc' ?_ t).div_const _
  intro s w
  apply (((hd (s * w)).comp s ((hasDerivAt_id s).mul_const w)).const_mul (w ^ n)).congr_deriv
  simp only [pow_succ]
  ring

@[fun_prop] private lemma g_continuous : Continuous g :=
  continuous_iff_continuousAt.2 fun x => (g_deriv x).continuousAt

@[fun_prop] private lemma g1_continuous : Continuous g1 :=
  continuous_iff_continuousAt.2 fun x => (g1_deriv x).continuousAt

@[fun_prop] private lemma g2_continuous : Continuous g2 :=
  continuous_iff_continuousAt.2 fun x => (g2_deriv x).continuousAt

private lemma F0_eq (t : ℝ) : F0 density 3 t = averaged g 1 t := by
  unfold F0 averaged g
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  congr 2
  · simp
  · congr 1; ring

private lemma F0_deriv (t : ℝ) :
    HasDerivAt (F0 density 3) (averaged g1 2 t) t := by
  have heq : F0 density 3 = averaged g 1 := funext F0_eq
  rw [heq]
  exact averaged_deriv g g1 g_continuous g1_continuous g_deriv 1 t

private def logKernel (x : ℝ) : ℝ := Real.log ((Real.exp x + 2) / 3)

private lemma logKernel_deriv (x : ℝ) :
    HasDerivAt logKernel ((1 + 2 * g x) / 3) x := by
  apply ((((Real.hasDerivAt_exp x).add_const 2).div_const 3).log
    (ne_of_gt (by positivity))).congr_deriv
  dsimp [g]
  field_simp
  ring

private def Kp (t : ℝ) : ℝ := (F0 density 3 t - t * averaged g1 2 t) / 3
private def Kpp (t : ℝ) : ℝ := -t * averaged g2 3 t / 3

private lemma K_deriv (t : ℝ) : HasDerivAt (K density 3) (Kp t) t := by
  have hlog : Continuous logKernel :=
    continuous_iff_continuousAt.2 fun x => (logKernel_deriv x).continuousAt
  have hc : Continuous (fun z : ℝ × ℝ => logKernel (z.1 * z.2)) := by fun_prop
  have hc' : Continuous (fun z : ℝ × ℝ => z.2 * ((1 + 2 * g (z.1 * z.2)) / 3)) := by
    fun_prop
  have hd := expectation_deriv (fun s w => logKernel (s * w))
    (fun s w => w * ((1 + 2 * g (s * w)) / 3)) hc hc'
    (fun s w => by
      apply ((logKernel_deriv (s * w)).comp s ((hasDerivAt_id s).mul_const w)).congr_deriv
      ring) t
  have heq : (∫ w, w * ((1 + 2 * g (t * w)) / 3) * density w) =
      moment density 1 / 3 + 2 / 3 * (∫ w, w * g (t * w) * density w) := by
    have h1 := weighted_density_integrable (fun w => w) continuous_id
    have h2 := weighted_density_integrable (fun w => w * g (t * w))
      (by fun_prop)
    rw [show (fun w => w * ((1 + 2 * g (t * w)) / 3) * density w) =
      (fun w => 1 / 3 * (w * density w) + 2 / 3 * (w * g (t * w) * density w)) by
        ext w; ring, integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
    simp only [moment, pow_one]
    ring
  have hμ : moment density 1 ≠ 0 := by rw [density_moments.1]; norm_num
  have hlogder := hd.div_const (moment density 1)
  have h := hlogder.sub
    (((hasDerivAt_id t).mul (F0_deriv t)).const_mul (1 / 3))
  have h' := h.sub ((hasDerivAt_id t).div_const 3)
  convert h' using 1
  · ext s
    unfold K logKernel
    simp only [show ∀ x : ℝ, Real.exp x + 3 - 1 = Real.exp x + 2 from fun x => by ring,
      Pi.sub_apply, Pi.mul_apply, id_eq]
    norm_num
    ring
  · rw [heq]
    unfold Kp
    rw [F0_eq]
    simp only [averaged, pow_one, id_eq]
    field_simp [hμ]
    simp only [mul_comm t]
    ring

private lemma Kp_deriv (t : ℝ) : HasDerivAt Kp (Kpp t) t := by
  have h1 := averaged_deriv g1 g2 g1_continuous g2_continuous g1_deriv 2 t
  apply (((F0_deriv t).sub ((hasDerivAt_id t).mul h1)).div_const 3).congr_deriv
  dsimp [Kpp]
  ring

private lemma K_at_zero : K density 3 0 = 0 := by
  simp [K]

private lemma Kp_at_zero : Kp 0 = 0 := by
  simp [Kp, F0]

private lemma g3_negative {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) : g3 x < 0 := by
  have he0 : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx0
  have he1 : Real.exp 1 < 68 / 25 := Real.exp_one_lt_d9.trans (by norm_num)
  have he2 : Real.exp x < 149 / 20 := by
    have hpow : Real.exp 2 = Real.exp 1 ^ 2 := by
      simpa using Real.exp_nat_mul 1 2
    have hex := Real.exp_le_exp.mpr hx2
    rw [hpow] at hex
    nlinarith [Real.exp_pos 1]
  have hp : (Real.exp x) ^ 2 - 8 * Real.exp x + 4 < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he0) (sub_nonneg.mpr he2.le)]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Real.exp_pos _)) hp) (by positivity)

private lemma weighted_density_negative (h : ℝ → ℝ) (hh : Continuous h)
    (hneg : ∀ w ∈ Icc (999 / 1000 : ℝ) (11001 / 1000), h w < 0) :
    (∫ w, h w * density w) < 0 := by
  have hi (a b : ℝ) (hab : a < b)
      (hsub : Ioo a b ⊆ Icc (999 / 1000 : ℝ) (11001 / 1000)) :
      (∫ w in a..b, h w) < 0 := by
    have hp := intervalIntegral.intervalIntegral_pos_of_pos_on
      (hh.neg.intervalIntegrable a b) (fun w hw => neg_pos.mpr (hneg w (hsub hw))) hab
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg, neg_pos] using hp
  rw [integral_weighted_density _ hh]
  have h1 := hi (999 / 1000) (1001 / 1000) (by norm_num) (by
    intro w hw; constructor <;> linarith [hw.1, hw.2])
  have h11 := hi (10999 / 1000) (11001 / 1000) (by norm_num) (by
    intro w hw; constructor <;> linarith [hw.1, hw.2])
  linarith

private lemma F2_deriv (t : ℝ) :
    HasDerivAt (averaged g2 3) (averaged g3 4 t) t := by
  have hc : Continuous g3 := by
    unfold g3
    exact ((continuous_const.mul Real.continuous_exp).mul
      ((Real.continuous_exp.pow 2).sub (continuous_const.mul Real.continuous_exp) |>.add
        continuous_const)).div ((Real.continuous_exp.add continuous_const).pow 4)
          (fun x => by positivity)
  exact averaged_deriv g2 g3 g2_continuous hc g2_deriv 3 t

private lemma F2_strictAnti : StrictAntiOn (averaged g2 3) (Icc 0 (9 / 50)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_iff_continuousAt.2 (fun t => (F2_deriv t).continuousAt)).continuousOn
  intro t ht
  rw [(F2_deriv t).deriv]
  have ht' : 0 < t ∧ t < 9 / 50 := by simpa only [interior_Icc, mem_Ioo] using ht
  have hneg : (∫ w, w ^ 4 * g3 (t * w) * density w) < 0 := by
    apply weighted_density_negative _ (by
      have hc : Continuous g3 := by
        unfold g3
        apply Continuous.div (by fun_prop) (by fun_prop)
        intro x; positivity
      fun_prop)
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hx : t * w ≤ 2 := by nlinarith [hw.2]
    exact mul_neg_of_pos_of_neg (pow_pos hw0 _) (g3_negative (mul_nonneg ht'.1.le hw0.le) hx)
  exact div_neg_of_neg_of_pos hneg (by rw [density_moments.1]; norm_num)

private lemma F2_at_zero : 0 < averaged g2 3 0 := by
  have heq : averaged g2 3 0 = moment density 3 / (9 * moment density 1) := by
    unfold averaged
    simp only [zero_mul, g2, Real.exp_zero]
    norm_num
    rw [show (fun w => w ^ 3 * (1 / 9) * density w) =
      fun w => 1 / 9 * (w ^ 3 * density w) by ext w; ring, integral_const_mul]
    unfold moment
    ring
  rw [heq, density_moments.1, density_moments.2.1]
  norm_num

private def expPoly (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 16, (q / 8) ^ k / (k.factorial : ℚ)
private def expError : ℚ := 17 / (16 * (16).factorial)

private lemma exp_rational_bounds (q l u : ℚ) (hq : 0 ≤ q ∧ q ≤ 8)
    (hl : l ≤ expPoly q ^ 8) (hu : (expPoly q + expError) ^ 8 ≤ u) :
    (l : ℝ) ≤ Real.exp (q : ℝ) ∧ Real.exp (q : ℝ) ≤ (u : ℝ) := by
  have hq0 : 0 ≤ (q : ℝ) / 8 := by exact_mod_cast (div_nonneg hq.1 (by norm_num) : 0 ≤ q / 8)
  have hq1 : (q : ℝ) / 8 ≤ 1 := by exact_mod_cast (show q / 8 ≤ 1 by linarith [hq.2])
  have hp : (expPoly q : ℝ) = ∑ k ∈ Finset.range 16, ((q : ℝ) / 8) ^ k / (k.factorial : ℝ) := by
    simp only [expPoly]; push_cast; rfl
  have hp0 : 0 ≤ (expPoly q : ℝ) := by rw [hp]; positivity
  have hlow : (expPoly q : ℝ) ≤ Real.exp ((q : ℝ) / 8) := by
    rw [hp]; exact Real.sum_le_exp_of_nonneg hq0 16
  have hupper : Real.exp ((q : ℝ) / 8) ≤ (expPoly q : ℝ) + (expError : ℝ) := by
    have h := Real.exp_bound' hq0 hq1 (by norm_num : 0 < (16 : ℕ))
    have hpow : ((q : ℝ) / 8) ^ 16 ≤ 1 := pow_le_one₀ hq0 hq1
    rw [← hp] at h
    norm_num [expError] at h ⊢
    linarith
  have heq : Real.exp (q : ℝ) = Real.exp ((q : ℝ) / 8) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hl' : (l : ℝ) ≤ (expPoly q : ℝ) ^ 8 := by exact_mod_cast hl
  have hu' : ((expPoly q : ℝ) + (expError : ℝ)) ^ 8 ≤ (u : ℝ) := by exact_mod_cast hu
  rw [heq]
  exact ⟨hl'.trans (pow_le_pow_left₀ hp0 hlow 8),
    (pow_le_pow_left₀ (Real.exp_pos _).le hupper 8).trans hu'⟩

private def logLower (a : ℚ) : ℚ :=
  2 * ∑ k ∈ Finset.range 16, ((a - 1) / (a + 1)) ^ (2 * k + 1) / (2 * k + 1)

private lemma log_rational_lower (a : ℚ) (ha : 1 ≤ a) : (logLower a : ℝ) ≤ Real.log (a : ℝ) := by
  have ha' : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have h0 : 0 ≤ ((a : ℝ) - 1) / (a + 1) := by positivity
  have h1 : ((a : ℝ) - 1) / (a + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have h := Real.sum_range_le_log_div h0 h1 16
  have heq : (1 + ((a : ℝ) - 1) / (a + 1)) / (1 - ((a : ℝ) - 1) / (a + 1)) = a := by
    field_simp; ring
  rw [heq] at h
  have hp : (logLower a : ℝ) =
      2 * ∑ k ∈ Finset.range 16, (((a : ℝ) - 1) / (a + 1)) ^ (2 * k + 1) / (2 * k + 1) := by
    simp only [logLower]; push_cast; rfl
  rw [hp]; linarith

private lemma interval_exp_bounds (a b l u : ℚ) (ha : 0 ≤ a) (hb : b ≤ 8)
    (hl : l ≤ expPoly a ^ 8) (hu : (expPoly b + expError) ^ 8 ≤ u)
    {x : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)) :
    (l : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (u : ℝ) := by
  have hab : a ≤ b := by exact_mod_cast hx.1.trans hx.2
  have h1 := exp_rational_bounds a l ((expPoly a + expError) ^ 8)
    ⟨ha, hab.trans hb⟩ hl le_rfl
  have h2 := exp_rational_bounds b (expPoly b ^ 8) u ⟨ha.trans hab, hb⟩ le_rfl hu
  exact ⟨h1.1.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans h2.2⟩

private lemma curvature_upper (w wu e el eu : ℝ) (hw : 0 ≤ w) (hwu : w ≤ wu)
    (he : 0 < e) (hel : 0 < el) (hle : el ≤ e) (heu : e ≤ eu) :
    w ^ 3 * (3 * e * (2 - e) / (e + 2) ^ 3) ≤
      3 * wu ^ 3 * eu * max 0 (2 - el) / (el + 2) ^ 3 := by
  have hwu0 : 0 ≤ wu := hw.trans hwu
  have heu0 : 0 ≤ eu := he.le.trans heu
  have hsub : 2 - e ≤ max 0 (2 - el) := (sub_le_sub_left hle 2).trans (le_max_right _ _)
  have hnum : 3 * w ^ 3 * e * (2 - e) ≤ 3 * wu ^ 3 * eu * max 0 (2 - el) := by
    by_cases h2 : e ≤ 2
    · have h2' : 0 ≤ 2 - e := sub_nonneg.mpr h2
      gcongr <;> first | positivity | assumption
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)).trans (by positivity)
  calc
    _ = (3 * w ^ 3 * e * (2 - e)) / (e + 2) ^ 3 := by ring
    _ ≤ (3 * wu ^ 3 * eu * max 0 (2 - el)) / (e + 2) ^ 3 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)

private lemma curvature_upper_negative (w wl e el eu : ℝ) (hw : 0 ≤ wl) (hwl : wl ≤ w)
    (hel : 2 < el) (hle : el ≤ e) (heu : e ≤ eu) :
    w ^ 3 * (3 * e * (2 - e) / (e + 2) ^ 3) ≤
      -3 * wl ^ 3 * el * (el - 2) / (eu + 2) ^ 3 := by
  have he : 0 < e := by linarith
  have he0 : 0 < el := by linarith
  have hw0 : 0 ≤ w := hw.trans hwl
  have heu0 : 0 < eu := he.trans_le heu
  have he2 : 0 ≤ e - 2 := by linarith
  have hnum : 3 * wl ^ 3 * el * (el - 2) ≤ 3 * w ^ 3 * e * (e - 2) := by
    gcongr <;> positivity
  have h : (3 * wl ^ 3 * el * (el - 2)) / (eu + 2) ^ 3 ≤
      (3 * w ^ 3 * e * (e - 2)) / (e + 2) ^ 3 := by
    calc
      _ ≤ (3 * w ^ 3 * e * (e - 2)) / (eu + 2) ^ 3 :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  calc
    _ = -((3 * w ^ 3 * e * (e - 2)) / (e + 2) ^ 3) := by ring
    _ ≤ -((3 * wl ^ 3 * el * (el - 2)) / (eu + 2) ^ 3) := neg_le_neg h
    _ = _ := by ring

private lemma weighted_density_le (h : ℝ → ℝ) (hh : Continuous h) (l u : ℝ)
    (hl : ∀ w ∈ Icc (999 / 1000 : ℝ) (1001 / 1000), h w ≤ l)
    (hu : ∀ w ∈ Icc (10999 / 1000 : ℝ) (11001 / 1000), h w ≤ u) :
    (∫ w, h w * density w) ≤ 1331 / 1340 * l + 9 / 1340 * u := by
  have h1 := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (999 / 1000 : ℝ) ≤ 1001 / 1000)
    (hh.intervalIntegrable _ _) intervalIntegrable_const hl
  have h11 := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (10999 / 1000 : ℝ) ≤ 11001 / 1000)
    (hh.intervalIntegrable _ _) intervalIntegrable_const hu
  rw [integral_weighted_density _ hh]
  norm_num at h1 h11
  linarith

private def gridA (i : Fin 26) : ℚ := 9 / 50 + (i.val : ℚ) / 50
private def gridB (i : Fin 26) : ℚ := gridA i + 1 / 50
private def gridData : Fin 26 → ℚ × ℚ × ℚ × ℚ :=
  ![
    (119700 / 100000, 122165 / 100000, 724143 / 100000, 902682 / 100000),
    (122115 / 100000, 124636 / 100000, 902320 / 100000, 1124834 / 100000),
    (124580 / 100000, 127156 / 100000, 1124338 / 100000, 1401657 / 100000),
    (127094 / 100000, 129727 / 100000, 1400984 / 100000, 1746607 / 100000),
    (129659 / 100000, 132351 / 100000, 1745698 / 100000, 2176450 / 100000),
    (132275 / 100000, 135027 / 100000, 2175231 / 100000, 2712078 / 100000),
    (134945 / 100000, 137757 / 100000, 2710450 / 100000, 3379525 / 100000),
    (137668 / 100000, 140543 / 100000, 3377361 / 100000, 4211231 / 100000),
    (140446 / 100000, 143385 / 100000, 4208367 / 100000, 5247622 / 100000),
    (143281 / 100000, 146285 / 100000, 5243844 / 100000, 6539070 / 100000),
    (146172 / 100000, 149243 / 100000, 6534101 / 100000, 8148346 / 100000),
    (149122 / 100000, 152261 / 100000, 8141829 / 100000, 10153667 / 100000),
    (152132 / 100000, 155340 / 100000, 10145141 / 100000, 12652502 / 100000),
    (155202 / 100000, 158481 / 100000, 12641371 / 100000, 15766303 / 100000),
    (158334 / 100000, 161686 / 100000, 15751804 / 100000, 19646416 / 100000),
    (161529 / 100000, 164955 / 100000, 19627564 / 100000, 24481431 / 100000),
    (164789 / 100000, 168291 / 100000, 24456961 / 100000, 30506352 / 100000),
    (168115 / 100000, 171694 / 100000, 30474641 / 100000, 38014015 / 100000),
    (171508 / 100000, 175166 / 100000, 37972982 / 100000, 47369327 / 100000),
    (174969 / 100000, 178708 / 100000, 47316302 / 100000, 59026997 / 100000),
    (178500 / 100000, 182322 / 100000, 58958564 / 100000, 73553638 / 100000),
    (182102 / 100000, 186009 / 100000, 73465426 / 100000, 91655310 / 100000),
    (185777 / 100000, 189770 / 100000, 91541727 / 100000, 114211833 / 100000),
    (189526 / 100000, 193607 / 100000, 114065735 / 100000, 142319554 / 100000),
    (193351 / 100000, 197523 / 100000, 142131815 / 100000, 177344631 / 100000),
    (197253 / 100000, 201517 / 100000, 177103606 / 100000, 220989438 / 100000)]

private def gridLow (i : Fin 26) : ℚ :=
  3 * (1001 / 1000) ^ 3 * (gridData i).2.1 * max 0 (2 - (gridData i).1) /
    ((gridData i).1 + 2) ^ 3
private def gridHigh (i : Fin 26) : ℚ :=
  -3 * (10999 / 1000) ^ 3 * (gridData i).2.2.1 * ((gridData i).2.2.1 - 2) /
    ((gridData i).2.2.2 + 2) ^ 3

private lemma grid_certified (i : Fin 26) :
    0 < (gridData i).1 ∧ 2 < (gridData i).2.2.1 ∧
    (gridData i).1 ≤ expPoly (gridA i * (999 / 1000)) ^ 8 ∧
    (expPoly (gridB i * (1001 / 1000)) + expError) ^ 8 ≤ (gridData i).2.1 ∧
    (gridData i).2.2.1 ≤ expPoly (gridA i * (10999 / 1000)) ^ 8 ∧
    (expPoly (gridB i * (11001 / 1000)) + expError) ^ 8 ≤ (gridData i).2.2.2 ∧
    1331 * gridLow i + 9 * gridHigh i < 0 := by
  revert i
  set_option maxRecDepth 10000 in
    set_option maxHeartbeats 8000000 in
      decide +kernel

private lemma F2_middle_negative :
    ∀ t ∈ Icc (9 / 50 : ℝ) (7 / 10), averaged g2 3 t < 0 := by
  intro t ht
  have hgrid : ∃ i : Fin 26, (gridA i : ℝ) ≤ t ∧ t ≤ (gridB i : ℝ) := by
    by_cases hlast : t = 7 / 10
    · refine ⟨25, ?_, ?_⟩ <;> norm_num [gridA, gridB, hlast]
    · let n : ℕ := ⌊50 * (t - 9 / 50)⌋₊
      have hn0 : 0 ≤ 50 * (t - 9 / 50) := by linarith [ht.1]
      have hn := Nat.floor_le hn0
      have hn' := Nat.lt_floor_add_one (50 * (t - 9 / 50))
      have hlt : n < 26 := by
        apply (Nat.floor_lt hn0).2
        have htt : t < 7 / 10 := lt_of_le_of_ne ht.2 hlast
        linarith
      refine ⟨⟨n, hlt⟩, ?_, ?_⟩ <;> simp only [gridA, gridB, Rat.cast_add,
        Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
      · linarith
      · linarith
  obtain ⟨i, hta, htb⟩ := hgrid
  have hi := grid_certified i
  have hir : (i.val : ℚ) < 26 := by exact_mod_cast i.isLt
  have hbounds (w wl wu : ℝ) (hw : wl ≤ w ∧ w ≤ wu) (hl : 0 ≤ wl) :
      (gridA i : ℝ) * wl ≤ t * w ∧ t * w ≤ (gridB i : ℝ) * wu := by
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ha0 : 0 ≤ (gridA i : ℝ) := by simp [gridA]; positivity
    exact ⟨mul_le_mul hta hw.1 hl ht0,
      mul_le_mul htb hw.2 (hl.trans hw.1) (ha0.trans (hta.trans htb))⟩
  have hs (w : ℝ) (hw : w ∈ Icc (999 / 1000 : ℝ) (1001 / 1000)) :=
    interval_exp_bounds (gridA i * (999 / 1000)) (gridB i * (1001 / 1000))
      (gridData i).1 (gridData i).2.1 (by dsimp [gridA]; positivity)
      (by dsimp [gridB, gridA]; nlinarith) hi.2.2.1 hi.2.2.2.1
      (by simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hbounds w _ _ hw (by norm_num))
  have hh (w : ℝ) (hw : w ∈ Icc (10999 / 1000 : ℝ) (11001 / 1000)) :=
    interval_exp_bounds (gridA i * (10999 / 1000)) (gridB i * (11001 / 1000))
      (gridData i).2.2.1 (gridData i).2.2.2 (by dsimp [gridA]; positivity)
      (by dsimp [gridB, gridA]; nlinarith) hi.2.2.2.2.1 hi.2.2.2.2.2.1
      (by simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hbounds w _ _ hw (by norm_num))
  have hle := weighted_density_le (fun w => w ^ 3 * g2 (t * w)) (by fun_prop)
    (gridLow i) (gridHigh i) (fun w hw => by
      have he := hs w hw
      have h := curvature_upper w (1001 / 1000) (Real.exp (t * w))
        (gridData i).1 (gridData i).2.1 (by linarith [hw.1]) hw.2 (Real.exp_pos _)
        (by exact_mod_cast hi.1) he.1 he.2
      simpa only [g2, gridLow, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_sub, Rat.cast_add, Rat.cast_ofNat, Rat.cast_max, Rat.cast_zero] using h)
    (fun w hw => by
      have he := hh w hw
      have h := curvature_upper_negative w (10999 / 1000) (Real.exp (t * w))
        (gridData i).2.2.1 (gridData i).2.2.2 (by norm_num) hw.1
        (by exact_mod_cast hi.2.1) he.1 he.2
      simpa only [g2, gridHigh, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_sub, Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg] using h)
  apply div_neg_of_neg_of_pos ?_ (by rw [density_moments.1]; norm_num)
  have hcert : (1331 : ℝ) * (gridLow i : ℝ) + 9 * (gridHigh i : ℝ) < 0 := by
    exact_mod_cast hi.2.2.2.2.2.2
  linarith

private lemma F2_tail_negative {t : ℝ} (ht : 7 / 10 ≤ t) : averaged g2 3 t < 0 := by
  apply div_neg_of_neg_of_pos ?_ (by rw [density_moments.1]; norm_num)
  apply weighted_density_negative _ (by fun_prop)
  intro w hw
  have hw0 : 0 < w := by linarith [hw.1]
  have hx : Real.log 2 < t * w := by
    have hlog := Real.log_two_lt_d9
    nlinarith [hw.1]
  exact mul_neg_of_pos_of_neg (pow_pos hw0 _) (g2_negative hx)

private lemma F2_sign_change :
    ∃ s : ℝ, 0 < s ∧ s ≤ 9 / 50 ∧ averaged g2 3 s = 0 ∧
      (∀ t, 0 < t → t < s → 0 < averaged g2 3 t) ∧
      (∀ t, s < t → averaged g2 3 t < 0) := by
  have hc : Continuous (averaged g2 3) :=
    continuous_iff_continuousAt.2 fun t => (F2_deriv t).continuousAt
  obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 9 / 50)
    hc.continuousOn ⟨(F2_middle_negative (9 / 50) (by norm_num)).le, F2_at_zero.le⟩
  have hs0 : 0 < s := by
    have hne : s ≠ 0 := by intro h; subst s; linarith [F2_at_zero]
    exact lt_of_le_of_ne hs.1 (Ne.symm hne)
  refine ⟨s, hs0, hs.2, hzero, ?_, ?_⟩
  · intro t ht hts
    have h := F2_strictAnti ⟨ht.le, (hts.trans_le hs.2).le⟩ hs hts
    rwa [hzero] at h
  · intro t hst
    by_cases ht : t ≤ 9 / 50
    · have h := F2_strictAnti hs ⟨(hs0.trans hst).le, ht⟩ hst
      rwa [hzero] at h
    · by_cases htm : t ≤ 7 / 10
      · exact F2_middle_negative t ⟨(lt_of_not_ge ht).le, htm⟩
      · exact F2_tail_negative (lt_of_not_ge htm).le

private lemma density_curvature :
    ∃ s : ℝ, 0 < s ∧
      (∀ t, 0 < t → t < s → 0 < iteratedDeriv 2 (F0 density 3) t) ∧
      (∀ t, s < t → iteratedDeriv 2 (F0 density 3) t < 0) := by
  have hfirst : deriv (F0 density 3) = averaged g1 2 :=
    funext fun t => (F0_deriv t).deriv
  have hsecond (t : ℝ) : iteratedDeriv 2 (F0 density 3) t = averaged g2 3 t := by
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, hfirst]
    exact (averaged_deriv g1 g2 g1_continuous g2_continuous g1_deriv 2 t).deriv
  obtain ⟨s, hs, _, _, hpos, hneg⟩ := F2_sign_change
  exact ⟨s, hs, fun t ht hts => (hsecond t).symm ▸ hpos t ht hts,
    fun t hst => (hsecond t).symm ▸ hneg t hst⟩

private lemma F2_zero_unique :
    ∀ x y : ℝ, 0 < x → 0 < y → averaged g2 3 x = 0 → averaged g2 3 y = 0 → x = y := by
  have hsmall (x : ℝ) (hx : 0 < x) (hzero : averaged g2 3 x = 0) : x < 9 / 50 := by
    by_contra h
    have hxlow : 9 / 50 ≤ x := le_of_not_gt h
    by_cases hxhi : x ≤ 7 / 10
    · linarith [F2_middle_negative x ⟨hxlow, hxhi⟩]
    · linarith [F2_tail_negative (le_of_not_ge hxhi)]
  intro x y hx hy hx0 hy0
  have hxsmall := hsmall x hx hx0
  have hysmall := hsmall y hy hy0
  exact F2_strictAnti.injOn ⟨hx.le, hxsmall.le⟩ ⟨hy.le, hysmall.le⟩ (hx0.trans hy0.symm)

private lemma K_zero_unique :
    ∀ x y : ℝ, 0 < x → 0 < y → K density 3 x = 0 → K density 3 y = 0 → x = y := by
  apply positive_zeros_unique (K density 3) Kp Kpp K_deriv Kp_deriv K_at_zero Kp_at_zero
  intro x y hx hy hx0 hy0
  have hcancel (z : ℝ) (hz : 0 < z) (hz0 : Kpp z = 0) : averaged g2 3 z = 0 := by
    unfold Kpp at hz0
    exact (mul_eq_zero.mp (((div_eq_zero_iff).1 hz0).resolve_right (by norm_num))).resolve_left
      (neg_ne_zero.mpr (ne_of_gt hz))
  exact F2_zero_unique x y hx hy (hcancel x hx hx0) (hcancel y hy hy0)

private def scalarK (x : ℝ) : ℝ := logKernel x - x / 3 * g x - x / 3
private def scalarKp (x : ℝ) : ℝ := (g x - x * g1 x) / 3
private def scalarKpp (x : ℝ) : ℝ := -x / 3 * g2 x

private lemma scalarK_deriv (x : ℝ) : HasDerivAt scalarK (scalarKp x) x := by
  apply (((logKernel_deriv x).sub (((hasDerivAt_id x).div_const 3).mul (g_deriv x))).sub
    ((hasDerivAt_id x).div_const 3)).congr_deriv
  dsimp [scalarKp]; ring

private lemma scalarKp_deriv (x : ℝ) : HasDerivAt scalarKp (scalarKpp x) x := by
  apply (((g_deriv x).sub ((hasDerivAt_id x).mul (g1_deriv x))).div_const 3).congr_deriv
  dsimp [scalarKpp]; ring

private lemma K_scalar (t : ℝ) :
    K density 3 t = (∫ w, scalarK (t * w) * density w) / moment density 1 := by
  have hlc : Continuous logKernel :=
    continuous_iff_continuousAt.2 fun x => (logKernel_deriv x).continuousAt
  have hl := weighted_density_integrable (fun w => logKernel (t * w)) (by fun_prop)
  have hg := weighted_density_integrable (fun w => w * g (t * w)) (by fun_prop)
  have hw := weighted_density_integrable (fun w : ℝ => w) continuous_id
  have heq : (fun w => scalarK (t * w) * density w) = fun w =>
      logKernel (t * w) * density w - (t / 3) * (w * g (t * w) * density w) -
        (t / 3) * (w * density w) := by ext w; unfold scalarK; ring
  rw [heq, integral_sub
      (f := fun w => logKernel (t * w) * density w - (t / 3) * (w * g (t * w) * density w))
      (g := fun w => (t / 3) * (w * density w)) (hl.sub (hg.const_mul _)) (hw.const_mul _),
    integral_sub (f := fun w => logKernel (t * w) * density w)
      (g := fun w => (t / 3) * (w * g (t * w) * density w)) hl (hg.const_mul _),
    integral_const_mul, integral_const_mul]
  unfold K
  simp only [show ∀ x : ℝ, Real.exp x + 3 - 1 = Real.exp x + 2 from fun x => by ring]
  rw [F0_eq]
  simp only [averaged, pow_one, logKernel]
  have hm : (∫ w, w * density w) = moment density 1 := by simp [moment]
  rw [hm, density_moments.1]
  ring

private def scalarLower (q l u : ℚ) : ℚ :=
  logLower ((l + 2) / 3) - q / 3 * ((u - 1) / (u + 2)) - q / 3

private lemma scalar_lower (q l u : ℚ) (hq : 0 ≤ q) (hl : 1 ≤ l)
    (he : (l : ℝ) ≤ Real.exp (q : ℝ) ∧ Real.exp (q : ℝ) ≤ (u : ℝ)) :
    (scalarLower q l u : ℝ) ≤ scalarK (q : ℝ) := by
  have hl' : 1 ≤ (l : ℝ) := by exact_mod_cast hl
  have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hu' : 1 ≤ (u : ℝ) := hl'.trans (he.1.trans he.2)
  have hlog := log_rational_lower ((l + 2) / 3) (by linarith)
  push_cast at hlog
  have hlog' : Real.log (((l : ℝ) + 2) / 3) ≤ logKernel (q : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  have hg : g (q : ℝ) ≤ ((u : ℝ) - 1) / (u + 2) := by
    unfold g
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [he.2]
  have hprod := mul_le_mul_of_nonneg_left hg (div_nonneg hq' (by norm_num : (0 : ℝ) ≤ 3))
  unfold scalarLower
  push_cast
  unfold scalarK
  linarith

private lemma scalar_pair_positive :
    (3 / 20000000 : ℝ) ≤
      1331 / 1340 * scalarK (6931 / 50000) + 9 / 1340 * scalarK (76241 / 50000) := by
  have h1 := exp_rational_bounds (6931 / 50000) (1148687515801 / 10 ^ 12)
    (1148687515803 / 10 ^ 12) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ])
    (by norm_num [expPoly, expError, Finset.sum_range_succ])
  have h11 := exp_rational_bounds (76241 / 50000) (4594316517901 / 10 ^ 12)
    (4594316517904 / 10 ^ 12) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ])
    (by norm_num [expPoly, expError, Finset.sum_range_succ])
  have hb1 := scalar_lower _ _ _ (by norm_num) (by norm_num) h1
  have hb11 := scalar_lower _ _ _ (by norm_num) (by norm_num) h11
  have hc : (3 / 20000000 : ℚ) ≤
      1331 / 1340 * scalarLower (6931 / 50000) (1148687515801 / 10 ^ 12) (1148687515803 / 10 ^ 12) +
      9 / 1340 * scalarLower (76241 / 50000) (4594316517901 / 10 ^ 12) (4594316517904 / 10 ^ 12) := by
    norm_num [scalarLower, logLower, Finset.sum_range_succ]
  have hc' := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at hc'
  norm_num at hb1 hb11 hc'
  linarith

private lemma g2_abs_le_one (x : ℝ) : |g2 x| ≤ 1 := by
  have he := Real.exp_pos x
  have hab : |2 - Real.exp x| ≤ Real.exp x + 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : 3 * Real.exp x ≤ (Real.exp x + 2) ^ 2 := by nlinarith [sq_nonneg (Real.exp x)]
  unfold g2
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    abs_of_pos he, abs_of_pos (by positivity : 0 < (Real.exp x + 2) ^ 3)]
  apply (div_le_one (by positivity)).2
  calc
    3 * Real.exp x * |2 - Real.exp x| ≤ 3 * Real.exp x * (Real.exp x + 2) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ (Real.exp x + 2) ^ 2 * (Real.exp x + 2) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

private lemma symmetric_integral_lower (h hp hpp : ℝ → ℝ) (a e M : ℝ)
    (he : 0 < e) (hM : 0 ≤ M) (hd : ∀ x, HasDerivAt h (hp x) x)
    (hdp : ∀ x, HasDerivAt hp (hpp x) x)
    (hb : ∀ x ∈ Icc (a - e) (a + e), |hpp x| ≤ M) :
    2 * e * (h a - M * e ^ 2) ≤ ∫ x in (a - e)..(a + e), h x := by
  have ha : a ∈ Icc (a - e) (a + e) := by constructor <;> linarith
  have hnorm (x : ℝ) (hx : x ∈ Icc (a - e) (a + e)) : |x - a| ≤ e := by
    exact abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpb (x : ℝ) (hx : x ∈ Icc (a - e) (a + e)) : |hp x - hp a| ≤ M * e := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ => (hdp y).hasDerivWithinAt) (fun y hy => by simpa using hb y hy)
      (convex_Icc (a - e) (a + e)) ha hx
    exact (show |hp x - hp a| ≤ M * |x - a| by simpa using h).trans
      (mul_le_mul_of_nonneg_left (hnorm x hx) hM)
  let r : ℝ → ℝ := fun x => h x - h a - (x - a) * hp a
  have hr (x : ℝ) : HasDerivAt r (hp x - hp a) x := by
    apply (((hd x).sub_const (h a)).sub
      (((hasDerivAt_id x).sub_const a).mul_const (hp a))).congr_deriv
    simp
  have hc : Continuous h := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hpoint (x : ℝ) (hx : x ∈ Icc (a - e) (a + e)) :
      h a + (x - a) * hp a - M * e ^ 2 ≤ h x := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ => (hr y).hasDerivWithinAt) (fun y hy => by simpa using hpb y hy)
      (convex_Icc (a - e) (a + e)) ha hx
    have hh : |r x| ≤ M * e ^ 2 := by
      have h' : |r x| ≤ M * e * |x - a| := by simpa [r] using h
      exact h'.trans (by nlinarith [mul_le_mul_of_nonneg_left (hnorm x hx) (mul_nonneg hM he.le)])
    have h' := (abs_le.mp hh).1
    dsimp [r] at h'; linarith
  have hlincont : Continuous (fun x => h a + (x - a) * hp a - M * e ^ 2) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a - e ≤ a + e)
    (hlincont.intervalIntegrable _ _) (hc.intervalIntegrable _ _) hpoint
  have hlin : (∫ x in (a - e)..(a + e), h a + (x - a) * hp a - M * e ^ 2) =
      2 * e * (h a - M * e ^ 2) := by
    have heq : (fun x : ℝ => h a + (x - a) * hp a - M * e ^ 2) =
        fun x => (h a - a * hp a - M * e ^ 2) + x * hp a := by ext x; ring
    rw [heq, intervalIntegral.integral_add (f := fun _ : ℝ => h a - a * hp a - M * e ^ 2)
      (g := fun x : ℝ => x * hp a) intervalIntegrable_const
      ((continuous_id.mul continuous_const).intervalIntegrable _ _),
      intervalIntegral.integral_mul_const]
    simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rwa [hlin] at hi

private lemma K_positive_test : 0 < K density 3 (6931 / 50000) := by
  let T : ℝ := 6931 / 50000
  have hd (w : ℝ) : HasDerivAt (fun x => scalarK (T * x)) (T * scalarKp (T * w)) w := by
    apply ((scalarK_deriv (T * w)).comp w ((hasDerivAt_id w).const_mul T)).congr_deriv
    ring
  have hdp (w : ℝ) :
      HasDerivAt (fun x => T * scalarKp (T * x)) (T ^ 2 * scalarKpp (T * w)) w := by
    apply (((scalarKp_deriv (T * w)).comp w
      ((hasDerivAt_id w).const_mul T)).const_mul T).congr_deriv
    ring
  have hmean (a : ℝ) (ha : a = 1 ∨ a = 11) :
      scalarK (T * a) - 1 / 10000000 ≤
        500 * ∫ w in (a - 1 / 1000)..(a + 1 / 1000), scalarK (T * w) := by
    have hb (w : ℝ) (hw : w ∈ Icc (a - 1 / 1000) (a + 1 / 1000)) :
        |T ^ 2 * scalarKpp (T * w)| ≤ 1 / 10 := by
      have hw0 : 0 ≤ w := by rcases ha with rfl | rfl <;> linarith [hw.1]
      have hw12 : w ≤ 12 := by rcases ha with rfl | rfl <;> linarith [hw.2]
      have hx : |T * w| ≤ 2 := by rw [abs_of_nonneg (by positivity)]; dsimp [T]; linarith
      unfold scalarKpp
      rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num [T] : 0 ≤ T),
        abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_neg]
      have hg2 := g2_abs_le_one (T * w)
      calc
        _ ≤ T ^ 2 * (2 / 3 * 1) := by gcongr
        _ ≤ _ := by norm_num [T]
    have hi := symmetric_integral_lower (fun w => scalarK (T * w))
      (fun w => T * scalarKp (T * w)) (fun w => T ^ 2 * scalarKpp (T * w))
      a (1 / 1000) (1 / 10) (by norm_num) (by norm_num) hd hdp hb
    nlinarith
  have h1 := hmean 1 (Or.inl rfl)
  have h11 := hmean 11 (Or.inr rfl)
  have hc : Continuous (fun w => scalarK (T * w)) :=
    continuous_iff_continuousAt.2 fun w => (hd w).continuousAt
  rw [K_scalar]
  apply div_pos ?_ (by rw [density_moments.1]; norm_num)
  change 0 < ∫ w, scalarK (T * w) * density w
  rw [integral_weighted_density _ hc]
  norm_num [T] at h1 h11 ⊢
  linarith [scalar_pair_positive]

private lemma test_below_bound :
    (6931 / 50000 : ℝ) < 2 * (moment density 3 / moment density 4) * Real.log (3 - 1) := by
  rw [density_moments.2.1, density_moments.2.2]
  norm_num
  nlinarith [Real.log_two_gt_d9]

private lemma density_small_zero :
    ∃ t : ℝ, 0 < t ∧ K density 3 t = 0 ∧
      t ≤ 2 * (moment density 3 / moment density 4) * Real.log (3 - 1) := by
  obtain ⟨a, ha0, _, _, hbefore, _⟩ := F2_sign_change
  let d : ℝ := min (a / 2) (6931 / 100000)
  have hd0 : 0 < d := lt_min (by positivity) (by norm_num)
  have hda : d < a := (min_le_left _ _).trans_lt (by linarith)
  have hdT : d < 6931 / 50000 := (min_le_right _ _).trans_lt (by norm_num)
  have hpos : ∀ t ∈ Ioo 0 d, 0 < averaged g2 3 t := by
    intro t ht
    exact hbefore t ht.1 (ht.2.trans hda)
  have hpanti : StrictAntiOn Kp (Icc 0 d) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_iff_continuousAt.2 (fun t => (Kp_deriv t).continuousAt)).continuousOn
    intro t ht
    have ht' : t ∈ Ioo 0 d := by simpa only [interior_Icc] using ht
    rw [(Kp_deriv t).deriv]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos ht'.1) (hpos t ht')) (by norm_num)
  have hkanti : StrictAntiOn (K density 3) (Icc 0 d) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_iff_continuousAt.2 (fun t => (K_deriv t).continuousAt)).continuousOn
    intro t ht
    have ht' : t ∈ Ioo 0 d := by simpa only [interior_Icc] using ht
    rw [(K_deriv t).deriv]
    have h := hpanti ⟨le_rfl, hd0.le⟩ ⟨ht'.1.le, ht'.2.le⟩ ht'.1
    rwa [Kp_at_zero] at h
  have hdneg : K density 3 d < 0 := by
    have h := hkanti ⟨le_rfl, hd0.le⟩ ⟨hd0.le, le_rfl⟩ hd0
    rwa [K_at_zero] at h
  obtain ⟨t, ht, htzero⟩ := intermediate_value_Icc hdT.le
    (continuous_iff_continuousAt.2 (fun t => (K_deriv t).continuousAt)).continuousOn
    ⟨hdneg.le, K_positive_test.le⟩
  exact ⟨t, hd0.trans_le ht.1, htzero, ht.2.trans test_below_bound.le⟩

private lemma density_unique_zero : ∃! t : ℝ, 0 < t ∧ K density 3 t = 0 := by
  obtain ⟨t, ht, hzero, _⟩ := density_small_zero
  exact ⟨t, ⟨ht, hzero⟩, fun s hs => K_zero_unique s t hs.1 ht hs.2 hzero⟩

/-- The two-block density contradicts the proposed general moment lower bound. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨t, ht, hKt, hbound⟩ := density_small_zero
  have h := hc 3 (by norm_num) density density_integrable density_nonneg density_zero
    density_mass density_fourth_integrable density_curvature density_unique_zero t ht hKt
  exact (not_lt_of_ge hbound) h

end D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation
