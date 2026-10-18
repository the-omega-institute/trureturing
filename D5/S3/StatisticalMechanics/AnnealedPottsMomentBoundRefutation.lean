/- GID: D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.claim; result=D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation.result; claim=D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation.claim
   digest: A two-block density tests the general annealed Potts moment lower bound. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay

/-! The functions use Lebesgue integration against a density on the real line.
The uniqueness condition in the proposed inequality is part of the claim. -/

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

/-- The general lower inequality in equation (84), with uniqueness explicit. -/
def claim : Prop :=
  ∀ (q : ℝ), 2 < q → ∀ f : ℝ → ℝ,
    Integrable f →
    (∀ w, 0 ≤ f w) →
    (∀ w, w ≤ 0 → f w = 0) →
    (∫ w, f w) = 1 →
    Integrable (fun w => w ^ 4 * f w) →
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

private lemma g2_positive {x : ℝ} (hx : x < Real.log 2) : 0 < g2 x := by
  have he : Real.exp x < 2 := (Real.lt_log_iff_exp_lt (by norm_num)).1 hx
  exact div_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (sub_pos.mpr he))
    (by positivity)

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

private lemma F2_middle_negative :
    ∀ t ∈ Icc (9 / 50 : ℝ) (7 / 10), averaged g2 3 t < 0 := by
  sorry

private lemma F2_tail_negative {t : ℝ} (ht : 7 / 10 ≤ t) : averaged g2 3 t < 0 := by
  apply div_neg_of_neg_of_pos ?_ (by rw [density_moments.1]; norm_num)
  apply weighted_density_negative _ (by fun_prop)
  intro w hw
  have hw0 : 0 < w := by linarith [hw.1]
  have hx : Real.log 2 < t * w := by
    have hlog := Real.log_two_lt_d9
    nlinarith [hw.1]
  exact mul_neg_of_pos_of_neg (pow_pos hw0 _) (g2_negative hx)

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

private lemma K_positive_test : 0 < K density 3 (6931 / 50000) := by
  sorry

private lemma test_below_bound :
    (6931 / 50000 : ℝ) < 2 * (moment density 3 / moment density 4) * Real.log (3 - 1) := by
  rw [density_moments.2.1, density_moments.2.2]
  norm_num
  nlinarith [Real.log_two_gt_d9]

private lemma density_small_zero :
    ∃ t : ℝ, 0 < t ∧ K density 3 t = 0 ∧
      t ≤ 2 * (moment density 3 / moment density 4) * Real.log (3 - 1) := by
  have hc : Continuous (averaged g2 3) :=
    continuous_iff_continuousAt.2 fun t => (F2_deriv t).continuousAt
  obtain ⟨a, ha, hazero⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 9 / 50)
    hc.continuousOn ⟨(F2_middle_negative (9 / 50) (by norm_num)).le, F2_at_zero.le⟩
  have ha0 : 0 < a := by
    have hne : a ≠ 0 := by intro h; subst a; linarith [F2_at_zero]
    exact lt_of_le_of_ne ha.1 (Ne.symm hne)
  let d : ℝ := min (a / 2) (6931 / 100000)
  have hd0 : 0 < d := lt_min (by positivity) (by norm_num)
  have hda : d < a := (min_le_left _ _).trans_lt (by linarith)
  have hdT : d < 6931 / 50000 := (min_le_right _ _).trans_lt (by norm_num)
  have hpos : ∀ t ∈ Ioo 0 d, 0 < averaged g2 3 t := by
    intro t ht
    have hta : t < a := ht.2.trans hda
    have h := F2_strictAnti ⟨ht.1.le, (hta.trans_le ha.2).le⟩ ha hta
    rwa [hazero] at h
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
    density_mass density_fourth_integrable density_unique_zero t ht hKt
  exact (not_lt_of_ge hbound) h

end D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation
