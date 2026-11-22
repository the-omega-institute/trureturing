/- GID: D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedBIntegerClock
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: The perturbed exact integer clock has a unique large root near the unperturbed root. -/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The late roots of the original inverse clock with a fixed real perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock

open Real Filter Set
open scoped Topology

/-- The unperturbed clock price at log scale `L`. -/
def basePrice (L : ℝ) : ℝ := log 2 * exp (-L) / L

/-- The full price after equation (19) of the fixed-clock construction. -/
def price (ε B L : ℝ) : ℝ :=
  log 2 * exp (-L) / L - B * exp (-(1 + ε) * L) * L ^ 4

private def clockPower (e : ℤ) : ℝ := (2 : ℝ) ^ (e + 2 : ℤ)

/-- The exact price for integer height `e`. -/
def targetPrice (e : ℤ) : ℝ := log (1 + 1 / ((2 : ℝ) ^ (e + 2 : ℤ) - 2))

/-- The original logarithmic inverse clock on the positive-price branch. -/
def inverseClock (ε B L : ℝ) : ℝ :=
  log (2 + 1 / (exp (price ε B L) - 1)) / log 2 - 2

private theorem logTwo_pos : 0 < log 2 := log_pos (by norm_num)

private theorem clockPower_eq_exp (e : ℤ) :
    clockPower e = exp (log 2 * ((e : ℝ) + 2)) := by
  unfold clockPower
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
  push_cast
  rfl

private theorem clockDen_pos {e : ℤ} (he : 0 ≤ e) : 0 < clockPower e - 2 := by
  have hcast : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have harg : log 2 < log 2 * ((e : ℝ) + 2) := by
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left (show (1 : ℝ) < (e : ℝ) + 2 by linarith only [hcast]) logTwo_pos
  rw [clockPower_eq_exp]
  apply sub_pos.mpr
  calc
    (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
    _ < _ := exp_lt_exp.mpr harg

theorem targetPrice_pos {e : ℤ} (he : 0 ≤ e) : 0 < targetPrice e := by
  change 0 < log (1 + 1 / (clockPower e - 2))
  exact log_pos (lt_add_of_pos_right _ (one_div_pos.mpr (clockDen_pos he)))

theorem targetPrice_tendsto_zero : Tendsto targetPrice atTop (𝓝 0) := by
  have hshift : Tendsto (fun e : ℤ => (e : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_intCast_atTop_atTop
  have hpow : Tendsto clockPower atTop atTop :=
    (tendsto_exp_atTop.comp (Tendsto.const_mul_atTop logTwo_pos hshift)).congr
      (fun e => (clockPower_eq_exp e).symm)
  have hden : Tendsto (fun e => clockPower e - 2) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(2 : ℝ)) hpow
  have harg : Tendsto (fun e => 1 + 1 / (clockPower e - 2)) atTop (𝓝 1) := by
    simpa only [one_div, Pi.inv_apply, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add hden.inv_tendsto_atTop
  change Tendsto (fun e => log (1 + 1 / (clockPower e - 2))) atTop (𝓝 0)
  simpa only [log_one] using harg.log one_ne_zero

/-- At a nonnegative integer height and positive price, the two exact clock equations agree. -/
theorem inverseClock_eq_iff {ε B L : ℝ} {e : ℤ} (he : 0 ≤ e)
    (ha : 0 < price ε B L) :
    inverseClock ε B L = (e : ℝ) ↔ price ε B L = targetPrice e := by
  let a := price ε B L
  let d := clockPower e - 2
  have hd : 0 < d := clockDen_pos he
  have hExp : 0 < exp a - 1 := sub_pos.mpr (one_lt_exp_iff.mpr ha)
  have harg : 0 < 2 + 1 / (exp a - 1) :=
    add_pos (by norm_num) (one_div_pos.mpr hExp)
  have htargetArg : 0 < 1 + 1 / d := add_pos zero_lt_one (one_div_pos.mpr hd)
  have hLog : log (clockPower e) = log 2 * ((e : ℝ) + 2) := by
    rw [clockPower_eq_exp, log_exp]
  constructor
  · intro h
    change log (2 + 1 / (exp a - 1)) / log 2 - 2 = (e : ℝ) at h
    have hdiv : log (2 + 1 / (exp a - 1)) / log 2 = (e : ℝ) + 2 := by
      linarith only [h]
    have hlogs : log (2 + 1 / (exp a - 1)) = log (clockPower e) := by
      rw [hLog, mul_comm (log 2)]
      exact (div_eq_iff logTwo_pos.ne').mp hdiv
    have heq : 2 + 1 / (exp a - 1) = clockPower e :=
      log_injOn_pos harg
        (show 0 < clockPower e from (by norm_num : (0 : ℝ) < 2).trans (sub_pos.mp hd)) hlogs
    have hinv : 1 / (exp a - 1) = d := by
      dsimp only [d]
      linarith only [heq]
    have hsub : exp a - 1 = 1 / d := by
      simpa only [one_div, inv_inv] using congrArg (fun x : ℝ => x⁻¹) hinv
    change a = log (1 + 1 / d)
    rw [show 1 + 1 / d = exp a by linarith only [hsub], log_exp]
  · intro h
    change a = log (1 + 1 / d) at h
    have hexp : exp a = 1 + 1 / d := by rw [h, exp_log htargetArg]
    have hsub : exp a - 1 = 1 / d := by linarith only [hexp]
    have hinv : 1 / (exp a - 1) = d := by simp only [hsub, one_div, inv_inv]
    change log (2 + 1 / (exp a - 1)) / log 2 - 2 = (e : ℝ)
    rw [hinv, show 2 + d = clockPower e by dsimp only [d]; ring,
      hLog, mul_comm (log 2), mul_div_cancel_right₀ _ logTwo_pos.ne', add_sub_cancel_right]

private theorem basePrice_pos {L : ℝ} (hL : 0 < L) : 0 < basePrice L :=
  div_pos (mul_pos logTwo_pos (exp_pos _)) hL

private theorem basePrice_eq_iff {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    basePrice L = t ↔ L * exp L = log 2 / t := by
  have hprod : L * exp L ≠ 0 := (mul_pos hL (exp_pos _)).ne'
  have hbase : basePrice L = log 2 / (L * exp L) := by
    unfold basePrice
    rw [exp_neg]
    field_simp [hL.ne', (exp_pos L).ne'] <;> ring
  rw [hbase, div_eq_iff hprod, eq_div_iff ht.ne', mul_comm t (L * exp L)]
  exact eq_comm

private theorem mul_exp_strictMonoOn :
    StrictMonoOn (fun L : ℝ => L * exp L) (Ici 0) := by
  intro x _ y hy hxy
  exact (mul_lt_mul_of_pos_right hxy (exp_pos x)).trans_le
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hxy.le) hy)

private theorem exists_reference (e : ℤ) :
    ∃ L : ℝ, 0 < L ∧ (0 ≤ e → basePrice L = targetPrice e) := by
  by_cases he : 0 ≤ e
  · let m := log 2 / targetPrice e
    have hm : 0 < m := div_pos logTwo_pos (targetPrice_pos he)
    have hmem : m ∈ Icc ((0 : ℝ) * exp 0) (m * exp m) :=
      ⟨by simpa only [zero_mul] using hm.le,
        le_mul_of_one_le_right hm.le (one_le_exp_iff.mpr hm.le)⟩
    have hcont : Continuous (fun L : ℝ => L * exp L) := continuous_id.mul continuous_exp
    obtain ⟨L, hL, hEq⟩ := intermediate_value_Icc hm.le hcont.continuousOn hmem
    have hLne : L ≠ 0 := by
      intro hz
      have hmz : m = 0 := by simpa only [hz, zero_mul] using hEq.symm
      exact hm.ne' hmz
    have hLpos : 0 < L := lt_of_le_of_ne hL.1 (Ne.symm hLne)
    exact ⟨L, hLpos, fun _ => (basePrice_eq_iff hLpos (targetPrice_pos he)).2 hEq⟩
  · exact ⟨1, zero_lt_one, fun h => (he h).elim⟩

/-- The positive unperturbed root for each nonnegative height. -/
def reference (e : ℤ) : ℝ := Classical.choose (exists_reference e)

theorem reference_pos (e : ℤ) : 0 < reference e := (Classical.choose_spec (exists_reference e)).1

theorem reference_price (ε : ℝ) {e : ℤ} (he : 0 ≤ e) :
    price ε 0 (reference e) = targetPrice e := by
  unfold price
  simp only [zero_mul, sub_zero]
  exact (Classical.choose_spec (exists_reference e)).2 he

theorem reference_tendsto : Tendsto reference atTop atTop := by
  apply tendsto_atTop.mpr
  intro c
  let r := max c 1
  have hr : 0 < r := zero_lt_one.trans_le (le_max_right c 1)
  have hm : 0 < r * exp r := mul_pos hr (exp_pos _)
  have hsmall : 0 < log 2 / (r * exp r) := div_pos logTwo_pos hm
  filter_upwards [targetPrice_tendsto_zero.eventually (eventually_lt_nhds hsmall),
    eventually_ge_atTop (0 : ℤ)] with e heSmall he
  have ht := targetPrice_pos he
  have hbase : basePrice (reference e) = targetPrice e :=
    (Classical.choose_spec (exists_reference e)).2 he
  have hEq := (basePrice_eq_iff (reference_pos e) ht).mp hbase
  have hprod : r * exp r < reference e * exp (reference e) := by
    rw [hEq]
    exact (lt_div_iff₀ ht).mpr
      (by simpa only [mul_comm] using (lt_div_iff₀ hm).mp heSmall)
  have hlt : r < reference e :=
    (mul_exp_strictMonoOn.lt_iff_lt hr.le (reference_pos e).le).mp hprod
  exact (le_max_left c 1).trans hlt.le

private def decay (ε : ℝ) (n : ℕ) (L : ℝ) : ℝ := exp (-ε * L) * L ^ n

private theorem decay_tendsto_zero {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Tendsto (decay ε n) atTop (𝓝 0) := by
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) ε hε).congr fun x => ?_
  simp only [decay, Real.rpow_natCast, mul_comm]

private def relativeFactor (ε B L : ℝ) : ℝ := 1 - (B / log 2) * decay ε 5 L

private theorem exp_split (ε L : ℝ) : exp (-(1 + ε) * L) = exp (-L) * exp (-ε * L) := by
  rw [show -(1 + ε) * L = -L + -ε * L by ring, exp_add]

private theorem price_eq_mul_factor {ε B L : ℝ} (hL : 0 < L) :
    price ε B L = basePrice L * relativeFactor ε B L := by
  unfold price basePrice relativeFactor decay
  rw [exp_split]
  field_simp [hL.ne', logTwo_pos.ne'] <;> ring

private theorem factor_tendsto_one {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    Tendsto (relativeFactor ε B) atTop (𝓝 1) := by
  change Tendsto (fun L : ℝ => 1 - (B / log 2) * decay ε 5 L) atTop (𝓝 1)
  simpa only [mul_zero, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((decay_tendsto_zero hε 5).const_mul (B / log 2))

private def derivativeFactor (ε B L : ℝ) : ℝ :=
  -(1 + 1 / L) + (B / log 2) * ((1 + ε) * decay ε 5 L - 4 * decay ε 4 L)

private theorem hasDerivAt_price {ε B L : ℝ} (hL : 0 < L) :
    HasDerivAt (price ε B) (basePrice L * derivativeFactor ε B L) L := by
  have hb := ((hasDerivAt_neg' L).exp.const_mul (log 2)).fun_div (hasDerivAt_id' L) hL.ne'
  have hp := (((hasDerivAt_const_mul (x := L) (-(1 + ε))).exp.const_mul B).mul
    (hasDerivAt_pow 4 L))
  apply (hb.sub hp).congr_deriv
  dsimp only [basePrice, derivativeFactor, decay]
  rw [exp_split]
  field_simp [hL.ne', logTwo_pos.ne'] <;> ring

private theorem derivativeFactor_tendsto {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    Tendsto (derivativeFactor ε B) atTop (𝓝 (-1)) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hc := (((decay_tendsto_zero hε 5).const_mul (1 + ε)).sub
    ((decay_tendsto_zero hε 4).const_mul (4 : ℝ))).const_mul (B / log 2)
  change Tendsto (fun L : ℝ =>
    -(1 + 1 / L) + (B / log 2) * ((1 + ε) * decay ε 5 L - 4 * decay ε 4 L)) atTop (𝓝 (-1))
  simpa only [one_div, add_zero, mul_zero, sub_zero] using
    ((tendsto_const_nhds (x := (1 : ℝ))).add hi).neg.add hc

private theorem exists_price_strictAntiOn {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ StrictAntiOn (price ε B) (Ici R) := by
  have hneg : ∀ᶠ L : ℝ in atTop, derivativeFactor ε B L < 0 :=
    (derivativeFactor_tendsto hε B).eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨r, hr⟩ := eventually_atTop.mp hneg
  let R := max r 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right r 1)
  have hcont : ContinuousOn (price ε B) (Ici R) := by
    intro x hx
    exact (hasDerivAt_price (hR.trans_le hx)).continuousAt.continuousWithinAt
  refine ⟨R, hR, strictAntiOn_of_deriv_neg (convex_Ici R) hcont ?_⟩
  intro x hx
  have hxR : R ≤ x := interior_subset hx
  rw [(hasDerivAt_price (hR.trans_le hxR)).deriv]
  exact mul_neg_of_pos_of_neg (basePrice_pos (hR.trans_le hxR))
    (hr x ((le_max_left r 1).trans hxR))

private theorem basePrice_add (r t : ℝ) :
    basePrice (r + t) = exp (-t) * (log 2 * exp (-r) / (r + t)) := by
  unfold basePrice
  rw [show -(r + t) = -t + -r by ring, exp_add]
  ring

private theorem price_bracket {ε B r : ℝ} (hr : 0 < r - 1)
    (hlo : exp (-1) < relativeFactor ε B (r - 1))
    (hhi : relativeFactor ε B (r + 1) < exp 1) :
    price ε B (r + 1) < basePrice r ∧ basePrice r < price ε B (r - 1) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr1 : 0 < r + 1 := by linarith only [hr]
  have hnum : 0 ≤ log 2 * exp (-r) := (mul_pos logTwo_pos (exp_pos _)).le
  have hleft : exp 1 * basePrice r ≤ basePrice (r - 1) := by
    rw [sub_eq_add_neg, basePrice_add, neg_neg]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum hr (by linarith))
      (exp_pos _).le
  have hright : basePrice (r + 1) ≤ exp (-1) * basePrice r := by
    rw [basePrice_add]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum hr0 (by linarith))
      (exp_pos _).le
  have hexp : exp 1 * exp (-1) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  constructor
  · rw [price_eq_mul_factor hr1, mul_comm (basePrice (r + 1))]
    calc
      _ < exp 1 * basePrice (r + 1) := mul_lt_mul_of_pos_right hhi (basePrice_pos hr1)
      _ ≤ exp 1 * (exp (-1) * basePrice r) := mul_le_mul_of_nonneg_left hright (exp_pos _).le
      _ = basePrice r := by rw [← mul_assoc, hexp, one_mul]
  · rw [price_eq_mul_factor hr, mul_comm (basePrice (r - 1))]
    calc
      basePrice r = exp (-1) * (exp 1 * basePrice r) := by
        rw [← mul_assoc, mul_comm (exp (-1)) (exp 1), hexp, one_mul]
      _ ≤ exp (-1) * basePrice (r - 1) := mul_le_mul_of_nonneg_left hleft (exp_pos _).le
      _ < _ := mul_lt_mul_of_pos_right hlo (basePrice_pos hr)

private theorem eventually_bracketed_root {ε : ℝ} (hε : 0 < ε) (B R : ℝ) (hR : 0 < R) :
    ∀ᶠ e : ℤ in atTop, ∃ L : ℝ,
      R ≤ L ∧ price ε B L = targetPrice e ∧ |L - reference e| ≤ 1 := by
  have hminus : Tendsto (fun e => reference e - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) reference_tendsto
  have hplus : Tendsto (fun e => reference e + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 reference_tendsto
  have hexpLow : exp (-1) < 1 := calc
    exp (-1) < exp 0 := exp_lt_exp.mpr (by norm_num)
    _ = 1 := exp_zero
  have hexpHigh : 1 < exp 1 := one_lt_exp_iff.mpr zero_lt_one
  filter_upwards [eventually_ge_atTop (0 : ℤ), hminus.eventually_ge_atTop R,
    ((factor_tendsto_one hε B).comp hminus).eventually (eventually_gt_nhds hexpLow),
    ((factor_tendsto_one hε B).comp hplus).eventually (eventually_lt_nhds hexpHigh)]
    with e he hle hlo hhi
  let r := reference e
  have hr : 0 < r - 1 := hR.trans_le hle
  obtain ⟨hleft, hright⟩ := price_bracket hr hlo hhi
  have hbase : basePrice r = targetPrice e :=
    (Classical.choose_spec (exists_reference e)).2 he
  rw [hbase] at hleft hright
  have hcont : ContinuousOn (price ε B) (Icc (r - 1) (r + 1)) := by
    intro x hx
    exact (hasDerivAt_price (hr.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨L, hL, hEq⟩ := intermediate_value_Icc' (by linarith : r - 1 ≤ r + 1) hcont
    (show targetPrice e ∈ Icc (price ε B (r + 1)) (price ε B (r - 1)) from ⟨hleft.le, hright.le⟩)
  have hLlo : r - 1 ≤ L := hL.1
  have hLhi : L ≤ r + 1 := hL.2
  refine ⟨L, hle.trans hLlo, hEq, abs_le.mpr ⟨?_, ?_⟩⟩
  · change -1 ≤ L - r
    linarith only [hLlo]
  · change L - r ≤ 1
    linarith only [hLhi]

private theorem exists_large_roots {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ L : ℤ → ℝ, Tendsto L atTop atTop ∧ ∃ R : ℝ, 0 < R ∧
      ∀ᶠ e : ℤ in atTop,
        R ≤ L e ∧ price ε B (L e) = targetPrice e ∧ |L e - reference e| ≤ 1 ∧
          ∀ x : ℝ, R ≤ x → price ε B x = targetPrice e → x = L e := by
  classical
  obtain ⟨R, hR, hanti⟩ := exists_price_strictAntiOn hε B
  let Good (e : ℤ) (x : ℝ) := R ≤ x ∧ price ε B x = targetPrice e ∧ |x - reference e| ≤ 1
  let L (e : ℤ) : ℝ := if h : ∃ x, Good e x then Classical.choose h else 1
  have hgood : ∀ᶠ e in atTop, Good e (L e) :=
    (eventually_bracketed_root hε B R hR).mono fun e he => by
      change ∃ x, Good e x at he
      simpa only [L, dif_pos he] using (Classical.choose_spec he)
  have hT : Tendsto L atTop atTop := by
    apply tendsto_atTop.mpr
    intro c
    filter_upwards [hgood, reference_tendsto.eventually_ge_atTop (c + 1)] with e he hc
    have hlower := (abs_le.mp he.2.2).1
    linarith only [hc, hlower]
  refine ⟨L, hT, R, hR, ?_⟩
  filter_upwards [hgood] with e he
  exact ⟨he.1, he.2.1, he.2.2, fun x hx hEq => hanti.injOn hx he.1 (hEq.trans he.2.1.symm)⟩

/-- For fixed `B` the clock eventually follows the unique root above a fixed positive
threshold. Its reference is the actual `B = 0` clock. -/
theorem exists_fixedB_integerClock {ε : ℝ} (hε : 0 < ε) :
    ∃ clock : ℝ → ℤ → ℝ, clock 0 = reference ∧
      ∀ B : ℝ, Tendsto (clock B) atTop atTop ∧ ∃ R : ℝ, 0 < R ∧
        ∀ᶠ e : ℤ in atTop,
          R ≤ clock B e ∧ price ε B (clock B e) = targetPrice e ∧
          inverseClock ε B (clock B e) = (e : ℝ) ∧ |clock B e - clock 0 e| ≤ 1 ∧
            ∀ x : ℝ, R ≤ x → price ε B x = targetPrice e → x = clock B e := by
  classical
  let clock (B : ℝ) : ℤ → ℝ :=
    if B = 0 then reference else Classical.choose (exists_large_roots hε B)
  have hzero : clock 0 = reference := by simp [clock]
  refine ⟨clock, hzero, ?_⟩
  intro B
  have hlarge : Tendsto (clock B) atTop atTop ∧ ∃ R : ℝ, 0 < R ∧
      ∀ᶠ e : ℤ in atTop,
        R ≤ clock B e ∧ price ε B (clock B e) = targetPrice e ∧
        |clock B e - reference e| ≤ 1 ∧
          ∀ x : ℝ, R ≤ x → price ε B x = targetPrice e → x = clock B e := by
    by_cases hB : B = 0
    · subst B
      rw [hzero]
      obtain ⟨R, hR, hanti⟩ := exists_price_strictAntiOn hε 0
      refine ⟨reference_tendsto, R, hR, ?_⟩
      filter_upwards [eventually_ge_atTop (0 : ℤ), reference_tendsto.eventually_ge_atTop R]
        with e he hRe
      have hprice := reference_price ε he
      exact ⟨hRe, hprice, by simp, fun x hx hEq => hanti.injOn hx hRe (hEq.trans hprice.symm)⟩
    · simpa only [clock, if_neg hB] using (Classical.choose_spec (exists_large_roots hε B))
  obtain ⟨hT, R, hR, hsol⟩ := hlarge
  refine ⟨hT, R, hR, ?_⟩
  filter_upwards [hsol, eventually_ge_atTop (0 : ℤ)] with e he he0
  have hpos : 0 < price ε B (clock B e) := by rw [he.2.1]; exact targetPrice_pos he0
  refine ⟨he.1, he.2.1, (inverseClock_eq_iff he0 hpos).2 he.2.1, ?_, he.2.2.2⟩
  rw [hzero]
  exact he.2.2.1

end D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
