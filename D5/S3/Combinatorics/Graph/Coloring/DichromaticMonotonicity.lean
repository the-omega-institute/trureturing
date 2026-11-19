/- GID: D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive singleton-split transfers give real dichromatic monotonicity. -/

import D5.S3.Combinatorics.Graph.Coloring.DichromaticPartitionExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Singleton-split balance and Crew et al.'s dichromatic monotonicity conjecture. -/

namespace D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity

namespace CrewSingletonSplit

open MeasureTheory Set
open scoped BigOperators

noncomputable section

local notation "fall" => (fun (x : ℝ) (k : ℕ) => Polynomial.eval x (descPochhammer ℝ k))

/-- The weight of a marked singleton split. The finset indexes the other blocks. -/
private def weight {ι : Type*} (s : Finset ι) (b : ι → ℕ) (r : ℕ) (x : ℝ) : ℝ :=
  (descPochhammer ℝ s.card).eval (x - 1) -
    ∑ I ∈ s.powerset,
      (-1 : ℝ) ^ I.card * (I.card.factorial : ℝ) * (descPochhammer ℝ (s.card - I.card)).eval x /
        ((r + ∑ i ∈ I, b i : ℕ) : ℝ)

private theorem beta_moment {d : ℝ} (hd : 0 < d) (j : ℕ) :
    (∫ v in (0 : ℝ)..1, v ^ j * (1 - v) ^ (d - 1)) =
      (j.factorial : ℝ) / ∏ i ∈ Finset.range (j + 1), (d + (i : ℝ)) := by
  apply Complex.ofReal_injective
  have hb := Complex.betaIntegral_eval_nat_add_one_right
    (u := (d : ℂ)) (by simpa using hd) j
  rw [Complex.betaIntegral_symm] at hb
  push_cast
  rw [← hb, Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hv
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_cpow (sub_nonneg.mpr hv.2)]
  push_cast
  rw [add_sub_cancel_right, Complex.cpow_natCast]

private theorem falling_moment {x : ℝ} {k j : ℕ} (hj : j ≤ k) (hd : 0 < x - k) :
    fall x (k + 1) * (∫ v in (0 : ℝ)..1, v ^ j * (1 - v) ^ (x - k - 1)) =
      (j.factorial : ℝ) * fall x (k - j) := by
  have hsplit : k - j + (j + 1) = k + 1 := by omega
  have hfactor :
      fall x (k + 1) =
        fall x (k - j) * ∏ i ∈ Finset.range (j + 1), (x - k + (i : ℝ)) := by
    simp only [descPochhammer_eval_eq_prod_range]
    conv_lhs => rw [← hsplit, Finset.prod_range_add]
    congr 1
    rw [← Finset.prod_range_reflect (fun i : ℕ => x - k + (i : ℝ)) (j + 1)]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hk : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := Nat.cast_sub hj
    have hr : ((j + 1 - 1 - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
      simpa using (Nat.cast_sub hi' : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ))
    rw [Nat.cast_add, hk, hr]
    ring
  rw [beta_moment hd, hfactor]
  have hp : 0 < ∏ i ∈ Finset.range (j + 1), (x - k + (i : ℝ)) := by
    exact Finset.prod_pos fun i _ => add_pos_of_pos_of_nonneg hd (Nat.cast_nonneg i)
  field_simp [hp.ne']

private theorem factor_bound {u v : ℝ} (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) (h : ℕ) :
    (1 - v) ^ h * (1 - v * u ^ (h + 1)) ≤ (1 - v * u) ^ (h + 1) := by
  have hvu : 0 ≤ 1 - v * u := sub_nonneg.mpr ((mul_le_mul_of_nonneg_left hu.2 hv.1).trans (by simpa using hv.2))
  induction h with
  | zero => simp
  | succ h ih =>
    have hstep : (1 - v) * (1 - v * u ^ (h + 1 + 1)) ≤
        (1 - v * u) * (1 - v * u ^ (h + 1)) := by
      apply sub_nonneg.mp
      calc
        _ = v * (1 - u) * (1 - u ^ (h + 1)) := by rw [pow_succ u (h + 1)]; ring
        _ ≥ 0 := mul_nonneg (mul_nonneg hv.1 (sub_nonneg.mpr hu.2))
          (sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2))
    calc
      _ = (1 - v) ^ h * ((1 - v) * (1 - v * u ^ (h + 1 + 1))) := by
        rw [pow_succ (1 - v) h, mul_assoc]
      _ ≤ (1 - v) ^ h * ((1 - v * u) * (1 - v * u ^ (h + 1))) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hv.2) _)
      _ = ((1 - v) ^ h * (1 - v * u ^ (h + 1))) * (1 - v * u) := by ring
      _ ≤ (1 - v * u) ^ (h + 1) * (1 - v * u) := mul_le_mul_of_nonneg_right ih hvu
      _ = _ := (pow_succ _ _).symm

private theorem product_bound {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    {x u v : ℝ} (hb : ∀ i ∈ s, 1 ≤ b i)
    (hx : (∑ i ∈ s, (b i : ℝ)) + 1 ≤ x) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    (1 - v) ^ (x - s.card - 1) * (∏ i ∈ s, (1 - v * u ^ b i)) ≤
      (1 - v * u) ^ (x - 1) := by
  let h : ℕ := ∑ i ∈ s, (b i - 1)
  let m : ℕ := ∑ i ∈ s, b i
  let q : ℝ := x - (m : ℝ) - 1
  have hm : h + s.card = m := by
    dsimp [h, m]
    have hc : (∑ _ ∈ s, (1 : ℕ)) = s.card := by simp
    rw [← hc, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by have := hb i hi; omega
  have hmR : (h : ℝ) + (s.card : ℝ) = (m : ℝ) := by exact_mod_cast hm
  have hq : 0 ≤ q := by
    dsimp [q, m]
    push_cast
    linarith
  have hv' : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
  have hbase : 1 - v ≤ 1 - v * u := by
    have := mul_le_mul_of_nonneg_left hu.2 hv.1
    linarith
  have hvu : 0 ≤ 1 - v * u := hv'.trans hbase
  have hfactor_nonneg (i : ι) : 0 ≤ 1 - v * u ^ b i := by
    have hpow := pow_le_one₀ hu.1 hu.2 (n := b i)
    have := mul_le_mul_of_nonneg_left hpow hv.1
    linarith [hv.2]
  have hprod :
      (1 - v) ^ h * (∏ i ∈ s, (1 - v * u ^ b i)) ≤ (1 - v * u) ^ m := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀
    · intro i _
      exact mul_nonneg (pow_nonneg hv' _) (hfactor_nonneg i)
    · intro i hi
      have he : b i - 1 + 1 = b i := by have := hb i hi; omega
      simpa only [he] using factor_bound hu hv (b i - 1)
  have hqv : (1 - v) ^ q ≤ (1 - v * u) ^ q := Real.rpow_le_rpow hv' hbase hq
  have hleft : x - (s.card : ℝ) - 1 = q + (h : ℝ) := by dsimp [q]; linarith
  have hright : x - 1 = q + (m : ℝ) := by dsimp [q]; ring
  rw [hleft, hright, Real.rpow_add_of_nonneg hv' hq (Nat.cast_nonneg h),
    Real.rpow_add_of_nonneg hvu hq (Nat.cast_nonneg m),
    Real.rpow_natCast, Real.rpow_natCast, mul_assoc]
  exact mul_le_mul hqv hprod
    (mul_nonneg (pow_nonneg hv' _) (Finset.prod_nonneg fun i _ => hfactor_nonneg i))
    (Real.rpow_nonneg hvu _)

private theorem integral_one_sub_rpow {p : ℝ} (hp : -1 < p) :
    (∫ u in (0 : ℝ)..1, (1 - u) ^ p) = 1 / (p + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ p) 1, sub_self, sub_zero,
    integral_rpow (Or.inl hp)]
  have hne : p + 1 ≠ 0 := by linarith
  simp [Real.zero_rpow hne]

private theorem scaled_inner_integral {x u : ℝ} (hx : 1 ≤ x) :
    x * u * (∫ v in (0 : ℝ)..1, (1 - v * u) ^ (x - 1)) = 1 - (1 - u) ^ x := by
  have hbase : Continuous (fun v : ℝ => 1 - v * u) := by fun_prop
  have hcont : Continuous (fun v : ℝ => (1 - v * u) ^ x) :=
    hbase.rpow_const (fun _ => Or.inr (by linarith))
  have hderiv : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => (1 - v * u) ^ x)
        (-(x * u) * (1 - v * u) ^ (x - 1)) v := by
    intro v hv
    have hb : HasDerivAt (fun v : ℝ => 1 - v * u) (-u) v := by
      simpa using ((hasDerivAt_id v).mul_const u).const_sub (1 : ℝ)
    have hd := hb.rpow_const (p := x) (Or.inr hx)
    convert hd using 1
    ring
  have hint : Continuous (fun v : ℝ => -(x * u) * (1 - v * u) ^ (x - 1)) :=
    (hbase.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hx))).const_mul _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hcont.continuousOn hderiv (hint.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at he
  simp only [one_mul, zero_mul, sub_zero, Real.one_rpow, neg_mul] at he
  linarith

private theorem integral_sum_powers {ι : Type*} (s : Finset ι) (c : ι → ℝ) (p : ι → ℕ) :
    (∫ u in (0 : ℝ)..1, ∑ i ∈ s, c i * u ^ p i) =
      ∑ i ∈ s, c i / ((p i : ℝ) + 1) := by
  have hint (i : ι) : IntervalIntegrable (fun u : ℝ => c i * u ^ p i) volume 0 1 :=
    ((continuous_id.pow (p i)).const_mul (c i)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [div_eq_mul_inv]

private def coefficient (x : ℝ) (k : ℕ) {ι : Type*} (I : Finset ι) : ℝ :=
  (-1 : ℝ) ^ I.card * (I.card.factorial : ℝ) * fall x (k - I.card)

private def kernel {ι : Type*} (s : Finset ι) (b : ι → ℕ) (x u : ℝ) : ℝ :=
  ∑ I ∈ s.powerset, coefficient x s.card I * u ^ (∑ i ∈ I, b i)

private theorem kernel_eq_scaled_integral {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    {x : ℝ} (hd : 1 ≤ x - s.card) (u : ℝ) :
    kernel s b x u = fall x (s.card + 1) *
      (∫ v in (0 : ℝ)..1, (1 - v) ^ (x - s.card - 1) * ∏ i ∈ s, (1 - v * u ^ b i)) := by
  classical
  let w : ℝ → ℝ := fun v => (1 - v) ^ (x - s.card - 1)
  let c : Finset ι → ℝ := fun I => (-1 : ℝ) ^ I.card * u ^ (∑ i ∈ I, b i)
  have hw : Continuous w :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr (sub_nonneg.mpr hd)
  have hexpand : (fun v : ℝ => w v * ∏ i ∈ s, (1 - v * u ^ b i)) =
      (fun v : ℝ => ∑ I ∈ s.powerset, c I * (v ^ I.card * w v)) := by
    funext v
    rw [Finset.prod_sub (fun _ => (1 : ℝ)) (fun i => v * u ^ b i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_pow_eq_pow_sum, c]
    ring
  have hint (I : Finset ι) :
      IntervalIntegrable (fun v : ℝ => c I * (v ^ I.card * w v)) volume 0 1 :=
    (((continuous_id.pow I.card).mul hw).const_mul (c I)).intervalIntegrable 0 1
  change kernel s b x u = fall x (s.card + 1) * (∫ v in (0 : ℝ)..1,
    w v * ∏ i ∈ s, (1 - v * u ^ b i))
  rw [hexpand, intervalIntegral.integral_finsetSum (fun I _ => hint I), Finset.mul_sum]
  unfold kernel
  apply Finset.sum_congr rfl
  intro I hI
  have hc := Finset.card_le_card (Finset.mem_powerset.mp hI)
  rw [intervalIntegral.integral_const_mul, mul_left_comm (fall x (s.card + 1)) (c I)]
  change coefficient x s.card I * u ^ (∑ i ∈ I, b i) =
    c I * (fall x (s.card + 1) * ∫ v in (0 : ℝ)..1, v ^ I.card * (1 - v) ^ (x - s.card - 1))
  rw [falling_moment hc (lt_of_lt_of_le zero_lt_one hd)]
  unfold coefficient c
  ring

private theorem falling_pos {x : ℝ} {k : ℕ} (hx : (k : ℝ) + 1 ≤ x) :
    0 < fall (x - 1) k := by
  dsimp only
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_pos
  intro i hi
  have hi' : (i : ℝ) < (k : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
  linarith

private theorem weighted_kernel_bound {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    {x : ℝ} {r : ℕ} (hr : 2 ≤ r) (hb : ∀ i ∈ s, 1 ≤ b i)
    (hx : (∑ i ∈ s, (b i : ℝ)) + 1 ≤ x) (hcard : (s.card : ℝ) + 1 ≤ x) :
    (∫ u in (0 : ℝ)..1, u ^ (r - 1) * kernel s b x u) ≤
      fall (x - 1) s.card * (x / (x + 1)) := by
  have hx1 : 1 ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) s.card]
  have hd : 1 ≤ x - s.card := by linarith
  have hfall := falling_pos hcard
  have hnorm : fall x (s.card + 1) = x * fall (x - 1) s.card := by
    dsimp only
    rw [descPochhammer_succ_left]
    simp
  have hkernel : Continuous (kernel s b x) := by
    unfold kernel
    fun_prop
  have hleft : Continuous (fun u : ℝ => u ^ (r - 1) * kernel s b x u) :=
    (continuous_id.pow (r - 1)).mul hkernel
  have hpow : Continuous (fun u : ℝ => (1 - u) ^ x) :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr (by linarith)
  have hright : Continuous (fun u : ℝ => fall (x - 1) s.card * (1 - (1 - u) ^ x)) :=
    (continuous_const.sub hpow).const_mul _
  have hcompare : (∫ u in (0 : ℝ)..1, u ^ (r - 1) * kernel s b x u) ≤
      (∫ u in (0 : ℝ)..1, fall (x - 1) s.card * (1 - (1 - u) ^ x)) := by
    apply intervalIntegral.integral_mono_on zero_le_one (hleft.intervalIntegrable 0 1)
      (hright.intervalIntegrable 0 1)
    intro u hu
    have hl : Continuous (fun v : ℝ =>
        (1 - v) ^ (x - s.card - 1) * ∏ i ∈ s, (1 - v * u ^ b i)) := by
      apply Continuous.mul
      · exact (continuous_const.sub continuous_id).rpow_const fun _ =>
          Or.inr (sub_nonneg.mpr hd)
      · fun_prop
    have hg : Continuous (fun v : ℝ => (1 - v * u) ^ (x - 1)) :=
      (show Continuous (fun v : ℝ => 1 - v * u) by fun_prop).rpow_const fun _ =>
        Or.inr (sub_nonneg.mpr hx1)
    have hinner := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (hl.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
      (fun v hv => product_bound s b hb hx hu hv)
    have hnonneg : 0 ≤ ∫ v in (0 : ℝ)..1, (1 - v * u) ^ (x - 1) := by
      apply intervalIntegral.integral_nonneg zero_le_one
      intro v hv
      apply Real.rpow_nonneg
      have := mul_le_mul_of_nonneg_left hu.2 hv.1
      linarith [hv.2]
    have hupow : u ^ (r - 1) ≤ u := by
      simpa using pow_le_pow_of_le_one hu.1 hu.2 (show 1 ≤ r - 1 by omega)
    calc
      _ = (x * fall (x - 1) s.card) * (u ^ (r - 1) *
          (∫ v in (0 : ℝ)..1, (1 - v) ^ (x - s.card - 1) * ∏ i ∈ s, (1 - v * u ^ b i))) := by
        rw [kernel_eq_scaled_integral s b hd, hnorm]
        ring
      _ ≤ (x * fall (x - 1) s.card) * (u *
          (∫ v in (0 : ℝ)..1, (1 - v * u) ^ (x - 1))) :=
        mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_left hinner (pow_nonneg hu.1 _)).trans
            (mul_le_mul_of_nonneg_right hupow hnonneg))
          (mul_nonneg (zero_le_one.trans hx1) hfall.le)
      _ = _ := by
        rw [show ∀ t : ℝ, (x * fall (x - 1) s.card) * (u * t) =
          fall (x - 1) s.card * (x * u * t) by intro t; ring, scaled_inner_integral hx1]
  refine hcompare.trans_eq ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 1)
      (hpow.intervalIntegrable 0 1), integral_one_sub_rpow (by linarith : -1 < x)]
  have hconst : (∫ _ in (0 : ℝ)..1, (1 : ℝ)) = 1 := by
    norm_num [intervalIntegral.integral_const]
  rw [hconst, show 1 - 1 / (x + 1) = x / (x + 1) by
    have hne : x + 1 ≠ 0 := by linarith
    field_simp [hne]
    ring]

private theorem weight_eq_integral {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    weight s b r x = fall (x - 1) s.card -
      ∫ u in (0 : ℝ)..1, u ^ (r - 1) * kernel s b x u := by
  have hint : (∫ u in (0 : ℝ)..1, u ^ (r - 1) * kernel s b x u) =
      ∑ I ∈ s.powerset, coefficient x s.card I / ((r + ∑ i ∈ I, b i : ℕ) : ℝ) := by
    calc
      _ = ∫ u in (0 : ℝ)..1, ∑ I ∈ s.powerset,
            coefficient x s.card I * u ^ (r - 1 + ∑ i ∈ I, b i) := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        rw [kernel, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        rw [pow_add]
        ring
      _ = ∑ I ∈ s.powerset, coefficient x s.card I /
            (((r - 1 + ∑ i ∈ I, b i : ℕ) : ℝ) + 1) :=
        integral_sum_powers s.powerset (coefficient x s.card) (fun I => r - 1 + ∑ i ∈ I, b i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro I _
        congr 1
        exact_mod_cast (show r - 1 + (∑ i ∈ I, b i) + 1 = r + ∑ i ∈ I, b i by omega)
  rw [hint]
  rfl

/-- For any finite family of positive block sizes, the marked singleton-split weight
is strictly positive and bounded below by the falling factorial divided by `x + 1`. -/
private theorem weight_bounds {ι : Type*} (s : Finset ι) (b : ι → ℕ) {r : ℕ} {x : ℝ}
    (hr : 2 ≤ r) (hb : ∀ i ∈ s, 1 ≤ b i)
    (hx : ((r + ∑ i ∈ s, b i : ℕ) : ℝ) - 1 ≤ x) :
    (descPochhammer ℝ s.card).eval (x - 1) / (x + 1) ≤ weight s b r x ∧
      0 < weight s b r x := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  push_cast at hx
  have hm : (∑ i ∈ s, (b i : ℝ)) + 1 ≤ x := by linarith
  have hc : s.card ≤ ∑ i ∈ s, b i := by
    calc
      s.card = ∑ _ ∈ s, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum hb
  have hcR : (s.card : ℝ) ≤ ∑ i ∈ s, (b i : ℝ) := by exact_mod_cast hc
  have hcard : (s.card : ℝ) + 1 ≤ x := by linarith
  have hw := weighted_kernel_bound s b hr hb hm hcard
  have hden : 0 < x + 1 := by linarith [Nat.cast_nonneg (α := ℝ) s.card]
  have hbound : fall (x - 1) s.card / (x + 1) ≤ weight s b r x := by
    rw [weight_eq_integral s b (by omega) x]
    calc
      _ = fall (x - 1) s.card - fall (x - 1) s.card * (x / (x + 1)) := by
        field_simp [hden.ne']
        ring
      _ ≤ _ := sub_le_sub_left hw _
  exact ⟨hbound, (div_pos (falling_pos hcard) hden).trans_le hbound⟩

end
end CrewSingletonSplit

namespace CrewCoefficientIdentity

open Finset Polynomial
open scoped BigOperators

noncomputable section

private theorem smeval_desc (x : ℝ) (k : ℕ) :
    (descPochhammer ℤ k).smeval x = (descPochhammer ℝ k).eval x := by
  rw [← descPochhammer_map (Int.castRingHom ℝ), eval_map, smeval_eq_sum, eval₂_eq_sum]
  unfold Polynomial.sum
  apply Finset.sum_congr rfl
  intro n _
  exact zsmul_eq_mul _ _

private theorem falling_neg_one (k : ℕ) :
    (descPochhammer ℝ k).eval (-1) = (-1 : ℝ) ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ]
    ring

private def logCoefficient (x : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then 0 else (-1 : ℝ) ^ (j - 1) * ((j - 1).factorial : ℝ) *
    (descPochhammer ℝ (k - j)).eval x

private theorem deriv_zero_falling (j : ℕ) :
    (descPochhammer ℝ j).derivative.eval 0 =
      if j = 0 then 0 else (-1 : ℝ) ^ (j - 1) * ((j - 1).factorial : ℝ) := by
  cases j with
  | zero => simp
  | succ j =>
    rw [descPochhammer_succ_left, derivative_mul]
    simp [eval_comp, falling_neg_one]

/-- Differentiating finite Vandermonde at the second variable zero gives the
signed factorial coefficient for each nonempty subset of the blocks. -/
private theorem derivative_descPochhammer_eq_sum_subsets {ι : Type*} (s : Finset ι) (x : ℝ) :
    (descPochhammer ℝ s.card).derivative.eval x =
      ∑ U ∈ s.powerset, logCoefficient x s.card U.card := by
  rw [sum_powerset_apply_card]
  let k := s.card
  have h (y : ℝ) : (descPochhammer ℝ k).eval (y + x) = ∑ i ∈ range (k + 1),
      (k.choose i : ℝ) * ((descPochhammer ℝ i).eval y * (descPochhammer ℝ (k - i)).eval x) := by
    rw [← smeval_desc, Ring.descPochhammer_smeval_add k (Commute.all y x),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [smeval_desc]
  have lhs : HasDerivAt (fun y ↦ (descPochhammer ℝ k).eval (y + x))
      ((descPochhammer ℝ k).derivative.eval x) 0 := by
    let p := descPochhammer ℝ k
    have hderiv : (p.comp (X + C x)).derivative.eval 0 = p.derivative.eval x := by
      simp [Polynomial.derivative_comp, Polynomial.eval_comp]
    have heval : (fun y ↦ (p.comp (X + C x)).eval y) = (fun y ↦ p.eval (y + x)) := by
      funext y
      simp [Polynomial.eval_comp]
    have hpoly := (p.comp (X + C x)).hasDerivAt 0
    rw [hderiv, heval] at hpoly
    exact hpoly
  have rhs : HasDerivAt (fun y ↦ ∑ i ∈ range (k + 1),
      (k.choose i : ℝ) * ((descPochhammer ℝ i).eval y * (descPochhammer ℝ (k - i)).eval x))
      (∑ i ∈ range (k + 1), (k.choose i : ℝ) * logCoefficient x k i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    convert (((descPochhammer ℝ i).hasDerivAt 0).mul_const
      ((descPochhammer ℝ (k - i)).eval x)).const_mul (k.choose i : ℝ) using 1
    by_cases hi : i = 0 <;> simp [deriv_zero_falling, logCoefficient, hi]
  simpa only [nsmul_eq_mul] using
    lhs.deriv.symm.trans ((congrArg (fun f : ℝ → ℝ ↦ deriv f 0) (funext h)).trans rhs.deriv)

private def integralCoefficient (x : ℝ) (k j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * (j.factorial : ℝ) * (descPochhammer ℝ (k - j)).eval x

private theorem sum_subsets_containing {ι A : Type*} [DecidableEq ι] [AddCommMonoid A]
    (s : Finset ι) (a : ι) (ha : a ∈ s) (f : Finset ι → A) :
    (∑ U ∈ s.powerset.filter (a ∈ ·), f U) =
      ∑ I ∈ (s.erase a).powerset, f (insert a I) := by
  refine sum_bij' (fun U _ ↦ U.erase a) (fun I _ ↦ insert a I) ?_ ?_ ?_ ?_ ?_
  · intro U hU
    obtain ⟨hU, _⟩ := mem_filter.mp hU
    exact mem_powerset.mpr (erase_subset_erase _ (mem_powerset.mp hU))
  · intro I hI
    exact mem_filter.mpr ⟨mem_powerset.mpr (insert_subset ha
      ((mem_powerset.mp hI).trans (erase_subset _ _))), mem_insert_self _ _⟩
  · intro U hU
    exact insert_erase ((mem_filter.mp hU).2)
  · intro I hI
    exact erase_insert (notMem_mono (mem_powerset.mp hI) (notMem_erase _ _))
  · intro U hU
    rw [insert_erase ((mem_filter.mp hU).2)]

/-- A subset of the remaining blocks together with one specified block can be
summed instead by selecting the full subset first and then its specified block. -/
private theorem sum_marked_subsets {ι A : Type*} [DecidableEq ι] [AddCommMonoid A]
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → Finset ι → A) :
    (∑ a ∈ s.filter p, ∑ I ∈ (s.erase a).powerset, f a (insert a I)) =
      ∑ U ∈ s.powerset, ∑ a ∈ U.filter p, f a U := by
  calc
    _ = ∑ a ∈ s.filter p, ∑ U ∈ s.powerset.filter (a ∈ ·), f a U :=
      sum_congr rfl fun a ha ↦ (sum_subsets_containing s a (mem_filter.mp ha).1 _).symm
    _ = _ := sum_comm' fun a U ↦ by
      simp only [mem_filter, mem_powerset]
      exact ⟨fun ⟨⟨_, hp⟩, hs, ha⟩ ↦ ⟨⟨ha, hp⟩, hs⟩,
        fun ⟨⟨ha, hp⟩, hs⟩ ↦ ⟨⟨hs ha, hp⟩, hs, ha⟩⟩

variable {ι : Type*} [DecidableEq ι]

local notation "fall" => (fun (x : ℝ) (k : ℕ) ↦ Polynomial.eval x (descPochhammer ℝ k))

private def groupedFraction (b : ι → ℕ) (q : ℕ) (x : ℝ) (k : ℕ) (J : Finset ι) : ℝ :=
  integralCoefficient x (k - 1) (J.card - 1) / ((q + ∑ C ∈ J, b C : ℕ) : ℝ)

private theorem sum_erase_integrals (s : Finset ι) (b : ι → ℕ) (a : ι → ℝ) (q : ℕ) (x : ℝ) :
    (∑ B ∈ s, a B * ∑ I ∈ (s.erase B).powerset,
      integralCoefficient x (s.erase B).card I.card /
        ((q + b B + ∑ C ∈ I, b C : ℕ) : ℝ)) =
    ∑ J ∈ s.powerset, (∑ B ∈ J, a B) * groupedFraction b q x s.card J := by
  calc
    _ = ∑ B ∈ s.filter (fun _ ↦ True), ∑ I ∈ (s.erase B).powerset,
        a B * groupedFraction b q x s.card (insert B I) := by
      rw [filter_true_of_mem (fun _ _ ↦ trivial)]
      apply sum_congr rfl
      intro B hB
      rw [mul_sum]
      apply sum_congr rfl
      intro I hI
      have hnot : B ∉ I := notMem_mono (mem_powerset.mp hI) (notMem_erase _ _)
      rw [groupedFraction, card_erase_of_mem hB, card_insert_of_notMem hnot,
        Nat.add_sub_cancel, sum_insert hnot, Nat.add_assoc]
    _ = _ := by
      rw [sum_marked_subsets s (fun _ ↦ True) (fun B J ↦ a B * groupedFraction b q x s.card J)]
      apply sum_congr rfl
      intro J _
      rw [filter_true_of_mem (fun _ _ ↦ trivial), sum_mul]

/-- Grouping the formal outgoing terms over all blocks gives the derivative
coefficient, with one separate constant term for each vertex. -/
private theorem all_outgoing_weight (s : Finset ι) (b : ι → ℕ) (hb : ∀ B ∈ s, 1 ≤ b B) (x : ℝ) :
    (∑ B ∈ s, (b B : ℝ) * CrewSingletonSplit.weight (s.erase B) b (b B) x) =
      ((∑ B ∈ s, b B : ℕ) : ℝ) * fall (x - 1) (s.card - 1) -
        (descPochhammer ℝ s.card).derivative.eval x := by
  classical
  rw [derivative_descPochhammer_eq_sum_subsets]
  simp only [CrewSingletonSplit.weight, mul_sub, sum_sub_distrib]
  congr 1
  · push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro B hB
    rw [card_erase_of_mem hB]
  · rw [show (∑ B ∈ s, (b B : ℝ) * ∑ I ∈ (s.erase B).powerset,
        (-1 : ℝ) ^ I.card * (I.card.factorial : ℝ) * fall x ((s.erase B).card - I.card) /
          ((b B + ∑ C ∈ I, b C : ℕ) : ℝ)) =
      ∑ J ∈ s.powerset, (∑ B ∈ J, (b B : ℝ)) * groupedFraction b 0 x s.card J by
        simpa only [integralCoefficient, zero_add] using
          sum_erase_integrals s b (fun B ↦ (b B : ℝ)) 0 x]
    apply sum_congr rfl
    intro J hJ
    by_cases h : J = ∅
    · simp [h, logCoefficient]
    have hc : J.card ≠ 0 := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)
    obtain ⟨B, hB⟩ := nonempty_iff_ne_empty.mpr h
    have hp : 0 < ∑ C ∈ J, b C :=
      lt_of_lt_of_le (hb B (mem_powerset.mp hJ hB)) (single_le_sum (fun _ _ ↦ Nat.zero_le _) hB)
    have hd : ((∑ C ∈ J, b C : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hcJ : s.card - 1 - (J.card - 1) = s.card - J.card := by
      have hj := card_le_card (mem_powerset.mp hJ)
      omega
    rw [groupedFraction, zero_add, ← Nat.cast_sum, mul_div_cancel₀ _ hd]
    simp [integralCoefficient, logCoefficient, hc, hcJ]

private theorem paired_coefficients (x : ℝ) (k j : ℕ) (hj : j ≠ 0) (hle : j ≤ k) :
    (j : ℝ) * integralCoefficient x (k - 1) (j - 1) +
      integralCoefficient x k j = 0 := by
  have hk : k - 1 - (j - 1) = k - j := by omega
  have hjs : j = (j - 1) + 1 := by omega
  have hp : (-1 : ℝ) ^ j = (-1) ^ (j - 1) * (-1) := by
    conv_lhs => rw [hjs]
    exact pow_succ _ _
  have hf : j.factorial = j * (j - 1).factorial := by
    conv_lhs => rw [hjs]
    rw [Nat.factorial_succ, ← hjs]
  rw [integralCoefficient, integralCoefficient, hk, hp, hf, Nat.cast_mul]
  ring

private theorem falling_shift (x : ℝ) (k : ℕ) :
    (k : ℝ) * fall (x - 1) (k - 1) + fall (x - 1) k = fall x k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [show k.succ - 1 = k by omega]
    have ha : fall x k.succ = x * fall (x - 1) k := by
      dsimp only
      rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp]
      simp
    rw [ha]
    dsimp only
    rw [descPochhammer_succ_eval]
    push_cast
    ring

/-- The incoming edges at a single marked singleton cancel the formal outgoing
term at that singleton. -/
private theorem singleton_incoming_cancel (s : Finset ι) (b : ι → ℕ) (x : ℝ) :
    (∑ B ∈ s, CrewSingletonSplit.weight (s.erase B) b (1 + b B) x) +
      CrewSingletonSplit.weight s b 1 x = 0 := by
  classical
  simp only [CrewSingletonSplit.weight, sum_sub_distrib]
  have hconst : (∑ B ∈ s, fall (x - 1) (s.erase B).card) = (s.card : ℝ) * fall (x - 1) (s.card - 1) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun B hB ↦ by rw [card_erase_of_mem hB]
  rw [hconst]
  have hgroup := sum_erase_integrals s b (fun _ ↦ (1 : ℝ)) 1 x
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at hgroup
  change (∑ B ∈ s, ∑ I ∈ (s.erase B).powerset,
        (-1 : ℝ) ^ I.card * (I.card.factorial : ℝ) * fall x ((s.erase B).card - I.card) /
          ((1 + b B + ∑ C ∈ I, b C : ℕ) : ℝ)) = _ at hgroup
  rw [hgroup]
  rw [sub_add_sub_comm, falling_shift, ← sum_add_distrib]
  have hsum : (∑ J ∈ s.powerset, ((J.card : ℝ) * groupedFraction b 1 x s.card J +
      integralCoefficient x s.card J.card / ((1 + ∑ C ∈ J, b C : ℕ) : ℝ))) =
      fall x s.card := by
    calc
      _ = ∑ J ∈ s.powerset, if J = ∅ then fall x s.card else 0 := by
        apply sum_congr rfl
        intro J hJ
        by_cases h : J = ∅
        · simp [h, groupedFraction, integralCoefficient]
        have hj : J.card ≠ 0 := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)
        rw [ite_eq_right h, groupedFraction, ← mul_div_assoc, ← add_div,
          paired_coefficients x _ _ hj (card_le_card (mem_powerset.mp hJ)), zero_div]
      _ = _ := by simp
  change fall x s.card - (∑ J ∈ s.powerset, ((J.card : ℝ) * groupedFraction b 1 x s.card J +
    integralCoefficient x s.card J.card / ((1 + ∑ C ∈ J, b C : ℕ) : ℝ))) = 0
  rw [hsum, sub_self]


end
end CrewCoefficientIdentity

open Classical Finset Polynomial
open D5.S3.Combinatorics.Graph.Coloring.DichromaticPartitionExpansion
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev Mark (V : Type*) [Fintype V] [DecidableEq V] :=
  {e : VertexPartition V × V // 1 < (e.1.part e.2).card}

private def split (P : VertexPartition V) (v : V) : VertexPartition V :=
  Finpartition.ofSetoid (Setoid.ker fun w ↦ (P.part w, w = v))

private theorem mem_split_part (P : VertexPartition V) (v a b : V) :
    b ∈ (split P v).part a ↔ b ∈ P.part a ∧ (a = v ↔ b = v) := by
  rw [split, Finpartition.mem_part_ofSetoid_iff_rel]
  change (P.part a, a = v) = (P.part b, b = v) ↔ _
  rw [Prod.mk.injEq, P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)]
  simp only [eq_comm (a := P.part a), eq_iff_iff]

private theorem split_le (P : VertexPartition V) (v : V) : split P v ≤ P := by
  intro B hB
  obtain ⟨a, ha⟩ := (split P v).nonempty_of_mem_parts hB
  refine ⟨P.part a, P.part_mem.mpr (mem_univ a), ?_⟩
  rw [← (split P v).part_eq_of_mem hB ha]
  exact fun _ hb ↦ ((mem_split_part P v a _).mp hb).1

private theorem split_mark_part (P : VertexPartition V) (v : V) : (split P v).part v = {v} := by
  ext b
  constructor
  · intro h
    exact mem_singleton.mpr (((mem_split_part P v v b).mp h).2.mp rfl)
  · intro h
    obtain rfl := mem_singleton.mp h
    exact (split P _).mem_part_self.mpr (mem_univ _)

private theorem split_other_part (P : VertexPartition V) {v a : V} (ha : a ≠ v) :
    (split P v).part a = (P.part a).erase v := by
  ext b
  rw [mem_split_part, mem_erase]
  simp only [ha, false_iff, and_comm]

private theorem split_parts (P : VertexPartition V) (v : V) (hv : 1 < (P.part v).card) :
    (split P v).parts = insert {v} (insert ((P.part v).erase v) (P.parts.erase (P.part v))) := by
  let Q := split P v
  have hPv := P.part_mem.mpr (mem_univ v)
  ext B
  constructor
  · intro hB
    obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB ha]
    by_cases h : a = v
    · subst a
      rw [split_mark_part]
      exact mem_insert_self _ _
    · rw [split_other_part P h]
      by_cases hpart : P.part a = P.part v
      · rw [hpart]
        exact mem_insert_of_mem (mem_insert_self _ _)
      · have hnot : v ∉ P.part a := fun hmem ↦ hpart
          ((P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mp hmem).symm
        rw [erase_eq_of_notMem hnot]
        exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr
          ⟨hpart, P.part_mem.mpr (mem_univ _)⟩))
  · intro hB
    rcases mem_insert.mp hB with rfl | hB
    · rw [← split_mark_part P v]
      exact Q.part_mem.mpr (mem_univ _)
    · rcases mem_insert.mp hB with rfl | hB
      · have hne : ((P.part v).erase v).Nonempty := by
          apply card_pos.mp
          rw [card_erase_of_mem (P.mem_part_self.mpr (mem_univ _))]
          omega
        obtain ⟨a, ha⟩ := hne
        obtain ⟨hav, haP⟩ := mem_erase.mp ha
        rw [← P.part_eq_of_mem hPv haP, ← split_other_part P hav]
        exact Q.part_mem.mpr (mem_univ _)
      · obtain ⟨hBv, hBP⟩ := mem_erase.mp hB
        obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hBP
        have haP := P.part_eq_of_mem hBP ha
        have hvB : v ∉ B := fun hvB ↦ hBv (P.part_eq_of_mem hBP hvB).symm
        have hav : a ≠ v := fun h ↦ hvB (h ▸ ha)
        rw [← erase_eq_of_notMem hvB, ← haP, ← split_other_part P hav]
        exact Q.part_mem.mpr (mem_univ _)

private theorem recover_source_parts (P : VertexPartition V) (v : V)
    (hv : 1 < (P.part v).card) :
    let Q := split P v
    let R := (P.part v).erase v
    P.parts = insert (insert v R) ((Q.parts.erase {v}).erase R) := by
  dsimp only
  let B := P.part v
  let R := B.erase v
  have hvB : v ∈ B := P.mem_part_self.mpr (mem_univ _)
  have hB : B ∈ P.parts := P.part_mem.mpr (mem_univ _)
  have hRv : v ∉ R := notMem_erase _ _
  have hsR : ({v} : Finset V) ≠ R := fun h ↦ hRv (h ▸ mem_singleton_self v)
  have hsing : ({v} : Finset V) ∉ P.parts.erase B := by
    intro h
    obtain ⟨hne, hmem⟩ := mem_erase.mp h
    exact hne (P.part_eq_of_mem hmem (mem_singleton_self v)).symm
  have hR : R ∉ P.parts.erase B := by
    intro h
    obtain ⟨hne, hmem⟩ := mem_erase.mp h
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hmem
    exact hne (P.eq_of_mem_parts hmem hB ha (mem_erase.mp ha).2)
  have hs : ({v} : Finset V) ∉ insert R (P.parts.erase B) := by
    simp only [mem_insert, hsR, hsing, or_self, not_false_eq_true]
  change P.parts = insert (insert v R) (((split P v).parts.erase {v}).erase R)
  rw [split_parts P v hv]
  change P.parts = insert (insert v R) (((insert ({v} : Finset V) (insert R
    (P.parts.erase B))).erase {v}).erase R)
  rw [erase_insert hs, erase_insert hR, insert_erase hvB, insert_erase hB]

private theorem sum_outgoing_by_blocks (P : VertexPartition V) (f : Finset V → ℝ) :
    (∑ v ∈ univ.filter (fun v ↦ 1 < (P.part v).card), f (P.part v)) =
      ∑ B ∈ P.parts.filter (fun B ↦ 1 < B.card), (B.card : ℝ) * f B := by
  rw [← Finset.sum_fiberwise_of_maps_to' (g := P.part)
    (t := P.parts.filter (fun B ↦ 1 < B.card)) (by
      intro v hv
      exact mem_filter.mpr ⟨P.part_mem.mpr (mem_univ _), (mem_filter.mp hv).2⟩)]
  apply sum_congr rfl
  intro B hB
  obtain ⟨hB, hcard⟩ := mem_filter.mp hB
  have hfilter : (univ.filter (fun v ↦ 1 < (P.part v).card)).filter
      (fun v ↦ P.part v = B) = B := by
    ext v
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ (P.part_eq_iff_mem hB).mp h.2,
      fun h ↦ by rw [(P.part_eq_iff_mem hB).mpr h]; exact ⟨hcard, rfl⟩⟩
  rw [hfilter, sum_const, nsmul_eq_mul]

private theorem recipient_avoids_mark (Q : VertexPartition V) {v : V} {R : Finset V}
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) : v ∉ R := by
  intro h
  exact (mem_erase.mp hR).1
    (Q.eq_of_mem_parts (mem_of_mem_erase hR) hv h (mem_singleton_self v))

private theorem merged_notMem_rest (Q : VertexPartition V) {v : V} {R : Finset V}
    (hv : ({v} : Finset V) ∈ Q.parts) :
    insert v R ∉ (Q.parts.erase {v}).erase R := by
  intro h
  obtain ⟨_, hne, hB⟩ := by simpa only [mem_erase] using h
  exact hne (Q.eq_of_mem_parts hB hv (mem_insert_self _ _) (mem_singleton_self _))

/-- Merge the marked singleton with the chosen distinct recipient block. -/
private def merge (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    VertexPartition V := by
  classical
  let s := (Q.parts.erase {v}).erase R
  have avoid (B : Finset V) (hB : B ∈ s) : Disjoint (insert v R) B := by
    obtain ⟨hneR, hnev, hBQ⟩ : B ≠ R ∧ B ≠ {v} ∧ B ∈ Q.parts :=
      by simpa only [s, mem_erase] using hB
    rw [Finset.disjoint_left]
    intro a ha haB
    rcases mem_insert.mp ha with rfl | haR
    · exact hnev (Q.eq_of_mem_parts hBQ hv haB (mem_singleton_self _))
    · exact hneR (Q.eq_of_mem_parts hBQ (mem_of_mem_erase hR) haB haR)
  refine ⟨insert (insert v R) s, ?_, ?_, ?_⟩
  · rw [supIndep_iff_pairwiseDisjoint]
    intro B hB C hC hne
    change Disjoint B C
    rcases mem_insert.mp hB with rfl | hB
    · exact avoid C (mem_insert.mp hC |>.resolve_left hne.symm)
    rcases mem_insert.mp hC with rfl | hC
    · exact (avoid B hB).symm
    exact Q.disjoint (mem_of_mem_erase (mem_of_mem_erase hB))
      (mem_of_mem_erase (mem_of_mem_erase hC)) hne
  · apply eq_univ_of_forall
    intro a
    obtain ⟨B, hB, ha⟩ := Q.exists_mem (mem_univ a)
    apply mem_sup.mpr
    by_cases hBv : B = {v}
    · exact ⟨insert v R, mem_insert_self _ _, mem_insert.mpr (Or.inl (mem_singleton.mp (hBv ▸ ha)))⟩
    by_cases hBR : B = R
    · exact ⟨insert v R, mem_insert_self _ _, mem_insert_of_mem (hBR ▸ ha)⟩
    exact ⟨B, mem_insert_of_mem (mem_erase.mpr ⟨hBR, mem_erase.mpr ⟨hBv, hB⟩⟩), ha⟩
  · intro hempty
    rcases mem_insert.mp hempty with he | he
    · simpa [← he] using (mem_insert_self v R)
    exact Q.ne_empty (mem_of_mem_erase (mem_of_mem_erase he)) rfl

private theorem merge_parts (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    (merge Q v R hv hR).parts =
      insert (insert v R) ((Q.parts.erase {v}).erase R) := rfl

private theorem merge_part_mark (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    (merge Q v R hv hR).part v = insert v R := by
  apply Finpartition.part_eq_of_mem
  · rw [merge_parts]
    exact mem_insert_self _ _
  · exact mem_insert_self _ _

private theorem merge_rest (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    (merge Q v R hv hR).parts.erase ((merge Q v R hv hR).part v) =
      (Q.parts.erase {v}).erase R := by
  rw [merge_part_mark, merge_parts, erase_insert (merged_notMem_rest Q hv)]

private theorem merge_mark_card (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    ((merge Q v R hv hR).part v).card = 1 + R.card := by
  rw [merge_part_mark, card_insert_of_notMem (recipient_avoids_mark Q hv hR), Nat.add_comm]

private theorem merge_residual (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    ((merge Q v R hv hR).part v).erase v = R := by
  rw [merge_part_mark, erase_insert (recipient_avoids_mark Q hv hR)]

private theorem merge_valid (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    1 < ((merge Q v R hv hR).part v).card := by
  rw [merge_mark_card]
  have := card_pos.mpr (Q.nonempty_of_mem_parts (mem_of_mem_erase hR))
  omega

private theorem split_merge (Q : VertexPartition V) (v : V) (R : Finset V)
    (hv : ({v} : Finset V) ∈ Q.parts) (hR : R ∈ Q.parts.erase {v}) :
    split (merge Q v R hv hR) v = Q := by
  apply Finpartition.ext
  rw [split_parts _ _ (merge_valid Q v R hv hR), merge_residual, merge_rest,
    insert_erase hR, insert_erase hv]

private theorem split_recipient (P : VertexPartition V) (v : V) (hv : 1 < (P.part v).card) :
    (P.part v).erase v ∈ (split P v).parts.erase {v} := by
  apply mem_erase.mpr
  refine ⟨?_, ?_⟩
  · intro h
    exact notMem_erase v (P.part v) (h ▸ mem_singleton_self v)
  · rw [split_parts _ _ hv]
    exact mem_insert_of_mem (mem_insert_self _ _)

private def edgeWeight (x : ℝ) (e : Mark V) : ℝ :=
  let B := e.val.1.part e.val.2
  CrewSingletonSplit.weight (e.val.1.parts.erase B) Finset.card B.card x

private def transfer (x : ℝ) (e : Mark V) : ℝ :=
  edgeWeight x e / x ^ Fintype.card V

private def contribution (x : ℝ) (e : Mark V) (P : VertexPartition V) : ℝ :=
  (if P = split e.val.1 e.val.2 then transfer x e else 0) -
    (if P = e.val.1 then transfer x e else 0)

private def expectation (f : VertexPartition V → ℝ) (x : ℝ) : ℝ :=
  ∑ P : VertexPartition V, partitionWeight x P * f P

private theorem weight_differentiable (P : VertexPartition V) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun t ↦ partitionWeight t P) x :=
  (((descPochhammer ℝ P.parts.card).hasDerivAt x).fun_div
    ((hasDerivAt_id x).pow (Fintype.card V)) (pow_ne_zero _ hx)).differentiableAt

private theorem deriv_weight (P : VertexPartition V) (n k : ℕ)
    (hn : Fintype.card V = n + 1) (hk : P.parts.card = k + 1) {x : ℝ} (hx : x ≠ 0) :
    deriv (fun t ↦ partitionWeight t P) x =
      ((descPochhammer ℝ (k + 1)).derivative.eval x -
        (n + 1 : ℕ) * (descPochhammer ℝ k).eval (x - 1)) / x ^ (n + 1) := by
  simp only [partitionWeight, hn, hk]
  have hd := (((descPochhammer ℝ (k + 1)).hasDerivAt x).fun_div
    ((hasDerivAt_id x).pow (n + 1)) (pow_ne_zero _ hx)).deriv
  change deriv (fun t ↦ (descPochhammer ℝ (k + 1)).eval t / t ^ (n + 1)) x = _
  simp only [Pi.pow_apply, id_eq] at hd
  rw [hd]
  have hval : (descPochhammer ℝ (k + 1)).eval x =
      x * (descPochhammer ℝ k).eval (x - 1) := by
    rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp]
    simp
  simp only [Nat.add_sub_cancel, mul_one, hval, pow_succ x n]
  have hpow : x ^ n ≠ 0 := pow_ne_zero _ hx
  field_simp

private theorem deriv_expectation (f : VertexPartition V → ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (expectation f) x =
      ∑ P : VertexPartition V, deriv (fun t ↦ partitionWeight t P) x * f P :=
  (HasDerivAt.fun_sum fun P _ ↦ ((weight_differentiable P hx).hasDerivAt.mul_const (f P))).deriv

private theorem expectation_differentiable (f : VertexPartition V → ℝ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (expectation f) x :=
  (HasDerivAt.fun_sum fun P _ ↦ ((weight_differentiable P hx).hasDerivAt.mul_const (f P))).differentiableAt

private theorem sum_contribution_mul (x : ℝ) (f : VertexPartition V → ℝ) :
    (∑ P : VertexPartition V, (∑ e : Mark V, contribution x e P) * f P) =
      ∑ e : Mark V, transfer x e * (f (split e.val.1 e.val.2) - f e.val.1) := by
  simp only [sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e _
  simp only [contribution, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', mem_univ, ite_true, mul_sub]

private theorem expectation_monotone_on
    (f : VertexPartition V → ℝ) (hf : Antitone f) (hn : 2 ≤ Fintype.card V)
    (balance : ∀ x : ℝ, (Fintype.card V : ℝ) - 1 < x →
      ∀ P : VertexPartition V,
        deriv (fun t ↦ partitionWeight t P) x = ∑ e : Mark V, contribution x e P)
    (nonnegative : ∀ x : ℝ, (Fintype.card V : ℝ) - 1 < x →
      ∀ e : Mark V, 0 ≤ transfer x e) :
    MonotoneOn (expectation f) (Set.Ici ((Fintype.card V : ℝ) - 1)) := by
  have hcard : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have positive (x : ℝ) (hx : (Fintype.card V : ℝ) - 1 ≤ x) : 0 < x := by linarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    (fun x hx ↦ ?_)
  · exact (expectation_differentiable f (positive x hx).ne').continuousAt.continuousWithinAt
  · rw [interior_Ici] at hx
    exact (expectation_differentiable f (positive x (le_of_lt hx)).ne').differentiableWithinAt
  · rw [interior_Ici] at hx
    have hx' : (Fintype.card V : ℝ) - 1 < x := hx
    rw [deriv_expectation f (positive x hx'.le).ne']
    simp_rw [balance x hx']
    rw [sum_contribution_mul]
    exact sum_nonneg fun e _ ↦ mul_nonneg (nonnegative x hx' e)
      (sub_nonneg.mpr (hf (split_le _ _)))

private theorem crew_monotone_on_of_transfer_hypotheses
    (D : Digraph V) (hn : 2 ≤ Fintype.card V)
    (balance : ∀ x : ℝ, (Fintype.card V : ℝ) - 1 < x →
      ∀ P : VertexPartition V,
        deriv (fun t ↦ partitionWeight t P) x = ∑ e : Mark V, contribution x e P)
    (nonnegative : ∀ x : ℝ, (Fintype.card V : ℝ) - 1 < x →
      ∀ e : Mark V, 0 ≤ transfer x e) :
    MonotoneOn (fun x : ℝ ↦ (dichromaticPolynomial D).eval x / x ^ Fintype.card V)
      (Set.Ici ((Fintype.card V : ℝ) - 1)) := by
  let f : VertexPartition V → ℝ := fun P ↦ if IsAcyclic D P then 1 else 0
  have hf : Antitone f := by
    intro P Q hPQ
    by_cases hQ : IsAcyclic D Q
    · simp [f, hQ, isAcyclic_of_le D hPQ hQ]
    · by_cases hP : IsAcyclic D P <;> simp [f, hP, hQ]
  have he : (fun x : ℝ ↦ (dichromaticPolynomial D).eval x / x ^ Fintype.card V) = expectation f := by
    funext x
    rw [dichromaticPolynomial_div_eq_sum_weight, expectation]
    apply sum_congr rfl
    intro P _
    by_cases h : IsAcyclic D P <;> simp [f, h]
  rw [he]
  exact expectation_monotone_on f hf hn balance
    nonnegative

private theorem small_order_monotone (D : Digraph V) (hn : Fintype.card V ≤ 1) :
    MonotoneOn (fun x : ℝ ↦ (dichromaticPolynomial D).eval x / x ^ Fintype.card V)
      (Set.Ici ((Fintype.card V : ℝ) - 1)) := by
  rcases dichromaticPolynomial_small D hn with hp | hp
  · simp only [hp, eval_pow, eval_X]
    have hn' : Fintype.card V = 0 ∨ Fintype.card V = 1 := by omega
    rcases hn' with hn₀ | hn₁
    · simp [hn₀, monotoneOn_const]
    · simp only [hn₁, Nat.cast_one, sub_self, pow_one]
      intro a ha b hb hab
      have ha' : 0 ≤ a := ha
      by_cases hzero : a = 0
      · by_cases hbzero : b = 0 <;> simp [hzero, hbzero]
      · change a / a ≤ b / b
        rw [div_self hzero, div_self (ne_of_gt ((lt_of_le_of_ne ha' (Ne.symm hzero)).trans_le hab))]
  · simp [hp, monotoneOn_const]

private theorem edge_incoming_term (Q : VertexPartition V) (x : ℝ) :
    (∑ e ∈ (univ : Finset (Mark V)).filter (fun e ↦ split e.val.1 e.val.2 = Q),
      edgeWeight x e) =
    ∑ A ∈ Q.parts.filter (fun A ↦ A.card = 1), ∑ R ∈ Q.parts.erase A,
      CrewSingletonSplit.weight ((Q.parts.erase A).erase R) Finset.card (1 + R.card) x := by
  classical
  rw [sum_sigma' (Q.parts.filter (fun A ↦ A.card = 1)) (fun A ↦ Q.parts.erase A)
    (fun A R ↦ CrewSingletonSplit.weight ((Q.parts.erase A).erase R) Finset.card (1 + R.card) x)]
  let idx (e : Mark V) : Sigma (fun _ : Finset V ↦ Finset V) :=
    ⟨{e.val.2}, (e.val.1.part e.val.2).erase e.val.2⟩
  have target (e : Mark V) (he : split e.val.1 e.val.2 = Q) :
      idx e ∈ (Q.parts.filter (fun A ↦ A.card = 1)).sigma (fun A ↦ Q.parts.erase A) := by
    rw [← he, mem_sigma]
    refine ⟨mem_filter.mpr ⟨?_, card_singleton _⟩, split_recipient _ _ e.property⟩
    change ({e.val.2} : Finset V) ∈ (split e.val.1 e.val.2).parts
    rw [← split_mark_part]
    exact (split e.val.1 e.val.2).part_mem.mpr (mem_univ _)
  refine sum_bij (fun e _ ↦ idx e) (fun e he ↦ target e (mem_filter.mp he).2) ?_ ?_ ?_
  · rintro ⟨⟨P, v⟩, hv⟩ he ⟨⟨P', v'⟩, hv'⟩ he' h
    have hA : ({v} : Finset V) = {v'} := congrArg Sigma.fst h
    have hV : v = v' := mem_singleton.mp (hA ▸ mem_singleton_self v)
    subst v'
    have hR : (P.part v).erase v = (P'.part v).erase v :=
      congrArg (fun z : Sigma (fun _ : Finset V ↦ Finset V) ↦ z.2) h
    have hq : split P v = Q := (mem_filter.mp he).2
    have hq' : split P' v = Q := (mem_filter.mp he').2
    have hP := recover_source_parts P v hv
    have hP' := recover_source_parts P' v hv'
    dsimp only at hP hP'
    have hp : P = P' := Finpartition.ext (by rw [hP, hP', hq, hq', hR])
    subst P'
    rfl
  · rintro ⟨A, R⟩ h
    obtain ⟨hA, hR⟩ := mem_sigma.mp h
    obtain ⟨v, rfl⟩ := card_eq_one.mp (mem_filter.mp hA).2
    let hv := (mem_filter.mp hA).1
    let e : Mark V := ⟨⟨merge Q v R hv hR, v⟩, merge_valid Q v R hv hR⟩
    refine ⟨e, mem_filter.mpr ⟨mem_univ _, split_merge Q v R hv hR⟩, ?_⟩
    change (⟨{v}, ((merge Q v R hv hR).part v).erase v⟩ :
      Sigma (fun _ : Finset V ↦ Finset V)) = ⟨{v}, R⟩
    rw [merge_residual]
  · intro e he
    let P := e.val.1
    let v := e.val.2
    let B := P.part v
    let R := B.erase v
    have hq : split P v = Q := (mem_filter.mp he).2
    have hsource : P.parts = insert (insert v R) ((Q.parts.erase {v}).erase R) := by
      simpa only [hq] using recover_source_parts P v e.property
    have hB : insert v R = B := insert_erase (P.mem_part_self.mpr (mem_univ v))
    have hvQ : ({v} : Finset V) ∈ Q.parts := (mem_filter.mp
      (mem_sigma.mp (target e hq)).1).1
    have hrest : P.parts.erase B = (Q.parts.erase {v}).erase R := by
      rw [hsource, ← hB, erase_insert (merged_notMem_rest Q hvQ)]
    have hc : B.card = 1 + R.card := by
      rw [← hB, card_insert_of_notMem (notMem_erase v B), Nat.add_comm]
    change CrewSingletonSplit.weight (P.parts.erase B) Finset.card B.card x =
      CrewSingletonSplit.weight ((Q.parts.erase {v}).erase R) Finset.card (1 + R.card) x
    rw [hrest, hc]

private theorem edge_outgoing_term (Q : VertexPartition V) (x : ℝ) :
    (∑ e ∈ (univ : Finset (Mark V)).filter (fun e ↦ e.val.1 = Q), edgeWeight x e) =
    ∑ B ∈ Q.parts.filter (fun B ↦ 1 < B.card),
      (B.card : ℝ) * CrewSingletonSplit.weight (Q.parts.erase B) Finset.card B.card x := by
  classical
  rw [← sum_outgoing_by_blocks]
  refine sum_bij (fun e _ ↦ e.val.2) ?_ ?_ ?_ ?_
  · intro e he
    have he' := (mem_filter.mp he).2
    exact mem_filter.mpr ⟨mem_univ _, he' ▸ e.property⟩
  · rintro ⟨⟨P, v⟩, hv⟩ he ⟨⟨P', v'⟩, hv'⟩ he' h
    obtain rfl : P = Q := (mem_filter.mp he).2
    obtain rfl : P' = P := (mem_filter.mp he').2
    obtain rfl : v = v' := h
    rfl
  · intro v hv
    exact ⟨⟨⟨Q, v⟩, (mem_filter.mp hv).2⟩, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩
  · intro e he
    simp only [edgeWeight, (mem_filter.mp he).2]



private theorem card_block_pos (Q : VertexPartition V) {B : Finset V} (hB : B ∈ Q.parts) :
    1 ≤ B.card :=
  card_pos.mpr (Q.nonempty_of_mem_parts hB)

private theorem unnormalized_balance (Q : VertexPartition V) (x : ℝ) :
    (∑ e ∈ (univ : Finset (Mark V)).filter (fun e ↦ split e.val.1 e.val.2 = Q), edgeWeight x e) -
      (∑ e ∈ (univ : Finset (Mark V)).filter (fun e ↦ e.val.1 = Q), edgeWeight x e) =
      (descPochhammer ℝ Q.parts.card).derivative.eval x -
        (Fintype.card V : ℝ) * (descPochhammer ℝ (Q.parts.card - 1)).eval (x - 1) := by
  classical
  rw [edge_incoming_term, edge_outgoing_term]
  let term (B : Finset V) := (B.card : ℝ) *
    CrewSingletonSplit.weight (Q.parts.erase B) Finset.card B.card x
  have hcancel : (∑ A ∈ Q.parts.filter (fun A ↦ A.card = 1), ∑ R ∈ Q.parts.erase A,
      CrewSingletonSplit.weight ((Q.parts.erase A).erase R) Finset.card (1 + R.card) x) =
      -(∑ A ∈ Q.parts.filter (fun A ↦ A.card = 1), term A) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro A hA
    have hcard := (mem_filter.mp hA).2
    have hweight := CrewCoefficientIdentity.singleton_incoming_cancel (Q.parts.erase A) Finset.card x
    have hterm : term A = CrewSingletonSplit.weight (Q.parts.erase A) Finset.card 1 x := by
      simp [term, hcard]
    rw [hterm]
    linarith
  have hfilter : Q.parts.filter (fun A ↦ A.card = 1) =
      Q.parts.filter (fun A ↦ ¬ 1 < A.card) := by
    ext A
    simp only [mem_filter]
    constructor
    · exact fun ⟨hA, h⟩ ↦ ⟨hA, by omega⟩
    · intro ⟨hA, h⟩
      have := card_block_pos Q hA
      exact ⟨hA, by omega⟩
  rw [hcancel, hfilter]
  change -(∑ B ∈ Q.parts.filter (fun B ↦ ¬ 1 < B.card), term B) -
    (∑ B ∈ Q.parts.filter (fun B ↦ 1 < B.card), term B) = _
  rw [show
    -(∑ B ∈ Q.parts.filter (fun B ↦ ¬ 1 < B.card), term B) -
        (∑ B ∈ Q.parts.filter (fun B ↦ 1 < B.card), term B) =
      -((∑ B ∈ Q.parts.filter (fun B ↦ ¬ 1 < B.card), term B) +
        (∑ B ∈ Q.parts.filter (fun B ↦ 1 < B.card), term B)) by ring,
    sum_filter_not_add_sum_filter]
  have hsum := CrewCoefficientIdentity.all_outgoing_weight Q.parts Finset.card
    (fun B hB ↦ card_block_pos Q hB) x
  rw [Q.sum_card_parts, card_univ] at hsum
  change -(∑ B ∈ Q.parts, term B) = _
  rw [show (∑ B ∈ Q.parts, term B) = _ from hsum]
  ring

private theorem singleton_split_balance (Q : VertexPartition V) (hn : 2 ≤ Fintype.card V)
    {x : ℝ} (hx : x ≠ 0) :
    deriv (fun t ↦ partitionWeight t Q) x = ∑ e : Mark V, contribution x e Q := by
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hk : 0 < Q.parts.card := card_pos.mpr
    ⟨Q.part v, Q.part_mem.mpr (mem_univ _)⟩
  have hd := deriv_weight Q (Fintype.card V - 1) (Q.parts.card - 1)
    (by omega) (by omega) hx
  rw [show Fintype.card V - 1 + 1 = Fintype.card V by omega,
    show Q.parts.card - 1 + 1 = Q.parts.card by omega] at hd
  rw [hd, ← unnormalized_balance]
  simp only [contribution, sum_sub_distrib]
  rw [show (∑ e : Mark V, if Q = split e.val.1 e.val.2 then transfer x e else 0) =
      ∑ e ∈ (univ : Finset (Mark V)).filter (fun e ↦ split e.val.1 e.val.2 = Q), transfer x e by
        simp only [sum_filter, eq_comm],
    show (∑ e : Mark V, if Q = e.val.1 then transfer x e else 0) =
      ∑ e ∈ (univ : Finset (Mark V)).filter (fun e ↦ e.val.1 = Q), transfer x e by
        simp only [sum_filter, eq_comm]]
  simp only [transfer]
  rw [sub_div, sum_div, sum_div]

private theorem transfer_pos (hn : 2 ≤ Fintype.card V) {x : ℝ}
    (hx : (Fintype.card V : ℝ) - 1 ≤ x) (e : Mark V) : 0 < transfer x e := by
  let P := e.val.1
  let B := P.part e.val.2
  have hB : B ∈ P.parts := P.part_mem.mpr (mem_univ _)
  have htotal : B.card + ∑ C ∈ P.parts.erase B, C.card = Fintype.card V := by
    rw [add_sum_erase P.parts card hB, P.sum_card_parts, card_univ]
  have hweight := CrewSingletonSplit.weight_bounds
    (P.parts.erase B) Finset.card (r := B.card) (x := x) e.property
    (fun C hC ↦ card_block_pos P (mem_of_mem_erase hC)) (by simpa only [htotal] using hx)
  have hcard : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : 0 < x := by linarith
  exact div_pos hweight.2 (pow_pos hpos _)

/-- The quotient in the conjecture, with its removable value at the order-one endpoint. -/
def normalizedDichromaticPolynomial (D : Digraph V) (x : ℝ) : ℝ :=
  if Fintype.card V = 1 ∧ x = 0 then (dichromaticPolynomial D).derivative.eval 0
  else (dichromaticPolynomial D).eval x / x ^ Fintype.card V

private theorem normalized_small (D : Digraph V) (hn : Fintype.card V ≤ 1) :
    normalizedDichromaticPolynomial D = (fun _ ↦ 1) ∨
      normalizedDichromaticPolynomial D = (fun _ ↦ 0) := by
  rcases dichromaticPolynomial_small D hn with hD | hD
  · left
    funext x
    have hor : Fintype.card V = 0 ∨ Fintype.card V = 1 := by omega
    rcases hor with hn₀ | hn₁
    · simp [normalizedDichromaticPolynomial, hD, hn₀]
    · by_cases hx : x = 0
      · simp [normalizedDichromaticPolynomial, hD, hn₁, hx]
      · simp [normalizedDichromaticPolynomial, hD, hn₁, hx]
  · right
    funext x
    by_cases hx : Fintype.card V = 1 ∧ x = 0 <;>
      simp [normalizedDichromaticPolynomial, hD, hx]

private theorem larger_order_monotone (D : Digraph V) (hn : 2 ≤ Fintype.card V) :
    MonotoneOn (fun x : ℝ ↦ (dichromaticPolynomial D).eval x / x ^ Fintype.card V)
      (Set.Ici ((Fintype.card V : ℝ) - 1)) := by
  have hcard : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  apply crew_monotone_on_of_transfer_hypotheses D hn
  · intro x hx Q
    exact singleton_split_balance Q hn (show 0 < x by linarith).ne'
  · intro x hx e
    exact (transfer_pos hn hx.le e).le

/-- Weak monotonicity also holds for the literal Lean quotient with totalized division. -/
private theorem dichromaticPolynomial_div_monotoneOn (D : Digraph V) :
    MonotoneOn (fun x : ℝ ↦ (dichromaticPolynomial D).eval x / x ^ Fintype.card V)
      (Set.Ici ((Fintype.card V : ℝ) - 1)) := by
  by_cases hn : 2 ≤ Fintype.card V
  · exact larger_order_monotone D hn
  · exact small_order_monotone D (by omega)

/-- Crew et al., Conjecture 2, with weak monotonicity and the continuous
value at the removable order-one endpoint. -/
theorem normalizedDichromaticPolynomial_monotoneOn (D : Digraph V) :
    MonotoneOn (normalizedDichromaticPolynomial D) (Set.Ici ((Fintype.card V : ℝ) - 1)) := by
  by_cases hne : Fintype.card V ≠ 1
  · have he : normalizedDichromaticPolynomial D =
        (fun x : ℝ ↦ (dichromaticPolynomial D).eval x / x ^ Fintype.card V) := by
      funext x
      simp [normalizedDichromaticPolynomial, hne]
    rw [he]
    exact dichromaticPolynomial_div_monotoneOn D
  · rcases normalized_small D (by omega) with h | h <;> rw [h] <;> exact monotoneOn_const

end

end D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity
