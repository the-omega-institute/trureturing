/- GID: D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The marked singleton-split weight has a strictly positive falling-factorial lower bound. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The signed subset coefficient for a marked singleton split. -/

namespace D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit

open MeasureTheory Set
open scoped BigOperators

noncomputable section

local notation "fall" => (fun (x : ℝ) (k : ℕ) => Polynomial.eval x (descPochhammer ℝ k))

/-- The weight of a marked singleton split. The finset indexes the other blocks. -/
def weight {ι : Type*} (s : Finset ι) (b : ι → ℕ) (r : ℕ) (x : ℝ) : ℝ :=
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

private theorem weighted_kernel_bound {ι : Type*} (s : Finset ι) (b : ι → ℕ)
    {x : ℝ} {r : ℕ} (hr : 2 ≤ r) (hb : ∀ i ∈ s, 1 ≤ b i)
    (hx : (∑ i ∈ s, (b i : ℝ)) + 1 ≤ x) (hcard : (s.card : ℝ) + 1 ≤ x) :
    (∫ u in (0 : ℝ)..1, u ^ (r - 1) * kernel s b x u) ≤
      fall (x - 1) s.card * (x / (x + 1)) := by
  have hx1 : 1 ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) s.card]
  have hd : 1 ≤ x - s.card := by linarith
  have hfall : 0 < fall (x - 1) s.card :=
    descPochhammer_pos (n := s.card) (s := x - 1) (by linarith)
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
theorem weight_bounds {ι : Type*} (s : Finset ι) (b : ι → ℕ) {r : ℕ} {x : ℝ}
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
  have hfall : 0 < fall (x - 1) s.card :=
    descPochhammer_pos (n := s.card) (s := x - 1) (by linarith)
  exact ⟨hbound, (div_pos hfall hden).trans_le hbound⟩

end
end D5.S3.Combinatorics.Graph.Coloring.CrewSingletonSplit
