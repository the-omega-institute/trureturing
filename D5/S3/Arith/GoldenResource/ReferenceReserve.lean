/- GID: D5/S3/Arith/GoldenResource/ReferenceReserve
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ReferenceReserve
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: The reference prime objective controls the optimizer reserve independently of ties. -/

import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import D5.S3.Arith.GoldenResource.ReferencePrefixDominance
import D5.S3.Arith.GoldenLocalThreshold
import D5.S3.Arith.GoldenResourceOptimalInteger
import D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
import D5.S3.Arith.GoldenLayerMarginalDecay
import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.GoldenResource.ReferenceReserve

open Finset Set Real
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay

local notation "Q" => PrefixDeficitKernel.Q
local notation "S" => PrefixDeficitKernel.S
local notation "D" => PrefixDeficitKernel.D

/-- The price associated to a real reference scale. -/
def scalePrice (x : ℝ) : ℝ := 1 / (x * Real.log x)

/-- The exponent of the largest prime power not exceeding the reference scale. -/
def referenceExponent (x : ℝ) (p : ℕ) : ℕ := ⌊Real.log x / Real.log p⌋₊

/-- Harmonic-prefix benefit less the logarithmic exponent cost. -/
def referenceObjective (x : ℝ) (p a : ℕ) : ℝ :=
  Q a (p : ℝ)⁻¹ - scalePrice x * a * Real.log p

/-- The prime reserve compares the reference value with the actual supremum.
It is zero on nonprime indices so that its total uses a natural-number sum. -/
def reserve (x : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then referenceObjective x p (referenceExponent x p) -
    sSup (Set.range (goldenPrimeLocalObjective (scalePrice x) p)) else 0

/-- The full reserve, summed over its bounded prime support. -/
def totalReserve (x : ℝ) : ℝ := ∑ p ∈ range ⌈x⌉₊, reserve x p

/-- The reserve retained above the K-th root of the scale. -/
def truncatedReserve (x : ℝ) (K : ℕ) : ℝ :=
  ∑ p ∈ (range ⌈x⌉₊).filter (fun p : ℕ => x ^ ((K : ℝ)⁻¹) < (p : ℝ)), reserve x p

private theorem prime_bounds {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ) ∧ 1 < (p : ℝ) ∧ 0 < Real.log p ∧
      0 < (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ < 1 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h0 : (0 : ℝ) < p := by linarith
  exact ⟨h0, h1, Real.log_pos h1, inv_pos.mpr h0, (inv_lt_one₀ h0).mpr h1⟩

private theorem exponent_spec {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ referenceExponent x p ≤ x ∧
      x < (p : ℝ) ^ (referenceExponent x p + 1) := by
  obtain ⟨hp0, _, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hquot : 0 ≤ Real.log x / Real.log p := div_nonneg (Real.log_pos hx).le hlog.le
  have hlo := Nat.floor_le hquot
  have hhi := Nat.lt_floor_add_one (Real.log x / Real.log p)
  constructor
  · apply (Real.log_le_log_iff (pow_pos hp0 _) hx0).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hlog).mp hlo
  · apply (Real.log_lt_log_iff hx0 (pow_pos hp0 _)).mp
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ hlog).mp hhi

private theorem reference_step (x : ℝ) (p a : ℕ) :
    referenceObjective x p (a + 1) - referenceObjective x p a =
      (p : ℝ)⁻¹ ^ (a + 1) / (a + 1) - scalePrice x * Real.log p := by
  unfold referenceObjective PrefixDeficitKernel.Q
  rw [sum_range_succ]
  push_cast
  ring

private theorem reference_increment_sign {x : ℝ} (hx : 1 < x) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) :
    (0 ≤ (p : ℝ)⁻¹ ^ k / k - scalePrice x * Real.log p ↔ (p : ℝ) ^ k ≤ x) := by
  obtain ⟨hp0, hp1, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hxlog := Real.log_pos hx
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow0 := pow_pos hp0 k
  have hpow1 : 1 ≤ (p : ℝ) ^ k := one_le_pow₀ hp1.le
  have hlogpow : Real.log ((p : ℝ) ^ k) = (k : ℝ) * Real.log p := Real.log_pow _ _
  have hmono := Real.mul_log_strictMonoOn
  have he : Real.exp (-1) ≤ (1 : ℝ) := (Real.exp_lt_one_iff.mpr (by norm_num)).le
  have hdomainX : x ∈ Set.Ici (Real.exp (-1)) := le_trans he hx.le
  have hdomainP : (p : ℝ) ^ k ∈ Set.Ici (Real.exp (-1)) := le_trans he hpow1
  have heq : (0 ≤ (p : ℝ)⁻¹ ^ k / k - scalePrice x * Real.log p) ↔
      (p : ℝ) ^ k * Real.log ((p : ℝ) ^ k) ≤ x * Real.log x := by
    have hi : (p : ℝ)⁻¹ ^ k / k = 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
      rw [inv_pow]
      field_simp
    have hc : scalePrice x * Real.log p = Real.log p / (x * Real.log x) := by
      unfold scalePrice
      ring
    rw [sub_nonneg, hi, hc, div_le_div_iff₀ (mul_pos hx0 hxlog) (mul_pos hk0 hpow0),
      one_mul, hlogpow]
    have hm : Real.log (p : ℝ) * ((k : ℝ) * (p : ℝ) ^ k) =
        (p : ℝ) ^ k * ((k : ℝ) * Real.log p) := by ring
    rw [hm]
  rw [heq]
  exact hmono.le_iff_le hdomainP hdomainX

private theorem reference_maximal {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    ∀ a, referenceObjective x p a ≤ referenceObjective x p (referenceExponent x p) := by
  let v := referenceExponent x p
  obtain ⟨hlo, hhi⟩ := exponent_spec hx hp
  obtain ⟨hp0, hp1, _, _, _⟩ := prime_bounds hp
  have hup : MonotoneOn (referenceObjective x p) (Set.Iic v) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Iic
    intro k _ _ hkv
    have hpow : (p : ℝ) ^ (k + 1) ≤ x :=
      (pow_le_pow_right₀ hp1.le hkv).trans hlo
    have hs := (reference_increment_sign hx hp (k := k + 1) (by omega)).mpr hpow
    push_cast at hs
    rw [← reference_step] at hs
    exact sub_nonneg.mp hs
  have hdown : AntitoneOn (referenceObjective x p) (Set.Ici v) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Ici
    intro k _ hvk _
    have hpow : x < (p : ℝ) ^ (k + 1) :=
      hhi.trans_le (pow_le_pow_right₀ hp1.le (Nat.succ_le_succ hvk))
    have hs : (p : ℝ)⁻¹ ^ (k + 1) / (k + 1) - scalePrice x * Real.log p < 0 :=
      lt_of_not_ge (fun h => not_le_of_gt hpow
        ((reference_increment_sign hx hp (by omega)).mp (by simpa using h)))
    rw [← reference_step] at hs
    exact (sub_neg.mp hs).le
  change ∀ a, referenceObjective x p a ≤ referenceObjective x p v
  intro a
  exact isMaxOn_univ_of_mono_anti hup hdown (Set.mem_univ a)

private theorem actual_eq_prefix (lambda : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective lambda p a =
      Real.log (S a (p : ℝ)⁻¹) - lambda * a * Real.log p := by
  obtain ⟨_, _, _, _, hi⟩ := prime_bounds hp
  unfold goldenPrimeLocalObjective PrefixDeficitKernel.S
  congr 2
  rw [geom_sum_eq hi.ne]
  apply (div_eq_div_iff (sub_ne_zero.mpr hi.ne') (sub_ne_zero.mpr hi.ne)).mpr
  ring

private theorem actual_le_reference (x : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective (scalePrice x) p a ≤ referenceObjective x p a := by
  rw [actual_eq_prefix _ hp]
  apply sub_le_sub_right
  by_cases ha : a = 0
  · simp [ha, PrefixDeficitKernel.S, PrefixDeficitKernel.Q]
  · obtain ⟨_, _, _, hi0, hi1⟩ := prime_bounds hp
    exact (ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix
      (by omega) hi0 hi1).le

private theorem actual_bounded {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    BddAbove (Set.range (goldenPrimeLocalObjective (scalePrice x) p)) := by
  refine ⟨referenceObjective x p (referenceExponent x p), ?_⟩
  rintro y ⟨a, rfl⟩
  exact (actual_le_reference x hp a).trans (reference_maximal hx hp a)

private theorem local_reserve_bounds {x : ℝ} (hx : 1 < x) :
    (∀ p : ℕ, p.Prime → 0 ≤ reserve x p ∧
      reserve x p ≤ D (referenceExponent x p) (p : ℝ)⁻¹) := by
  intro p hp
  have hb := actual_bounded hx hp
  have hsup := csSup_le (Set.range_nonempty _) (by
    rintro y ⟨a, rfl⟩
    exact (actual_le_reference x hp a).trans (reference_maximal hx hp a))
  have hval := le_csSup hb (Set.mem_range_self (referenceExponent x p))
  rw [actual_eq_prefix _ hp] at hval
  simp only [reserve, if_pos hp, referenceObjective, PrefixDeficitKernel.D] at *
  constructor <;> linarith

private theorem reference_nonpos {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : p.Prime) (hxp : x ≤ p) : ∀ a, referenceObjective x p a ≤ 0 := by
  obtain ⟨hp0, hp1, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hxlog := Real.log_pos hx
  have hanti : Antitone (referenceObjective x p) := by
    apply antitone_nat_of_succ_le
    intro a
    have ha0 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hpow0 : 0 < (p : ℝ) ^ (a + 1) := pow_pos hp0 _
    have hpow : x ≤ (p : ℝ) ^ (a + 1) := hxp.trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hp1.le (by omega : 1 ≤ a + 1))
    have hlogs : Real.log x ≤ ((a : ℝ) + 1) * Real.log p := by
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using Real.log_le_log hx0 hpow
    have hcross : x * Real.log x ≤ ((a : ℝ) + 1) * (p : ℝ) ^ (a + 1) * Real.log p := by
      calc
        _ ≤ (p : ℝ) ^ (a + 1) * (((a : ℝ) + 1) * Real.log p) :=
          mul_le_mul hpow hlogs hxlog.le hpow0.le
        _ = _ := by ring
    have hs : (p : ℝ)⁻¹ ^ (a + 1) / ((a : ℝ) + 1) ≤ scalePrice x * Real.log p := by
      have hi : (p : ℝ)⁻¹ ^ (a + 1) / ((a : ℝ) + 1) =
          1 / (((a : ℝ) + 1) * (p : ℝ) ^ (a + 1)) := by
        rw [inv_pow]
        field_simp
      have hc : scalePrice x * Real.log p = Real.log p / (x * Real.log x) := by
        unfold scalePrice
        ring
      rw [hi, hc]
      apply (div_le_div_iff₀ (mul_pos ha0 hpow0) (mul_pos hx0 hxlog)).mpr
      nlinarith
    rw [← sub_nonpos, reference_step]
    exact sub_nonpos.mpr hs
  intro a
  have hh := hanti (Nat.zero_le a)
  simpa [referenceObjective, PrefixDeficitKernel.Q] using hh

private theorem reserve_zero_of_scale_le {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hxp : x ≤ p) : reserve x p = 0 := by
  by_cases hp : p.Prime
  · have hnonpos := reference_nonpos hx hp hxp
    have hzero : goldenPrimeLocalObjective (scalePrice x) p 0 = 0 := by
      rw [actual_eq_prefix _ hp]
      simp [PrefixDeficitKernel.S]
    have hsup : sSup (Set.range (goldenPrimeLocalObjective (scalePrice x) p)) = 0 := by
      apply le_antisymm
      · apply csSup_le (Set.range_nonempty _)
        rintro y ⟨a, rfl⟩
        exact (actual_le_reference x hp a).trans (hnonpos a)
      · simpa only [hzero] using le_csSup (actual_bounded hx hp) (Set.mem_range_self 0)
    have hr := (local_reserve_bounds hx p hp).1
    simp only [reserve, if_pos hp, hsup, sub_zero] at hr ⊢
    exact le_antisymm (hnonpos _) hr
  · simp [reserve, hp]

private theorem reserve_finite_support {x : ℝ} (hx : 1 < x) :
    (Function.support (reserve x)).Finite := by
  apply (Set.finite_Iio ⌈x⌉₊).subset
  intro p hp
  change p < ⌈x⌉₊
  by_contra h
  have hxp : x ≤ (p : ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast (by omega : ⌈x⌉₊ ≤ p))
  exact hp (reserve_zero_of_scale_le hx hxp)

private theorem reserve_le_inv_pow {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    reserve x p ≤ (p : ℝ)⁻¹ ^ (referenceExponent x p + 1) := by
  obtain ⟨_, _, _, hi0, hi1⟩ := prime_bounds hp
  have hr := (local_reserve_bounds hx p hp).2
  by_cases hv : referenceExponent x p = 0
  · have hd : D (referenceExponent x p) (p : ℝ)⁻¹ = 0 := by
      simp [hv, PrefixDeficitKernel.D, PrefixDeficitKernel.Q, PrefixDeficitKernel.S]
    rw [hd] at hr
    exact hr.trans (pow_nonneg hi0.le _)
  · have hd := (PrefixDeficitKernel.result (referenceExponent x p) (p : ℝ)⁻¹
      (by omega) hi0 hi1).2.2.2
    apply hr.trans (hd.trans _)
    apply (div_le_iff₀ (by positivity : 0 < (referenceExponent x p : ℝ) + 1)).mpr
    nlinarith [pow_nonneg hi0.le (referenceExponent x p + 1)]

private theorem actual_attained {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    ∃ a : ℕ, (∀ b, goldenPrimeLocalObjective (scalePrice x) p b ≤
      goldenPrimeLocalObjective (scalePrice x) p a) ∧
      reserve x p = referenceObjective x p (referenceExponent x p) -
        goldenPrimeLocalObjective (scalePrice x) p a := by
  have hprice : 0 < scalePrice x := by
    exact div_pos zero_lt_one (mul_pos (by linarith) (Real.log_pos hx))
  obtain ⟨n, hn, _, hopt, _⟩ := GoldenResourceOptimalLayerCount.optimal_layer_count_spec hprice
  have hthreshold := (GoldenResourceThresholdCriterion.golden_resource_optimal_iff_layer_thresholds
    hprice hn).mp hopt
  have hmax : ∀ b, goldenPrimeLocalObjective (scalePrice x) p b ≤
      goldenPrimeLocalObjective (scalePrice x) p (n.factorization p) := by
    apply golden_prime_local_objective_maximal_of_threshold hp _ (hthreshold.1 p hp)
    by_cases ha : n.factorization p = 0
    · exact Or.inl ha
    · exact Or.inr (hthreshold.2 p hp (Nat.dvd_of_factorization_pos ha))
  refine ⟨n.factorization p, hmax, ?_⟩
  have heq : sSup (Set.range (goldenPrimeLocalObjective (scalePrice x) p)) =
      goldenPrimeLocalObjective (scalePrice x) p (n.factorization p) := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro y ⟨b, rfl⟩
      exact hmax b
    · exact le_csSup (actual_bounded hx hp) (Set.mem_range_self _)
  simp only [reserve, if_pos hp, heq]

private theorem retained_layer_bound {x : ℝ} (hx : 1 < x) {K p : ℕ}
    (hK : 2 ≤ K) (hp : p.Prime) (hxK : (K : ℝ) ^ K ≤ x)
    (hretain : x ^ ((K : ℝ)⁻¹) < p) : goldenLayerMarginal p (K + 1) < scalePrice x := by
  obtain ⟨hp0, _, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hpow : x < (p : ℝ) ^ K := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_inv_lt_iff_of_pos hx0.le hp0.le hK0).mp hretain
  have hpK : (K : ℝ) < p := by
    by_contra h
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg p) (le_of_not_gt h) K
    exact not_le_of_gt hpow (hh.trans hxK)
  have hlogs : Real.log x < (K : ℝ) * Real.log p := by
    simpa only [Real.log_pow] using Real.log_lt_log hx0 hpow
  have hlogp : Real.log x < (p : ℝ) * Real.log p :=
    hlogs.trans (mul_lt_mul_of_pos_right hpK hlog)
  have hcross : x * Real.log x < (p : ℝ) ^ (K + 1) * Real.log p := by
    calc
      _ < (p : ℝ) ^ K * ((p : ℝ) * Real.log p) :=
        mul_lt_mul hpow hlogp.le (Real.log_pos hx) (pow_pos hp0 K).le
      _ = _ := by rw [pow_succ]; ring
  apply (golden_layer_marginal_le_inv_pow hp (by omega)).trans_lt
  have hi : (p : ℝ)⁻¹ ^ (K + 1) / Real.log p =
      1 / ((p : ℝ) ^ (K + 1) * Real.log p) := by rw [inv_pow]; field_simp
  rw [hi, scalePrice]
  exact one_div_lt_one_div_of_lt (mul_pos hx0 (Real.log_pos hx)) hcross

private theorem retained_optimizer_bound {x : ℝ} (hx : 1 < x) {K p : ℕ}
    (hK : 2 ≤ K) (hp : p.Prime) (hxK : (K : ℝ) ^ K ≤ x)
    (hretain : x ^ ((K : ℝ)⁻¹) < p) (a : ℕ)
    (hmax : ∀ b, goldenPrimeLocalObjective (scalePrice x) p b ≤
      goldenPrimeLocalObjective (scalePrice x) p a) : a ≤ K := by
  have hcut := retained_layer_bound hx hK hp hxK hretain
  have hlog := (prime_bounds hp).2.2.1
  have hanti : StrictAntiOn (goldenPrimeLocalObjective (scalePrice x) p) (Set.Ici K) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Ici
    intro k _ hk _
    have hm : goldenLayerMarginal p (k + 1) < scalePrice x := by
      rcases eq_or_lt_of_le (Nat.succ_le_succ hk) with heq | hlt
      · have hkk : K = k := Nat.succ.inj heq
        subst k
        exact hcut
      · exact (golden_layer_strict_decrease hp (by omega) hlt).trans hcut
    have hs := mul_neg_of_neg_of_pos (sub_neg.mpr hm) hlog
    rw [← golden_prime_local_objective_diff hp (scalePrice x)] at hs
    exact sub_neg.mp hs
  by_contra h
  have hka : K < a := by omega
  exact not_lt_of_ge (hmax K) (hanti (by simp) hka.le hka)

private theorem finite_integer_tail (t : ℝ) (K : ℕ) (s : Finset ℕ)
    (ht : 1 ≤ t) (hK : 2 ≤ K) (hs : ∀ n ∈ s, t < n) :
    (∑ n ∈ s, (n : ℝ)⁻¹ ^ (K + 1)) ≤
      (1 + 1 / (K : ℝ)) * t ^ (-(K : ℝ)) := by
  let m := ⌊t⌋₊ + 1
  let N := s.sup id + 1
  let r : ℝ := -((K : ℝ) + 1)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hm : t < (m : ℝ) := by simpa [m] using Nat.lt_floor_add_one t
  have hnm : ∀ n ∈ s, m ≤ n := by
    intro n hn
    exact Nat.add_one_le_iff.mpr ((Nat.floor_lt ht0.le).mpr (hs n hn))
  have hinj : Set.InjOn (fun n : ℕ => n - m) s := by
    intro a ha b hb hab
    have hma := hnm a ha
    have hmb := hnm b hb
    dsimp only at hab
    omega
  have himage : s.image (fun n => n - m) ⊆ range (N + 1) := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
    have hnN : n ≤ s.sup id := le_sup (f := id) hn
    simp only [Finset.mem_range]
    dsimp [N]
    omega
  have hanti : AntitoneOn (fun u : ℝ => u ^ r) (Set.Ici t) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (ht0.trans_le ha) hab (by dsimp [r]; linarith)
  have hsum : (∑ n ∈ s, (n : ℝ)⁻¹ ^ (K + 1)) ≤
      ∑ j ∈ range (N + 1), (t + j) ^ r := by
    calc
      _ = ∑ n ∈ s, (n : ℝ) ^ r := by
        apply sum_congr rfl
        intro n hn
        dsimp [r]
        rw [show -((K : ℝ) + 1) = -((K + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, inv_pow]
      _ ≤ ∑ n ∈ s, (t + (n - m : ℕ)) ^ r := by
        apply sum_le_sum
        intro n hn
        have hnEq : (n : ℝ) = (m : ℝ) + (n - m : ℕ) := by
          exact_mod_cast (Nat.add_sub_of_le (hnm n hn)).symm
        apply hanti (by
          change t ≤ t + ((n - m : ℕ) : ℝ)
          exact le_add_of_nonneg_right (Nat.cast_nonneg (n - m))) ((hs n hn).le)
        rw [hnEq]
        linarith
      _ = ∑ j ∈ s.image (fun n => n - m), (t + j) ^ r :=
        (sum_image (f := fun j : ℕ => (t + j) ^ r) hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg himage (fun j _ _ =>
        Real.rpow_nonneg (by positivity) _)
  have hi := (hanti.mono Set.Icc_subset_Ici_self).sum_le_integral (a := N)
  have hz : (0 : ℝ) ∉ Set.uIcc t (t + N) := by
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N))]
    intro h
    linarith [h.1]
  have heval := integral_rpow (a := t) (b := t + N) (r := r)
    (Or.inr ⟨by dsimp [r]; linarith, hz⟩)
  have hr : r + 1 = -(K : ℝ) := by dsimp [r]; ring
  rw [hr] at heval
  have htail : (∫ u in t..t + N, u ^ r) ≤ t ^ (-(K : ℝ)) / K := by
    rw [heval]
    have hpos := Real.rpow_nonneg (by positivity : 0 ≤ t + (N : ℝ)) (-(K : ℝ))
    rw [div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (sub_le_self _ hpos) hK0.le
  have hfirst : t ^ r ≤ t ^ (-(K : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le ht
    dsimp [r]
    linarith
  rw [sum_range_succ'] at hsum
  simp only [Nat.cast_zero, add_zero] at hsum
  have hh := add_le_add hi hfirst
  have hlast := add_le_add htail (le_refl (t ^ (-(K : ℝ))))
  calc
    _ ≤ t ^ (-(K : ℝ)) / K + t ^ (-(K : ℝ)) := hsum.trans (hh.trans hlast)
    _ = _ := by ring

private theorem reserve_nonneg {x : ℝ} (hx : 1 < x) (p : ℕ) : 0 ≤ reserve x p := by
  by_cases hp : p.Prime
  · exact (local_reserve_bounds hx p hp).1
  · simp [reserve, hp]

private theorem reserve_le_two_div_scale {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    reserve x p ≤ 2 / x := by
  have hx0 : 0 < x := by linarith
  have hi : (p : ℝ)⁻¹ ^ (referenceExponent x p + 1) < 1 / x := by
    rw [inv_pow, one_div]
    exact inv_strictAnti₀ hx0 (exponent_spec hx hp).2
  have hlast : 1 / x ≤ 2 / x := div_le_div_of_nonneg_right (by norm_num) hx0.le
  exact (reserve_le_inv_pow hx hp).trans (hi.le.trans hlast)

private theorem middle_exponent {x : ℝ} (hx : 1 < x) {K p : ℕ}
    (hK : 2 ≤ K) (hp : p.Prime)
    (hlo : x ^ ((K + 1 : ℕ) : ℝ)⁻¹ < p)
    (hhi : (p : ℝ) ≤ x ^ ((K : ℝ)⁻¹)) : referenceExponent x p = K := by
  obtain ⟨hp0, _, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hpowlo : (p : ℝ) ^ K ≤ x := by
    simpa only [Real.rpow_natCast] using
      (Real.le_rpow_inv_iff_of_pos hp0.le hx0.le hK0).mp hhi
  have hpowhi : x < (p : ℝ) ^ (K + 1) := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_inv_lt_iff_of_pos hx0.le hp0.le hK1).mp hlo
  unfold referenceExponent
  apply (Nat.floor_eq_iff (div_nonneg (Real.log_pos hx).le hlog.le)).mpr
  constructor
  · apply (le_div_iff₀ hlog).mpr
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp0 K) hpowlo
  · apply (div_lt_iff₀ hlog).mpr
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using Real.log_lt_log hx0 hpowhi

private theorem truncation_difference (x : ℝ) (K : ℕ) :
    totalReserve x - truncatedReserve x K =
      ∑ p ∈ (range ⌈x⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ x ^ ((K : ℝ)⁻¹)),
        reserve x p := by
  classical
  unfold totalReserve truncatedReserve
  rw [sum_filter, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hroot : x ^ ((K : ℝ)⁻¹) < p
  · simp [hprime, hroot, not_le_of_gt hroot]
  · simp [hprime, hroot, le_of_not_gt hroot]
  · simp [reserve, hprime]
  · simp [reserve, hprime]

private theorem truncation_tail_bound {x : ℝ} (hx : 1 < x) {K : ℕ} (hK : 2 ≤ K) :
    0 ≤ totalReserve x - truncatedReserve x K ∧
    totalReserve x - truncatedReserve x K ≤
      (4 + 2 / (K : ℝ)) * x ^ (-(K : ℝ) / ((K : ℝ) + 1)) := by
  classical
  let t : ℝ := x ^ (((K : ℝ) + 1)⁻¹)
  let s := (range ⌈x⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ x ^ ((K : ℝ)⁻¹))
  let a := s.filter (fun p : ℕ => (p : ℝ) ≤ t)
  let b := s.filter (fun p : ℕ => ¬(p : ℝ) ≤ t)
  have hx0 : 0 < x := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK1 : 0 < (K : ℝ) + 1 := by positivity
  have ht : 1 ≤ t := (Real.one_lt_rpow hx (inv_pos.mpr hK1)).le
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime ∧ (p : ℝ) ≤ x ^ ((K : ℝ)⁻¹) :=
    (mem_filter.mp hp).2
  have hcard : (a.card : ℝ) ≤ t := by
    have hsub : a ⊆ Icc 1 ⌊t⌋₊ := by
      intro p hp
      obtain ⟨hps, hpt⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(hs p hps).1.one_lt.le, Nat.le_floor hpt⟩
    have hc := Finset.card_le_card hsub
    have hc' : a.card ≤ ⌊t⌋₊ := by simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc
    have hcReal : (a.card : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hc'
    exact hcReal.trans (Nat.floor_le (by linarith : 0 ≤ t))
  have ha : (∑ p ∈ a, reserve x p) ≤ 2 * t / x := by
    calc
      _ ≤ ∑ _p ∈ a, (2 / x : ℝ) := sum_le_sum (fun p hp =>
        reserve_le_two_div_scale hx (hs p (mem_filter.mp hp).1).1)
      _ = (a.card : ℝ) * (2 / x) := by simp
      _ ≤ t * (2 / x) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hb : (∑ p ∈ b, reserve x p) ≤
      2 * ((1 + 1 / (K : ℝ)) * t ^ (-(K : ℝ))) := by
    calc
      _ ≤ ∑ p ∈ b, 2 * (p : ℝ)⁻¹ ^ (K + 1) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hps, hpt⟩ := mem_filter.mp hp
        have hprime := (hs p hps).1
        have hv := middle_exponent hx hK hprime (by
          simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hpt) (hs p hps).2
        have hr := reserve_le_inv_pow hx hprime
        rw [hv] at hr
        have hpow : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ (K + 1) := by positivity
        linarith
      _ = 2 * ∑ p ∈ b, (p : ℝ)⁻¹ ^ (K + 1) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_integer_tail t K b ht hK (fun p hp =>
        lt_of_not_ge (mem_filter.mp hp).2)) (by norm_num)
  have hsplit : (∑ p ∈ a, reserve x p) + ∑ p ∈ b, reserve x p =
      ∑ p ∈ s, reserve x p := by
    dsimp [a, b]
    exact sum_filter_add_sum_filter_not _ _ _
  have htPow : t ^ (-(K : ℝ)) = x ^ (-(K : ℝ) / ((K : ℝ) + 1)) := by
    dsimp [t]
    rw [← Real.rpow_mul hx0.le]
    congr 1
    ring
  have htDiv : t / x = x ^ (-(K : ℝ) / ((K : ℝ) + 1)) := by
    dsimp [t]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hx0]
    congr 1
    field_simp
    ring
  rw [truncation_difference]
  change 0 ≤ (∑ p ∈ s, reserve x p) ∧ _
  constructor
  · exact sum_nonneg (fun p _ => reserve_nonneg hx p)
  · rw [← hsplit]
    calc
      _ ≤ 2 * t / x + 2 * ((1 + 1 / (K : ℝ)) * t ^ (-(K : ℝ))) := add_le_add ha hb
      _ = (4 + 2 / (K : ℝ)) * x ^ (-(K : ℝ) / ((K : ℝ) + 1)) := by
        rw [mul_div_assoc, htDiv, htPow]
        ring

/-- The reserve has finite support and a uniform tail at every finite root scale.
At scales at least K^K, every retained prime's actual maximizing exponent is at most K. -/
theorem result {x : ℝ} (hx : 1 < x) :
    (Function.support (reserve x)).Finite ∧
    (∀ p : ℕ, p.Prime → ∃ a : ℕ,
      (∀ b, goldenPrimeLocalObjective (scalePrice x) p b ≤
        goldenPrimeLocalObjective (scalePrice x) p a) ∧
      reserve x p = referenceObjective x p (referenceExponent x p) -
        goldenPrimeLocalObjective (scalePrice x) p a) ∧
    (∀ K : ℕ, 2 ≤ K →
      0 ≤ totalReserve x - truncatedReserve x K ∧
      totalReserve x - truncatedReserve x K ≤
        (4 + 2 / (K : ℝ)) * x ^ (-(K : ℝ) / ((K : ℝ) + 1))) ∧
    (∀ K : ℕ, 2 ≤ K → (K : ℝ) ^ K ≤ x → ∀ p : ℕ, p.Prime →
      x ^ ((K : ℝ)⁻¹) < p → ∀ a : ℕ,
      (∀ b, goldenPrimeLocalObjective (scalePrice x) p b ≤
        goldenPrimeLocalObjective (scalePrice x) p a) → a ≤ K) := by
  refine ⟨reserve_finite_support hx, fun _ hp => actual_attained hx hp, ?_, ?_⟩
  · intro K hK
    exact truncation_tail_bound hx hK
  · intro K hK hxK p hp hretain a hmax
    exact retained_optimizer_bound hx hK hp hxK hretain a hmax

end D5.S3.Arith.GoldenResource.ReferenceReserve
