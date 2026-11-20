/- GID: D5/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBoundCountingCheck
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBoundCountingCheck
   mirror-E: none(waiver:temporary-compiled-fragment)
   anchors: []
   utility: none
   digest: Finite prime-window and binomial estimates for the lower-bound construction. -/

import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound

open Finset Real Filter
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

private lemma theta_interval_sum {y z : ℝ} (hyz : y ≤ z) :
    Chebyshev.theta z - Chebyshev.theta y =
      ∑ p ∈ primeInterval y z, Real.log (p : ℝ) := by
  classical
  have he : primeInterval y z = Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
    ext p
    simp only [primeInterval, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun h => (Nat.not_le_of_lt hlo) h.1⟩
    · rintro ⟨⟨hhi, hp⟩, hlo⟩
      exact ⟨⟨lt_of_not_ge (fun h => hlo ⟨h, hp⟩), hhi⟩, hp⟩
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.floor_mono hyz),
        (Nat.mem_primesLE.mp hp).2⟩
  rw [he, Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  have h := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
  linarith

private lemma theta_interval_le_card {y z : ℝ} (hyz : y ≤ z) (hz : 0 ≤ z) :
    Chebyshev.theta z - Chebyshev.theta y ≤
      (primeInterval y z).card * Real.log z := by
  rw [theta_interval_sum hyz]
  calc
    _ ≤ ∑ _p ∈ primeInterval y z, Real.log z := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
      have hpz : (p : ℝ) ≤ z :=
        (Nat.le_floor_iff hz).mp (Finset.mem_Ioc.mp hpI).2
      exact Real.log_le_log (by exact_mod_cast hpP.pos) hpz
    _ = _ := by simp

private lemma theta_cubic_threshold : ∃ U : ℝ, 2 ≤ U ∧
    ∀ x : ℝ, U ≤ x → |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3 := by
  have he : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3 := by
    filter_upwards [(theta_error_log_power 3).def (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx1
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_pos (div_pos hx0 (pow_pos hlog 3))] using hx
  obtain ⟨U, hU⟩ := eventually_atTop.mp he
  exact ⟨max 2 U, le_max_left _ _, fun x hx => hU x ((le_max_right _ _).trans hx)⟩

-- The proof requires only error bounds at TWO endpoints. It does not need
-- MovingBoxCapacity or uniform local Abel summation.
private lemma prime_block_capacity {U α : ℝ} {k : ℕ}
    (hU : 2 ≤ U)
    (herr : ∀ x : ℝ, U ≤ x → |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3)
    (hα : U ≤ α) (hk : 3 ≤ k) (hgap : 2 * ((k : ℝ) - 1) ≤ α)
    (hcube : 8 * (k : ℝ) ≤ Real.log α ^ 3) :
    α / (4 * Real.log ((k : ℝ) * α)) ≤
      ((primeInterval (((k : ℝ) - 1) * (α + 1)) ((k : ℝ) * α)).card : ℝ) := by
  let y := ((k : ℝ) - 1) * (α + 1)
  let z := (k : ℝ) * α
  have hα2 : 2 ≤ α := hU.trans hα
  have hα0 : 0 < α := by linarith
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hyα : α ≤ y := by dsimp [y]; nlinarith
  have hwidth : α / 2 ≤ z - y := by dsimp [y, z]; nlinarith
  have hyz : y ≤ z := by linarith
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlα : 0 < Real.log α := Real.log_pos (by linarith)
  have hpoint (x : ℝ) (hxα : α ≤ x) (hxz : x ≤ z) :
      |Chebyshev.theta x - x| ≤ α / 8 := by
    have hx0 : 0 < x := hα0.trans_le hxα
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog : Real.log α ^ 3 ≤ Real.log x ^ 3 := by
      gcongr
    calc
      _ ≤ x / Real.log x ^ 3 := herr x (hα.trans hxα)
      _ ≤ z / Real.log α ^ 3 :=
        div_le_div₀ hz0.le hxz (by positivity) hlog
      _ ≤ α / 8 := by
        apply (div_le_iff₀ (pow_pos hlα 3)).mpr
        dsimp [z]
        nlinarith [mul_le_mul_of_nonneg_right hcube hα0.le]
  have hey := hpoint y hyα hyz
  have hez := hpoint z (hyα.trans hyz) le_rfl
  have htheta : α / 4 ≤ Chebyshev.theta z - Chebyshev.theta y := by
    obtain ⟨heyL, heyU⟩ := abs_le.mp hey
    obtain ⟨hezL, hezU⟩ := abs_le.mp hez
    linarith
  have hcount := theta_interval_le_card hyz hz0.le
  have hlogz : 0 < Real.log z := Real.log_pos (by nlinarith)
  change α / (4 * Real.log z) ≤ _
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlogz)).mpr
  nlinarith

-- A weaker factor 2 in the binomial bound costs only k log 2 = o(log X).
-- Reuse Mathlib's pow_le_choose; do not reprove a binomial-coefficient estimate.
private lemma choose_half_lower {N k : ℕ} (hk : 0 < k) (hNk : 2 * k ≤ N) :
    ((N : ℝ) / (2 * k)) ^ k ≤ (N.choose k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (N : ℝ) / 2 ≤ ((N + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ N + 1)]
    push_cast
    have hNkR : 2 * (k : ℝ) ≤ N := by exact_mod_cast hNk
    linarith
  have hf : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  calc
    _ = ((N : ℝ) / 2) ^ k / (k : ℝ) ^ k := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ (((N + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) := by
      apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hf
    _ ≤ (N.choose k : ℝ) := Nat.pow_le_choose k N


private lemma parameter_slack {C D a : ℝ} (ha : 0 < a)
    (hbudget : C + a < D) (hgain : (39 / 40 : ℝ) * D < a) :
    ∀ᶠ t : ℝ in atTop,
      1 ≤ t ∧ 5 ≤ ⌊a * t⌋₊ ∧ (⌊a * t⌋₊ : ℝ) ≤ a * t ∧
      t + log (3 * a) + log t ≤ 2 * t ∧
      C * t ^ 2 + (⌊a * t⌋₊ : ℝ) * (t + log (3 * a) + log t) ≤ D * t ^ 2 ∧
      (39 / 40 : ℝ) * D * t ^ 2 ≤
        (⌊a * t⌋₊ : ℝ) * (t - log (16 * a) - 2 * log t) ∧
      8 * (⌊a * t⌋₊ : ℝ) ≤ t ^ 3 ∧ 16 * a * t ^ 2 ≤ exp t := by
  let b (t : ℝ) := t + log (3 * a) + log t
  let c (t : ℝ) := t - log (16 * a) - 2 * log t
  have ht : Tendsto (fun t : ℝ => t) atTop atTop := tendsto_id
  have hlog : Tendsto (fun t : ℝ => log t / t) atTop (𝓝 0) := by
    simpa only [rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hb : Tendsto (fun t : ℝ => b t / t) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add
      (ht.const_div_atTop (log (3 * a)))).add hlog
    norm_num only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
    dsimp only [b]
    field_simp
  have hc : Tendsto (fun t : ℝ => c t / t) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
      (ht.const_div_atTop (log (16 * a)))).sub (hlog.const_mul 2)
    norm_num only [mul_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
    dsimp only [c]
    field_simp
  have hk := tendsto_nat_floor_mul_div_atTop ha.le
  have hcost := (hk.mul hb).const_add C
  have hproduce := hk.mul hc
  simp only [mul_one] at hcost hproduce
  have hklarge : Tendsto (fun t : ℝ => ⌊a * t⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (ht.const_mul_atTop ha)
  have ht2 : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hklarge.eventually_ge_atTop 5,
    hb.eventually_lt_const (by norm_num : (1 : ℝ) < 2),
    hcost.eventually_lt_const hbudget, hproduce.eventually_const_lt hgain,
    ht2.eventually_ge_atTop (8 * a),
    (tendsto_exp_div_pow_atTop 2).eventually_ge_atTop (16 * a)]
    with t ht1 hk5 hb2 hcostD hproduceD ht2a hexp
  have ht0 : 0 < t := by linarith
  have hfloor : (⌊a * t⌋₊ : ℝ) ≤ a * t := Nat.floor_le (by positivity)
  have hcostD' : C * t ^ 2 + (⌊a * t⌋₊ : ℝ) * b t < D * t ^ 2 := by
    have he : C + (⌊a * t⌋₊ : ℝ) / t * (b t / t) =
        (C * t ^ 2 + (⌊a * t⌋₊ : ℝ) * b t) / t ^ 2 := by
      field_simp
      <;> ring
    rw [he] at hcostD
    exact (div_lt_iff₀ (pow_pos ht0 2)).mp hcostD
  have hproduceD' : (39 / 40 : ℝ) * D * t ^ 2 <
      (⌊a * t⌋₊ : ℝ) * c t := by
    have he : (⌊a * t⌋₊ : ℝ) / t * (c t / t) =
        ((⌊a * t⌋₊ : ℝ) * c t) / t ^ 2 := by
      field_simp
      <;> ring
    rw [he] at hproduceD
    exact (lt_div_iff₀ (pow_pos ht0 2)).mp hproduceD
  refine ⟨ht1, hk5, hfloor, (div_lt_iff₀ ht0).mp hb2 |>.le,
    hcostD'.le, hproduceD'.le, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right ht2a ht0.le]
  · exact (le_div_iff₀ (pow_pos ht0 2)).mp hexp

private lemma binomial_log_gain {N k : ℕ} {a t D α z : ℝ}
    (hk : 0 < k) (hNk : 2 * k ≤ N) (ha : 0 < a) (ht : 0 < t)
    (hz : 1 < z) (hN : α / (4 * log z) ≤ N) (hα : exp t ≤ α)
    (hden : 8 * (k : ℝ) * log z ≤ 16 * a * t ^ 2)
    (hgain : (39 / 40 : ℝ) * D * t ^ 2 ≤
      (k : ℝ) * (t - log (16 * a) - 2 * log t)) :
    (39 / 40 : ℝ) * D * t ^ 2 ≤ log (N.choose k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlz : 0 < log z := log_pos hz
  have hN' : α ≤ (N : ℝ) * (4 * log z) :=
    (div_le_iff₀ (by positivity : 0 < 4 * log z)).mp hN
  have hfrac : exp t / (16 * a * t ^ 2) ≤ (N : ℝ) / (2 * k) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * a * t ^ 2)
      (by positivity : (0 : ℝ) < 2 * k)).mpr
    have h1 := mul_le_mul_of_nonneg_right (hα.trans hN')
      (by positivity : (0 : ℝ) ≤ 2 * k)
    have h2 := mul_le_mul_of_nonneg_left hden hN0.le
    nlinarith
  have heq : log (exp t / (16 * a * t ^ 2)) =
      t - log (16 * a) - 2 * log t := by
    rw [log_div (exp_ne_zero _) (by positivity), log_exp,
      log_mul (by positivity) (by positivity), log_pow]
    ring
  have hlog := log_le_log (by positivity : 0 < exp t / (16 * a * t ^ 2)) hfrac
  rw [heq] at hlog
  have hchoose := log_le_log
    (pow_pos (div_pos hN0 (by positivity : (0 : ℝ) < 2 * k)) k)
    (choose_half_lower hk hNk)
  rw [log_pow] at hchoose
  exact hgain.trans ((mul_le_mul_of_nonneg_left hlog hk0.le).trans hchoose)

private lemma lower_bound_parameters (C : ℝ) :
    let D := 1000 * (|C| + 1)
    let a := (99 / 100 : ℝ) * D
    ∀ᶠ t : ℝ in atTop,
      ∀ α : ℝ, exp t ≤ α → α ≤ 3 * exp t →
      let k := ⌊a * t⌋₊
      let z := (k : ℝ) * α
      5 ≤ k ∧ 2 * ((k : ℝ) - 1) ≤ α ∧ 8 * (k : ℝ) ≤ log α ^ 3 ∧
      C * t ^ 2 + (k : ℝ) * log z ≤ D * t ^ 2 ∧
      ∀ N : ℕ, α / (4 * log z) ≤ N →
        2 * k ≤ N ∧ (39 / 40 : ℝ) * D * t ^ 2 ≤ log (N.choose k : ℝ) := by
  dsimp only
  let D := 1000 * (|C| + 1)
  let a := (99 / 100 : ℝ) * D
  have hD : 0 < D := by dsimp [D]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hCa : C + a < D := by
    dsimp [a, D]
    nlinarith [le_abs_self C, abs_nonneg C]
  have hDa : (39 / 40 : ℝ) * D < a := by dsimp [a]; nlinarith
  filter_upwards [parameter_slack ha hCa hDa] with t hslack
  obtain ⟨ht1, hk5, hka, hb, hbudget, hgain, hcube, hexp⟩ := hslack
  have ht0 : 0 < t := by linarith
  intro α hαL hαU
  let k := ⌊a * t⌋₊
  let z := (k : ℝ) * α
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk5
  have hα0 : 0 < α := (exp_pos t).trans_le hαL
  have hα1 : 1 < α := (one_lt_exp_iff.mpr ht0).trans_le hαL
  have hz1 : 1 < z := by dsimp [z]; nlinarith
  have hαt : t ≤ log α := by simpa only [log_exp] using log_le_log (exp_pos t) hαL
  have hzU : z ≤ 3 * a * t * exp t := by
    dsimp [z]
    calc
      _ ≤ (a * t) * (3 * exp t) := mul_le_mul hka hαU hα0.le (by positivity)
      _ = _ := by ring
  have hlogz : log z ≤ t + log (3 * a) + log t := by
    have h := log_le_log (by linarith : 0 < z) hzU
    rw [log_mul (by positivity) (exp_ne_zero _), log_exp,
      log_mul (by positivity) ht0.ne'] at h
    linarith
  have hden : 8 * (k : ℝ) * log z ≤ 16 * a * t ^ 2 := by
    have hlogz2 := hlogz.trans hb
    have h1 := mul_le_mul_of_nonneg_left hlogz2 (by positivity : (0 : ℝ) ≤ 8 * k)
    have h2 := mul_le_mul_of_nonneg_right hka (by positivity : (0 : ℝ) ≤ 16 * t)
    nlinarith
  have hgap : 2 * ((k : ℝ) - 1) ≤ α := by
    have h1 : 2 * (k : ℝ) ≤ 16 * a * t ^ 2 := by
      nlinarith [mul_nonneg ha.le (sq_nonneg (t - 1))]
    linarith
  refine ⟨hk5, hgap, ?_, ?_, ?_⟩
  · exact hcube.trans (by gcongr)
  · have h := mul_le_mul_of_nonneg_left hlogz (by positivity : (0 : ℝ) ≤ k)
    linarith
  · intro N hN
    have hlogz0 : 0 < log z := log_pos hz1
    have hN' := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlogz0)).mp hN
    have hNk : 2 * k ≤ N := by
      have h1 : 8 * (k : ℝ) * log z ≤ α := hden.trans (hexp.trans hαL)
      have h2 : 2 * (k : ℝ) ≤ N := by nlinarith [log_pos hz1]
      exact_mod_cast h2
    have hk0 : 0 < k := by dsimp only [k]; omega
    exact ⟨hNk, binomial_log_gain hk0 hNk ha ht0 hz1 hN hαL hden hgain⟩

private lemma cutoff_parameter_atTop {D : ℝ} (hD : 0 < D) :
    Tendsto (fun X : ℝ => sqrt (log X / D)) atTop atTop ∧
      ∀ᶠ X : ℝ in atTop, D * sqrt (log X / D) ^ 2 = log X := by
  refine ⟨tendsto_sqrt_atTop.comp (tendsto_log_atTop.atTop_div_const hD), ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [sq_sqrt (div_nonneg (log_pos hX).le hD.le)]
  field_simp

end D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
