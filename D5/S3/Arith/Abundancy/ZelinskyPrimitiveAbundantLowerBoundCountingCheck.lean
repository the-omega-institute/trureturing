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
  rw [he, Finset.sum_sdiff hsub, Chebyshev.theta_eq_sum_primesLE,
    Chebyshev.theta_eq_sum_primesLE]

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
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ x / Real.log x ^ 3)] using hx
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
        div_le_div₀ hx0.le hxz (by positivity) hlog
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


end D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
