/- GID: D5/S3/CharacterSums/DirichletRampPrimeTail
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletRampPrimeTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The mod-four nonprime Mangoldt sum and its integrated tail have square-root coefficients one and two. -/

import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Finset MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt Topology
open D5.S3.Arith.Robin.EulerLayerRootCorrection
  (psi_theta_root_limit theta_sqrt_scale)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (diff_integrable root_integrable root_integral)

namespace D5.S3.CharacterSums.DirichletRampPrimeTail

/-- The real-valued mod-four character on natural numbers. -/
def chiFour (n : ℕ) : ℝ := (ZMod.χ₄ (n : ZMod 4) : ℝ)

private def nonprimeUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => ¬ n.Prime

/-- The nonprime part of the mod-four Mangoldt summatory function. -/
def HChi (x : ℝ) : ℝ :=
  ∑ n ∈ nonprimeUpTo ⌊x⌋₊, Λ n * chiFour n

private theorem norm_chiFour_le (n : ℕ) : ‖chiFour n‖ ≤ 1 := by
  rw [chiFour, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num [Real.norm_eq_abs]

private theorem chiFour_prime_sq {p : ℕ} (hp : p.Prime) :
    chiFour (p ^ 2) = if p = 2 then 0 else 1 := by
  by_cases hp2 : p = 2
  · subst p
    rw [chiFour, ZMod.χ₄_nat_eq_if_mod_four]
    norm_num
  · have hpodd := hp.eq_two_or_odd.resolve_left hp2
    have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hsq : p ^ 2 % 4 = 1 := by
      rw [Nat.pow_mod]
      rcases hpmod with h | h <;> norm_num [h]
    rw [chiFour, ZMod.χ₄_nat_one_mod_four hsq, Int.cast_one, ite_eq_right hp2]

private def squareEmbedding : ℕ ↪ ℕ :=
  ⟨fun p => p ^ 2, Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)⟩

/-- The prime squares whose bases are at most the square root of the cutoff. -/
def primeSquares (x : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.sqrt x⌋₊).map squareEmbedding

private theorem mem_primeSquares_iff {x : ℝ} {n : ℕ} (hx : 0 ≤ x) :
    n ∈ primeSquares x ↔ ∃ p : ℕ, p.Prime ∧ p ^ 2 = n ∧ n ≤ ⌊x⌋₊ := by
  change n ∈ (Nat.primesLE ⌊Real.sqrt x⌋₊).map squareEmbedding ↔ _
  constructor
  · intro hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    obtain ⟨hle, hp'⟩ := Nat.mem_primesLE.mp hp
    have hroot := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mp hle
    have hsq : (p : ℝ) ^ 2 ≤ x := (Real.le_sqrt (Nat.cast_nonneg p) hx).mp hroot
    have hcut : p ^ 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).mpr (by exact_mod_cast hsq)
    exact ⟨p, hp', rfl, hcut⟩
  · rintro ⟨p, hp, rfl, hcut⟩
    have hsq : (p : ℝ) ^ 2 ≤ x := by exact_mod_cast (Nat.le_floor_iff hx).mp hcut
    have hroot := (Real.le_sqrt (Nat.cast_nonneg p) hx).mpr hsq
    have hle := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr hroot
    exact Finset.mem_map.mpr ⟨p, Nat.mem_primesLE.mpr ⟨hle, hp⟩, rfl⟩

private theorem primeSquares_subset_nonprime {x : ℝ} (hx : 0 ≤ x) :
    primeSquares x ⊆ nonprimeUpTo ⌊x⌋₊ := by
  intro n hn
  obtain ⟨p, hp, rfl, hcut⟩ := (mem_primeSquares_iff hx).mp hn
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨pow_pos hp.pos _, hcut⟩, Nat.Prime.not_prime_pow (x := p) le_rfl⟩

private theorem sum_nonprime_eq (x : ℝ) :
    (∑ n ∈ nonprimeUpTo ⌊x⌋₊, Λ n) = Chebyshev.psi x - Chebyshev.theta x := by
  simpa only [nonprimeUpTo] using (Chebyshev.psi_sub_theta_eq_sum_not_prime x).symm

private theorem sum_primeSquares (x : ℝ) :
    (∑ n ∈ primeSquares x, Λ n) = Chebyshev.theta (Real.sqrt x) := by
  rw [primeSquares, sum_map, Chebyshev.theta_eq_sum_primesLE]
  refine sum_congr rfl fun p hp => ?_
  change Λ (p ^ 2) = Real.log (p : ℝ)
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]

/-- Weighting the prime squares by the character removes exactly the square of two. -/
private theorem sum_primeSquares_twist (x : ℝ) :
    (∑ n ∈ primeSquares x, Λ n * chiFour n) =
      ∑ p ∈ (Nat.primesLE ⌊Real.sqrt x⌋₊).erase 2, Real.log (p : ℝ) := by
  rw [primeSquares, sum_map, ← filter_ne', sum_filter]
  refine sum_congr rfl fun p hp => ?_
  change Λ (p ^ 2) * chiFour (p ^ 2) = if p ≠ 2 then Real.log (p : ℝ) else 0
  have hp' := Nat.prime_of_mem_primesLE hp
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp', chiFour_prime_sq hp']
  by_cases h : p = 2 <;> simp [h]

private theorem norm_twistedMangoldt_sum_le (s : Finset ℕ) :
    ‖∑ n ∈ s, Λ n * chiFour n‖ ≤ ∑ n ∈ s, Λ n := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (norm_chiFour_le n)

private theorem norm_HChi_le (x : ℝ) :
    ‖HChi x‖ ≤ Chebyshev.psi x - Chebyshev.theta x := by
  rw [← sum_nonprime_eq x]
  exact norm_twistedMangoldt_sum_le _

/-- The absolute error after removing the odd prime squares is bounded by the
unweighted mass left after removing all prime squares. -/
private theorem norm_HChi_sub_square_sum_le {x : ℝ} (hx : 0 ≤ x) :
    ‖HChi x - (∑ p ∈ (Nat.primesLE ⌊Real.sqrt x⌋₊).erase 2, Real.log (p : ℝ))‖ ≤
      Chebyshev.psi x - Chebyshev.theta x - Chebyshev.theta (Real.sqrt x) := by
  rw [← sum_primeSquares_twist x, ← sum_nonprime_eq x, ← sum_primeSquares x, HChi]
  have hsub := primeSquares_subset_nonprime hx
  calc
    _ = ‖∑ n ∈ nonprimeUpTo ⌊x⌋₊ \ primeSquares x, Λ n * chiFour n‖ := by
      rw [sum_sdiff_eq_sub hsub]
    _ ≤ ∑ n ∈ nonprimeUpTo ⌊x⌋₊ \ primeSquares x, Λ n := norm_twistedMangoldt_sum_le _
    _ = _ := sum_sdiff_eq_sub hsub

private theorem odd_square_sum_eq {x : ℝ} (hx : 4 ≤ x) :
    (∑ p ∈ (Nat.primesLE ⌊Real.sqrt x⌋₊).erase 2, Real.log (p : ℝ)) =
      Chebyshev.theta (Real.sqrt x) - Real.log 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hroot : (2 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) hx0).mpr
      (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hx)
  have htwo : (2 : ℕ) ∈ Nat.primesLE ⌊Real.sqrt x⌋₊ :=
    Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr
      (by exact_mod_cast hroot), Nat.prime_two⟩
  rw [Chebyshev.theta_eq_sum_primesLE]
  have h := sum_erase_add _ (fun p : ℕ => Real.log (p : ℝ)) htwo
  exact eq_sub_of_add_eq (by simpa only [Nat.cast_ofNat] using h)

/-- The mod-four nonprime Mangoldt contribution is asymptotic to the square root. -/
theorem HChi_root_limit :
    Tendsto (fun x : ℝ => HChi x / Real.sqrt x) atTop (𝓝 1) := by
  have htheta : Tendsto (fun x : ℝ => Chebyshev.theta (Real.sqrt x) / Real.sqrt x)
      atTop (𝓝 1) := by
    simpa only [one_mul] using theta_sqrt_scale (c := 1) one_pos
  have hhigher : Tendsto (fun x : ℝ =>
      (Chebyshev.psi x - Chebyshev.theta x - Chebyshev.theta (Real.sqrt x)) / Real.sqrt x)
      atTop (𝓝 0) := by
    simpa only [sub_self, ← sub_div] using psi_theta_root_limit.sub htheta
  have herror : Tendsto (fun x : ℝ =>
      (HChi x - (Chebyshev.theta (Real.sqrt x) - Real.log 2)) / Real.sqrt x)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhigher
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    rw [norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg x), ← odd_square_sum_eq hx]
    exact div_le_div_of_nonneg_right (norm_HChi_sub_square_sum_le (x := x) (by linarith))
      (Real.sqrt_nonneg x)
  have htwo : Tendsto (fun x : ℝ => Real.log 2 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h := herror.add (htheta.sub htwo)
  simp only [sub_zero, zero_add] at h
  apply h.congr'
  exact Eventually.of_forall fun x => by
    change (HChi x - (Chebyshev.theta (Real.sqrt x) - Real.log 2)) / Real.sqrt x +
      (Chebyshev.theta (Real.sqrt x) / Real.sqrt x - Real.log 2 / Real.sqrt x) =
        HChi x / Real.sqrt x
    rw [← sub_div, ← add_div, sub_add_cancel]

private theorem HChi_measurable : Measurable HChi := by
  exact (measurable_of_countable (fun N : ℕ => ∑ n ∈ nonprimeUpTo N, Λ n * chiFour n)).comp
    measurable_id.nat_floor

private theorem HChi_kernel_integrable :
    IntegrableOn (fun t : ℝ => HChi t / t ^ 2) (Ioi 1) := by
  have hdiff : IntegrableOn
      (fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) (Ioi 1) :=
    diff_integrable
  apply hdiff.mono' (HChi_measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    change ‖HChi t / t ^ 2‖ ≤ (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
    rw [norm_div, Real.norm_of_nonneg (sq_nonneg t)]
    exact div_le_div_of_nonneg_right (norm_HChi_le t) (sq_nonneg t)

/-- The mod-four nonprime correction to the integrated ramp has coefficient two
at the square-root scale. -/
theorem HChi_ramp_tail_root_limit :
    Tendsto (fun x : ℝ => x * (∫ t in Ioi x, HChi t / t ^ 2) / Real.sqrt x)
      atTop (𝓝 2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp HChi_root_limit) (ε / 4) (by positivity))
  filter_upwards [eventually_ge_atTop (max T 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hbounds (t : ℝ) (ht : t ∈ Ioi x) :
      (1 - ε / 4) * Real.sqrt t ≤ HChi t ∧ HChi t ≤ (1 + ε / 4) * Real.sqrt t := by
    have ht' : x < t := ht
    have hts := Real.sqrt_pos.mpr (hx0.trans ht')
    have h := hT t ((le_max_left _ _).trans (hx.trans ht'.le))
    rw [Real.dist_eq, abs_lt] at h
    exact ⟨(le_div_iff₀ hts).mp (by linarith only [h.1]),
      (div_le_iff₀ hts).mp (by linarith only [h.2])⟩
  have hi := HChi_kernel_integrable.mono_set (Ioi_subset_Ioi hx1)
  have hr : IntegrableOn (fun t : ℝ => Real.sqrt t / t ^ 2) (Ioi x) :=
    root_integrable hx0
  have hrEq : (∫ t in Ioi x, Real.sqrt t / t ^ 2) = 2 / Real.sqrt x :=
    root_integral hx0
  have hl : (1 - ε / 4) * (2 / Real.sqrt x) ≤ ∫ t in Ioi x, HChi t / t ^ 2 := by
    rw [← hrEq, ← integral_const_mul]
    apply setIntegral_mono_on (hr.const_mul _) hi measurableSet_Ioi
    intro t ht
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (hbounds t ht).1 (sq_nonneg t)
  have hu : (∫ t in Ioi x, HChi t / t ^ 2) ≤ (1 + ε / 4) * (2 / Real.sqrt x) := by
    rw [← hrEq, ← integral_const_mul]
    apply setIntegral_mono_on hi (hr.const_mul _) measurableSet_Ioi
    intro t ht
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (hbounds t ht).2 (sq_nonneg t)
  have hl' := mul_le_mul_of_nonneg_left hl hs0.le
  have hu' := mul_le_mul_of_nonneg_left hu hs0.le
  have hcancel (a : ℝ) : Real.sqrt x * (a * (2 / Real.sqrt x)) = a * 2 := by
    field_simp [hs0.ne'] <;> ring
  rw [hcancel] at hl' hu'
  have hxdiv : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hs0.ne').mpr
    simpa only [pow_two] using (Real.sq_sqrt hx0.le).symm
  have hscale (a : ℝ) : x * a / Real.sqrt x = Real.sqrt x * a := by
    calc
      _ = (x / Real.sqrt x) * a := by ring
      _ = _ := by rw [hxdiv]
  rw [Real.dist_eq, abs_lt, hscale]
  constructor <;> linarith only [hl', hu', hε]

end D5.S3.CharacterSums.DirichletRampPrimeTail
