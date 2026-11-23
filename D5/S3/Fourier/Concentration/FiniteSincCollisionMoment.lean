/- GID: D5/S3/Fourier/Concentration/FiniteSincCollisionMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteSincCollisionMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sinc-squared moments are controlled by weighted near-collisions. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.SpectralSampling
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Control of a finite weighted sinc matrix at the scale of its near-collisions. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

namespace D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

private def binKernel (d : ℤ) : ℝ :=
  if d.natAbs ≤ 1 then 1 else 1 / ((d.natAbs : ℝ) - 1) ^ 2

private theorem binKernel_nonneg (d : ℤ) : 0 ≤ binKernel d := by
  unfold binKernel
  split <;> positivity

private theorem binKernel_even : Function.Even binKernel := by
  intro d
  simp [binKernel]

private theorem binKernel_succ (n : ℕ) :
    binKernel ((n + 1 : ℕ) : ℤ) = (if n = 0 then 1 else 0) + 1 / (n : ℝ) ^ 2 := by
  cases n with
  | zero => norm_num [binKernel]
  | succ n =>
    rw [binKernel, Int.natAbs_natCast, ite_eq_right (by omega)]
    simp [Nat.cast_succ]

private theorem binKernel_sum :
    Summable binKernel ∧ (∑' d : ℤ, binKernel d) ≤ 7 := by
  have hsingle : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by simp)
  have hnat : Summable (fun n : ℕ => binKernel (n : ℤ)) := by
    rw [← summable_nat_add_iff 1]
    simp_rw [binKernel_succ]
    exact hsingle.add hasSum_zeta_two.summable
  have hint : Summable binKernel := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨hnat, hnat.congr fun n => (binKernel_even (n : ℤ)).symm⟩
  refine ⟨hint, ?_⟩
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat binKernel_even hint,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => binKernel (n : ℤ))]
  have hsum :
      (∑' n : ℕ, binKernel ((n + 1 : ℕ) : ℤ)) = 1 + Real.pi ^ 2 / 6 := by
    simp_rw [binKernel_succ]
    rw [hsingle.tsum_add hasSum_zeta_two.summable, tsum_ite_eq, hasSum_zeta_two.tsum_eq]
  rw [hsum, show binKernel 0 = 1 by norm_num [binKernel]]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have hpi : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
  linarith

private theorem row_le (bins : Finset ℤ) (k : ℤ) :
    ∑ l ∈ bins, binKernel (k - l) ≤ 7 := by
  let e : ℤ ≃ ℤ := Equiv.subLeft k
  change (∑ l ∈ bins, binKernel (e.toEmbedding l)) ≤ 7
  rw [← sum_map bins e.toEmbedding]
  exact (binKernel_sum.1.sum_le_tsum _ (fun d _ => binKernel_nonneg d)).trans binKernel_sum.2

private theorem sinc_sq_le_binKernel (x y : ℝ) :
    Real.sinc (x - y) ^ 2 ≤ binKernel (frequencyBin x - frequencyBin y) := by
  let d := frequencyBin x - frequencyBin y
  change Real.sinc (x - y) ^ 2 ≤ binKernel d
  unfold binKernel
  split_ifs with h
  · have hs : |Real.sinc (x - y)| ≤ |(1 : ℝ)| := by
      simpa only [abs_one] using Real.abs_sinc_le_one (x - y)
    simpa only [one_pow] using sq_le_sq.mpr hs
  · have hx := mem_frequencyBin x
    have hy := mem_frequencyBin y
    have hd : (d.natAbs : ℝ) - 1 ≤ |x - y| := by
      rw [Nat.cast_natAbs]
      push_cast
      have he : (d : ℝ) = (frequencyBin x : ℝ) - (frequencyBin y : ℝ) := by
        simp [d]
      rw [he]
      rcases le_total (frequencyBin x : ℝ) (frequencyBin y : ℝ) with hxy | hyx
      · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith [hx.2, hy.1, neg_abs_le (x - y)]
      · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        linarith [hx.1, hy.2, le_abs_self (x - y)]
    have hdpos : 0 < (d.natAbs : ℝ) - 1 := by
      have : 1 < d.natAbs := by omega
      exact sub_pos.mpr (by exact_mod_cast this)
    have hxy : x - y ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hd
      exact (not_lt_of_ge hd) hdpos
    calc
      _ = (|Real.sin (x - y)| / |x - y|) ^ 2 := by
        rw [Real.sinc_of_ne_zero hxy, ← abs_div, sq_abs]
      _ ≤ (1 / ((d.natAbs : ℝ) - 1)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hdpos hd
          |>.trans' (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _))
      _ = _ := by rw [div_pow, one_pow]

private theorem bin_quadratic_le (bins : Finset ℤ) (mass : ℤ → ℝ) :
    (∑ k ∈ bins, ∑ l ∈ bins, mass k * mass l * binKernel (k - l)) ≤
      7 * ∑ k ∈ bins, mass k ^ 2 := by
  have hswap :
      (∑ k ∈ bins, ∑ l ∈ bins, mass l ^ 2 * binKernel (k - l)) =
        ∑ k ∈ bins, ∑ l ∈ bins, mass k ^ 2 * binKernel (k - l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [show l - k = -(k - l) by omega, binKernel_even]
  calc
    _ ≤ ∑ k ∈ bins, ∑ l ∈ bins, (mass k ^ 2 + mass l ^ 2) / 2 * binKernel (k - l) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      refine mul_le_mul_of_nonneg_right ?_ (binKernel_nonneg _)
      nlinarith only [sq_nonneg (mass k - mass l)]
    _ = ∑ k ∈ bins, ∑ l ∈ bins, mass k ^ 2 * binKernel (k - l) := by
      simp only [div_mul_eq_mul_div, ← Finset.sum_div, add_mul, Finset.sum_add_distrib]
      rw [hswap]
      ring
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [← Finset.mul_sum, mul_comm 7]
      exact mul_le_mul_of_nonneg_left (row_le bins k) (sq_nonneg _)

private theorem regroup {I : Type*} (s : Finset I) (b : I → ℤ) (c : I → ℝ)
    (K : ℤ → ℤ → ℝ) :
    let mass := fun k => ∑ i ∈ s with b i = k, c i
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * K (b i) (b j)) =
      ∑ k ∈ s.image b, ∑ l ∈ s.image b, mass k * mass l * K k l := by
  intro mass
  let bins := s.image b
  have hb : ∀ i ∈ s, b i ∈ bins := fun i hi => mem_image_of_mem b hi
  calc
    _ = ∑ k ∈ bins, ∑ i ∈ s with b i = k, ∑ l ∈ bins, ∑ j ∈ s with b j = l,
        c i * c j * K (b i) (b j) := by
      rw [sum_fiberwise_of_maps_to hb]
      refine sum_congr rfl fun i hi => ?_
      exact (sum_fiberwise_of_maps_to hb _).symm
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      rw [sum_comm]
      refine sum_congr rfl fun l hl => ?_
      dsimp only [mass]
      simp only [sum_mul]
      refine sum_congr rfl fun i hi => ?_
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [(mem_filter.mp hi).2, (mem_filter.mp hj).2]

/-- The mass of pairs of sampled frequencies whose difference has magnitude at most `r`. -/
def nearCollisionMass {I : Type*} (s : Finset I) (x c : I → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, if |x i - x j| ≤ r then c i * c j else 0

private theorem sinc_sq_ge_quarter {x : ℝ} (hx : |x| ≤ 1) :
    (1 : ℝ) / 4 ≤ Real.sinc x ^ 2 := by
  have hcos := (Real.one_sub_sq_div_two_le_cos (x := x))
  have hsinc : Real.cos x ≤ Real.sinc x :=
    Real.cos_le_sinc (hx.trans_lt (by linarith [Real.pi_gt_three]))
  have hx' : |x| ≤ |(1 : ℝ)| := by simpa only [abs_one] using hx
  have hsq : x ^ 2 ≤ 1 := by simpa only [one_pow] using sq_le_sq.mpr hx'
  have hhalf : (1 : ℝ) / 2 ≤ Real.sinc x := by linarith
  nlinarith only [sq_nonneg (Real.sinc x - 1 / 2), hhalf]

/-- A sinc-squared pair sum is comparable to the weighted collision mass at its frequency scale. -/
theorem sinc_pair_comparison {I : Type*} (s : Finset I) (x c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) {r : ℝ} (hr : 0 < r) :
    nearCollisionMass s x c r / 4 ≤
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.sinc ((x i - x j) / r) ^ 2) ∧
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.sinc ((x i - x j) / r) ^ 2) ≤
      7 * nearCollisionMass s x c r := by
  classical
  constructor
  · simp only [nearCollisionMass, sum_div]
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    have hnonneg := mul_nonneg (hc i hi) (hc j hj)
    split_ifs with h
    · rw [div_eq_mul_inv, show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
      apply mul_le_mul_of_nonneg_left _ hnonneg
      apply sinc_sq_ge_quarter
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul]
      exact h
    · rw [zero_div]
      positivity
  · let b (i : I) := frequencyBin (x i / r)
    let bins := s.image b
    let mass (k : ℤ) := ∑ i ∈ s with b i = k, c i
    have hdiag : (∑ k ∈ bins, mass k ^ 2) ≤ nearCollisionMass s x c r := by
      have hregroup := regroup s b c (fun k l => if k = l then 1 else 0)
      simp only [mul_ite, mul_one, mul_zero] at hregroup
      have heq : (∑ i ∈ s, ∑ j ∈ s, if b i = b j then c i * c j else 0) =
          ∑ k ∈ bins, mass k ^ 2 := by
        simp only [pow_two]
        change _ = ∑ k ∈ s.image b, mass k * mass k
        rw [hregroup]
        apply sum_congr rfl
        intro k hk
        simp [hk, mass]
      rw [← heq]
      refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
      by_cases hij : b i = b j
      · have hx := mem_frequencyBin (x i / r)
        have hy := mem_frequencyBin (x j / r)
        change (x i / r) ∈ Set.Ioc (b i : ℝ) ((b i : ℝ) + 1) at hx
        change (x j / r) ∈ Set.Ioc (b j : ℝ) ((b j : ℝ) + 1) at hy
        rw [← hij] at hy
        have hdist : |x i - x j| ≤ r := by
          have hs : |(x i - x j) / r| ≤ 1 := by
            rw [sub_div]
            exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
          rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul] at hs
          exact hs
        simp [hij, hdist]
      · simp only [hij, ite_false]
        split_ifs
        · exact mul_nonneg (hc i hi) (hc j hj)
        · exact le_rfl
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * binKernel (b i - b j) := by
        refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc i hi) (hc j hj))
        rw [sub_div]
        exact sinc_sq_le_binKernel (x i / r) (x j / r)
      _ = ∑ k ∈ bins, ∑ l ∈ bins, mass k * mass l * binKernel (k - l) :=
        regroup s b c (fun k l => binKernel (k - l))
      _ ≤ 7 * ∑ k ∈ bins, mass k ^ 2 := bin_quadratic_le bins mass
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (by norm_num)

end D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
