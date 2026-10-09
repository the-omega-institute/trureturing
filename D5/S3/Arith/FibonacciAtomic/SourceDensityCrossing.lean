/- GID: D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real finite-product extension of adjacent Fibonacci source densities. -/

import D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import D5.S1.Scale.Fibonacci
import D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing

open scoped BigOperators
open Filter Set SourceDensityMonotonicity

/-- Density of the iterated substitution image in its actual composition fiber.
Its interpretation on the `t`-leaf source grid requires `1 ≤ t` and `i ≤ t`.
The definition still has values outside this domain, for example `fiberCount (0, 0) = 1`.
The theorem uses only `j + 1 ≤ t` with `i = j` or `i = j + 1`. -/
noncomputable def sourceDensity (k t i : ℕ) : ℝ :=
  (GenealogicalFiberTransport.fiberCount (t - i, i) : ℝ) /
    (GenealogicalFiberTransport.fiberCount
      (GraftAffineClosure.step^[3 * k] (t - i, i)) : ℝ)

/-- Strict increase, asymptotic slope, and the unique bounded crossing of the real ratio. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    0 < c k ∧
    (∀ t : ℝ, (j : ℝ) + 1 ≤ t →
      0 < q k j t ∧
      HasDerivAt (fun z : ℝ => Real.log (q k j z)) (g k j t) t ∧
      lowerEnvelope k j t ≤ g k j t) ∧
    StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) ∧
    Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) ∧
    (∃! τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1) ∧
    (∃ τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1 ∧
      2 * j + 1 < τ ∧ τ < j + (j + 1) / c k ∧
      ∀ t : ℕ, j + 1 ≤ t →
        (q k j t < 1 ↔ (t : ℝ) < τ) ∧
        (q k j t = 1 ↔ (t : ℝ) = τ) ∧
        (1 < q k j t ↔ τ < (t : ℝ)) ∧
        (sourceDensity k t (j + 1) / sourceDensity k t j < 1 ↔ (t : ℝ) < τ) ∧
        (sourceDensity k t (j + 1) / sourceDensity k t j = 1 ↔ (t : ℝ) = τ) ∧
        (1 < sourceDensity k t (j + 1) / sourceDensity k t j ↔ τ < (t : ℝ))) ∧
    (∀ t : ℕ, j + 1 ≤ t →
      q k j t = sourceDensity k t (j + 1) / sourceDensity k t j) := by
  have rising_pos (x : ℝ) (hx : 0 < x) (m : ℕ) : 0 < rising x m :=
    Finset.prod_pos (fun i _ => by positivity)
  have real :
    0 < c k ∧
    (∀ t : ℝ, (j : ℝ) + 1 ≤ t →
      0 < q k j t ∧
      HasDerivAt (fun z : ℝ => Real.log (q k j z)) (g k j t) t ∧
      lowerEnvelope k j t ≤ g k j t) ∧
    StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) ∧
    Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) ∧
    (∃! τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1) ∧
    (∃ τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1 ∧
      2 * j + 1 < τ ∧ τ < j + (j + 1) / c k ∧
      ∀ t : ℕ, j + 1 ≤ t →
        (q k j t < 1 ↔ (t : ℝ) < τ) ∧
        (q k j t = 1 ↔ (t : ℝ) = τ) ∧
        (1 < q k j t ↔ τ < (t : ℝ))) := by
    have reciprocal_block_bounds (x : ℝ) (hx : 0 < x) (m : ℕ) :
        Real.log (x + m) - Real.log x - m / (2 * x * (x + m)) ≤
          ∑ i ∈ Finset.range m, 1 / (x + 1 + i) ∧
        (1 / 2 < x → (∑ i ∈ Finset.range m, 1 / (x - 1 / 2 + i)) ≤
          Real.log (x + m) - Real.log x + m / ((x - 1 / 2) * (x + m - 1 / 2))) := by
      have unit (y : ℝ) (hy : 0 < y) :
          1 / (y + 1 / 2) ≤ Real.log (y + 1) - Real.log y ∧
          Real.log (y + 1) - Real.log y ≤ (1 / y + 1 / (y + 1)) / 2 := by
        have h := D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich.logMean_kernel_sandwich
          (a := y + 1) (b := y) (by linarith) hy (by linarith)
        simp only [add_sub_cancel_right, div_one, ← one_div] at h
        constructor
        · convert h.1 using 1 <;> field_simp <;> ring
        · convert h.2 using 1 <;> ring
      have unit_upper (y : ℝ) (hy : 0 < y) := (unit y hy).2
      have unit_lower (y : ℝ) (hy : 0 < y) := (unit y hy).1
      have lower (m : ℕ) :
          Real.log (x + m) - Real.log x - (1 / x - 1 / (x + m)) / 2 ≤
            ∑ i ∈ Finset.range m, 1 / (x + 1 + i) := by
        induction m with
        | zero => simp
        | succ m hm =>
          rw [Finset.sum_range_succ, Nat.cast_add_one]
          have h := unit_upper (x + m) (by positivity)
          have he : x + 1 + m = x + m + 1 := by ring
          rw [he]
          simp only [← add_assoc] at *
          linarith
      have midpoint (m : ℕ) :
          (∑ i ∈ Finset.range m, 1 / (x + 1 / 2 + i)) ≤
            Real.log (x + m) - Real.log x := by
        induction m with
        | zero => simp
        | succ m hm =>
          rw [Finset.sum_range_succ, Nat.cast_add_one]
          have h := unit_lower (x + m) (by positivity)
          have he : x + 1 / 2 + m = x + m + 1 / 2 := by ring
          rw [he]
          simp only [← add_assoc] at *
          linarith
      constructor
      · have he : (1 / x - 1 / (x + m)) / 2 = m / (2 * x * (x + m)) := by
          have hp : 0 < x + m := by positivity
          field_simp <;> ring
        simpa only [he] using lower m
      · intro hxhalf
        have telescope (m : ℕ) :
            (∑ i ∈ Finset.range m, 1 / (x - 1 / 2 + i)) -
              (∑ i ∈ Finset.range m, 1 / (x + 1 / 2 + i)) =
              1 / (x - 1 / 2) - 1 / (x + m - 1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          convert Finset.sum_range_sub' (fun i : ℕ => 1 / (x - 1 / 2 + (i : ℝ))) m using 1
          · congr 1
            funext i
            push_cast
            congr 1
            ring
          · simp only [Nat.cast_zero, add_zero]
            congr 1
            ring
        have he : 1 / (x - 1 / 2) - 1 / (x + m - 1 / 2) =
            m / ((x - 1 / 2) * (x + m - 1 / 2)) := by
          have hp : 0 < x - 1 / 2 := by linarith
          have hq : 0 < x + m - 1 / 2 := by
            have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            linarith
          rw [div_sub_div _ _ hp.ne' hq.ne']
          congr 1
          ring
        linarith [telescope m, midpoint m]


    have heNat : 0 < E k := Nat.fib_pos.mpr (by omega)
    have haNat : 0 < A k := Nat.fib_pos.mpr (by omega)
    have hdNat : 0 < D k := Nat.fib_pos.mpr (by omega)
    have hlNat : 0 < L k := Nat.fib_pos.mpr (by omega)
    have he : (0 : ℝ) < E k := by exact_mod_cast heNat
    have hα : (0 : ℝ) < A k := by exact_mod_cast haNat
    have hδ : (0 : ℝ) < D k := by exact_mod_cast hdNat
    have hℓ : (0 : ℝ) < L k := by exact_mod_cast hlNat
    have hδeq : D k = E k + A k := by
      dsimp [D, E, A]
      rw [show 3 * k = (3 * k - 2) + 2 by omega, Nat.fib_add_two]
      congr 2 <;> omega
    have hℓeq : L k = A k + D k := by
      dsimp [L, A, D]
      rw [show 3 * k + 1 = (3 * k - 1) + 2 by omega, Nat.fib_add_two]
      congr 2 <;> omega
    have hcassini : ((A k : ℝ) ^ 2 - D k * E k) ^ 2 = 1 := by
      have hc := D5.S1.Scale.fib_cassini_from_golden_norm (3 * k - 2)
      have h1 : 3 * k - 2 + 1 = 3 * k - 1 := by omega
      have h2 : 3 * k - 2 + 2 = 3 * k := by omega
      rw [h1, h2] at hc
      have hp : ((-1 : ℤ) ^ (3 * k - 1)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm (3 * k - 1) 2, pow_mul]
        norm_num
      have hi : ((A k : ℤ) ^ 2 - D k * E k) ^ 2 = 1 := by
        dsimp [A, D, E]
        nlinarith [congrArg (fun z : ℤ => z ^ 2) hc]
      exact_mod_cast hi
    have hL3 : (3 : ℝ) ≤ L k := by
      have h := Nat.fib_mono (show 4 ≤ 3 * k + 1 by omega)
      norm_num at h
      exact_mod_cast h
    have coords (z : ℝ) (hz : (j : ℝ) + 1 / 2 < z) :
        0 < a k j z ∧ 0 < b k j z ∧ 0 < n k j z - 1 / 2 ∧ 0 < z - j := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hzpos : 0 < z := by linarith
      have ha : 0 < a k j z := by dsimp [a]; positivity
      have hb : 0 < b k j z := by dsimp [b]; positivity
      have hn : 1 / 2 < n k j z := by
        have hmin : 3 * z ≤ n k j z := by
          dsimp [n]
          nlinarith [mul_nonneg hδ.le hj, mul_le_mul_of_nonneg_right hL3 hzpos.le]
        linarith
      exact ⟨ha, hb, sub_pos.mpr hn, by linarith⟩
    have positive (z : ℝ) (hz : (j : ℝ) + 1 / 2 < z) : 0 < q k j z := by
      obtain ⟨ha, hb, hn, ht⟩ := coords z hz
      dsimp [q, H]
      exact div_pos (mul_pos ht
        (div_pos (mul_pos (rising_pos _ (by linarith) _) (rising_pos _ (by linarith) _))
          (mul_pos (by positivity) (rising_pos _ hn _)))) (by positivity)
    have analytic : ∀ t : ℝ, (j : ℝ) + 1 ≤ t →
        0 < q k j t ∧
        HasDerivAt (fun z : ℝ => Real.log (q k j z)) (g k j t) t ∧
        lowerEnvelope k j t ≤ g k j t := by
      intro t ht
      have ht0 : 0 < t := by have := Nat.cast_nonneg (α := ℝ) j; linarith
      have hhalf : (j : ℝ) + 1 / 2 < t := by linarith
      obtain ⟨ha, hb, hn, htj⟩ := coords t hhalf
      refine ⟨positive t hhalf, ?_, ?_⟩
      · let f : ℝ → ℝ := fun z => Real.log (z - j) +
          (∑ i ∈ Finset.range (E k), Real.log (a k j z + 1 + i)) +
          (∑ i ∈ Finset.range (A k), Real.log (b k j z + 1 + i)) -
          ((D k : ℝ) * Real.log 4 +
            ∑ i ∈ Finset.range (D k), Real.log (n k j z - 1 / 2 + i)) - Real.log (j + 1)
        have left (i : ℕ) :
            HasDerivAt (fun z : ℝ => Real.log (a k j z + 1 + i))
              (A k / (a k j t + 1 + i)) t := by
          apply HasDerivAt.log _ (by positivity)
          simpa [a] using ((((hasDerivAt_id t).const_mul (A k : ℝ)).add_const
            ((E k : ℝ) * j)).add_const 1).add_const (i : ℝ)
        have right (i : ℕ) :
            HasDerivAt (fun z : ℝ => Real.log (b k j z + 1 + i))
              (D k / (b k j t + 1 + i)) t := by
          apply HasDerivAt.log _ (by positivity)
          simpa [b] using ((((hasDerivAt_id t).const_mul (D k : ℝ)).add_const
            ((A k : ℝ) * j)).add_const 1).add_const (i : ℝ)
        have denominator (i : ℕ) :
            HasDerivAt (fun z : ℝ => Real.log (n k j z - 1 / 2 + i))
              (L k / (n k j t - 1 / 2 + i)) t := by
          apply HasDerivAt.log _ (by positivity)
          simpa [n] using ((((hasDerivAt_id t).const_mul (L k : ℝ)).add_const
            ((D k : ℝ) * j)).sub_const (1 / 2)).add_const (i : ℝ)
        have raw : HasDerivAt f
            (1 / (t - j) + (∑ i ∈ Finset.range (E k), A k / (a k j t + 1 + i)) +
              (∑ i ∈ Finset.range (A k), D k / (b k j t + 1 + i)) -
              (∑ i ∈ Finset.range (D k), L k / (n k j t - 1 / 2 + i))) t := by
          simpa only [f, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, id_eq, one_div, add_zero, sub_zero] using
            (((((hasDerivAt_id t).sub_const (j : ℝ)).log htj.ne').add
              (HasDerivAt.sum (u := Finset.range (E k)) (fun i _ => left i))).add
              (HasDerivAt.sum (u := Finset.range (A k)) (fun i _ => right i))).sub
              ((HasDerivAt.sum (u := Finset.range (D k)) (fun i _ => denominator i)).const_add
                ((D k : ℝ) * Real.log 4)) |>.sub_const (Real.log (j + 1))
        have hd : HasDerivAt f (g k j t) t := by
          convert raw using 1
          simp only [g, div_eq_mul_inv, ← Finset.mul_sum, mul_one, one_mul]
        apply hd.congr_of_eventuallyEq
        filter_upwards [eventually_gt_nhds hhalf] with z hz
        obtain ⟨ha, hb, hn, hzj⟩ := coords z hz
        have hp1 := rising_pos (a k j z + 1) (by linarith) (E k)
        have hp2 := rising_pos (b k j z + 1) (by linarith) (A k)
        have hp3 := rising_pos (n k j z - 1 / 2) hn (D k)
        dsimp [q, H, f]
        rw [Real.log_div (mul_pos hzj (div_pos (mul_pos hp1 hp2)
          (mul_pos (by positivity) hp3))).ne' (by positivity),
          Real.log_mul hzj.ne' (div_pos (mul_pos hp1 hp2) (mul_pos (by positivity) hp3)).ne',
          Real.log_div (mul_pos hp1 hp2).ne' (mul_pos (by positivity) hp3).ne',
          Real.log_mul hp1.ne' hp2.ne', Real.log_mul (by positivity) hp3.ne', Real.log_pow]
        simp only [rising]
        rw [Real.log_prod (fun i _ => by positivity), Real.log_prod (fun i _ => by positivity),
          Real.log_prod (fun i _ => by positivity)]
        ring
      · have hleft := (reciprocal_block_bounds (a k j t) ha (E k)).1
        have hright := (reciprocal_block_bounds (b k j t) hb (A k)).1
        have hdenom := (reciprocal_block_bounds (n k j t) (by linarith) (D k)).2 (by linarith)
        have hcomp := logarithmic_compensation (E k) (A k) (D k) (L k) t j
          he hα hδ hℓ (by exact_mod_cast hδeq) (by exact_mod_cast hℓeq) hcassini ht0
          (Nat.cast_nonneg j)
        have hae : (A k : ℝ) * t + E k * (j + 1) = a k j t + E k := by dsimp [a]; ring
        have hba : (D k : ℝ) * t + A k * (j + 1) = b k j t + A k := by dsimp [b]; ring
        have hnd : (L k : ℝ) * t + D k * (j + 1) = n k j t + D k := by dsimp [n]; ring
        rw [hae, hba, hnd] at hcomp
        change -(j + 1 / 2) / ((L k : ℝ) * A k * D k * t ^ 2) ≤
          A k * (Real.log (a k j t + E k) - Real.log (a k j t)) +
          D k * (Real.log (b k j t + A k) - Real.log (b k j t)) -
          L k * (Real.log (n k j t + D k) - Real.log (n k j t)) at hcomp
        have hl := mul_le_mul_of_nonneg_left hleft hα.le
        have hr := mul_le_mul_of_nonneg_left hright hδ.le
        have hn' := mul_le_mul_of_nonneg_left hdenom hℓ.le
        dsimp [lowerEnvelope, g]
        simp only [mul_sub, mul_add, mul_div_assoc, neg_div] at hl hr hn' hcomp ⊢
        linarith
    have monotonic : StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) := by
      have hD2 : (2 : ℝ) ≤ D k := by
        have h := Nat.fib_mono (show 3 ≤ 3 * k by omega)
        norm_num at h
        exact_mod_cast h
      have hEA : (E k : ℝ) ≤ A k := by
        exact_mod_cast (Nat.fib_mono (show 3 * k - 2 ≤ 3 * k - 1 by omega))
      have coarse (v : ℕ) : 3 * Nat.fib (v + 2) ≤ 2 * Nat.fib (v + 3) ∧
          Nat.fib (v + 3) ≤ 2 * Nat.fib (v + 2) := by
        have h1 := Nat.fib_add_two (n := v)
        have h2 := Nat.fib_add_two (n := v + 1)
        have hm := Nat.fib_mono (show v ≤ v + 1 by omega)
        rw [show v + 1 + 2 = v + 3 by omega, show v + 1 + 1 = v + 2 by omega] at h2
        omega
      have hAD : (3 : ℝ) * A k ≤ 2 * D k := by
        have h := (coarse (3 * k - 3)).1
        rw [show 3 * k - 3 + 2 = 3 * k - 1 by omega,
          show 3 * k - 3 + 3 = 3 * k by omega] at h
        exact_mod_cast h
      have hDL : (3 : ℝ) * D k ≤ 2 * L k := by
        have h := (coarse (3 * k - 2)).1
        rw [show 3 * k - 2 + 2 = 3 * k by omega,
          show 3 * k - 2 + 3 = 3 * k + 1 by omega] at h
        exact_mod_cast h
      let y : ℝ := E k / A k
      let r : ℝ := A k / D k
      let s : ℝ := D k / L k
      let u : ℝ := 1 / (2 * L k)
      let v : ℝ := 1 / ((L k : ℝ) * A k * D k)
      have hy : 0 < y := div_pos he hα
      have hr : 0 < r := div_pos hα hδ
      have hs : 0 < s := div_pos hδ hℓ
      have hu : 0 < u := by dsimp [u]; positivity
      have hv : 0 < v := by dsimp [v]; positivity
      have hy1 : y ≤ 1 := (div_le_one hα).mpr hEA
      have hr23 : r ≤ 2 / 3 := by dsimp [r]; apply (div_le_iff₀ hδ).mpr; linarith
      have hs23 : s ≤ 2 / 3 := by dsimp [s]; apply (div_le_iff₀ hℓ).mpr; linarith
      have hu6 : u ≤ 1 / 6 := by dsimp [u]; apply (div_le_iff₀ (by positivity)).mpr; linarith
      have hus : u ≤ s := by dsimp [u, s]; field_simp; linarith
      have hv6 : v ≤ 1 / 6 := by
        dsimp [v]
        apply (div_le_iff₀ (by positivity)).mpr
        have hA1 : (1 : ℝ) ≤ A k := by exact_mod_cast haNat
        have hprod := mul_le_mul hL3 hA1 (by norm_num) hℓ.le
        have hprod' := mul_le_mul hprod hD2 (by norm_num) (by positivity)
        linarith
      have envelope_eq (t : ℝ) : lowerEnvelope k j t =
          1 / (t - j) - v * (j + 1 / 2) / t ^ 2 -
            y / (2 * (t + y * j) * (t + y * (j + 1))) -
            r / (2 * (t + r * j) * (t + r * (j + 1))) -
            s / ((t + s * j - u) * (t + s * (j + 1) - u)) := by
        dsimp [lowerEnvelope, a, b, n, y, r, s, u, v]
        field_simp
        <;> ring
      have gpositive (t : ℝ) (ht : (j : ℝ) + 1 ≤ t) : 0 < g k j t := by
        have ht1 : 1 ≤ t := by have := Nat.cast_nonneg (α := ℝ) j; linarith
        have ht0 : 0 < t := by linarith
        have htj : 0 < t - j := by linarith
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have hlower := (analytic t ht).2.2
        rw [envelope_eq] at hlower
        by_cases ht2 : 2 ≤ t
        · have e1 : y / (2 * (t + y * j) * (t + y * (j + 1))) ≤ 1 / (2 * t ^ 2) := by
            have h1 : t ≤ t + y * j := by linarith [mul_nonneg hy.le hj]
            have h2 : t ≤ t + y * (j + 1) := by linarith [mul_nonneg hy.le (by linarith : (0 : ℝ) ≤ j + 1)]
            have hp := mul_le_mul h1 h2 ht0.le (by positivity)
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            nlinarith only [hp, mul_le_mul_of_nonneg_right hy1 (show 0 ≤ 2 * t ^ 2 by positivity)]
          have e2 : r / (2 * (t + r * j) * (t + r * (j + 1))) ≤ 1 / (3 * t ^ 2) := by
            have h1 : t ≤ t + r * j := by linarith [mul_nonneg hr.le hj]
            have h2 : t ≤ t + r * (j + 1) := by linarith [mul_nonneg hr.le (by linarith : (0 : ℝ) ≤ j + 1)]
            have hp := mul_le_mul h1 h2 ht0.le (by positivity)
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            nlinarith only [hp, mul_le_mul_of_nonneg_right hr23 (show 0 ≤ 3 * t ^ 2 by positivity)]
          have e3 : s / ((t + s * j - u) * (t + s * (j + 1) - u)) ≤ 8 / (11 * t ^ 2) := by
            have h1 : (11 / 12) * t ≤ t + s * j - u := by
              nlinarith [mul_nonneg hs.le hj]
            have h2 : t ≤ t + s * (j + 1) - u := by nlinarith [mul_nonneg hs.le hj]
            have hp := mul_le_mul h1 h2 ht0.le (by linarith)
            apply (div_le_div_iff₀ (by nlinarith) (by positivity)).mpr
            nlinarith only [hp, mul_le_mul_of_nonneg_right hs23 (show 0 ≤ 11 * t ^ 2 by positivity)]
          have e4 : v * (j + 1 / 2) / t ^ 2 ≤ (t - 1 / 2) / (6 * t ^ 2) := by
            have h1 := mul_le_mul hv6 (show (j : ℝ) + 1 / 2 ≤ t - 1 / 2 by linarith)
              (by linarith : (0 : ℝ) ≤ j + 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 6)
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            nlinarith only [mul_le_mul_of_nonneg_right h1 (show 0 ≤ 6 * t ^ 2 by positivity)]
          have e0 : 1 / t ≤ 1 / (t - j) := one_div_le_one_div_of_le htj (by linarith)
          have hp : 0 < 1 / t - (t - 1 / 2) / (6 * t ^ 2) - 1 / (2 * t ^ 2) -
              1 / (3 * t ^ 2) - 8 / (11 * t ^ 2) := by
            have heq : 1 / t - (t - 1 / 2) / (6 * t ^ 2) - 1 / (2 * t ^ 2) -
                1 / (3 * t ^ 2) - 8 / (11 * t ^ 2) = (110 * t - 195) / (132 * t ^ 2) := by
              field_simp <;> ring
            rw [heq]
            exact div_pos (by linarith) (by positivity)
          linarith
        · have hj0 : j = 0 := by
            have ht2' : t < 2 := lt_of_not_ge ht2
            have : (j : ℝ) < 1 := by linarith
            have : j < 1 := by exact_mod_cast this
            omega
          subst j
          by_cases hk2 : 2 ≤ k
          · have hL13 : (13 : ℝ) ≤ L k := by
              have h := Nat.fib_mono (show 7 ≤ 3 * k + 1 by omega)
              norm_num at h
              exact_mod_cast h
            have hA5 : (5 : ℝ) ≤ A k := by
              have h := Nat.fib_mono (show 5 ≤ 3 * k - 1 by omega)
              norm_num at h
              exact_mod_cast h
            have hD8 : (8 : ℝ) ≤ D k := by
              have h := Nat.fib_mono (show 6 ≤ 3 * k by omega)
              norm_num at h
              exact_mod_cast h
            have hu26 : u ≤ 1 / 26 := by
              dsimp [u]; apply (div_le_iff₀ (by positivity)).mpr; linarith
            have hv520 : v ≤ 1 / 520 := by
              dsimp [v]; apply (div_le_iff₀ (by positivity)).mpr
              have hp := mul_le_mul hL13 hA5 (by norm_num) hℓ.le
              have hq := mul_le_mul hp hD8 (by norm_num) (by positivity)
              linarith
            simp only [Nat.cast_zero, mul_zero, zero_add, zero_sub, add_zero, sub_zero] at hlower
            have e1 : y / (2 * t * (t + y)) ≤ 1 / (4 * t) := by
              apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
              nlinarith [mul_le_mul_of_nonneg_right (show y ≤ t by linarith) ht0.le]
            have e2 : r / (2 * t * (t + r)) ≤ 1 / (5 * t) := by
              apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
              nlinarith [mul_le_mul_of_nonneg_right hr23 ht0.le, sq_nonneg (t - 1)]
            have e3 : s / ((t - u) * (t + s - u)) ≤ 1 / (2 * t) := by
              have hp : 0 < t - u := by linarith
              have hq : 0 < t + s - u := by linarith
              apply (div_le_div_iff₀ (mul_pos hp hq) (by positivity)).mpr
              have hsT := mul_le_mul_of_nonneg_right hs23 ht0.le
              have huT := mul_le_mul_of_nonneg_right hu26 ht0.le
              have hus' := mul_le_mul hu26 hs23 hs.le (by norm_num : (0 : ℝ) ≤ 1 / 26)
              nlinarith only [hsT, huT, hus', sq_nonneg u, mul_nonneg (sub_nonneg.mpr ht1) ht0.le, ht1]
            have e4 : v * (1 / 2) / t ^ 2 ≤ 1 / (1040 * t) := by
              apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
              nlinarith [mul_le_mul_of_nonneg_right hv520 ht0.le,
                mul_nonneg (sub_nonneg.mpr ht1) ht0.le]
            have hp : 0 < 1 / t - 1 / (4 * t) - 1 / (5 * t) - 1 / (2 * t) - 1 / (1040 * t) := by
              have heq : 1 / t - 1 / (4 * t) - 1 / (5 * t) - 1 / (2 * t) - 1 / (1040 * t) =
                  51 / (1040 * t) := by field_simp; ring
              rw [heq]; positivity
            simp only [mul_one, one_mul] at hlower
            linarith only [hlower, hp, e1, e2, e3, e4]
          · have hk1 : k = 1 := by omega
            subst k
            have ht1sq : 1 ≤ t ^ 2 := by nlinarith
            have numerator : 0 < 72 * t ^ 4 - 42 * t ^ 2 - 6 * t - 1 := by
              have hp : 0 ≤ (t - 1) * (72 * t ^ 3 + 72 * t ^ 2 + 7 * t + 1) := by positivity
              nlinarith [sq_nonneg (t ^ 2 - 1)]
            have hden : 0 < t * (t + 1) * (2 * t + 1) * (36 * t ^ 2 - 1) := by
              have hlast : 0 < 36 * t ^ 2 - 1 := by nlinarith only [ht1sq]
              positivity
            have heq : g 1 0 t = (72 * t ^ 4 - 42 * t ^ 2 - 6 * t - 1) /
                (t * (t + 1) * (2 * t + 1) * (36 * t ^ 2 - 1)) := by
              norm_num [g, E, A, D, L, Nat.fib, a, b, n, Finset.sum_range_succ]
              field_simp (disch := first | positivity | nlinarith only [ht1, ht1sq, hden])
              <;> ring
            rw [heq]
            exact div_pos numerator hden
      have logmono : StrictMonoOn (fun t : ℝ => Real.log (q k j t)) (Ici ((j : ℝ) + 1)) := by
        apply strictMonoOn_of_deriv_pos (convex_Ici _)
        · intro t ht
          exact (analytic t ht).2.1.continuousAt.continuousWithinAt
        · intro t ht
          have hmem := interior_subset ht
          rw [(analytic t hmem).2.1.deriv]
          exact gpositive t hmem
      intro t ht z hz htz
      have h := logmono ht hz htz
      exact (Real.log_lt_log_iff (analytic t ht).1 (analytic z hz).1).mp h
    have scaled_product (α β : ℝ) (m : ℕ) :
        Tendsto (fun t : ℝ => rising (α * t + β) m / t ^ m) atTop (nhds (α ^ m)) := by
      have individual (i : ℕ) :
          Tendsto (fun t : ℝ => (α * t + β + i) / t) atTop (nhds α) := by
        have h : Tendsto (fun t : ℝ => α + (β + i) * t⁻¹) atTop (nhds α) := by
          simpa using (tendsto_const_nhds (x := α)).add ((tendsto_const_nhds (x := β + (i : ℝ))).mul tendsto_inv_atTop_zero)
        apply h.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        field_simp <;> ring
      have h := tendsto_finsetProd (Finset.range m) (fun i _ => individual i)
      simpa only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, rising] using h
    have hleft : Tendsto (fun t : ℝ => rising (a k j t + 1) (E k) / t ^ E k)
        atTop (nhds ((A k : ℝ) ^ E k)) := by
      simpa only [a, add_assoc] using scaled_product (A k) ((E k : ℝ) * j + 1) (E k)
    have hright : Tendsto (fun t : ℝ => rising (b k j t + 1) (A k) / t ^ A k)
        atTop (nhds ((D k : ℝ) ^ A k)) := by
      simpa only [b, add_assoc] using scaled_product (D k) ((A k : ℝ) * j + 1) (A k)
    have hdenom : Tendsto (fun t : ℝ => rising (n k j t - 1 / 2) (D k) / t ^ D k)
        atTop (nhds ((L k : ℝ) ^ D k)) := by
      simpa only [n, sub_eq_add_neg, add_assoc] using
        scaled_product (L k) ((D k : ℝ) * j - 1 / 2) (D k)
    have hH : Tendsto (H k j) atTop (nhds (c k)) := by
      have h := (hleft.mul hright).div ((tendsto_const_nhds (x := (4 : ℝ) ^ D k)).mul hdenom) (by positivity)
      change Tendsto _ _ (nhds (c k)) at h
      apply h.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      dsimp [H]
      rw [hδeq]
      simp only [pow_add]
      field_simp
      <;> ring
    have asymptotic : Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) := by
      have hlin : Tendsto (fun t : ℝ => (t - j) / t) atTop (nhds 1) := by
        have h : Tendsto (fun t : ℝ => 1 - (j : ℝ) * t⁻¹) atTop (nhds 1) := by
          simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_const_nhds (x := (j : ℝ))).mul tendsto_inv_atTop_zero)
        apply h.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        field_simp <;> ring
      have hlim := (hlin.mul hH).div_const ((j : ℝ) + 1)
      simp only [one_mul] at hlim
      apply hlim.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      dsimp [q]
      ring
    have Hpos (z : ℝ) (hz : (j : ℝ) + 1 / 2 < z) : 0 < H k j z := by
      obtain ⟨ha, hb, hn, _⟩ := coords z hz
      dsimp [H]
      exact div_pos (mul_pos (rising_pos _ (by linarith) _) (rising_pos _ (by linarith) _))
        (mul_pos (by positivity) (rising_pos _ hn _))
    have riemann (x : ℝ) (hx : 0 < x) (m : ℕ) :
        (∑ i ∈ Finset.range m, 1 / (x + 1 + i)) ≤ Real.log (x + m) - Real.log x ∧
        Real.log (x + m) - Real.log x ≤ (∑ i ∈ Finset.range m, 1 / (x + i)) := by
      have unit (x : ℝ) (hx : 0 < x) :
          1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
          Real.log (x + 1) - Real.log x ≤ 1 / x := by
        have h1 := Real.one_sub_inv_le_log_of_pos (div_pos (by linarith : 0 < x + 1) hx)
        have h2 := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < x + 1) hx)
        rw [Real.log_div (by positivity) hx.ne'] at h1 h2
        constructor
        · convert h1 using 1 <;> field_simp <;> ring
        · convert h2 using 1 <;> field_simp <;> ring
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add_one]
        have h := unit (x + m) (by positivity)
        simp only [← add_assoc] at h ⊢
        have heq : x + 1 + (m : ℝ) = x + m + 1 := by ring
        rw [heq]
        constructor <;> linarith only [ih.1, ih.2, h.1, h.2]
    have Hnegative (t : ℝ) (ht : (j : ℝ) + 1 ≤ t) : g k j t - 1 / (t - j) < 0 := by
      have ht0 : 0 < t := by have := Nat.cast_nonneg (α := ℝ) j; linarith
      obtain ⟨ha, hb, hn, _⟩ := coords t (by linarith)
      let aa := fun z : ℝ => (A k : ℝ) * t + E k * (j + z)
      let bb := fun z : ℝ => (D k : ℝ) * t + A k * (j + z)
      let nn := fun z : ℝ => (L k : ℝ) * t + D k * (j + z)
      let f := fun z : ℝ => (A k : ℝ) * Real.log (aa z) +
        D k * Real.log (bb z) - L k * Real.log (nn z)
      have hd (z : ℝ) (hz : 0 ≤ z) :
          HasDerivAt f (-t * (j + z) / (aa z * bb z * nn z)) z := by
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have ha' : 0 < aa z := by dsimp [aa]; positivity
        have hb' : 0 < bb z := by dsimp [bb]; positivity
        have hn' : 0 < nn z := by dsimp [nn]; positivity
        have da : HasDerivAt aa (E k) z := by
          simpa [aa] using (((hasDerivAt_id z).const_add (j : ℝ)).const_mul (E k : ℝ)).const_add ((A k : ℝ) * t)
        have db : HasDerivAt bb (A k) z := by
          simpa [bb] using (((hasDerivAt_id z).const_add (j : ℝ)).const_mul (A k : ℝ)).const_add ((D k : ℝ) * t)
        have dn : HasDerivAt nn (D k) z := by
          simpa [nn] using (((hasDerivAt_id z).const_add (j : ℝ)).const_mul (D k : ℝ)).const_add ((L k : ℝ) * t)
        have raw : HasDerivAt f ((A k : ℝ) * (E k / aa z) + D k * (A k / bb z) - L k * (D k / nn z)) z :=
          (((da.log ha'.ne').const_mul (A k : ℝ)).add
            ((db.log hb'.ne').const_mul (D k : ℝ))).sub ((dn.log hn'.ne').const_mul (L k : ℝ))
        have hδeqR : (D k : ℝ) = E k + A k := by exact_mod_cast hδeq
        have hℓeqR : (L k : ℝ) = A k + D k := by exact_mod_cast hℓeq
        have identity :
            (A k : ℝ) * E k * (bb z * nn z) + D k * A k * (aa z * nn z) -
              L k * D k * (aa z * bb z) =
                -(((A k : ℝ) ^ 2 - D k * E k) ^ 2) * t * (j + z) := by
          dsimp [aa, bb, nn]
          rw [hℓeqR, hδeqR]
          ring
        have heq : (A k : ℝ) * (E k / aa z) + D k * (A k / bb z) - L k * (D k / nn z) =
            -t * (j + z) / (aa z * bb z * nn z) := by
          apply (eq_div_iff (by positivity : aa z * bb z * nn z ≠ 0)).mpr
          field_simp
          rw [hcassini] at identity
          nlinarith only [identity]
        rwa [heq] at raw
      have hm : AntitoneOn f (Ici 0) :=
        antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
          (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
          (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
          (fun z hz => by
            have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            have hz' : 0 ≤ z := interior_subset hz
            have hden : 0 < aa z * bb z * nn z := by dsimp [aa, bb, nn]; positivity
            exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg ht0.le (add_nonneg hj hz')]) hden.le)
      have hcomp := hm (by simp) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
      dsimp [f, aa, bb, nn] at hcomp
      simp only [add_zero] at hcomp
      have hleft := (riemann (a k j t) ha (E k)).1
      have hright := (riemann (b k j t) hb (A k)).1
      have hden := (riemann (n k j t) (by linarith) (D k)).2
      have hshift : (∑ i ∈ Finset.range (D k), 1 / (n k j t + i)) <
          ∑ i ∈ Finset.range (D k), 1 / (n k j t - 1 / 2 + i) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hdNat⟩
        intro i _
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
      have hdenstrict := hden.trans_lt hshift
      have heqa : (A k : ℝ) * t + E k * (j + 1) = a k j t + E k := by dsimp [a]; ring
      have heqb : (D k : ℝ) * t + A k * (j + 1) = b k j t + A k := by dsimp [b]; ring
      have heqn : (L k : ℝ) * t + D k * (j + 1) = n k j t + D k := by dsimp [n]; ring
      rw [heqa, heqb, heqn] at hcomp
      change (A k : ℝ) * Real.log (a k j t + E k) + D k * Real.log (b k j t + A k) -
        L k * Real.log (n k j t + D k) ≤
        A k * Real.log (a k j t) + D k * Real.log (b k j t) - L k * Real.log (n k j t) at hcomp
      have hl := mul_le_mul_of_nonneg_left hleft hα.le
      have hr := mul_le_mul_of_nonneg_left hright hδ.le
      have hn' := mul_lt_mul_of_pos_left hdenstrict hℓ
      dsimp [g]
      nlinarith only [hcomp, hl, hr, hn']
    have logH_deriv (t : ℝ) (ht : (j : ℝ) + 1 ≤ t) :
        HasDerivAt (fun z : ℝ => Real.log (H k j z)) (g k j t - 1 / (t - j)) t := by
      have htj : 0 < t - j := by linarith
      have raw := ((analytic t ht).2.1.sub (((hasDerivAt_id t).sub_const (j : ℝ)).log htj.ne')).add_const
        (Real.log (j + 1))
      apply raw.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show (j : ℝ) + 1 / 2 < t by linarith)] with z hz
      have hzj : 0 < z - j := by linarith
      dsimp [q]
      rw [Real.log_div (mul_pos hzj (Hpos z hz)).ne' (by positivity),
        Real.log_mul hzj.ne' (Hpos z hz).ne']
      ring
    have Hanti : StrictAntiOn (H k j) (Ici ((j : ℝ) + 1)) := by
      have hlog : StrictAntiOn (fun t : ℝ => Real.log (H k j t)) (Ici ((j : ℝ) + 1)) := by
        apply strictAntiOn_of_deriv_neg (convex_Ici _)
        · intro t ht
          exact (logH_deriv t ht).continuousAt.continuousWithinAt
        · intro t ht
          have hm := interior_subset ht
          rw [(logH_deriv t hm).deriv]
          exact Hnegative t hm
      intro t ht z hz htz
      change (j : ℝ) + 1 ≤ t at ht
      change (j : ℝ) + 1 ≤ z at hz
      exact (Real.log_lt_log_iff (Hpos z (by linarith [hz])) (Hpos t (by linarith [ht]))).mp
        (hlog ht hz htz)
    have Hlower (t : ℝ) (ht : (j : ℝ) + 1 ≤ t) : c k < H k j t := by
      have hlimit : c k ≤ H k j (t + 1) := by
        apply le_of_tendsto hH
        filter_upwards [eventually_ge_atTop (t + 1)] with z hz
        apply Hanti.antitoneOn (show (j : ℝ) + 1 ≤ t + 1 by linarith)
          (show (j : ℝ) + 1 ≤ z by linarith) hz
      exact hlimit.trans_lt (Hanti ht (show (j : ℝ) + 1 ≤ t + 1 by linarith)
        (by linarith : t < t + 1))
    have Hupper (t : ℝ) (ht : (j : ℝ) + 1 ≤ t) : H k j t < 1 := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have ht1 : 1 ≤ t := by linarith
      have ht0 : 0 < t := by linarith
      obtain ⟨ha, hb, hn, _⟩ := coords t (by linarith)
      have hab : a k j t + b k j t = n k j t := by
        dsimp [a, b, n]
        simp only [hℓeq, hδeq, Nat.cast_add]
        ring
      have haA : (A k : ℝ) ≤ a k j t := by
        dsimp [a]
        nlinarith only [mul_le_mul_of_nonneg_left ht1 hα.le, mul_nonneg he.le hj]
      have hbE : (E k : ℝ) ≤ b k j t := by
        have hED : E k ≤ D k := by omega
        have hEDR : (E k : ℝ) ≤ D k := by exact_mod_cast hED
        dsimp [b]
        nlinarith only [hEDR, mul_le_mul_of_nonneg_left ht1 hδ.le, mul_nonneg hα.le hj]
      have hn3 : 3 ≤ n k j t := by
        dsimp [n]
        nlinarith only [hL3, mul_le_mul_of_nonneg_left ht1 hℓ.le, mul_nonneg hδ.le hj]
      have hp1 : rising (a k j t + 1) (E k) ≤ n k j t ^ E k := by
        have h := Finset.prod_le_prod₀ (s := Finset.range (E k))
          (f := fun i : ℕ => a k j t + 1 + (i : ℝ)) (g := fun _ : ℕ => n k j t)
          (fun i _ => by positivity) (by
            intro i hi
            have hi' : (i : ℝ) + 1 ≤ E k := by
              exact_mod_cast (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hi))
            linarith only [hi', hbE, hab])
        simpa only [rising, Finset.prod_const, Finset.card_range] using h
      have hp2 : rising (b k j t + 1) (A k) ≤ n k j t ^ A k := by
        have h := Finset.prod_le_prod₀ (s := Finset.range (A k))
          (f := fun i : ℕ => b k j t + 1 + (i : ℝ)) (g := fun _ : ℕ => n k j t)
          (fun i _ => by positivity) (by
            intro i hi
            have hi' : (i : ℝ) + 1 ≤ A k := by
              exact_mod_cast (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hi))
            linarith only [hi', haA, hab])
        simpa only [rising, Finset.prod_const, Finset.card_range] using h
      have hnum : rising (a k j t + 1) (E k) * rising (b k j t + 1) (A k) ≤ n k j t ^ D k := by
        rw [hδeq, pow_add]
        exact mul_le_mul hp1 hp2 (rising_pos _ (by linarith) _).le (by positivity)
      have hden : n k j t ^ D k < (4 : ℝ) ^ D k * rising (n k j t - 1 / 2) (D k) := by
        have h := Finset.prod_lt_prod_of_nonempty₀
          (s := Finset.range (D k)) (f := fun _ : ℕ => n k j t)
          (g := fun i : ℕ => 4 * (n k j t - 1 / 2 + i))
          (fun _ _ => by linarith)
          (fun i _ => by nlinarith only [hn3, Nat.cast_nonneg (α := ℝ) i])
          ⟨0, Finset.mem_range.mpr hdNat⟩
        simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, rising] using h
      exact (div_lt_one (mul_pos (by positivity) (rising_pos _ hn _))).mpr (hnum.trans_lt hden)
    have hcpos : 0 < c k := by dsimp [c]; positivity
    have hc1 : c k < 1 := (Hlower ((j : ℝ) + 1) le_rfl).trans (Hupper _ le_rfl)
    let U : ℝ := j + (j + 1) / c k
    have hU : 2 * j + 1 < U := by
      dsimp [U]
      have hj1 : 0 < (j : ℝ) + 1 := by positivity
      have hdiv : (j : ℝ) + 1 < (j + 1) / c k := (lt_div_iff₀ hcpos).mpr (by nlinarith)
      linarith
    have hq2 : q k j (2 * j + 1) < 1 := by
      have h := Hupper (2 * j + 1) (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
      have heq : q k j (2 * j + 1) = H k j (2 * j + 1) := by
        dsimp [q]
        field_simp
        <;> ring
      rwa [heq]
    have hqU : 1 < q k j U := by
      have h := Hlower U (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
      have heq : q k j U = H k j U / c k := by dsimp [q, U]; field_simp <;> ring
      rw [heq]
      exact (one_lt_div hcpos).mpr h
    have qcontinuous : ContinuousOn (q k j) (Ici ((j : ℝ) + 1)) := by
      intro t ht
      change (j : ℝ) + 1 ≤ t at ht
      have hexp := (analytic t ht).2.1.exp.continuousAt
      have hq : ContinuousAt (q k j) t := by
        apply hexp.congr_of_eventuallyEq
        filter_upwards [eventually_gt_nhds (show (j : ℝ) + 1 / 2 < t by linarith)] with z hz
        exact (Real.exp_log (positive z hz)).symm
      exact hq.continuousWithinAt
    have h2legal : (j : ℝ) + 1 ≤ 2 * j + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    obtain ⟨τ, hτ, hroot⟩ := intermediate_value_Icc hU.le
      (qcontinuous.mono (fun z hz => h2legal.trans hz.1)) ⟨hq2.le, hqU.le⟩
    have hτlegal : (j : ℝ) + 1 ≤ τ := h2legal.trans hτ.1
    have hτlow : 2 * j + 1 < τ := by
      rcases hτ.1.lt_or_eq with h | h
      · exact h
      · rw [← h] at hroot; linarith
    have hτhigh : τ < U := by
      rcases hτ.2.lt_or_eq with h | h
      · exact h
      · rw [h] at hroot; linarith
    refine ⟨hcpos, analytic, monotonic, asymptotic, ?_, ?_⟩
    · refine ⟨τ, ⟨hτlegal, hroot⟩, ?_⟩
      intro z hz
      exact monotonic.injOn hz.1 hτlegal (hz.2.trans hroot.symm)
    · refine ⟨τ, hτlegal, hroot, hτlow, hτhigh, ?_⟩
      intro t ht
      have htlegal : (j : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast ht
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hroot] using monotonic.lt_iff_lt htlegal hτlegal
      · constructor
        · intro h
          exact monotonic.injOn htlegal hτlegal (h.trans hroot.symm)
        · rintro h; simpa only [h] using hroot
      · simpa only [hroot] using monotonic.lt_iff_lt hτlegal htlegal
  have hδeq : D k = E k + A k := by
    dsimp [D, E, A]
    rw [show 3 * k = (3 * k - 2) + 2 by omega, Nat.fib_add_two]
    congr 2 <;> omega
  have hℓeq : L k = A k + D k := by
    dsimp [L, A, D]
    rw [show 3 * k + 1 = (3 * k - 1) + 2 by omega, Nat.fib_add_two]
    congr 2 <;> omega
  have grid_coords (t i : ℕ) (hi : i ≤ t) :
      GraftAffineClosure.step^[3 * k] (t - i, i) =
        (A k * t + E k * i, D k * t + A k * i) := by
    have hh : GraftAffineClosure.step^[3 * k] (t - i, i) =
        (Nat.fib (3 * k - 1) * (t - i) + Nat.fib (3 * k) * i,
          Nat.fib (3 * k) * (t - i) + Nat.fib (3 * k + 1) * i) := by
      apply Prod.ext
      · exact GlobalGcdSampling.iterate_first (3 * k) (by omega) (t - i, i)
      · exact GlobalGcdSampling.iterate_second (3 * k) (t - i, i)
    rw [hh]
    change (A k * (t - i) + D k * i, D k * (t - i) + L k * i) = _
    ext <;> simp only [hδeq, hℓeq]
    · calc
        _ = A k * ((t - i) + i) + E k * i := by ring
        _ = _ := by rw [Nat.sub_add_cancel hi]
    · calc
        _ = (E k + A k) * ((t - i) + i) + A k * i := by ring
        _ = _ := by rw [Nat.sub_add_cancel hi]
  have factorial_pos (m : ℕ) : (0 : ℝ) < m.factorial := by
    exact_mod_cast Nat.factorial_pos m
  have count_formula (x y : ℕ) (hxy : 1 ≤ x + y) :
      (GenealogicalFiberTransport.fiberCount (x, y) : ℝ) =
        ((2 * (x + y - 1)).factorial : ℝ) /
          (((x + y - 1).factorial : ℝ) * x.factorial * y.factorial) := by
    let m := x + y - 1
    have hm : m + 1 = x + y := by dsimp [m]; omega
    have hc : (x + y).choose x * x.factorial * y.factorial = (x + y).factorial := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right x y))
    have hs : (x + y) * catalan m = Nat.centralBinom m := by
      rw [← hm]; exact succ_mul_catalan_eq_centralBinom m
    have hb : Nat.centralBinom m * m.factorial * m.factorial = (2 * m).factorial := by
      simpa only [Nat.centralBinom, two_mul] using
        Nat.add_choose_mul_factorial_mul_factorial m m
    have hn : GenealogicalFiberTransport.fiberCount (x, y) * m.factorial *
        x.factorial * y.factorial = (2 * m).factorial := by
      calc
        _ = catalan m * m.factorial * ((x + y).choose x * x.factorial * y.factorial) := by
          dsimp [GenealogicalFiberTransport.fiberCount, m]; ring
        _ = catalan m * m.factorial * (x + y).factorial := by rw [hc]
        _ = ((x + y) * catalan m) * m.factorial * m.factorial := by
          rw [← hm, Nat.factorial_succ]; ring
        _ = _ := by rw [hs, hb]
    apply (eq_div_iff (by positivity :
      ((m.factorial : ℝ) * x.factorial * y.factorial) ≠ 0)).mpr
    exact_mod_cast (by simpa only [m, mul_assoc] using hn)
  have rising_cast (x m : ℕ) : (x.ascFactorial m : ℝ) = rising x m := by
    simp only [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, rising]
  have factorial_shift (x m : ℕ) :
      ((x + m).factorial : ℝ) = (x.factorial : ℝ) * rising (x + 1) m := by
    simpa only [Nat.cast_mul, rising_cast, Nat.cast_add, Nat.cast_one] using
      (congrArg (fun u : ℕ => (u : ℝ)) (Nat.factorial_mul_ascFactorial x m)).symm
  have rising_succ (x : ℝ) (m : ℕ) :
      rising x (m + 1) = rising x m * (x + m) := by
    simp only [rising, Finset.prod_range_succ]
  have duplication (x : ℝ) (m : ℕ) :
      rising (2 * x) (2 * m) = 4 ^ m * rising x m * rising (x + 1 / 2) m := by
    induction m with
    | zero => simp [rising]
    | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        rising_succ, rising_succ, ih, rising_succ, rising_succ, pow_succ]
      push_cast
      ring
  have count_shift (x y e α : ℕ) (hxy : 1 ≤ x + y) :
      (GenealogicalFiberTransport.fiberCount (x, y) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x + e, y + α) : ℝ) =
      rising (x + y : ℕ) (e + α) * rising (x + 1) e * rising (y + 1) α /
        rising (2 * (x + y : ℕ) - 1 : ℝ) (2 * (e + α)) := by
    rw [count_formula x y hxy, count_formula (x + e) (y + α) (by omega)]
    have hs : x + e + (y + α) - 1 = (x + y - 1) + (e + α) := by omega
    have hd : 2 * (x + e + (y + α) - 1) = 2 * (x + y - 1) + 2 * (e + α) := by omega
    rw [hd, hs, factorial_shift (2 * (x + y - 1)) (2 * (e + α)),
      factorial_shift (x + y - 1) (e + α), factorial_shift x e, factorial_shift y α]
    have hn : ((x + y - 1 : ℕ) : ℝ) + 1 = (x + y : ℕ) := by
      exact_mod_cast (show x + y - 1 + 1 = x + y by omega)
    have hn2 : ((2 * (x + y - 1) : ℕ) : ℝ) + 1 = 2 * (x + y : ℕ) - 1 := by
      push_cast at hn ⊢; linarith
    rw [hn, hn2]
    have hp := rising_pos _ (by positivity : (0 : ℝ) < x + 1) e
    have hq := rising_pos _ (by positivity : (0 : ℝ) < y + 1) α
    have hr := rising_pos _ (by exact_mod_cast (show 0 < x + y by omega) : (0 : ℝ) < (x + y : ℕ)) (e + α)
    have ht := rising_pos _ (by
      have hh : (1 : ℝ) ≤ (x + y : ℕ) := by exact_mod_cast hxy
      linarith : (0 : ℝ) < 2 * (x + y : ℕ) - 1) (2 * (e + α))
    field_simp [(factorial_pos (2 * (x + y - 1))).ne',
      (factorial_pos (x + y - 1)).ne', (factorial_pos x).ne',
      (factorial_pos y).ne', hp.ne', hq.ne', hr.ne', ht.ne']
    <;> ring
  have count_pos (x y : ℕ) (hxy : 1 ≤ x + y) :
      (0 : ℝ) < GenealogicalFiberTransport.fiberCount (x, y) := by
    have hf := GenealogicalFiberTransport.result.1 x y hxy
    letI : Finite (GenealogicalFiberTransport.Fiber (x, y)) := hf.1
    letI : Nonempty (GenealogicalFiberTransport.Fiber (x, y)) := hf.2.2.1
    exact_mod_cast (by simpa only [hf.2.1] using
      (Nat.card_pos (α := GenealogicalFiberTransport.Fiber (x, y))))
  have source_ratio (t : ℕ) (ht : j + 1 ≤ t) :
      (GenealogicalFiberTransport.fiberCount (t - (j + 1), j + 1) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (t - j, j) : ℝ) =
        ((t : ℝ) - j) / (j + 1) := by
    have htotal0 : t - j + j = t := Nat.sub_add_cancel (by omega)
    have htotal1 : t - (j + 1) + (j + 1) = t := Nat.sub_add_cancel ht
    have hchoose : (t.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (t.choose j : ℝ) * ((t : ℝ) - j) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_sub (show j ≤ t by omega)] using
        congrArg (fun u : ℕ => (u : ℝ)) (Nat.choose_succ_right_eq t j)
    apply (div_eq_div_iff (count_pos _ _ (by omega)).ne' (by positivity)).mpr
    simp only [GenealogicalFiberTransport.fiberCount, htotal0, htotal1,
      Nat.choose_symm (show j ≤ t by omega), Nat.choose_symm ht, Nat.cast_mul]
    linear_combination (catalan (t - 1) : ℝ) * hchoose
  have bridge (t : ℕ) (ht : j + 1 ≤ t) :
      q k j t = sourceDensity k t (j + 1) / sourceDensity k t j := by
    let x := A k * t + E k * j
    let y := D k * t + A k * j
    have htotal : x + y = L k * t + D k * j := by
      dsimp [x, y]; rw [hℓeq, hδeq]; ring
    have hpos : 1 ≤ x + y := by
      have hL : 0 < L k := Nat.fib_pos.mpr (by omega)
      rw [htotal]
      have hprod := Nat.mul_pos hL (show 0 < t by omega)
      omega
    have hshift : (A k * t + E k * (j + 1), D k * t + A k * (j + 1)) =
        (x + E k, y + A k) := by dsimp [x, y]; ext <;> ring
    have htarget := count_shift x y (E k) (A k) hpos
    have hn : (x + y : ℝ) = n k j t := by
      rw [← Nat.cast_add, htotal]; simp [n]
    have ha : (x : ℝ) = a k j t := by dsimp [x, a]; push_cast; ring
    have hb : (y : ℝ) = b k j t := by dsimp [y, b]; push_cast; ring
    have hnpos : 0 < n k j t - 1 / 2 := by
      have hh : (1 : ℝ) ≤ (x + y : ℕ) := by exact_mod_cast hpos
      rw [← hn]; push_cast at hh; linarith
    have hdup : rising (2 * n k j t - 1) (2 * D k) =
        4 ^ D k * rising (n k j t - 1 / 2) (D k) * rising (n k j t) (D k) := by
      simpa only [show 2 * (n k j t - 1 / 2) = 2 * n k j t - 1 by ring,
        show n k j t - 1 / 2 + 1 / 2 = n k j t by ring] using
        duplication (n k j t - 1 / 2) (D k)
    have hV : (GenealogicalFiberTransport.fiberCount (x, y) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x + E k, y + A k) : ℝ) = H k j t := by
      rw [← hδeq, Nat.cast_add, hn, ha, hb, hdup] at htarget
      rw [htarget, H]
      have hnr := rising_pos _ (by linarith : 0 < n k j t) (D k)
      have hhalf := rising_pos _ hnpos (D k)
      field_simp [hnr.ne', hhalf.ne']
      <;> ring
    dsimp [sourceDensity]
    rw [grid_coords t (j + 1) ht, grid_coords t j (by omega), hshift]
    change q k j t =
      ((GenealogicalFiberTransport.fiberCount (t - (j + 1), j + 1) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x + E k, y + A k) : ℝ)) /
      ((GenealogicalFiberTransport.fiberCount (t - j, j) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x, y) : ℝ))
    rw [div_div_div_comm, source_ratio t ht, div_div_eq_mul_div,
      mul_div_assoc, hV, q]
    ring
  rcases real with ⟨hc, hd, hm, hl, hu, τ, hτ, hr, hlo, hhi, hcmp⟩
  refine ⟨hc, hd, hm, hl, hu, ⟨τ, hτ, hr, hlo, hhi, ?_⟩, bridge⟩
  intro t ht
  obtain ⟨hlt, heq, hgt⟩ := hcmp t ht
  exact ⟨hlt, heq, hgt, by rwa [← bridge t ht], by rwa [← bridge t ht],
    by rwa [← bridge t ht]⟩

end D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
