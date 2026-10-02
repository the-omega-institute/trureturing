/- GID: D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real finite-product extension of adjacent Fibonacci source densities. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S1.Scale.Fibonacci
import D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing

open scoped BigOperators
open Filter Set

/-- The two numerator lengths, denominator length, and total composition coefficient. -/
def E (k : ℕ) : ℕ := Nat.fib (3 * k - 2)
def A (k : ℕ) : ℕ := Nat.fib (3 * k - 1)
def D (k : ℕ) : ℕ := Nat.fib (3 * k)
def L (k : ℕ) : ℕ := Nat.fib (3 * k + 1)

/-- Target alpha, beta, and total coordinates for the fixed ancestor minority. -/
def a (k j : ℕ) (t : ℝ) : ℝ := A k * t + E k * j
def b (k j : ℕ) (t : ℝ) : ℝ := D k * t + A k * j
def n (k j : ℕ) (t : ℝ) : ℝ := L k * t + D k * j

/-- Rising finite product; nonintegral arguments are auxiliary real parameters. -/
noncomputable def rising (x : ℝ) (m : ℕ) : ℝ :=
  ∏ i ∈ Finset.range m, (x + i)

/-- The real finite-product factor, with no interpretation as a nonintegral tree count. -/
noncomputable def H (k j : ℕ) (t : ℝ) : ℝ :=
  rising (a k j t + 1) (E k) * rising (b k j t + 1) (A k) /
    ((4 : ℝ) ^ D k * rising (n k j t - 1 / 2) (D k))

/-- Adjacent density ratio on the integer grid, extended by real finite products. -/
noncomputable def q (k j : ℕ) (t : ℝ) : ℝ :=
  (t - j) * H k j t / (j + 1)

/-- Leading finite-product coefficient. -/
noncomputable def c (k : ℕ) : ℝ :=
  (A k : ℝ) ^ E k * (D k : ℝ) ^ A k /
    ((4 : ℝ) ^ D k * (L k : ℝ) ^ D k)

/-- Density of the iterated substitution image in its actual composition fiber. -/
noncomputable def sourceDensity (k t i : ℕ) : ℝ :=
  (GenealogicalFiberTransport.fiberCount (t - i, i) : ℝ) /
    (GenealogicalFiberTransport.fiberCount
      (GraftAffineClosure.step^[3 * k] (t - i, i)) : ℝ)

/-- The six clauses of the real crossing and integer source-density bridge. -/
def Conclusion (k j : ℕ) : Prop :=
  0 < c k ∧
  StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) ∧
  Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) ∧
  (∃! τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1) ∧
  (∃ τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1 ∧
    2 * j + 1 < τ ∧ τ < j + (j + 1) / c k ∧
    ∀ t : ℕ, j + 1 ≤ t →
      (q k j t < 1 ↔ (t : ℝ) < τ) ∧
      (q k j t = 1 ↔ (t : ℝ) = τ) ∧
      (1 < q k j t ↔ τ < (t : ℝ))) ∧
  (∀ t : ℕ, j + 1 ≤ t →
    q k j t = sourceDensity k t (j + 1) / sourceDensity k t j)

/-- Joint logarithmic compensation from the common affine composition coordinates. -/
private theorem logarithmic_compensation (e α δ ℓ t j : ℝ)
    (he : 0 < e) (hα : 0 < α) (hδ : 0 < δ) (hℓ : 0 < ℓ)
    (hδeq : δ = e + α) (hℓeq : ℓ = α + δ)
    (hcassini : (α ^ 2 - δ * e) ^ 2 = 1) (ht : 0 < t) (hj : 0 ≤ j) :
    -(j + 1 / 2) / (ℓ * α * δ * t ^ 2) ≤
      α * (Real.log (α * t + e * (j + 1)) - Real.log (α * t + e * j)) +
      δ * (Real.log (δ * t + α * (j + 1)) - Real.log (δ * t + α * j)) -
      ℓ * (Real.log (ℓ * t + δ * (j + 1)) - Real.log (ℓ * t + δ * j)) := by
  let aa := fun s : ℝ => α * t + e * (j + s)
  let bb := fun s : ℝ => δ * t + α * (j + s)
  let nn := fun s : ℝ => ℓ * t + δ * (j + s)
  let K := ℓ * α * δ * t ^ 2
  let f := fun s : ℝ => α * Real.log (aa s) + δ * Real.log (bb s) -
    ℓ * Real.log (nn s) + (j * s + s ^ 2 / 2) / K
  have hK : 0 < K := by dsimp [K]; positivity
  have apos (s : ℝ) (hs : 0 ≤ s) : 0 < aa s := by dsimp [aa]; positivity
  have bpos (s : ℝ) (hs : 0 ≤ s) : 0 < bb s := by dsimp [bb]; positivity
  have npos (s : ℝ) (hs : 0 ≤ s) : 0 < nn s := by dsimp [nn]; positivity
  have hd (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt f (α * e / aa s + δ * α / bb s - ℓ * δ / nn s + (j + s) / K) s := by
    have da : HasDerivAt aa e s := by
      simpa [aa] using (((hasDerivAt_id s).const_add j).const_mul e).const_add (α * t)
    have db : HasDerivAt bb α s := by
      simpa [bb] using (((hasDerivAt_id s).const_add j).const_mul α).const_add (δ * t)
    have dn : HasDerivAt nn δ s := by
      simpa [nn] using (((hasDerivAt_id s).const_add j).const_mul δ).const_add (ℓ * t)
    have dq : HasDerivAt (fun s : ℝ => (j * s + s ^ 2 / 2) / K) ((j + s) / K) s := by
      have raw : HasDerivAt (fun s : ℝ => (j * s + s ^ 2 / 2) / K)
          ((j * 1 + (2 * s ^ (2 - 1) * 1) / 2) / K) s :=
        (((hasDerivAt_id s).const_mul j).add
          (((hasDerivAt_id s).pow 2).div_const 2)).div_const K
      convert raw using 1 <;> ring
    have raw : HasDerivAt f
        (α * (e / aa s) + δ * (α / bb s) - ℓ * (δ / nn s) + (j + s) / K) s :=
      ((((da.log (apos s hs).ne').const_mul α).add
        ((db.log (bpos s hs).ne').const_mul δ)).sub
        ((dn.log (npos s hs).ne').const_mul ℓ)).add dq
    convert raw using 1 <;> ring
  have hnonneg (s : ℝ) (hs : 0 ≤ s) :
      0 ≤ α * e / aa s + δ * α / bb s - ℓ * δ / nn s + (j + s) / K := by
    have ha := apos s hs
    have hb := bpos s hs
    have hn := npos s hs
    have identity :
        α * e * (bb s * nn s) + δ * α * (aa s * nn s) - ℓ * δ * (aa s * bb s) =
          -((α ^ 2 - δ * e) ^ 2) * t * (j + s) := by
      dsimp [aa, bb, nn]
      rw [hℓeq, hδeq]
      ring
    have hid : α * e / aa s + δ * α / bb s - ℓ * δ / nn s =
        -t * (j + s) / (aa s * bb s * nn s) := by
      apply (eq_div_iff (by positivity : aa s * bb s * nn s ≠ 0)).mpr
      field_simp
      rw [hcassini] at identity
      nlinarith [identity]
    have hamin : α * t ≤ aa s := by
      dsimp [aa]; linarith [mul_nonneg he.le (add_nonneg hj hs)]
    have hbmin : δ * t ≤ bb s := by
      dsimp [bb]; linarith [mul_nonneg hα.le (add_nonneg hj hs)]
    have hnmin : ℓ * t ≤ nn s := by
      dsimp [nn]; linarith [mul_nonneg hδ.le (add_nonneg hj hs)]
    have hab : α * t * (δ * t) ≤ aa s * bb s :=
      mul_le_mul hamin hbmin (by positivity) ha.le
    have hprod : α * t * (δ * t) * (ℓ * t) ≤ aa s * bb s * nn s :=
      mul_le_mul hab hnmin (by positivity) (mul_pos ha hb).le
    have hfrac : t * (j + s) / (aa s * bb s * nn s) ≤ (j + s) / K := by
      calc
        _ ≤ t * (j + s) / (α * t * (δ * t) * (ℓ * t)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
        _ = _ := by dsimp [K]; field_simp
    rw [hid, neg_mul, neg_div]
    linarith
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => hnonneg s (interior_subset hs))
  have h := hm (by simp) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [f, aa, bb, nn, K] at h
  norm_num at h
  rw [neg_div]
  linarith

/-- Explicit logarithmic derivative of the finite-product extension. -/
noncomputable def g (k j : ℕ) (t : ℝ) : ℝ :=
  1 / (t - j) +
    A k * (∑ i ∈ Finset.range (E k), 1 / (a k j t + 1 + i)) +
    D k * (∑ i ∈ Finset.range (A k), 1 / (b k j t + 1 + i)) -
    L k * (∑ i ∈ Finset.range (D k), 1 / (n k j t - 1 / 2 + i))

/-- Lower envelope combining both numerator errors and the shifted denominator error. -/
noncomputable def lowerEnvelope (k j : ℕ) (t : ℝ) : ℝ :=
  1 / (t - j) - (j + 1 / 2) / ((L k : ℝ) * A k * D k * t ^ 2) -
    (A k : ℝ) * E k / (2 * a k j t * (a k j t + E k)) -
    (D k : ℝ) * A k / (2 * b k j t * (b k j t + A k)) -
    (L k : ℝ) * D k / ((n k j t - 1 / 2) * (n k j t + D k - 1 / 2))

/-- The common affine coordinates give the three-block logarithmic derivative bound. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    0 < c k ∧
    ∀ t : ℝ, (j : ℝ) + 1 ≤ t →
      0 < q k j t ∧
      HasDerivAt (fun z : ℝ => Real.log (q k j z)) (g k j t) t ∧
      lowerEnvelope k j t ≤ g k j t := by
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
        field_simp; ring
      simpa only [he] using lower m
    · intro hxhalf
      have telescope (m : ℕ) :
          (∑ i ∈ Finset.range m, 1 / (x - 1 / 2 + i)) -
            (∑ i ∈ Finset.range m, 1 / (x + 1 / 2 + i)) =
            1 / (x - 1 / 2) - 1 / (x + m - 1 / 2) := by
        induction m with
        | zero => simp
        | succ m hm =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add_one]
          have h1 : x - 1 / 2 + m = x + m - 1 / 2 := by ring
          have h2 : x + 1 / 2 + m = x + (m + 1) - 1 / 2 := by ring
          rw [h1, h2]
          linarith
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
  have product_pos (x : ℝ) (hx : 0 < x) (m : ℕ) : 0 < rising x m :=
    Finset.prod_pos (fun i _ => by positivity)
  have positive (z : ℝ) (hz : (j : ℝ) + 1 / 2 < z) : 0 < q k j z := by
    obtain ⟨ha, hb, hn, ht⟩ := coords z hz
    dsimp [q, H]
    exact div_pos (mul_pos ht
      (div_pos (mul_pos (product_pos _ (by linarith) _) (product_pos _ (by linarith) _))
        (mul_pos (by positivity) (product_pos _ hn _)))) (by positivity)
  constructor
  · dsimp [c]; positivity
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
    have hp1 := product_pos (a k j z + 1) (by linarith) (E k)
    have hp2 := product_pos (b k j z + 1) (by linarith) (A k)
    have hp3 := product_pos (n k j z - 1 / 2) hn (D k)
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

end D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
