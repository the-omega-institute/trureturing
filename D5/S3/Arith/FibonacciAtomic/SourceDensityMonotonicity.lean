/- GID: D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Three-block logarithmic compensation for real Fibonacci source density ratios. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity

open scoped BigOperators
open Set

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

/-- Real finite-product ratio with auxiliary nonintegral arguments. -/
noncomputable def q (k j : ℕ) (t : ℝ) : ℝ :=
  (t - j) * H k j t / (j + 1)

/-- Leading finite-product coefficient. -/
noncomputable def c (k : ℕ) : ℝ :=
  (A k : ℝ) ^ E k * (D k : ℝ) ^ A k /
    ((4 : ℝ) ^ D k * (L k : ℝ) ^ D k)

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

/-- Joint logarithmic compensation for three affine blocks with squared determinant one. -/
theorem logarithmic_compensation (e α δ ℓ t j : ℝ)
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

end D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity
