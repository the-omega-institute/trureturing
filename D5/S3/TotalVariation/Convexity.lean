/- GID: D5/S3/TotalVariation/Convexity
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Convexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove joint convexity of total variation and squared Hellinger distance. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `Hellinger`, `totalVariation`, `total variation`,
     `joint.*convex`, `Bhattacharyya`, `add_pow_le_pow_mul_pow_of_sq_le_sq`,
     `inner_mul_le_norm_mul_norm`, `concaveOn.*sqrt`, `sqrt_mul`,
     and `sum_sqrt_mul_sqrt_le`.
   * No finite statistical total-variation or Hellinger joint-convexity theorem, and no exact
     two-variable geometric-mean concavity theorem, was found. Mathlib's total variations are
     measure- or function-variation notions; its Hellinger hits are Hellinger--Toeplitz.
     `Real.sum_sqrt_mul_sqrt_le` is the finite Cauchy--Schwarz core reused below.
   * Repository grep over all 676 Lean declaration starts below `D5/S3` found exactly one
     declaration whose name contains `convex`: the sibling `kl_divergence_joint_convex`.
     Other raw `convex` hits are search-audit prose and local convexity facts in existing proofs.
-/

import D5.S3.TotalVariation.Hellinger

namespace D5.S3.TotalVariation.Convexity

open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.Pinsker

/-- Total variation is joint convex for arbitrary finite real functions. The interval hypothesis
is used only to identify the absolute values of the two mixture weights. -/
theorem total_variation_joint_convex {ι : Type*} [Fintype ι]
    (p1 p2 q1 q2 : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    totalVariation (fun i => t * p1 i + (1 - t) * p2 i)
        (fun i => t * q1 i + (1 - t) * q2 i) ≤
      t * totalVariation p1 q1 + (1 - t) * totalVariation p2 q2 := by
  have hone_sub_t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  rw [totalVariation, totalVariation, totalVariation]
  have hsum :
      (∑ i, |(t * p1 i + (1 - t) * p2 i) -
          (t * q1 i + (1 - t) * q2 i)|) ≤
        ∑ i, (t * |p1 i - q1 i| + (1 - t) * |p2 i - q2 i|) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      |(t * p1 i + (1 - t) * p2 i) -
          (t * q1 i + (1 - t) * q2 i)| =
          |t * (p1 i - q1 i) + (1 - t) * (p2 i - q2 i)| := by ring_nf
      _ ≤ |t * (p1 i - q1 i)| + |(1 - t) * (p2 i - q2 i)| :=
        abs_add_le _ _
      _ = t * |p1 i - q1 i| + (1 - t) * |p2 i - q2 i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hone_sub_t]
  calc
    (1 / 2 : ℝ) *
        ∑ i, |(t * p1 i + (1 - t) * p2 i) -
          (t * q1 i + (1 - t) * q2 i)| ≤
        (1 / 2 : ℝ) *
          ∑ i, (t * |p1 i - q1 i| + (1 - t) * |p2 i - q2 i|) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = t * ((1 / 2 : ℝ) * ∑ i, |p1 i - q1 i|) +
        (1 - t) * ((1 / 2 : ℝ) * ∑ i, |p2 i - q2 i|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- Squared root distance is jointly convex on the nonnegative quadrant. The Cauchy--Schwarz
core is `Real.sum_sqrt_mul_sqrt_le`, specialized to the two mixture components. -/
theorem sq_sqrt_mix_sub_sqrt_mix_le
    (a1 a2 b1 b2 t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    (Real.sqrt (t * a1 + (1 - t) * a2) -
        Real.sqrt (t * b1 + (1 - t) * b2)) ^ 2 ≤
      t * (Real.sqrt a1 - Real.sqrt b1) ^ 2 +
        (1 - t) * (Real.sqrt a2 - Real.sqrt b2) ^ 2 := by
  have hone_sub_t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hmix_a : 0 ≤ t * a1 + (1 - t) * a2 :=
    add_nonneg (mul_nonneg ht.1 ha1) (mul_nonneg hone_sub_t ha2)
  have hmix_b : 0 ≤ t * b1 + (1 - t) * b2 :=
    add_nonneg (mul_nonneg ht.1 hb1) (mul_nonneg hone_sub_t hb2)
  have hcauchy :
      Real.sqrt (t * a1) * Real.sqrt (t * b1) +
          Real.sqrt ((1 - t) * a2) * Real.sqrt ((1 - t) * b2) ≤
        Real.sqrt (t * a1 + (1 - t) * a2) *
          Real.sqrt (t * b1 + (1 - t) * b2) := by
    simpa [Fintype.sum_bool, add_comm] using
      (Real.sum_sqrt_mul_sqrt_le Finset.univ
        (f := fun k : Bool => match k with
          | false => t * a1
          | true => (1 - t) * a2)
        (g := fun k : Bool => match k with
          | false => t * b1
          | true => (1 - t) * b2)
        (fun k => by
          cases k with
          | false => exact mul_nonneg ht.1 ha1
          | true => exact mul_nonneg hone_sub_t ha2)
        (fun k => by
          cases k with
          | false => exact mul_nonneg ht.1 hb1
          | true => exact mul_nonneg hone_sub_t hb2))
  have hgeometric :
      t * (Real.sqrt a1 * Real.sqrt b1) +
          (1 - t) * (Real.sqrt a2 * Real.sqrt b2) ≤
        Real.sqrt (t * a1 + (1 - t) * a2) *
          Real.sqrt (t * b1 + (1 - t) * b2) := by
    calc
      t * (Real.sqrt a1 * Real.sqrt b1) +
          (1 - t) * (Real.sqrt a2 * Real.sqrt b2) =
          Real.sqrt (t * a1) * Real.sqrt (t * b1) +
            Real.sqrt ((1 - t) * a2) * Real.sqrt ((1 - t) * b2) := by
        rw [Real.sqrt_mul ht.1, Real.sqrt_mul ht.1,
          Real.sqrt_mul hone_sub_t, Real.sqrt_mul hone_sub_t]
        calc
          t * (Real.sqrt a1 * Real.sqrt b1) +
              (1 - t) * (Real.sqrt a2 * Real.sqrt b2) =
              Real.sqrt t ^ 2 * (Real.sqrt a1 * Real.sqrt b1) +
                Real.sqrt (1 - t) ^ 2 * (Real.sqrt a2 * Real.sqrt b2) := by
            rw [Real.sq_sqrt ht.1, Real.sq_sqrt hone_sub_t]
          _ = Real.sqrt t * Real.sqrt a1 * (Real.sqrt t * Real.sqrt b1) +
              Real.sqrt (1 - t) * Real.sqrt a2 *
                (Real.sqrt (1 - t) * Real.sqrt b2) := by ring
      _ ≤ Real.sqrt (t * a1 + (1 - t) * a2) *
          Real.sqrt (t * b1 + (1 - t) * b2) := hcauchy
  have hsq1 :
      (Real.sqrt a1 - Real.sqrt b1) ^ 2 =
        a1 + b1 - 2 * (Real.sqrt a1 * Real.sqrt b1) := by
    rw [show (Real.sqrt a1 - Real.sqrt b1) ^ 2 =
      Real.sqrt a1 ^ 2 + Real.sqrt b1 ^ 2 -
        2 * (Real.sqrt a1 * Real.sqrt b1) by ring,
      Real.sq_sqrt ha1, Real.sq_sqrt hb1]
  have hsq2 :
      (Real.sqrt a2 - Real.sqrt b2) ^ 2 =
        a2 + b2 - 2 * (Real.sqrt a2 * Real.sqrt b2) := by
    rw [show (Real.sqrt a2 - Real.sqrt b2) ^ 2 =
      Real.sqrt a2 ^ 2 + Real.sqrt b2 ^ 2 -
        2 * (Real.sqrt a2 * Real.sqrt b2) by ring,
      Real.sq_sqrt ha2, Real.sq_sqrt hb2]
  calc
    (Real.sqrt (t * a1 + (1 - t) * a2) -
        Real.sqrt (t * b1 + (1 - t) * b2)) ^ 2 =
        (t * a1 + (1 - t) * a2) + (t * b1 + (1 - t) * b2) -
          2 * (Real.sqrt (t * a1 + (1 - t) * a2) *
            Real.sqrt (t * b1 + (1 - t) * b2)) := by
      rw [show (Real.sqrt (t * a1 + (1 - t) * a2) -
          Real.sqrt (t * b1 + (1 - t) * b2)) ^ 2 =
        Real.sqrt (t * a1 + (1 - t) * a2) ^ 2 +
          Real.sqrt (t * b1 + (1 - t) * b2) ^ 2 -
            2 * (Real.sqrt (t * a1 + (1 - t) * a2) *
              Real.sqrt (t * b1 + (1 - t) * b2)) by ring,
        Real.sq_sqrt hmix_a, Real.sq_sqrt hmix_b]
    _ ≤ t * (a1 + b1 - 2 * (Real.sqrt a1 * Real.sqrt b1)) +
        (1 - t) * (a2 + b2 - 2 * (Real.sqrt a2 * Real.sqrt b2)) := by
      nlinarith
    _ = t * (Real.sqrt a1 - Real.sqrt b1) ^ 2 +
        (1 - t) * (Real.sqrt a2 - Real.sqrt b2) ^ 2 := by
      rw [hsq1, hsq2]

/-- Squared Hellinger distance is jointly convex on pointwise nonnegative finite mass functions.
Neither normalization nor discrete absolute continuity is needed. -/
theorem hellinger_sq_joint_convex {ι : Type*} [Fintype ι]
    (p1 p2 q1 q2 : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (hp1 : ∀ i, 0 ≤ p1 i) (hp2 : ∀ i, 0 ≤ p2 i)
    (hq1 : ∀ i, 0 ≤ q1 i) (hq2 : ∀ i, 0 ≤ q2 i) :
    hellingerSq (fun i => t * p1 i + (1 - t) * p2 i)
        (fun i => t * q1 i + (1 - t) * q2 i) ≤
      t * hellingerSq p1 q1 + (1 - t) * hellingerSq p2 q2 := by
  rw [hellingerSq, hellingerSq, hellingerSq]
  calc
    (∑ i, (Real.sqrt (t * p1 i + (1 - t) * p2 i) -
        Real.sqrt (t * q1 i + (1 - t) * q2 i)) ^ 2) ≤
        ∑ i, (t * (Real.sqrt (p1 i) - Real.sqrt (q1 i)) ^ 2 +
          (1 - t) * (Real.sqrt (p2 i) - Real.sqrt (q2 i)) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_sqrt_mix_sub_sqrt_mix_le
        (p1 i) (p2 i) (q1 i) (q2 i) t ht (hp1 i) (hp2 i) (hq1 i) (hq2 i)
    _ = t * (∑ i, (Real.sqrt (p1 i) - Real.sqrt (q1 i)) ^ 2) +
        (1 - t) * (∑ i, (Real.sqrt (p2 i) - Real.sqrt (q2 i)) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/- Total-variation joint convexity is strict when the two endpoint differences cancel. -/
example :
    totalVariation
        (fun _ : Unit => (1 / 2 : ℝ) * 1 + (1 - 1 / 2) * 0)
        (fun _ : Unit => (1 / 2 : ℝ) * 0 + (1 - 1 / 2) * 1) <
      (1 / 2 : ℝ) * totalVariation (fun _ : Unit => 1) (fun _ : Unit => 0) +
        (1 - 1 / 2) * totalVariation (fun _ : Unit => 0) (fun _ : Unit => 1) := by
  norm_num [totalVariation]

/- Squared-Hellinger joint convexity is strict for the same two crossed endpoint pairs. -/
example :
    hellingerSq
        (fun _ : Unit => (1 / 2 : ℝ) * 1 + (1 - 1 / 2) * 0)
        (fun _ : Unit => (1 / 2 : ℝ) * 0 + (1 - 1 / 2) * 1) <
      (1 / 2 : ℝ) * hellingerSq (fun _ : Unit => 1) (fun _ : Unit => 0) +
        (1 - 1 / 2) * hellingerSq (fun _ : Unit => 0) (fun _ : Unit => 1) := by
  norm_num [hellingerSq]

/- The Hellinger cone hypothesis cannot be dropped: with one negative endpoint, `Real.sqrt`
truncation makes the midpoint distance larger than the endpoint average. Swapping endpoints
or the two arguments gives the corresponding counterexample for each of the four hypotheses. -/
example :
    ¬(hellingerSq
        (fun _ : Unit => (1 / 2 : ℝ) * (-1) + (1 - 1 / 2) * 1)
        (fun _ : Unit => (1 / 2 : ℝ) * 1 + (1 - 1 / 2) * 1) ≤
      (1 / 2 : ℝ) * hellingerSq (fun _ : Unit => -1) (fun _ : Unit => 1) +
        (1 - 1 / 2) * hellingerSq (fun _ : Unit => 1) (fun _ : Unit => 1)) := by
  norm_num [hellingerSq, Real.sqrt_eq_zero_of_nonpos]

/- Neither reflexivity nor simplification proves total-variation joint convexity. -/
example {ι : Type*} [Fintype ι]
    (p1 p2 q1 q2 : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    totalVariation (fun i => t * p1 i + (1 - t) * p2 i)
        (fun i => t * q1 i + (1 - t) * q2 i) ≤
      t * totalVariation p1 q1 + (1 - t) * totalVariation p2 q2 := by
  fail_if_success rfl
  fail_if_success simp
  exact total_variation_joint_convex p1 p2 q1 q2 t ht

/- Neither reflexivity nor simplification proves squared-Hellinger joint convexity. -/
example {ι : Type*} [Fintype ι]
    (p1 p2 q1 q2 : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (hp1 : ∀ i, 0 ≤ p1 i) (hp2 : ∀ i, 0 ≤ p2 i)
    (hq1 : ∀ i, 0 ≤ q1 i) (hq2 : ∀ i, 0 ≤ q2 i) :
    hellingerSq (fun i => t * p1 i + (1 - t) * p2 i)
        (fun i => t * q1 i + (1 - t) * q2 i) ≤
      t * hellingerSq p1 q1 + (1 - t) * hellingerSq p2 q2 := by
  fail_if_success rfl
  fail_if_success simp
  exact hellinger_sq_joint_convex p1 p2 q1 q2 t ht hp1 hp2 hq1 hq2

#print axioms total_variation_joint_convex
#print axioms sq_sqrt_mix_sub_sqrt_mix_le
#print axioms hellinger_sq_joint_convex

end D5.S3.TotalVariation.Convexity
