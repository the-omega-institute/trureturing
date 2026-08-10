/- GID: D5/S3/DivergenceSupport/LogSumInequality
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/LogSumInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite log-sum and joint convexity of real-valued KL divergence. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep/read terms: `log_sum`, `logSum`, `sum.*Real.log`,
     `mul_klFun_le_toReal_klDiv`, `convexOn_klFun`, `ConvexOn.map_sum_le`,
     `strictConcaveOn_log_Ioi`, `Real.inner_mul_le_norm_mul_norm`,
     `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`, and `Real.mul_log_nonneg`.
   * No finite real-valued log-sum theorem or joint-convexity theorem for the repository's
     `klDivergence` was found. The measure-valued theorem `mul_klFun_le_toReal_klDiv` is analogous,
     but using it here would require a new bridge between finite sums and measure KL divergence.
   * `InformationTheory.convexOn_klFun` and `ConvexOn.map_sum_le` give the direct finite Jensen
     core used below. The affine correction in `klFun x = x * log x + 1 - x` converts it exactly
     to log-sum without probability-normalization hypotheses.
   * Repository grep terms under all of `D5/S3`: `log_sum`, `logSum`, `joint.*convex`, `convex`,
     `jensen`, `klDivergence`, `Kullback`, and `relative.*entropy`. Existing files contain KL
     identities, Gibbs/Pinsker bounds, and Jensen applications, but neither result below.
-/

import D5.S3.Divergence.ClassicalDPI

namespace D5.S3.DivergenceSupport.LogSumInequality

open D5.S3.Divergence.ClassicalDPI
open InformationTheory

/-!
The repository's real-valued divergence totalizes division and logarithm at zero:
`x / 0 = 0` and `Real.log 0 = 0`. Consequently, the mathematically meaningful finite log-sum
inequality requires discrete absolute continuity `b i = 0 -> a i = 0`; without it, a positive
mass above a zero reference mass is flattened instead of contributing positive infinity. The
compiled counterexample below shows that the unguarded finite inequality is actually false.
-/

/-- The finite log-sum inequality for nonnegative masses under discrete absolute continuity. -/
theorem log_sum_inequality {ι : Type*} [Fintype ι]
    (a b : ι -> Real)
    (ha : ∀ i, 0 <= a i)
    (hb : ∀ i, 0 <= b i)
    (hac : ∀ i, b i = 0 -> a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) <=
      ∑ i, a i * Real.log (a i / b i) := by
  classical
  by_cases hsum_b : (∑ i, b i) = 0
  · have hb_zero (i : ι) : b i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hb j).mp hsum_b i (Finset.mem_univ i)
    have ha_zero (i : ι) : a i = 0 := hac i (hb_zero i)
    simp [hb_zero, ha_zero]
  have hsum_b_nonneg : 0 <= ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have hsum_b_pos : 0 < ∑ i, b i := lt_of_le_of_ne hsum_b_nonneg (Ne.symm hsum_b)
  have hweighted_ratio (i : ι) :
      b i / (∑ j, b j) * (a i / b i) = a i / (∑ j, b j) := by
    by_cases hbi : b i = 0
    · simp [hbi, hac i hbi]
    · field_simp [hsum_b, hbi]
  have hweighted_sum :
      (∑ i, b i / (∑ j, b j) * (a i / b i)) =
        (∑ i, a i) / (∑ i, b i) := by
    calc
      (∑ i, b i / (∑ j, b j) * (a i / b i)) =
          ∑ i, a i / (∑ j, b j) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hweighted_ratio i
      _ = (∑ i, a i) / (∑ i, b i) := by rw [Finset.sum_div]
  have hjensen := convexOn_klFun.map_sum_le
    (t := Finset.univ)
    (w := fun i => b i / (∑ j, b j))
    (p := fun i => a i / b i)
    (fun i _ => div_nonneg (hb i) hsum_b_nonneg)
    (by rw [← Finset.sum_div, div_self hsum_b])
    (fun i _ => div_nonneg (ha i) (hb i))
  simp only [smul_eq_mul] at hjensen
  rw [hweighted_sum] at hjensen
  have hperspective :
      (∑ i, b i) * klFun ((∑ i, a i) / (∑ i, b i)) <=
        ∑ i, b i * klFun (a i / b i) := by
    calc
      (∑ i, b i) * klFun ((∑ i, a i) / (∑ i, b i)) <=
          (∑ i, b i) *
            (∑ i, b i / (∑ j, b j) * klFun (a i / b i)) :=
        mul_le_mul_of_nonneg_left hjensen hsum_b_nonneg
      _ = ∑ i, b i * klFun (a i / b i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hsum_b]
  have hleft :
      (∑ i, b i) * klFun ((∑ i, a i) / (∑ i, b i)) =
        (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) +
          (∑ i, b i) - ∑ i, a i := by
    rw [klFun_apply]
    field_simp [hsum_b]
  have hterm (i : ι) :
      b i * klFun (a i / b i) =
        a i * Real.log (a i / b i) + b i - a i := by
    by_cases hbi : b i = 0
    · simp [hbi, hac i hbi, klFun_apply]
    · rw [klFun_apply]
      field_simp [hbi]
  have hright :
      (∑ i, b i * klFun (a i / b i)) =
        (∑ i, a i * Real.log (a i / b i)) + (∑ i, b i) - ∑ i, a i := by
    calc
      (∑ i, b i * klFun (a i / b i)) =
          ∑ i, (a i * Real.log (a i / b i) + b i - a i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
      _ = (∑ i, a i * Real.log (a i / b i)) + (∑ i, b i) - ∑ i, a i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hleft, hright] at hperspective
  linarith

/- Without absolute continuity, `a = (1, 1)` and `b = (1, 0)` make the right side zero by the
totalized zero conventions, while the left side is `2 * log 2 > 0`. -/
example :
    let a : Bool -> Real := fun _ => 1
    let b : Bool -> Real := fun i => match i with | false => 1 | true => 0
    ¬ ((∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) <=
      ∑ i, a i * Real.log (a i / b i)) := by
  dsimp
  norm_num
  exact Real.log_pos (by norm_num)

/- The log-sum inequality is strict for `a = (1, 0)` and `b = (1/2, 1/2)`. -/
example :
    let a : Bool -> Real := fun i => match i with | false => 1 | true => 0
    let b : Bool -> Real := fun _ => 1 / 2
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) <
      ∑ i, a i * Real.log (a i / b i) := by
  dsimp
  norm_num
  exact Real.log_pos (by norm_num)

/- Neither reflexivity nor simplification proves the general log-sum statement. -/
example {ι : Type*} [Fintype ι]
    (a b : ι -> Real)
    (ha : ∀ i, 0 <= a i)
    (hb : ∀ i, 0 <= b i)
    (hac : ∀ i, b i = 0 -> a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) <=
      ∑ i, a i * Real.log (a i / b i) := by
  fail_if_success rfl
  fail_if_success simp
  exact log_sum_inequality a b ha hb hac

/-- Joint convexity of finite real-valued KL divergence on nonnegative absolutely continuous
pairs. No normalization is needed; `0 <= t <= 1` makes the two mixture weights nonnegative. -/
theorem kl_divergence_joint_convex {ι : Type*} [Fintype ι]
    (p1 p2 q1 q2 : ι -> Real) (t : Real)
    (ht : 0 <= t ∧ t <= 1)
    (hp1 : ∀ i, 0 <= p1 i) (hp2 : ∀ i, 0 <= p2 i)
    (hq1 : ∀ i, 0 <= q1 i) (hq2 : ∀ i, 0 <= q2 i)
    (hac1 : ∀ i, q1 i = 0 -> p1 i = 0)
    (hac2 : ∀ i, q2 i = 0 -> p2 i = 0) :
    klDivergence (fun i => t * p1 i + (1 - t) * p2 i)
        (fun i => t * q1 i + (1 - t) * q2 i) <=
      t * klDivergence p1 q1 + (1 - t) * klDivergence p2 q2 := by
  classical
  have hone_sub_t : 0 <= 1 - t := sub_nonneg.mpr ht.2
  have hscale1 (i : ι) :
      (t * p1 i) * Real.log ((t * p1 i) / (t * q1 i)) =
        t * (p1 i * Real.log (p1 i / q1 i)) := by
    by_cases ht_zero : t = 0
    · simp [ht_zero]
    · have hratio : (t * p1 i) / (t * q1 i) = p1 i / q1 i := by
        field_simp [ht_zero]
      rw [hratio]
      ring
  have hscale2 (i : ι) :
      ((1 - t) * p2 i) * Real.log (((1 - t) * p2 i) / ((1 - t) * q2 i)) =
        (1 - t) * (p2 i * Real.log (p2 i / q2 i)) := by
    by_cases hone_sub_t_zero : 1 - t = 0
    · simp [hone_sub_t_zero]
    · have hratio :
          ((1 - t) * p2 i) / ((1 - t) * q2 i) = p2 i / q2 i := by
        field_simp [hone_sub_t_zero]
      rw [hratio]
      ring
  have hcoordinate (i : ι) :
      (t * p1 i + (1 - t) * p2 i) *
          Real.log ((t * p1 i + (1 - t) * p2 i) /
            (t * q1 i + (1 - t) * q2 i)) <=
        t * (p1 i * Real.log (p1 i / q1 i)) +
          (1 - t) * (p2 i * Real.log (p2 i / q2 i)) := by
    have h := log_sum_inequality
      (fun k : Bool => match k with
        | false => t * p1 i
        | true => (1 - t) * p2 i)
      (fun k : Bool => match k with
        | false => t * q1 i
        | true => (1 - t) * q2 i)
      (fun k => by
        cases k with
        | false => exact mul_nonneg ht.1 (hp1 i)
        | true => exact mul_nonneg hone_sub_t (hp2 i))
      (fun k => by
        cases k with
        | false => exact mul_nonneg ht.1 (hq1 i)
        | true => exact mul_nonneg hone_sub_t (hq2 i))
      (fun k hk => by
        cases k with
        | false =>
            dsimp at hk ⊢
            rcases mul_eq_zero.mp hk with ht_zero | hq_zero
            · simp [ht_zero]
            · simp [hac1 i hq_zero]
        | true =>
            dsimp at hk ⊢
            rcases mul_eq_zero.mp hk with ht_zero | hq_zero
            · simp [ht_zero]
            · simp [hac2 i hq_zero])
    simpa only [Fintype.sum_bool, hscale1 i, hscale2 i, add_comm] using h
  rw [klDivergence, klDivergence, klDivergence]
  calc
    (∑ i, (t * p1 i + (1 - t) * p2 i) *
        Real.log ((t * p1 i + (1 - t) * p2 i) /
          (t * q1 i + (1 - t) * q2 i))) <=
        ∑ i, (t * (p1 i * Real.log (p1 i / q1 i)) +
          (1 - t) * (p2 i * Real.log (p2 i / q2 i))) :=
      Finset.sum_le_sum fun i _ => hcoordinate i
    _ = t * (∑ i, p1 i * Real.log (p1 i / q1 i)) +
        (1 - t) * (∑ i, p2 i * Real.log (p2 i / q2 i)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/- Joint convexity is strict at `t = 1/2` on a one-point type for
`(p1, q1) = (0, 1)` and `(p2, q2) = (2, 1)`. -/
example :
    klDivergence
        (fun _ : Unit => (1 / 2 : Real) * 0 + (1 - 1 / 2) * 2)
        (fun _ : Unit => (1 / 2 : Real) * 1 + (1 - 1 / 2) * 1) <
      (1 / 2 : Real) * klDivergence (fun _ : Unit => 0) (fun _ : Unit => 1) +
        (1 - 1 / 2) * klDivergence (fun _ : Unit => 2) (fun _ : Unit => 1) := by
  norm_num [klDivergence]
  exact Real.log_pos (by norm_num)

/- Neither reflexivity nor simplification proves the general joint-convexity statement. -/
example {ι : Type*} [Fintype ι]
    (p1 p2 q1 q2 : ι -> Real) (t : Real)
    (ht : 0 <= t ∧ t <= 1)
    (hp1 : ∀ i, 0 <= p1 i) (hp2 : ∀ i, 0 <= p2 i)
    (hq1 : ∀ i, 0 <= q1 i) (hq2 : ∀ i, 0 <= q2 i)
    (hac1 : ∀ i, q1 i = 0 -> p1 i = 0)
    (hac2 : ∀ i, q2 i = 0 -> p2 i = 0) :
    klDivergence (fun i => t * p1 i + (1 - t) * p2 i)
        (fun i => t * q1 i + (1 - t) * q2 i) <=
      t * klDivergence p1 q1 + (1 - t) * klDivergence p2 q2 := by
  fail_if_success rfl
  fail_if_success simp
  exact kl_divergence_joint_convex p1 p2 q1 q2 t ht hp1 hp2 hq1 hq2 hac1 hac2

end D5.S3.DivergenceSupport.LogSumInequality
