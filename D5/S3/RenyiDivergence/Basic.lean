/- GID: D5/S3/RenyiDivergence/Basic
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/Basic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite Renyi divergence and pin its half-order, self, and order-two identities. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `Renyi`, `Rényi`, `renyiDivergence`,
     `InformationTheory`, `rpow_sum`, `zero_rpow`, `sqrt_eq_rpow`, `rpow_add`,
     `geom_mean_le_arith_mean2_weighted`, and `HolderConjugate`.
   * No probability-theory Renyi divergence was found. Mathlib's information-theory divergence
     is measure-valued in `ENNReal`, with no frozen bridge to this repository's finite real sum.
   * The reusable finite ingredients are `Real.sqrt_eq_rpow`, `Real.rpow_add'`, and the
     two-variable weighted AM--GM theorem `Real.geom_mean_le_arith_mean2_weighted`.
   * A scan of all 631 `def`/`theorem`/`lemma` declarations below `D5/S3` found no Renyi
     declaration. The frozen Bhattacharyya coefficient is imported rather than redefined.
-/

import D5.S3.TotalVariation.Bhattacharyya

namespace D5.S3.RenyiDivergence

open D5.S3.TotalVariation.Bhattacharyya

/-!
`Real.rpow` is the required power because the order is real. It is totalized at zero:
`0 ^ 0 = 1`, while `0 ^ x = 0` for `x != 0`. Division and logarithm are also totalized, so
the displayed formula evaluates to zero at order one and `Real.log 0 = 0`. The definition is
therefore total, but no order-one/KL interpretation is claimed. The theorem statements below
record the hypotheses that keep each asserted finite-order interpretation meaningful.
-/

/-- Real-valued Renyi divergence of order `alpha` for finite mass functions. The order-one guard
lives on results interpreting this total formula, rather than as a proof argument to the data. -/
noncomputable def renyiDivergence {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) : Real :=
  (1 / (alpha - 1)) * Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha))

/-- At order one half, finite Renyi divergence is minus twice the logarithm of the frozen
Bhattacharyya coefficient. Pointwise nonnegativity of `p` is exactly what combines the two square
roots; normalization, absolute continuity, and nonnegativity of `q` are not used. -/
theorem renyi_divergence_one_half {ι : Type*} [Fintype ι]
    (p q : ι -> Real) (hp : forall i, 0 <= p i) :
    renyiDivergence (1 / 2) p q =
      -2 * Real.log (bhattacharyya p q) := by
  rw [renyiDivergence, bhattacharyya]
  norm_num
  congr 2
  funext i
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (hp i)]

/-- A normalized nonnegative mass function has zero Renyi divergence from itself at every real
order. At order one this records the totalized formula's value, not the KL limiting theorem. -/
theorem renyi_divergence_self {ι : Type*} [Fintype ι]
    (alpha : Real) (p : ι -> Real)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1) :
    renyiDivergence alpha p p = 0 := by
  rw [renyiDivergence]
  have hsum : (∑ i, (p i) ^ alpha * (p i) ^ (1 - alpha)) = 1 := by
    calc
      (∑ i, (p i) ^ alpha * (p i) ^ (1 - alpha)) = ∑ i, p i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.rpow_add' (hp.1 i) (by norm_num),
          show alpha + (1 - alpha) = 1 by ring, Real.rpow_one]
      _ = 1 := hp.2
  rw [hsum, Real.log_one, mul_zero]

/-- Finite Renyi divergence is nonnegative for orders strictly between zero and one. Discrete
absolute continuity is used to make the power sum strictly positive, excluding the disjoint-support
case that Lean's `Real.log 0 = 0` convention would otherwise flatten to zero. -/
theorem renyi_divergence_nonneg {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : (forall i, 0 <= q i) ∧ ∑ i, q i = 1)
    (hac : forall i, q i = 0 -> p i = 0) :
    0 <= renyiDivergence alpha p q := by
  have hexists : Exists fun i => 0 < p i := by
    have hsum_pos : 0 < ∑ i, p i := by rw [hp.2]; norm_num
    rcases (Finset.sum_pos_iff_of_nonneg fun i _ => hp.1 i).mp hsum_pos with
      ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  have hsum_pos : 0 < ∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha) := by
    apply Finset.sum_pos' (fun i _ => mul_nonneg
      (Real.rpow_nonneg (hp.1 i) alpha)
      (Real.rpow_nonneg (hq.1 i) (1 - alpha)))
    rcases hexists with ⟨i, hpi⟩
    have hqi_ne : q i = 0 -> False := by
      intro hqi
      linarith [hac i hqi]
    have hqi : 0 < q i := lt_of_le_of_ne (hq.1 i) (Ne.symm hqi_ne)
    exact ⟨i, Finset.mem_univ i, mul_pos
      (Real.rpow_pos_of_pos hpi alpha)
      (Real.rpow_pos_of_pos hqi (1 - alpha))⟩
  have hsum_le_one : (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) <= 1 := by
    calc
      (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) <=
          ∑ i, (alpha * p i + (1 - alpha) * q i) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.geom_mean_le_arith_mean2_weighted
          halpha.1.le (sub_nonneg.mpr halpha.2.le) (hp.1 i) (hq.1 i) (by ring)
      _ = 1 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
        ring
  have hlog_nonpos :
      Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) <= 0 :=
    Real.log_nonpos hsum_pos.le hsum_le_one
  have hprefactor_nonpos : 1 / (alpha - 1) <= 0 :=
    div_nonpos_of_nonneg_of_nonpos zero_le_one (sub_nonpos.mpr halpha.2.le)
  rw [renyiDivergence]
  exact mul_nonneg_of_nonpos_of_nonpos hprefactor_nonpos hlog_nonpos

/-- On the Bool point-mass-versus-uniform witness, order-two Renyi divergence is `log 2`. This
pin distinguishes the orientation of the two exponents, which order one half cannot do. -/
theorem renyi_divergence_two_point_order_two :
    renyiDivergence 2
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun _ : Bool => (1 / 2 : Real)) = Real.log 2 := by
  norm_num [renyiDivergence, Fintype.sum_bool]

/-- The `DisjointBoolPointMasses` witness violates absolute continuity. At order one half its
power sum is zero, so Lean's `Real.log 0 = 0` convention flattens the mathematically infinite
divergence to zero. -/
theorem renyi_divergence_disjoint_support_flattening_witness :
    renyiDivergence (1 / 2)
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun b : Bool => if b then 0 else (1 : Real)) = 0 := by
  norm_num [renyiDivergence, Fintype.sum_bool]

/- `PointVsUniformHalf`: dropping the prefactor gives `-log 2 / 2`, while the half-order pin gives
`log 2`. Thus the half-order identity detects this corruption. -/
example :
    Real.log (∑ b : Bool,
      ((if b then (1 : Real) else 0) ^ (1 / 2 : Real)) *
        ((1 / 2 : Real) ^ (1 - (1 / 2 : Real)))) = -Real.log 2 / 2 := by
  norm_num [Fintype.sum_bool]
  rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
    Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
  norm_num
  ring

/- `PointVsUniformHalf`: swapping the exponents survives the half-order pin because both exponents
are one half; the corrupted expression still gives `log 2`. -/
example :
    (1 / ((1 / 2 : Real) - 1)) * Real.log (∑ b : Bool,
      ((if b then (1 : Real) else 0) ^ (1 - (1 / 2 : Real))) *
        ((1 / 2 : Real) ^ (1 / 2 : Real))) = Real.log 2 := by
  norm_num [Fintype.sum_bool]
  rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
    Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
  norm_num
  ring

/- `PointVsUniformOrderTwo`: after swapping the exponents, the order-two value is `-2 * log 2`,
whereas `renyi_divergence_two_point_order_two` pins the correct value to `log 2`. -/
example :
    (1 / ((2 : Real) - 1)) * Real.log (∑ b : Bool,
      ((if b then (1 : Real) else 0) ^ (1 - (2 : Real))) *
        ((1 / 2 : Real) ^ (2 : Real))) = -2 * Real.log 2 := by
  norm_num [Fintype.sum_bool]
  rw [show (1 / 4 : Real) = ((2 : Real) ^ 2)⁻¹ by norm_num,
    Real.log_inv, Real.log_pow]
  norm_num

/- `PointVsUniformHalf`: replacing `1 - alpha` by `alpha` also survives at one half and gives the
correct value `log 2`. -/
example :
    (1 / ((1 / 2 : Real) - 1)) * Real.log (∑ b : Bool,
      ((if b then (1 : Real) else 0) ^ (1 / 2 : Real)) *
        ((1 / 2 : Real) ^ (1 / 2 : Real))) = Real.log 2 := by
  norm_num [Fintype.sum_bool]
  rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
    Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
  norm_num
  ring

/- `UniformSelfOrderTwo`: with `alpha, alpha`, self-divergence becomes `-3 * log 2` rather than
zero. The all-order self identity detects this corruption. -/
example :
    (1 / ((2 : Real) - 1)) * Real.log (∑ _b : Bool,
      ((1 / 2 : Real) ^ (2 : Real)) * ((1 / 2 : Real) ^ (2 : Real))) =
        -3 * Real.log 2 := by
  norm_num [Fintype.sum_bool]
  rw [show (1 / 8 : Real) = ((2 : Real) ^ 3)⁻¹ by norm_num,
    Real.log_inv, Real.log_pow]
  norm_num

end D5.S3.RenyiDivergence
