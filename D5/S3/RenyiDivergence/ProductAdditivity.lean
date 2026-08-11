/- GID: D5/S3/RenyiDivergence/ProductAdditivity
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/ProductAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove additivity of finite Renyi divergence under product mass functions. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms: `Renyi`, `Rényi`, `renyiDivergence`,
     `Renyi.*prod`, `prod.*Renyi`, `Fintype.sum_prod_type`, `Fintype.sum_mul_sum`,
     `Real.mul_rpow`, and `Real.log_mul`.
   * No probability-theory Renyi divergence or product-additivity theorem was found. The only
     Renyi-name hits concern Erdos--Renyi random graphs. The exact reusable algebraic lemmas are
     `Real.mul_rpow`, `Fintype.sum_prod_type`, `Fintype.sum_mul_sum`, and `Real.log_mul`.
   * A scan of all 784 pre-existing `def`/`theorem`/`lemma` declarations below `D5/S3` found no
     Renyi product-additivity theorem. The Renyi bucket contained its definition and nine prior
     theorems, all in `Basic`, `Monotone`, and `DataProcessing`.
-/

import D5.S3.RenyiDivergence.Basic

namespace D5.S3.RenyiDivergence

/-!
The shared factor `1 / (alpha - 1)` makes product additivity independent of its sign: after the
joint power sum is factorized, the factor distributes over the sum of logarithms. Thus the result
holds on both sides of order one and at order one itself, where the totalized prefactor is zero.

Nonnegativity is exactly what `Real.mul_rpow` needs. Normalization and coordinatewise strict
positivity are unnecessary. The two marginal power sums must be nonzero for `Real.log_mul`; if
exactly one vanishes, totalized `Real.log 0 = 0` can make the asserted identity false.
-/

/-- Finite Renyi divergence is additive on products of nonnegative finite mass functions whose
marginal power sums do not vanish. No normalization or restriction on the real order is needed. -/
theorem renyi_divergence_product_additive
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (alpha : Real) (p q : ι -> Real) (p' q' : κ -> Real)
    (hp : forall i, 0 <= p i) (hq : forall i, 0 <= q i)
    (hp' : forall j, 0 <= p' j) (hq' : forall j, 0 <= q' j)
    (hsum : (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) ≠ 0)
    (hsum' : (∑ j, (p' j) ^ alpha * (q' j) ^ (1 - alpha)) ≠ 0) :
    renyiDivergence alpha (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) =
      renyiDivergence alpha p q + renyiDivergence alpha p' q' := by
  fail_if_success rfl
  fail_if_success simp
  classical
  rw [renyiDivergence, renyiDivergence, renyiDivergence,
    Fintype.sum_prod_type]
  have hPowerSum :
      (∑ i, ∑ j,
          (p i * p' j) ^ alpha * (q i * q' j) ^ (1 - alpha)) =
        (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) *
          ∑ j, (p' j) ^ alpha * (q' j) ^ (1 - alpha) := by
    calc
      (∑ i, ∑ j,
          (p i * p' j) ^ alpha * (q i * q' j) ^ (1 - alpha)) =
          ∑ i, ∑ j,
            ((p i) ^ alpha * (q i) ^ (1 - alpha)) *
              ((p' j) ^ alpha * (q' j) ^ (1 - alpha)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Real.mul_rpow (hp i) (hp' j), Real.mul_rpow (hq i) (hq' j)]
        ring
      _ = (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) *
          ∑ j, (p' j) ^ alpha * (q' j) ^ (1 - alpha) :=
        (Fintype.sum_mul_sum _ _).symm
  rw [hPowerSum, Real.log_mul hsum hsum']
  ring

/- The non-vanishing hypotheses cannot both be dropped. At order one half, a disjoint first
marginal has power sum zero, while the point-mass-versus-uniform second marginal contributes
`log 2`. The joint power sum is zero, so totalized `Real.log 0 = 0` erases that contribution. -/
example :
    ¬(renyiDivergence (1 / 2)
        (fun z : Bool × Bool =>
          (if z.1 then (1 : Real) else 0) * (if z.2 then (1 : Real) else 0))
        (fun z : Bool × Bool =>
          (if z.1 then 0 else (1 : Real)) * (1 / 2 : Real)) =
      renyiDivergence (1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun b : Bool => if b then 0 else (1 : Real)) +
        renyiDivergence (1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real))) := by
  have hJoint :
      renyiDivergence (1 / 2)
          (fun z : Bool × Bool =>
            (if z.1 then (1 : Real) else 0) * (if z.2 then (1 : Real) else 0))
          (fun z : Bool × Bool =>
            (if z.1 then 0 else (1 : Real)) * (1 / 2 : Real)) = 0 := by
    norm_num [renyiDivergence, Fintype.sum_prod_type, Fintype.sum_bool]
  have hSecond :
      renyiDivergence (1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real)) = Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
      Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num
    ring
  rw [hJoint, renyi_divergence_disjoint_support_flattening_witness, hSecond, zero_add]
  exact (Real.log_pos (by norm_num : (1 : Real) < 2)).ne

/- On two independent copies of the Bool point-mass-versus-uniform experiment at order two,
the joint divergence computes to `log 4` and the two marginal divergences compute to
`log 2 + log 2`. -/
example :
    renyiDivergence 2
        (fun z : Bool × Bool =>
          (if z.1 then (1 : Real) else 0) * (if z.2 then (1 : Real) else 0))
        (fun _z : Bool × Bool => (1 / 2 : Real) * (1 / 2 : Real)) =
      renyiDivergence 2
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real)) +
        renyiDivergence 2
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real)) := by
  have hJoint :
      renyiDivergence 2
          (fun z : Bool × Bool =>
            (if z.1 then (1 : Real) else 0) * (if z.2 then (1 : Real) else 0))
          (fun _z : Bool × Bool => (1 / 2 : Real) * (1 / 2 : Real)) =
        Real.log 4 := by
    norm_num [renyiDivergence, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [hJoint, renyi_divergence_two_point_order_two,
    ← Real.log_mul (by norm_num : (2 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
  norm_num

#print axioms renyi_divergence_product_additive

end D5.S3.RenyiDivergence
