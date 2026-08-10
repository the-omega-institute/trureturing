/- GID: D5/S3/RenyiDivergence/Monotone
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/Monotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove order monotonicity of finite Renyi divergence on each side of order one. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `power mean`, `Holder`, `HolderConjugate`,
     `Real.inner_le_nnorm_mul_nnorm`, `Real.rpow_natCast`,
     `Real.rpow_le_rpow_left_iff`, `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`,
     `Finset.inner_mul_le_norm_mul_norm`, `Real.pow_arith_mean_le_arith_mean_pow`,
     `NNReal.inner_le_iff`, `rpow_arith_mean_le_arith_mean_rpow`, and
     `inner_le_Lp_mul_Lq`.
   * Mathlib has finite Holder inequalities and the weighted Jensen theorem
     `Real.rpow_arith_mean_le_arith_mean_rpow`. Its power-mean module explicitly records
     arbitrary-exponent generalized mean monotonicity, including negative exponents, as a TODO.
     The weighted Jensen theorem is reused below at the quotient of the two shifted orders.
   * A grep of all 789 pre-existing `def`/`theorem`/`lemma` starts below `D5/S3` found no
     order-monotonicity theorem for Renyi divergence. All Renyi declarations found by the
     repository search are in the imported `Basic` module.
-/

import D5.S3.RenyiDivergence.Basic

namespace D5.S3.RenyiDivergence

/-!
This module proves order monotonicity separately on the open intervals `(0, 1)` and `(1, +inf)`.
Order one is excluded: the repository definition is totalized to `renyiDivergence 1 p q = 0`,
whereas the point-mass-versus-uniform probability witness has positive divergence at order one
half. Thus a theorem including the order-one endpoint is false for the literal definition, not
merely absent from this proof. A comparison crossing one is also false under the minimal
hypotheses below: for uniform `p` and point-mass `q`, the half-order value is `log 2` while the
order-two value is `-2 * log 2`. Absolute continuity excludes that witness, but the crossing case
with that additional hypothesis is not proved here; the same-side Jensen argument depends on the
two shifted orders having the same sign.

The proof rewrites the power sum as a weighted power mean with weights `p`, applies mathlib's
weighted Jensen inequality, and then uses monotonicity of `Real.log`. If the supports do not
overlap, both endpoint sums are zero and the totalized divergences agree at zero; otherwise both
sums are positive and the logarithmic argument is legitimate.
-/

/-- Finite Renyi divergence is nondecreasing in its order strictly between zero and one. Only
the first mass function is normalized; scaling the nonnegative reference mass shifts every order
by the same constant and is irrelevant to monotonicity. -/
theorem renyi_divergence_monotone_of_lt_one {ι : Type*} [Fintype ι]
    (alpha beta : Real) (p q : ι -> Real)
    (horder : 0 < alpha ∧ alpha <= beta ∧ beta < 1)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq_nonneg : forall i, 0 <= q i) :
    renyiDivergence alpha p q <= renyiDivergence beta p q := by
  classical
  rcases horder with ⟨halpha_pos, hab, hbeta_lt⟩
  rcases hab.eq_or_lt with rfl | hab_lt
  · rfl
  have hbeta_pos : 0 < beta := halpha_pos.trans hab_lt
  have halpha_lt : alpha < 1 := hab_lt.trans hbeta_lt
  have halpha_ne_zero : alpha ≠ 0 := halpha_pos.ne'
  have hbeta_ne_zero : beta ≠ 0 := hbeta_pos.ne'
  have halpha_ne_one : alpha ≠ 1 := ne_of_lt halpha_lt
  have hbeta_ne_one : beta ≠ 1 := ne_of_lt hbeta_lt
  have hsum_as_mean (gamma : Real) (hgamma_ne_zero : gamma ≠ 0)
      (hgamma_ne_one : gamma ≠ 1) :
      (∑ i, (p i) ^ gamma * (q i) ^ (1 - gamma)) =
        ∑ i, p i * (p i / q i) ^ (gamma - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi_zero : p i = 0
    · simp [hpi_zero, Real.zero_rpow hgamma_ne_zero]
    by_cases hqi_zero : q i = 0
    · simp [hqi_zero, Real.zero_rpow (sub_ne_zero.mpr hgamma_ne_one),
        Real.zero_rpow (sub_ne_zero.mpr hgamma_ne_one.symm)]
    have hpi_pos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hpi_zero)
    calc
      (p i) ^ gamma * (q i) ^ (1 - gamma) =
          ((p i) ^ (1 : Real) * (p i) ^ (gamma - 1)) *
            ((q i) ^ (gamma - 1))⁻¹ := by
        rw [← Real.rpow_add hpi_pos, ← Real.rpow_neg (hq_nonneg i)]
        congr 2 <;> ring
      _ = p i * ((p i) ^ (gamma - 1) / (q i) ^ (gamma - 1)) := by
        rw [Real.rpow_one, div_eq_mul_inv]
        ring
      _ = p i * (p i / q i) ^ (gamma - 1) := by
        rw [Real.div_rpow (hp.1 i) (hq_nonneg i)]
  by_cases hoverlap : ∃ i, 0 < p i ∧ 0 < q i
  · have hsum_pos (gamma : Real) :
        0 < ∑ i, (p i) ^ gamma * (q i) ^ (1 - gamma) := by
      apply Finset.sum_pos' (fun i _ => mul_nonneg
        (Real.rpow_nonneg (hp.1 i) gamma)
        (Real.rpow_nonneg (hq_nonneg i) (1 - gamma)))
      rcases hoverlap with ⟨i, hpi, hqi⟩
      exact ⟨i, Finset.mem_univ i, mul_pos
        (Real.rpow_pos_of_pos hpi gamma)
        (Real.rpow_pos_of_pos hqi (1 - gamma))⟩
    have hratio_nonneg (i : ι) : 0 <= p i / q i :=
      div_nonneg (hp.1 i) (hq_nonneg i)
    have hratio_order : 1 <= (alpha - 1) / (beta - 1) :=
      (one_le_div_of_neg (sub_neg.mpr hbeta_lt)).2 (sub_le_sub_right hab_lt.le 1)
    have hpow_term (i : ι) :
        ((p i / q i) ^ (beta - 1)) ^ ((alpha - 1) / (beta - 1)) =
          (p i / q i) ^ (alpha - 1) := by
      rw [← Real.rpow_mul (hratio_nonneg i)]
      congr 1
      field_simp [sub_ne_zero.mpr hbeta_ne_one]
    have hmean_raw := Real.rpow_arith_mean_le_arith_mean_rpow
      Finset.univ (fun i => p i) (fun i => (p i / q i) ^ (beta - 1))
      (fun i _ => hp.1 i) (by simpa using hp.2)
      (fun i _ => Real.rpow_nonneg (hratio_nonneg i) (beta - 1)) hratio_order
    have hmean :
        (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) ^
            ((alpha - 1) / (beta - 1)) <=
          ∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha) := by
      rw [hsum_as_mean beta hbeta_ne_zero hbeta_ne_one,
        hsum_as_mean alpha halpha_ne_zero halpha_ne_one]
      simpa [hpow_term] using hmean_raw
    have hlog :
        ((alpha - 1) / (beta - 1)) *
            Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) <=
          Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) := by
      calc
        ((alpha - 1) / (beta - 1)) *
            Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) =
            Real.log ((∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) ^
              ((alpha - 1) / (beta - 1))) :=
          (Real.log_rpow (hsum_pos beta) _).symm
        _ <= Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) :=
          Real.log_le_log
            (Real.rpow_pos_of_pos (hsum_pos beta) ((alpha - 1) / (beta - 1))) hmean
    rw [renyiDivergence, renyiDivergence]
    calc
      (1 / (alpha - 1)) *
          Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
          Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) /
            (alpha - 1) := by ring
      _ <= Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) /
          (beta - 1) := by
        rw [div_le_iff_of_neg (sub_neg.mpr halpha_lt)]
        calc
          (Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) /
              (beta - 1)) * (alpha - 1) =
              ((alpha - 1) / (beta - 1)) *
                Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) := by ring
          _ <= Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) := hlog
      _ = (1 / (beta - 1)) *
          Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) := by ring
  · have hsum_zero (gamma : Real) (hgamma_ne_zero : gamma ≠ 0)
        (hgamma_ne_one : gamma ≠ 1) :
        (∑ i, (p i) ^ gamma * (q i) ^ (1 - gamma)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases not_and_or.mp (not_exists.mp hoverlap i) with hpi | hqi
      · have hpi_zero : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp.1 i)
        simp [hpi_zero, Real.zero_rpow hgamma_ne_zero]
      · have hqi_zero : q i = 0 := le_antisymm (le_of_not_gt hqi) (hq_nonneg i)
        simp [hqi_zero, Real.zero_rpow (sub_ne_zero.mpr hgamma_ne_one.symm)]
    rw [renyiDivergence, renyiDivergence,
      hsum_zero alpha halpha_ne_zero halpha_ne_one,
      hsum_zero beta hbeta_ne_zero hbeta_ne_one]
    simp

/-- Finite Renyi divergence is nondecreasing in its order strictly above one. Only the first mass
function is normalized; neither normalization of the reference mass nor absolute continuity is
needed under the repository's totalized zero-power convention. -/
theorem renyi_divergence_monotone_of_one_lt {ι : Type*} [Fintype ι]
    (alpha beta : Real) (p q : ι -> Real)
    (horder : 1 < alpha ∧ alpha <= beta)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq_nonneg : forall i, 0 <= q i) :
    renyiDivergence alpha p q <= renyiDivergence beta p q := by
  classical
  rcases horder with ⟨halpha_pos, hab⟩
  rcases hab.eq_or_lt with rfl | hab_lt
  · rfl
  have hbeta_pos : 1 < beta := halpha_pos.trans hab_lt
  have halpha_ne_zero : alpha ≠ 0 := ne_of_gt (zero_lt_one.trans halpha_pos)
  have hbeta_ne_zero : beta ≠ 0 := ne_of_gt (zero_lt_one.trans hbeta_pos)
  have halpha_ne_one : alpha ≠ 1 := ne_of_gt halpha_pos
  have hbeta_ne_one : beta ≠ 1 := ne_of_gt hbeta_pos
  have hsum_as_mean (gamma : Real) (hgamma_ne_zero : gamma ≠ 0)
      (hgamma_ne_one : gamma ≠ 1) :
      (∑ i, (p i) ^ gamma * (q i) ^ (1 - gamma)) =
        ∑ i, p i * (p i / q i) ^ (gamma - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi_zero : p i = 0
    · simp [hpi_zero, Real.zero_rpow hgamma_ne_zero]
    by_cases hqi_zero : q i = 0
    · simp [hqi_zero, Real.zero_rpow (sub_ne_zero.mpr hgamma_ne_one),
        Real.zero_rpow (sub_ne_zero.mpr hgamma_ne_one.symm)]
    have hpi_pos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hpi_zero)
    calc
      (p i) ^ gamma * (q i) ^ (1 - gamma) =
          ((p i) ^ (1 : Real) * (p i) ^ (gamma - 1)) *
            ((q i) ^ (gamma - 1))⁻¹ := by
        rw [← Real.rpow_add hpi_pos, ← Real.rpow_neg (hq_nonneg i)]
        congr 2 <;> ring
      _ = p i * ((p i) ^ (gamma - 1) / (q i) ^ (gamma - 1)) := by
        rw [Real.rpow_one, div_eq_mul_inv]
        ring
      _ = p i * (p i / q i) ^ (gamma - 1) := by
        rw [Real.div_rpow (hp.1 i) (hq_nonneg i)]
  by_cases hoverlap : ∃ i, 0 < p i ∧ 0 < q i
  · have hsum_pos (gamma : Real) :
        0 < ∑ i, (p i) ^ gamma * (q i) ^ (1 - gamma) := by
      apply Finset.sum_pos' (fun i _ => mul_nonneg
        (Real.rpow_nonneg (hp.1 i) gamma)
        (Real.rpow_nonneg (hq_nonneg i) (1 - gamma)))
      rcases hoverlap with ⟨i, hpi, hqi⟩
      exact ⟨i, Finset.mem_univ i, mul_pos
        (Real.rpow_pos_of_pos hpi gamma)
        (Real.rpow_pos_of_pos hqi (1 - gamma))⟩
    have hratio_nonneg (i : ι) : 0 <= p i / q i :=
      div_nonneg (hp.1 i) (hq_nonneg i)
    have hratio_order : 1 <= (beta - 1) / (alpha - 1) :=
      (one_le_div (sub_pos.mpr halpha_pos)).2 (sub_le_sub_right hab_lt.le 1)
    have hpow_term (i : ι) :
        ((p i / q i) ^ (alpha - 1)) ^ ((beta - 1) / (alpha - 1)) =
          (p i / q i) ^ (beta - 1) := by
      rw [← Real.rpow_mul (hratio_nonneg i)]
      congr 1
      field_simp [sub_ne_zero.mpr halpha_ne_one]
    have hmean_raw := Real.rpow_arith_mean_le_arith_mean_rpow
      Finset.univ (fun i => p i) (fun i => (p i / q i) ^ (alpha - 1))
      (fun i _ => hp.1 i) (by simpa using hp.2)
      (fun i _ => Real.rpow_nonneg (hratio_nonneg i) (alpha - 1)) hratio_order
    have hmean :
        (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) ^
            ((beta - 1) / (alpha - 1)) <=
          ∑ i, (p i) ^ beta * (q i) ^ (1 - beta) := by
      rw [hsum_as_mean alpha halpha_ne_zero halpha_ne_one,
        hsum_as_mean beta hbeta_ne_zero hbeta_ne_one]
      simpa [hpow_term] using hmean_raw
    have hlog :
        ((beta - 1) / (alpha - 1)) *
            Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) <=
          Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) := by
      calc
        ((beta - 1) / (alpha - 1)) *
            Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
            Real.log ((∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) ^
              ((beta - 1) / (alpha - 1))) :=
          (Real.log_rpow (hsum_pos alpha) _).symm
        _ <= Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) :=
          Real.log_le_log
            (Real.rpow_pos_of_pos (hsum_pos alpha) ((beta - 1) / (alpha - 1))) hmean
    rw [renyiDivergence, renyiDivergence]
    calc
      (1 / (alpha - 1)) *
          Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
          Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) /
            (alpha - 1) := by ring
      _ <= Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) /
          (beta - 1) := by
        rw [le_div_iff₀ (sub_pos.mpr hbeta_pos)]
        calc
          (Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) /
              (alpha - 1)) * (beta - 1) =
              ((beta - 1) / (alpha - 1)) *
                Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) := by ring
          _ <= Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) := hlog
      _ = (1 / (beta - 1)) *
          Real.log (∑ i, (p i) ^ beta * (q i) ^ (1 - beta)) := by ring
  · have hsum_zero (gamma : Real) (hgamma_ne_zero : gamma ≠ 0)
        (hgamma_ne_one : gamma ≠ 1) :
        (∑ i, (p i) ^ gamma * (q i) ^ (1 - gamma)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases not_and_or.mp (not_exists.mp hoverlap i) with hpi | hqi
      · have hpi_zero : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp.1 i)
        simp [hpi_zero, Real.zero_rpow hgamma_ne_zero]
      · have hqi_zero : q i = 0 := le_antisymm (le_of_not_gt hqi) (hq_nonneg i)
        simp [hqi_zero, Real.zero_rpow (sub_ne_zero.mpr hgamma_ne_one.symm)]
    rw [renyiDivergence, renyiDivergence,
      hsum_zero alpha halpha_ne_zero halpha_ne_one,
      hsum_zero beta hbeta_ne_zero hbeta_ne_one]
    simp

/- Monotonicity is strict for two strictly positive probability vectors at orders two and three. -/
example :
    renyiDivergence 2
        (fun b : Bool => if b then (1 / 3 : Real) else 2 / 3)
        (fun b : Bool => if b then (2 / 3 : Real) else 1 / 3) <
      renyiDivergence 3
        (fun b : Bool => if b then (1 / 3 : Real) else 2 / 3)
        (fun b : Bool => if b then (2 / 3 : Real) else 1 / 3) := by
  have htwo :
      renyiDivergence 2
          (fun b : Bool => if b then (1 / 3 : Real) else 2 / 3)
          (fun b : Bool => if b then (2 / 3 : Real) else 1 / 3) =
        Real.log (3 / 2) := by
    norm_num [renyiDivergence, Fintype.sum_bool]
  have hthree :
      renyiDivergence 3
          (fun b : Bool => if b then (1 / 3 : Real) else 2 / 3)
          (fun b : Bool => if b then (2 / 3 : Real) else 1 / 3) =
        (1 / 2) * Real.log (11 / 4) := by
    norm_num [renyiDivergence, Fintype.sum_bool]
  rw [htwo, hthree]
  have hlog : Real.log ((3 / 2 : Real) ^ 2) < Real.log (11 / 4) :=
    (Real.log_lt_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  linarith

/- The order-one endpoint cannot be included: the point-mass-versus-uniform probability witness
has positive half-order divergence, while the totalized order-one value is zero. -/
example :
    ¬(renyiDivergence (1 / 2)
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun _ : Bool => (1 / 2 : Real)) <=
      renyiDivergence 1
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun _ : Bool => (1 / 2 : Real))) := by
  have hhalf :
      renyiDivergence (1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _ : Bool => (1 / 2 : Real)) = Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
      Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num
    ring
  have hone :
      renyiDivergence 1
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _ : Bool => (1 / 2 : Real)) = 0 := by
    norm_num [renyiDivergence]
  rw [hhalf, hone]
  exact not_le_of_gt (Real.log_pos (by norm_num))

/- Crossing order one is false without absolute continuity, even when both arguments are
probability vectors: the totalization drops the missing-support coordinate above order one. -/
example :
    ¬(renyiDivergence (1 / 2)
        (fun _ : Bool => (1 / 2 : Real))
        (fun b : Bool => if b then (1 : Real) else 0) <=
      renyiDivergence 2
        (fun _ : Bool => (1 / 2 : Real))
        (fun b : Bool => if b then (1 : Real) else 0)) := by
  have hhalf :
      renyiDivergence (1 / 2)
          (fun _ : Bool => (1 / 2 : Real))
          (fun b : Bool => if b then (1 : Real) else 0) = Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
      Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num
    ring
  have htwo :
      renyiDivergence 2
          (fun _ : Bool => (1 / 2 : Real))
          (fun b : Bool => if b then (1 : Real) else 0) = -2 * Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [show (1 / 4 : Real) = ((2 : Real) ^ 2)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  rw [hhalf, htwo]
  linarith [Real.log_pos (by norm_num : (1 : Real) < 2)]

/- Neither reflexivity nor simplification proves sub-unit order monotonicity. -/
example {ι : Type*} [Fintype ι]
    (alpha beta : Real) (p q : ι -> Real)
    (horder : 0 < alpha ∧ alpha <= beta ∧ beta < 1)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq_nonneg : forall i, 0 <= q i) :
    renyiDivergence alpha p q <= renyiDivergence beta p q := by
  fail_if_success rfl
  fail_if_success simp
  exact renyi_divergence_monotone_of_lt_one alpha beta p q horder hp hq_nonneg

/- Neither reflexivity nor simplification proves super-unit order monotonicity. -/
example {ι : Type*} [Fintype ι]
    (alpha beta : Real) (p q : ι -> Real)
    (horder : 1 < alpha ∧ alpha <= beta)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq_nonneg : forall i, 0 <= q i) :
    renyiDivergence alpha p q <= renyiDivergence beta p q := by
  fail_if_success rfl
  fail_if_success simp
  exact renyi_divergence_monotone_of_one_lt alpha beta p q horder hp hq_nonneg

#print axioms renyi_divergence_monotone_of_lt_one
#print axioms renyi_divergence_monotone_of_one_lt

end D5.S3.RenyiDivergence
