/- GID: D5/S3/Analytic/QGammaTuran/FunctionResult
   generality: G
   mirror-B: D5/B/S3/Analytic/QGammaTuran/FunctionResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/QGammaTuran/FunctionResult.claim; result=D5/S3/Analytic/QGammaTuran/FunctionResult.result; claim=D5/S3/Analytic/QGammaTuran/FunctionResult.claim
   digest: A convergent reciprocal q-gamma series with a strictly negative function Turanian. -/

/-
admission_basis: open-problem-resolution (Conjecture 1, function clause; Refuted).
Frozen D5 dependency identity table (declaration identities):
* F1: GID D5/S3/Analytic/QGammaTuran/Result.qprod;
  declaration D5.S3.Analytic.QGammaTuran.Result.qprod;
  DECLARATION statement_id sha256:102741937a30352c055770194f7c1c4f248ae8ecfb2e0e90b687277348fa17e6.
* F2: GID D5/S3/Analytic/QGammaTuran/Result.rqgamma;
  declaration D5.S3.Analytic.QGammaTuran.Result.rqgamma;
  DECLARATION statement_id sha256:ab476dd764739df0f7601665b6752e7088069909de5c7ee0b40b1fb362b7a7c1.
* F3: GID D5/S3/Analytic/ReciprocalGammaTuran/Defs.AdmissibleSeq;
  declaration D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq;
  DECLARATION statement_id sha256:abfc032d4781455ce9be9b5d79eeec0ec7d429144bd78d17dfed678546f63347.
* F4: GID D5/S3/Analytic/ReciprocalGammaTuran/Defs.admissible_one;
  declaration D5.S3.Analytic.ReciprocalGammaTuran.Defs.admissible_one;
  DECLARATION statement_id sha256:542b2ef036086b557abca79ec9fd79a7a609bad51893576abe9466237f76c069.
* F5: GID D5/S3/Factorization/JordanCototientRecordLimitInfinity.one_sub_prod_le_sum;
  declaration D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum;
  DECLARATION statement_id sha256:2ae9c4b59c9a8107bcc321a08d511c7f7b3dbfd7742469936401e2f244f3e6bd.
Per-declaration judgments:
Frozen_D5_dependencies references only the identity table above; none means
no frozen D5 dependency after expansion of same-delivery helpers. Consumers
are declarations in this module unless a mathematical conclusion is named.
* qprod_multipliable:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: qprod_le_one, qprod_lower, qprod_split, qprod_step;
  frozen_D5_dependencies: none.
* qprod_step:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds;
  frozen_D5_dependencies: F1.
* qprod_nonneg:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: hbounds, hsummable, qprod_pos;
  frozen_D5_dependencies: F1.
* qprod_ne_zero:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: qprod_pos;
  frozen_D5_dependencies: F1.
* qprod_pos:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: witness_negative;
  frozen_D5_dependencies: F1.
* qprod_le_one:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: hbounds, hsummable, qprod_bounds;
  frozen_D5_dependencies: F1.
* qprod_lower:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: qprod_bounds;
  frozen_D5_dependencies: F1, F5.
* qprod_split:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: qprod_bounds;
  frozen_D5_dependencies: F1.
* qprod_bounds:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: hbounds, numP3, numP6;
  frozen_D5_dependencies: F1, F5.
* rqgamma_eq:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: normalizedTerm;
  frozen_D5_dependencies: F1, F2.
* hsum:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: hbounds, hshift, negative_bounds, numH10, numH3, numH6, series_eq, series_product, witness_negative;
  frozen_D5_dependencies: F1.
* hsummable:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: hbounds, hshift, hsummable_any;
  frozen_D5_dependencies: F1.
* hshift:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds;
  frozen_D5_dependencies: F1.
* plower:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: hbounds, numH10, numH3, numH6;
  frozen_D5_dependencies: none.
* pupper:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: hbounds, numH10, numH3, numH6;
  frozen_D5_dependencies: none.
* hbounds:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: numH10, numH3, numH6;
  frozen_D5_dependencies: F1, F5.
* qseries:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: claim, result, series_eq, series_product, witness_negative;
  frozen_D5_dependencies: F2.
* radius:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: claim, witness_radius;
  frozen_D5_dependencies: F2.
* claim:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: result;
  frozen_D5_dependencies: F2, F3.
* normalizedTerm:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: series_eq, series_summable;
  frozen_D5_dependencies: F1, F2.
* series_eq:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: series_product;
  frozen_D5_dependencies: F1, F2.
* hsummable_any:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: series_summable;
  frozen_D5_dependencies: F1.
* series_summable:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: witness_radius;
  frozen_D5_dependencies: F1, F2.
* r:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6, numP3, numP6, q, qlt, qpos, qpower, result, witness_negative, witness_radius, y, ylt, ypos;
  frozen_D5_dependencies: none.
* q:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6, numP3, numP6, qlt, qpos, qpower, result, witness_negative, witness_radius, y, ylt, ypos;
  frozen_D5_dependencies: none.
* y:
  proof_shape: bind-only (definition);
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6, witness_negative, ylt, ypos;
  frozen_D5_dependencies: none.
* qpos:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6, numP3, numP6, result, witness_negative, witness_radius;
  frozen_D5_dependencies: none.
* qlt:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6, numP3, numP6, result, witness_negative, witness_radius;
  frozen_D5_dependencies: none.
* ypos:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6;
  frozen_D5_dependencies: none.
* ylt:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds, numH10, numH3, numH6;
  frozen_D5_dependencies: none.
* numH3:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds, witness_negative;
  frozen_D5_dependencies: F1, F5.
* numH6:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds;
  frozen_D5_dependencies: F1, F5.
* numH10:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds;
  frozen_D5_dependencies: F1, F5.
* numP3:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds;
  frozen_D5_dependencies: F1, F5.
* numP6:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: negative_bounds;
  frozen_D5_dependencies: F1, F5.
* qpower:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: witness_negative;
  frozen_D5_dependencies: none.
* series_product:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: witness_negative;
  frozen_D5_dependencies: F1, F2.
* negative_bounds:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: witness_negative;
  frozen_D5_dependencies: F1, F5.
* witness_negative:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: result;
  frozen_D5_dependencies: F1, F2, F5.
* witness_radius:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: result;
  frozen_D5_dependencies: F1, F2.
* result:
  proof_shape: bind-only;
  escape_witness: none;
  consumers: settlement of the function clause;
  frozen_D5_dependencies: F1, F2, F3, F4, F5.
-/

import D5.S3.Analytic.QGammaTuran.Result
noncomputable section
open scoped BigOperators
open Filter
open D5.S3.Analytic.QGammaTuran.Result
open D5.S3.Analytic.ReciprocalGammaTuran.Defs
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Analytic.QGammaTuran.FunctionResult
private lemma qprod_multipliable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
    Multipliable (fun j : ℕ => 1 - a * q ^ j) := by
  simpa only [sub_eq_add_neg, neg_mul] using
    Real.multipliable_one_add_of_summable
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (-a))

private lemma qprod_step {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
    qprod q a = (1 - a) * qprod q (a*q) := by
  unfold qprod
  have htail : Multipliable (fun j : ℕ => 1 - a * q^(j+1)) := by
    convert qprod_multipliable hq0 hq1 (a*q) using 1
    ext j
    rw [pow_succ]
    ring
  rw [tprod_eq_zero_mul' htail]
  simp only [pow_zero, mul_one]
  congr 1
  apply tprod_congr
  intro j
  rw [pow_succ]
  ring

private lemma qprod_nonneg {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ qprod q a := by
  unfold qprod
  exact tprod_nonneg fun i => sub_nonneg.mpr
    (by nlinarith [pow_le_one₀ hq0 hq1.le (n := i)] : a*q^i ≤ 1)

private lemma qprod_ne_zero {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) : qprod q a ≠ 0 := by
  unfold qprod
  have hs : Summable (fun j : ℕ => ‖- (a * q^j)‖) := by
    simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha0 (pow_nonneg hq0 _))]
      using (summable_geometric_of_lt_one hq0 hq1).mul_left a
  have hn (j : ℕ) : 1 + -(a * q^j) ≠ 0 := by
    have h : a*q^j < 1 := by nlinarith [pow_le_one₀ hq0 hq1.le (n := j)]
    linarith
  simpa only [sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable hn hs

private lemma qprod_pos {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < qprod q a :=
  lt_of_le_of_ne (qprod_nonneg hq0 hq1 ha0 ha1.le) (qprod_ne_zero hq0 hq1 ha0 ha1).symm

private lemma qprod_le_one {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : qprod q a ≤ 1 := by
  apply (qprod_multipliable hq0 hq1 a).tprod_le_of_prod_range_le
  intro n
  exact Finset.prod_le_one₀
    (fun i _ => sub_nonneg.mpr (by nlinarith [pow_le_one₀ hq0 hq1.le (n := i)]))
    (fun i _ => sub_le_self _ (mul_nonneg ha0 (pow_nonneg hq0 _)))

private lemma qprod_lower {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 1 - a / (1-q) ≤ qprod q a := by
  have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left a
  have hp := (qprod_multipliable hq0 hq1 a).hasProd.tendsto_prod_nat
  have hsum := hs.hasSum.tendsto_sum_nat
  have hfinite (n : ℕ) : 1 - ∑ i ∈ Finset.range n, a*q^i ≤ ∏ i ∈ Finset.range n, (1-a*q^i) := by
    have h := D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum
      (Finset.range n) (fun i => a*q^i)
      (fun i _ => mul_nonneg ha0 (pow_nonneg hq0 i))
      (fun i _ => by nlinarith [pow_le_one₀ hq0 hq1.le (n := i)])
    linarith

  have h := le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub hsum) hp hfinite
  simpa only [qprod, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv] using h

private lemma qprod_split {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) (n : ℕ) :
    qprod q a = (∏ j ∈ Finset.range n, (1-a*q^j)) * qprod q (a*q^n) := by
  have ht : Multipliable (fun j : ℕ => 1-a*q^(j+n)) := by
    convert qprod_multipliable hq0 hq1 (a*q^n) using 1
    ext j
    rw [pow_add]
    ring
  rw [qprod, ← ht.prod_mul_tprod_nat_mul']
  congr 1
  apply tprod_congr
  intro j
  simp only [pow_add]
  ring

private lemma qprod_bounds {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1-a*q^j)) * (1-a*q^n/(1-q)) ≤ qprod q a ∧
    qprod q a ≤ ∏ j ∈ Finset.range n, (1-a*q^j) := by
  have ht0 := mul_nonneg ha0 (pow_nonneg hq0 n)
  have ht1 : a*q^n ≤ 1 := by nlinarith [pow_le_one₀ hq0 hq1.le (n := n)]
  have hp0 : 0 ≤ ∏ j ∈ Finset.range n, (1-a*q^j) :=
    Finset.prod_nonneg fun j _ => sub_nonneg.mpr
      (by nlinarith [pow_le_one₀ hq0 hq1.le (n := j)])
  rw [qprod_split hq0 hq1 a n]
  exact ⟨mul_le_mul_of_nonneg_left (qprod_lower hq0 hq1 ht0 ht1) hp0,
    (mul_le_mul_of_nonneg_left (qprod_le_one hq0 hq1 ht0 ht1) hp0).trans_eq (mul_one _)⟩

private lemma rqgamma_eq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    rqgamma q x = qprod q (q^x) / (qprod q q * (1-q)^(1-x)) := by
  unfold rqgamma
  have hn : (∏' j : ℕ, (1-q^(x+j))) = qprod q (q^x) := by
    unfold qprod
    apply tprod_congr
    intro j
    rw [Real.rpow_add_natCast (ne_of_gt hq)]
  have hd : (∏' j : ℕ, (1-q^((j:ℝ)+1))) = qprod q q := by
    unfold qprod
    apply tprod_congr
    intro j
    rw [Real.rpow_add_one (ne_of_gt hq), Real.rpow_natCast]
    ring
  rw [hn, hd]

private def hsum (q a y : ℝ) : ℝ := ∑' n : ℕ, y^n * qprod q (a*q^n)
private lemma hsummable {q a y : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Summable (fun n : ℕ => y^n * qprod q (a*q^n)) := by
  apply (summable_geometric_of_lt_one hy0 hy1).of_norm_bounded
  intro n
  have ha : a*q^n ≤ 1 := by nlinarith [pow_le_one₀ hq0 hq1.le (n := n)]
  have hp0 := qprod_nonneg hq0 hq1 (mul_nonneg ha0 (pow_nonneg hq0 n)) ha
  have hp1 := qprod_le_one hq0 hq1 (mul_nonneg ha0 (pow_nonneg hq0 n)) ha
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hy0 n) hp0)]
  exact mul_le_of_le_one_right (pow_nonneg hy0 n) hp1
private lemma hshift {q a y : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a*q ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    hsum q a y = qprod q a + y * hsum q (a*q) y := by
  have ht := hsummable hq0 hq1 (mul_nonneg ha0 hq0) ha1 hy0 hy1
  have htail : Summable (fun n : ℕ => y^(n+1)*qprod q (a*q^(n+1))) := by
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using ht.mul_left y
  have hs : Summable (fun n : ℕ => y^n*qprod q (a*q^n)) :=
    (summable_nat_add_iff 1).1 htail
  rw [hsum, hs.tsum_eq_zero_add]
  simp only [pow_zero, mul_one, one_mul]
  congr 1
  rw [hsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [pow_succ]
  ring
private def plower (q a : ℝ) (N : ℕ) : ℝ :=
  (∏ j ∈ Finset.range N, (1-a*q^j)) * (1-a*q^N/(1-q))
private def pupper (q a : ℝ) (N : ℕ) : ℝ := ∏ j ∈ Finset.range N, (1-a*q^j)
private lemma hbounds {q a y : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) (K N : ℕ) :
    (∑ n ∈ Finset.range K, y^n * plower q (a*q^n) N) ≤ hsum q a y ∧
    hsum q a y ≤ (∑ n ∈ Finset.range K, y^n * pupper q (a*q^n) N) + y^K/(1-y) := by
  have hs := hsummable hq0 hq1 ha0 ha1 hy0 hy1
  have hp (n : ℕ) := qprod_bounds hq0 hq1
    (mul_nonneg ha0 (pow_nonneg hq0 n))
    (by nlinarith [pow_le_one₀ hq0 hq1.le (n := n)] : a*q^n ≤ 1) N
  constructor
  · refine le_trans (Finset.sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (hp n).1 (pow_nonneg hy0 n)) ?_
    exact hs.sum_le_tsum (Finset.range K) (fun n _ =>
      mul_nonneg (pow_nonneg hy0 n) (qprod_nonneg hq0 hq1
        (mul_nonneg ha0 (pow_nonneg hq0 n))
        (by nlinarith [pow_le_one₀ hq0 hq1.le (n := n)])))
  · have htail : (∑' n : ℕ, y^(n+K)*qprod q (a*q^(n+K))) ≤ y^K/(1-y) := by
      have hg := (summable_geometric_of_lt_one hy0 hy1).mul_right (y^K)
      have hm (n : ℕ) : y^(n+K)*qprod q (a*q^(n+K)) ≤ y^n*y^K := by
        rw [← pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hy0 _) (qprod_le_one hq0 hq1
          (mul_nonneg ha0 (pow_nonneg hq0 _))
          (by nlinarith [pow_le_one₀ hq0 hq1.le (n := n+K)]))
      have hh := Summable.tsum_le_tsum hm ((summable_nat_add_iff K).2 hs) hg
      rw [tsum_mul_right, tsum_geometric_of_lt_one hy0 hy1] at hh
      simpa only [div_eq_mul_inv, mul_comm] using hh
    rw [hsum, ← hs.sum_add_tsum_nat_add K]
    exact add_le_add (Finset.sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (hp n).2 (pow_nonneg hy0 n)) htail
open D5.S3.Analytic.ReciprocalGammaTuran.Defs
def qseries (q μ x : ℝ) (g : ℕ → ℝ) : ℝ := ∑' n : ℕ, g n*x^n*rqgamma q (μ+n)
def radius (q μ : ℝ) (g : ℕ → ℝ) : ENNReal :=
  (FormalMultilinearSeries.ofScalars ℝ (fun n => g n * rqgamma q (μ+n))).radius
def claim : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ g : ℕ → ℝ, AdmissibleSeq g →
  ∀ μ α β : ℝ, 0 < α → 0 < β → max (-β) (-1) ≤ μ →
  ∀ x : ℝ, 0 < x → ENNReal.ofReal x < radius q μ g →
  0 < qseries q (μ+α) x g * qseries q (μ+β) x g -
    qseries q μ x g * qseries q (μ+α+β) x g
private lemma normalizedTerm {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (s x : ℝ) (n : ℕ) :
    x^n*rqgamma q (s+n) =
      ((x*(1-q))^n*qprod q (q^s*q^n))/(qprod q q*(1-q)^(1-s)) := by
  have hb : 0 < 1-q := sub_pos.mpr hq1
  have hp : (1-q)^(1-s) = (1-q)^(1-(s+n)) * (1-q)^n := by
    rw [← Real.rpow_add_natCast (ne_of_gt hb)]
    congr 1
    ring
  rw [rqgamma_eq hq0, Real.rpow_add_natCast (ne_of_gt hq0), hp, mul_pow]
  field_simp
private lemma series_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (s x : ℝ) :
    qseries q s x (fun _ => 1) =
      hsum q (q^s) (x*(1-q))/(qprod q q*(1-q)^(1-s)) := by
  unfold qseries hsum
  simp_rw [one_mul, normalizedTerm hq0 hq1]
  rw [tsum_div_const]
private lemma hsummable_any {q a y : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a*q ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Summable (fun n : ℕ => y^n*qprod q (a*q^n)) := by
  apply (summable_nat_add_iff 1).1
  convert (hsummable hq0 hq1 (mul_nonneg ha0 hq0) ha1 hy0 hy1).mul_left y using 1
  ext n
  simp only [pow_succ]
  ring
private lemma series_summable {q x s : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : q^s*q ≤ 1) (hx0 : 0 ≤ x*(1-q)) (hx1 : x*(1-q) < 1) :
    Summable (fun n : ℕ => (1:ℝ)*x^n*rqgamma q (s+n)) := by
  simpa only [one_mul, normalizedTerm hq0 hq1] using
    (hsummable_any hq0.le hq1 (Real.rpow_pos_of_pos hq0 s).le ha hx0 hx1).div_const
      (qprod q q*(1-q)^(1-s))
private def r : ℝ := 93/100
private def q : ℝ := r^10
private def y : ℝ := r*(1-q)
private lemma qpos : 0 < q := by norm_num [q,r]
private lemma qlt : q < 1 := by norm_num [q,r]
private lemma ypos : 0 ≤ y := by norm_num [y,q,r]
private lemma ylt : y < 1 := by norm_num [y,q,r]
private lemma numH3 : (621758/1000000:ℝ) ≤ hsum q (r^3) y ∧ hsum q (r^3) y ≤ 627611/1000000 := by
  have h := hbounds qpos.le qlt (by norm_num [r] : 0 ≤ r^3)
    (by norm_num [r]) ypos ylt 10 6
  constructor
  · refine le_trans ?_ h.1
    norm_num [r,q,y,plower,Finset.sum_range_succ,Finset.prod_range_succ]
  · refine le_trans h.2 ?_
    norm_num [r,q,y,pupper,Finset.sum_range_succ,Finset.prod_range_succ]
private lemma numH6 : (779999/1000000:ℝ) ≤ hsum q (r^6) y ∧ hsum q (r^6) y ≤ 786930/1000000 := by
  have h := hbounds qpos.le qlt (by norm_num [r] : 0 ≤ r^6)
    (by norm_num [r]) ypos ylt 10 6
  constructor
  · refine le_trans ?_ h.1
    norm_num [r,q,y,plower,Finset.sum_range_succ,Finset.prod_range_succ]
  · refine le_trans h.2 ?_
    norm_num [r,q,y,pupper,Finset.sum_range_succ,Finset.prod_range_succ]
private lemma numH10 : (986336/1000000:ℝ) ≤ hsum q (r^10) y ∧ hsum q (r^10) y ≤ 993832/1000000 := by
  have h := hbounds qpos.le qlt (by norm_num [r] : 0 ≤ r^10)
    (by norm_num [r]) ypos ylt 10 6
  constructor
  · refine le_trans ?_ h.1
    norm_num [r,q,y,plower,Finset.sum_range_succ,Finset.prod_range_succ]
  · refine le_trans h.2 ?_
    norm_num [r,q,y,pupper,Finset.sum_range_succ,Finset.prod_range_succ]
private lemma numP3 : (80786/1000000:ℝ) ≤ qprod q (r^3) ∧ qprod q (r^3) ≤ 82438/1000000 := by
  have h := qprod_bounds qpos.le qlt (by norm_num [r] : 0 ≤ r^3)
    (by norm_num [r]) 6
  constructor
  · refine le_trans ?_ h.1
    norm_num [r,q,Finset.prod_range_succ]
  · refine le_trans h.2 ?_
    norm_num [r,q,Finset.prod_range_succ]
private lemma numP6 : (177796/1000000:ℝ) ≤ qprod q (r^6) ∧ qprod q (r^6) ≤ 180709/1000000 := by
  have h := qprod_bounds qpos.le qlt (by norm_num [r] : 0 ≤ r^6)
    (by norm_num [r]) 6
  constructor
  · refine le_trans ?_ h.1
    norm_num [r,q,Finset.prod_range_succ]
  · refine le_trans h.2 ?_
    norm_num [r,q,Finset.prod_range_succ]
private lemma qpower (n : ℕ) : q^((n:ℝ)/10) = r^n := by
  rw [q, ← Real.rpow_natCast_mul (by norm_num [r] : 0 ≤ r)]
  convert Real.rpow_natCast r n using 1
  congr 1
  ring
private lemma series_product {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (s t x : ℝ) :
    qseries q s x (fun _ => 1)*qseries q t x (fun _ => 1) =
    (hsum q (q^s) (x*(1-q))*hsum q (q^t) (x*(1-q)))/
      ((qprod q q)^2*(1-q)^(2-s-t)) := by
  rw [series_eq hq0 hq1, series_eq hq0 hq1, div_mul_div_comm]
  congr 1
  calc
    _ = (qprod q q)^2*((1-q)^(1-s)*(1-q)^(1-t)) := by ring
    _ = _ := by rw [← Real.rpow_add (sub_pos.mpr hq1)]; congr 2; ring
private lemma negative_bounds :
    (0:ℝ) ≤ hsum q ((r^4)⁻¹) y ∧ hsum q ((r^4)⁻¹) y ≤ 317763/1000000 ∧
    (243809/1000000:ℝ) ≤ hsum q ((r^7)⁻¹) y ∧
    (0:ℝ) ≤ hsum q 1 y ∧ hsum q 1 y ≤ 476937/1000000 := by
  have hr4 : (r^4)⁻¹*q = r^6 := by norm_num [q,r]
  have hr7 : (r^7)⁻¹*q = r^3 := by norm_num [q,r]
  have h4 := hshift qpos.le qlt (by norm_num [r] : 0 ≤ (r^4)⁻¹)
    (by norm_num [r,q]) ypos ylt
  have h7 := hshift qpos.le qlt (by norm_num [r] : 0 ≤ (r^7)⁻¹)
    (by norm_num [r,q]) ypos ylt
  have h0 := hshift qpos.le qlt (a := 1) (by norm_num)
    (by simpa using qlt.le) ypos ylt
  rw [hr4, qprod_step qpos.le qlt, hr4] at h4
  rw [hr7, qprod_step qpos.le qlt, hr7] at h7
  have hz : qprod q 1 = 0 := by rw [qprod_step qpos.le qlt]; ring
  simp only [one_mul, hz, zero_add] at h0
  have hp3 := numP3
  have hp6 := numP6
  have hh3 := numH3
  have hh6 := numH6
  have hh10 : (986336/1000000:ℝ) ≤ hsum q q y ∧ hsum q q y ≤ 993832/1000000 := numH10
  have h4n : 1-(r^4)⁻¹ ≤ 0 := by norm_num [r]
  have h7n : 1-(r^7)⁻¹ ≤ 0 := by norm_num [r]
  have h4l := mul_le_mul_of_nonpos_left hp6.2 h4n
  have h4u := mul_le_mul_of_nonpos_left hp6.1 h4n
  have h7l := mul_le_mul_of_nonpos_left hp3.2 h7n
  have h6l := mul_le_mul_of_nonneg_left hh6.1 ypos
  have h6u := mul_le_mul_of_nonneg_left hh6.2 ypos
  have h3l := mul_le_mul_of_nonneg_left hh3.1 ypos
  have h10l := mul_le_mul_of_nonneg_left hh10.1 ypos
  have h10u := mul_le_mul_of_nonneg_left hh10.2 ypos
  norm_num [r,q,y] at h4l h4u h7l h6l h6u h3l h10l h10u h4 h7 h0 ⊢
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
private lemma witness_negative :
    qseries q (-2/5) r (fun _ => 1)*qseries q 0 r (fun _ => 1) -
    qseries q (-7/10) r (fun _ => 1)*qseries q (3/10) r (fun _ => 1) < 0 := by
  have h4 : q^(-2/5:ℝ) = (r^4)⁻¹ := by
    rw [show (-2/5:ℝ) = -(4/10) by norm_num, Real.rpow_neg qpos.le]
    exact congrArg Inv.inv (qpower 4)
  have h7 : q^(-7/10:ℝ) = (r^7)⁻¹ := by
    rw [show (-7/10:ℝ) = -(7/10) by ring, Real.rpow_neg qpos.le]
    exact congrArg Inv.inv (qpower 7)
  have h3 : q^(3/10:ℝ) = r^3 := qpower 3
  rw [series_product qpos qlt, series_product qpos qlt]
  norm_num only [neg_div] at h4 h7
  norm_num only [Real.rpow_zero]
  rw [h4,h7,h3]
  change hsum q ((r^4)⁻¹) y * hsum q 1 y / ((qprod q q)^2*(1-q)^(12/5:ℝ)) -
    hsum q ((r^7)⁻¹) y * hsum q (r^3) y / ((qprod q q)^2*(1-q)^(12/5:ℝ)) < 0
  have hb := negative_bounds
  have hd := numH3
  have hA := mul_le_mul hb.2.1 hb.2.2.2.2 hb.2.2.2.1 (by norm_num)
  have hB := mul_le_mul hb.2.2.1 hd.1 (by norm_num) (by linarith [hb.2.2.1])
  have hden : 0 < (qprod q q)^2*(1-q)^(12/5:ℝ) :=
    mul_pos (sq_pos_of_pos (qprod_pos qpos.le qlt qpos.le qlt))
      (Real.rpow_pos_of_pos (sub_pos.mpr qlt) _)
  rw [← sub_div, div_neg_iff]
  exact Or.inr ⟨by linarith, hden⟩
private lemma witness_radius : ENNReal.ofReal r < radius q (-7/10) (fun _ => 1) := by
  have hs : Summable (fun n : ℕ => (1:ℝ)*(3/2)^n*rqgamma q (-7/10+n)) := by
    apply series_summable qpos qlt ?_ (by norm_num [q,r]) (by norm_num [q,r])
    rw [← Real.rpow_add_one (ne_of_gt qpos)]
    exact Real.rpow_le_one qpos.le qlt.le (by norm_num)
  have hrad : ((3/2 : NNReal) : ENNReal) ≤ radius q (-7/10) (fun _ => 1) := by
    apply FormalMultilinearSeries.le_radius_of_summable
    simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2),
      one_mul, NNReal.coe_div, NNReal.coe_ofNat, mul_comm] using hs.norm
  exact lt_of_lt_of_le
    ((ENNReal.ofReal_lt_coe_iff (by norm_num [r] : 0 ≤ r)).2 (by norm_num [r])) hrad
theorem result : ¬ claim := by
  intro hclaim
  have h := hclaim q qpos qlt (fun _ => 1) admissible_one
    (-7/10) (3/10) (7/10) (by norm_num) (by norm_num) (by norm_num)
    r (by norm_num [r]) witness_radius
  norm_num only at h
  exact (not_lt_of_ge h.le) (by simpa only [neg_div] using witness_negative)
end D5.S3.Analytic.QGammaTuran.FunctionResult
