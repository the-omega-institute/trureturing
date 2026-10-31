/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix, D5/S3/Analytic/OriginalHalfBinomialPeriod]
   utility: none
   digest: The original positive-frequency Gaussian on complex square-summable sequences. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
import D5.S3.Analytic.OriginalHalfBinomialPeriod
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Basic

/-! The literal signed Gaussian acts on one complex square-summable carrier. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent

open OriginalGaussianMatrix
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

abbrev H := lp (fun _ : ℕ => ℂ) 2

private lemma weight_le_one (n : ℕ) : centralWeight n ≤ 1 := by
  rw [centralWeight, div_le_one (by positivity)]
  exact_mod_cast Nat.centralBinom_le_four_pow n

private def basis (n : ℕ) : H := lp.single 2 n 1

private def rankOne (n m : ℕ) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 m).smulRight (basis n)

private lemma rankOne_norm_le (n m : ℕ) : ‖rankOne n m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x m • basis n‖ ≤ 1 * ‖x‖
  rw [norm_smul]
  simpa [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x m

private lemma entry_bound (z : ℂ) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    ‖matrixEntry z s t‖ ≤ ‖z‖ ^ (s + t) := by
  rw [matrixEntry_norm z s t hs ht]
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hsqrt := Real.sq_sqrt hs0
  have htsqrt := Real.sq_sqrt ht0
  have hp : 0 ≤ Real.sqrt (s : ℝ) * Real.sqrt (t : ℝ) := by positivity
  have hst : Real.sqrt (s : ℝ) * Real.sqrt (t : ℝ) ≤ (s : ℝ) + t := by
    nlinarith [sq_nonneg (Real.sqrt (s : ℝ) - Real.sqrt (t : ℝ))]
  have hw : centralWeight s * centralWeight t ≤ 1 := by
    simpa using mul_le_mul (weight_le_one s) (weight_le_one t)
      (centralWeight_nonneg t) zero_le_one
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < s + t)).mpr
  calc
    _ = (Real.sqrt (s : ℝ) * Real.sqrt (t : ℝ)) *
        (centralWeight s * centralWeight t) * ‖z‖ ^ (s + t) := by ring
    _ ≤ ((s : ℝ) + t) * 1 * ‖z‖ ^ (s + t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hst hw (mul_nonneg (centralWeight_nonneg s)
          (centralWeight_nonneg t)) (by positivity)) (by positivity)
    _ = _ := by ring

private def term (z : ℂ) (p : ℕ × ℕ) : H →L[ℂ] H :=
  matrixEntry z (p.1 + 1) (p.2 + 1) • rankOne p.1 p.2

private lemma term_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖term z p‖) := by
  have hg : Summable (fun n : ℕ => ‖z‖ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => ?_) (hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity))
  rw [term, norm_smul]
  calc
    _ ≤ ‖matrixEntry z (p.1 + 1) (p.2 + 1)‖ * 1 := by
      gcongr; exact rankOne_norm_le _ _
    _ ≤ ‖z‖ ^ ((p.1 + 1) + (p.2 + 1)) := by
      simpa using entry_bound z (p.1 + 1) (p.2 + 1) (by omega) (by omega)
    _ = _ := pow_add _ _ _

/-- Literal signed original entries on the single complex square-summable carrier. -/
def operator (z : ℂ) : H →L[ℂ] H := ∑' p : ℕ × ℕ, term z p

/-- The square cutoff uses exactly the positive frequencies 1,...,N. -/
def sectionOp (N : ℕ) (z : ℂ) : H →L[ℂ] H :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, term z (n, m)

private lemma sectionOp_tendsto {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N => sectionOp N z) atTop (𝓝 (operator z)) := by
  have h := (term_summable hz).of_norm.hasSum
  have hp := tendsto_finset_range.prodMk tendsto_finset_range
  rw [prod_atTop_atTop_eq] at hp
  have ht := tendsto_finsetProd_atTop.comp hp
  simpa [sectionOp, operator, Function.comp_def, Finset.sum_product] using h.comp ht

private lemma term_apply (z : ℂ) (i j n : ℕ) (x : H) :
    term z (i, j) x n =
      if i = n then matrixEntry z (n + 1) (j + 1) * x j else 0 := by
  change matrixEntry z (i + 1) (j + 1) *
    (x j * lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ) n) = _
  rw [lp.single_apply]
  by_cases hi : i = n
  · subst i; simp
  · simp [hi]

private lemma operator_apply {z : ℂ} (hz : ‖z‖ < 1) (x : H) (n : ℕ) :
    operator z x n = ∑' m : ℕ, matrixEntry z (n + 1) (m + 1) * x m := by
  let ev : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp
      (ContinuousLinearMap.apply ℂ H x)
  have h := ev.hasSum (term_summable hz).of_norm.hasSum
  have he (p : ℕ × ℕ) : ev (term z p) =
      if p.1 = n then matrixEntry z (n + 1) (p.2 + 1) * x p.2 else 0 := by
    exact term_apply z p.1 p.2 n x
  simp_rw [he] at h
  have hp := h.summable.tsum_prod
  have heq : (∑' b : ℕ, ∑' c : ℕ,
      if b = n then matrixEntry z (n + 1) (c + 1) * x c else 0) =
      ∑' c : ℕ, matrixEntry z (n + 1) (c + 1) * x c := by
    calc
      _ = ∑' b : ℕ, if b = n then
          (∑' c : ℕ, matrixEntry z (n + 1) (c + 1) * x c) else 0 := by
        apply tsum_congr
        intro b
        split_ifs <;> simp_all
      _ = _ := by simp
  exact (show operator z x n = _ from h.tsum_eq.symm).trans (hp.trans heq)

private def zeroExtend (N : ℕ) (x : EuclideanSpace ℂ (Fin N)) : H :=
  ∑ n ∈ Finset.range N, lp.single 2 n (if hn : n < N then x ⟨n, hn⟩ else 0)

private lemma zeroExtend_apply (N : ℕ) (x : EuclideanSpace ℂ (Fin N)) (n : ℕ) :
    zeroExtend N x n = if hn : n < N then x ⟨n, hn⟩ else 0 := by
  classical
  simp only [zeroExtend, lp.coeFn_sum, lp.coeFn_single]
  by_cases hn : n < N <;> simp [Finset.mem_range, hn]

private lemma zeroExtend_norm (N : ℕ) (x : EuclideanSpace ℂ (Fin N)) :
    ‖zeroExtend N x‖ = ‖x‖ := by
  have h := lp.norm_sum_single (p := 2) (by norm_num)
    (fun n : ℕ => if hn : n < N then x ⟨n, hn⟩ else 0) (Finset.range N)
  have h' : ‖zeroExtend N x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [zeroExtend, Real.rpow_two, Finset.sum_range, EuclideanSpace.norm_sq_eq]
      using h
  nlinarith [norm_nonneg (zeroExtend N x), norm_nonneg x]

private def inclusion (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] H :=
  ({ toFun := zeroExtend N
     map_add' := by
       intro x y
       ext n
       change zeroExtend N (x + y) n = zeroExtend N x n + zeroExtend N y n
       simp only [zeroExtend_apply]
       split_ifs <;> simp
     map_smul' := by
       intro c x
       ext n
       change zeroExtend N (c • x) n = c * zeroExtend N x n
       simp only [zeroExtend_apply]
       split_ifs <;> simp } : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] H).mkContinuous 1
    (by intro x; simpa using (zeroExtend_norm N x).le)

private def restriction (N : ℕ) : H →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  ({ toFun := fun x => WithLp.toLp 2 (fun i : Fin N => x i)
     map_add' := by intro x y; rfl
     map_smul' := by intro c x; rfl } : H →ₗ[ℂ] EuclideanSpace ℂ (Fin N)).mkContinuous 1
    (by
      intro x
      simp only [one_mul]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ i : Fin N, ‖x i‖ ^ 2) ≤ ‖x‖ ^ 2
      have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) x (Finset.range N)
      simpa [Real.rpow_two, Finset.sum_range] using h)

private lemma sectionOp_factorization (N : ℕ) (z : ℂ) :
    sectionOp N z = (inclusion N).comp
      ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (finiteSection N z)).comp
        (restriction N)) := by
  classical
  ext x n
  change (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, term z (i, j)) x n =
    zeroExtend N (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (finiteSection N z)
      (WithLp.toLp 2 (fun i : Fin N => x i))) n
  rw [zeroExtend_apply]
  simp only [ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp_rw [term_apply]
  by_cases hn : n < N
  · simp only [dif_pos hn]
    rw [Finset.sum_eq_single n]
    · simp only [ite_true]
      change (∑ j ∈ Finset.range N, matrixEntry z (n + 1) (j + 1) * x j) =
        ∑ j : Fin N, matrixEntry z (n + 1) (j.val + 1) * x j.val
      exact Finset.sum_range _
    · intro i hi hin
      simp [hin]
    · simp [Finset.mem_range, hn]
  · simp only [dif_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := by intro h; subst i; exact hn (Finset.mem_range.mp hi)
    simp [hin]

private lemma inclusion_norm_le (N : ℕ) : ‖inclusion N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa [inclusion] using (zeroExtend_norm N x).le

private lemma restriction_norm_le (N : ℕ) : ‖restriction N‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le _ zero_le_one

private lemma sectionOp_norm_le (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖sectionOp N z‖ ≤ ‖z‖ ^ 2 := by
  rw [sectionOp_factorization]
  calc
    _ ≤ ‖inclusion N‖ *
        (‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (finiteSection N z)‖ * ‖restriction N‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖z‖ ^ 2 * 1) := by
      gcongr
      · exact inclusion_norm_le N
      · exact finiteSection_opNorm_le N z hz
      · exact restriction_norm_le N
    _ = _ := by ring

private lemma operator_norm_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖operator z‖ ≤ ‖z‖ ^ 2 := by
  exact le_of_tendsto ((sectionOp_tendsto hz).norm)
    (Filter.Eventually.of_forall (fun N => sectionOp_norm_le N hz))

private lemma half_shifted_convolution (s n : ℕ) (hs : 0 < s) :
    halfBinomial (s + n) = (s : ℂ) * halfBinomial s *
      ∑ t ∈ Finset.range (n + 1),
        halfBinomial t * halfBinomial (n - t) / ((s : ℂ) + t) := by
  let h : PowerSeries ℂ := PowerSeries.mk halfBinomial
  let c : PowerSeries ℂ := PowerSeries.mk (fun n => Ring.choose (1 / 2 : ℂ) n)
  let K : PowerSeries ℂ := PowerSeries.mk (fun n => halfBinomial (s + n))
  let d : PowerSeries ℂ := PowerSeries.mk
    (fun n => (s : ℂ) * halfBinomial s * halfBinomial n / ((s : ℂ) + n))
  have hc : c * h = 1 := by
    ext k
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      h, c, PowerSeries.coeff_mk]
    have hz : Ring.choose (0 : ℂ) k = if k = 0 then 1 else 0 := by
      have hz := Ring.choose_natCast (R := ℂ) 0 k
      cases k <;> simpa using hz
    rw [← hz, show (0 : ℂ) = 1 / 2 + (-1 / 2) by ring,
      Ring.add_choose_eq k (Commute.all _ _)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [halfBinomial_choose]
  have hKc : K * c = d := by
    ext k
    simp only [K, c, d, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    change (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      halfBinomial (s + p.1) * Ring.choose (1 / 2 : ℂ) p.2) = _
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact halfBinomial_positive_convolution s k hs
  have hK : K = d * h := by rw [← hKc, mul_assoc, hc, mul_one]
  have he := congrArg (PowerSeries.coeff n) hK
  simp only [K, d, h, PowerSeries.coeff_mk, PowerSeries.coeff_mul] at he
  change halfBinomial (s + n) =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((s : ℂ) * halfBinomial s * halfBinomial p.1 / ((s : ℂ) + p.1)) *
        halfBinomial p.2 at he
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

private lemma shifted_convolution (s n : ℕ) (hs : 0 < s) :
    (s : ℝ) * centralWeight s *
      (∑ t ∈ Finset.range (n + 1),
        centralWeight t * centralWeight (n - t) / ((s : ℝ) + t)) =
      centralWeight (s + n) := by
  have h := half_shifted_convolution s n hs
  have hp : (-1 : ℂ) ^ (s + n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht (t : ℕ) (ht : t ∈ Finset.range (n + 1)) :
      halfBinomial t * halfBinomial (n - t) =
        (-1 : ℂ) ^ n * (centralWeight t * centralWeight (n - t) : ℝ) := by
    rw [halfBinomial_eq_signed_centralWeight, halfBinomial_eq_signed_centralWeight]
    push_cast
    rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_of_le (by simpa using ht)]
  have hsum :
      (∑ t ∈ Finset.range (n + 1),
        halfBinomial t * halfBinomial (n - t) / ((s : ℂ) + t)) =
      (-1 : ℂ) ^ n *
        ((∑ t ∈ Finset.range (n + 1),
          centralWeight t * centralWeight (n - t) / ((s : ℝ) + t) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t hmem
    rw [ht t hmem]
    push_cast
    ring
  rw [halfBinomial_eq_signed_centralWeight, halfBinomial_eq_signed_centralWeight, hsum] at h
  have hc : (-1 : ℂ) ^ (s + n) * (centralWeight (s + n) : ℂ) =
      (-1 : ℂ) ^ (s + n) *
        (((s : ℝ) * centralWeight s *
          ∑ t ∈ Finset.range (n + 1),
            centralWeight t * centralWeight (n - t) / ((s : ℝ) + t) : ℝ) : ℂ) := by
    convert h using 1; push_cast; simp only [pow_add]; ring
  exact_mod_cast (mul_left_cancel₀ hp hc).symm

private lemma weight_convolution (n : ℕ) :
    (∑ t ∈ Finset.range (n + 1), centralWeight t * centralWeight (n - t)) = 1 := by
  have hv := Ring.add_choose_eq (R := ℂ) (r := -1 / 2) (s := -1 / 2) n
    (Commute.all _ _)
  have hneg : Ring.choose (-1 : ℂ) n = (-1 : ℂ) ^ n := by
    simpa [Ring.multichoose_one, Units.smul_def, zsmul_eq_mul,
      Int.cast_negOnePow_natCast] using Ring.choose_neg' (1 : ℂ) n
  rw [show (-1 / 2 : ℂ) + (-1 / 2) = -1 by ring, hneg] at hv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have he : (-1 : ℂ) ^ n = (-1 : ℂ) ^ n *
      ((∑ t ∈ Finset.range (n + 1), centralWeight t * centralWeight (n - t) : ℝ) : ℂ) := by
    conv_lhs => rw [hv]
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← halfBinomial_choose, ← halfBinomial_choose,
      halfBinomial_eq_signed_centralWeight, halfBinomial_eq_signed_centralWeight]
    push_cast
    rw [mul_mul_mul_comm, ← pow_add, show t + (n - t) = n by
      have := Finset.mem_range.mp ht; omega]
  have he' := (mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)))
    (show (-1 : ℂ) ^ n * 1 = (-1 : ℂ) ^ n *
      ((∑ t ∈ Finset.range (n + 1), centralWeight t * centralWeight (n - t) : ℝ) : ℂ) by
        simpa using he)
  exact_mod_cast he'.symm

/-- The real restriction of the already defined original period. -/
def F (r : ℝ) : ℝ := (D5.S3.Analytic.OriginalHalfBinomialPeriod.period (r : ℂ)).re

/-- Shifted products of the same central-binomial coefficients, including k=0. -/
def L (r : ℝ) (s : ℕ) : ℝ :=
  ∑' k : ℕ, centralWeight k * centralWeight (k + s) * r ^ k

private lemma F_eq (r : ℝ) :
    F r = ∑' k : ℕ, centralWeight k ^ 2 * r ^ k := by
  have h : D5.S3.Analytic.OriginalHalfBinomialPeriod.period (r : ℂ) =
      ((∑' k : ℕ, centralWeight k ^ 2 * r ^ k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro k
    rw [halfBinomial_eq_signed_centralWeight]
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  exact congrArg Complex.re h

private lemma shifted_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    Summable (fun k : ℕ => centralWeight k * centralWeight (k + s) * r ^ k) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (mul_nonneg (centralWeight_nonneg k)
      (centralWeight_nonneg (k + s))) (pow_nonneg hr k)) (fun k => ?_)
    (summable_geometric_of_lt_one hr hr1)
  calc
    _ ≤ 1 * 1 * r ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (weight_le_one _) (weight_le_one _)
          (centralWeight_nonneg _) zero_le_one) (pow_nonneg hr k)
    _ = _ := by ring

private lemma period_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => centralWeight k ^ 2 * r ^ k) := by
  simpa [pow_two] using shifted_summable hr hr1 0

private lemma F_ge_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : 1 ≤ F r := by
  rw [F_eq]
  have h := (period_summable hr hr1).le_tsum 0 (fun k hk => by positivity)
  simpa [centralWeight_zero] using h

private lemma L_nonneg {r : ℝ} (hr : 0 ≤ r) (s : ℕ) : 0 ≤ L r s :=
  tsum_nonneg (fun k => mul_nonneg
    (mul_nonneg (centralWeight_nonneg k) (centralWeight_nonneg (k + s))) (pow_nonneg hr k))

private lemma L_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    L r s ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hr hr1]
  apply (shifted_summable hr hr1 s).tsum_le_tsum _
    (summable_geometric_of_lt_one hr hr1)
  intro k
  calc
    _ ≤ 1 * 1 * r ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (weight_le_one _) (weight_le_one _)
          (centralWeight_nonneg _) zero_le_one) (pow_nonneg hr k)
    _ = _ := by ring

private lemma pair_tsum_antidiagonal (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    (∑' p : ℕ × ℕ, f p) =
      ∑' n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p := by
  conv_rhs =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf).tsum_sigma'
    (fun n => (hasSum_fintype _).summable)

private def residualTerm (r : ℝ) (s : ℕ) (p : ℕ × ℕ) : ℝ :=
  centralWeight p.1 * centralWeight p.2 * centralWeight (p.1 + p.2) *
    r ^ (p.1 + p.2) / ((s : ℝ) + p.1)

private lemma residualTerm_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (s : ℕ) (hs : 0 < s) : Summable (residualTerm r s) := by
  have hg := summable_geometric_of_lt_one hr hr1
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity))
  · exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (centralWeight_nonneg _) (centralWeight_nonneg _))
        (centralWeight_nonneg _)) (pow_nonneg hr _)) (by positivity)
  · have hp : centralWeight p.1 * centralWeight p.2 ≤ 1 := by
      simpa using mul_le_mul (weight_le_one p.1) (weight_le_one p.2)
        (centralWeight_nonneg _) zero_le_one
    have hp' : centralWeight p.1 * centralWeight p.2 * centralWeight (p.1 + p.2) ≤ 1 := by
      simpa using mul_le_mul hp (weight_le_one (p.1 + p.2))
        (centralWeight_nonneg _) zero_le_one
    have hd : (1 : ℝ) ≤ s + p.1 := by exact_mod_cast (by omega : 1 ≤ s + p.1)
    rw [residualTerm, ← pow_add]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < s + p.1)).mpr
    calc
      _ ≤ 1 * r ^ (p.1 + p.2) :=
        mul_le_mul_of_nonneg_right hp' (pow_nonneg hr _)
      _ ≤ _ := by nlinarith [pow_nonneg hr (p.1 + p.2)]

private lemma residualTerm_row (r : ℝ) (s t : ℕ) :
    (∑' k : ℕ, residualTerm r s (t, k)) =
      centralWeight t * r ^ t * L r t / ((s : ℝ) + t) := by
  calc
    _ = ∑' k : ℕ, (centralWeight t * r ^ t) *
        (centralWeight k * centralWeight (k + t) * r ^ k) / ((s : ℝ) + t) := by
      apply tsum_congr
      intro k
      simp only [residualTerm, pow_add, Nat.add_comm t k]
      ring
    _ = _ := by rw [tsum_div_const, tsum_mul_left]; rfl

private lemma full_shifted_identity {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (s : ℕ) (hs : 0 < s) :
    (s : ℝ) * centralWeight s *
      (∑' t : ℕ, centralWeight t * r ^ t * L r t / ((s : ℝ) + t)) = L r s := by
  have hf := residualTerm_summable hr hr1 s hs
  have he : (∑' t : ℕ, centralWeight t * r ^ t * L r t / ((s : ℝ) + t)) =
      ∑' n : ℕ, ∑ t ∈ Finset.range (n + 1), residualTerm r s (t, n - t) := by
    calc
      _ = ∑' t : ℕ, ∑' k : ℕ, residualTerm r s (t, k) :=
        tsum_congr (fun t => (residualTerm_row r s t).symm)
      _ = _ := by
        rw [← hf.tsum_prod, pair_tsum_antidiagonal _ hf]
        congr 1
        ext n
        exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ n
  rw [he, ← tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    _ = (centralWeight n * r ^ n) *
        ((s : ℝ) * centralWeight s *
          ∑ t ∈ Finset.range (n + 1),
            centralWeight t * centralWeight (n - t) / ((s : ℝ) + t)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hn : t + (n - t) = n := by have := Finset.mem_range.mp ht; omega
      simp only [residualTerm, hn]
      ring
    _ = centralWeight n * centralWeight (n + s) * r ^ n := by
      rw [shifted_convolution s n hs, Nat.add_comm s n]
      ring

private lemma shifted_residual {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (s : ℕ) (hs : 0 < s) :
    (s : ℝ) * centralWeight s *
      (∑' t : ℕ, centralWeight (t + 1) * r ^ (t + 1) * L r (t + 1) /
        ((s : ℝ) + (t + 1 : ℕ))) = L r s - centralWeight s * F r := by
  have hf := full_shifted_identity hr hr1 s hs
  have hsum : Summable (fun t : ℕ =>
      centralWeight t * r ^ t * L r t / ((s : ℝ) + t)) := by
    simpa only [residualTerm_row] using (residualTerm_summable hr hr1 s hs).prod
  rw [hsum.tsum_eq_zero_add] at hf
  have hL0 : L r 0 = F r := by simp [L, F_eq, pow_two]
  simp only [centralWeight_zero, pow_zero, one_mul, Nat.cast_zero, add_zero, hL0] at hf
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have hcancel : (s : ℝ) * centralWeight s * (F r / s) = centralWeight s * F r := by
    field_simp
  rw [mul_add, hcancel] at hf
  linarith

/-- The prescribed original source column; n denotes frequency n+1. -/
def sourceValue (r : ℝ) (n : ℕ) : ℂ :=
  halfBinomial (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) /
    (Real.sqrt (n + 1 : ℝ) : ℂ)

def columnValue (r : ℝ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) * (L r (n + 1) : ℂ) /
    ((Real.sqrt (n + 1 : ℝ) : ℂ) * (F r : ℂ))

private lemma half_norm (n : ℕ) : ‖halfBinomial n‖ = centralWeight n := by
  rw [halfBinomial_eq_signed_centralWeight, norm_mul, norm_pow]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (centralWeight_nonneg n)]

private lemma sqrt_frequency_ge_one (n : ℕ) : 1 ≤ Real.sqrt (n + 1 : ℝ) := by
  apply Real.one_le_sqrt.mpr
  norm_num

private lemma sourceValue_bound (r : ℝ) (n : ℕ) :
    ‖sourceValue r n‖ ≤ Real.sqrt r ^ (n + 1) := by
  simp only [sourceValue, norm_div, norm_mul, norm_pow, half_norm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (n + 1 : ℝ))).mpr
  calc
    _ ≤ 1 * Real.sqrt r ^ (n + 1) := by gcongr; exact weight_le_one _
    _ ≤ _ := by nlinarith [sqrt_frequency_ge_one n, pow_nonneg (Real.sqrt_nonneg r) (n + 1)]

private lemma columnValue_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ‖columnValue r n‖ ≤ (1 - r)⁻¹ * Real.sqrt r ^ (n + 1) := by
  have hF := F_ge_one hr hr1
  have hL := L_nonneg hr (n + 1)
  have hs := sqrt_frequency_ge_one n
  have hden : 0 < Real.sqrt (n + 1 : ℝ) * F r := by positivity
  simp only [columnValue, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hL, abs_of_nonneg (by linarith : 0 ≤ F r)]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ Real.sqrt r ^ (n + 1) * (1 - r)⁻¹ := by gcongr; exact L_le hr hr1 _
    _ ≤ _ := by
      have hp : 0 ≤ (1 - r)⁻¹ * Real.sqrt r ^ (n + 1) := by positivity
      have hd : 1 ≤ Real.sqrt (n + 1 : ℝ) * F r := one_le_mul_of_one_le_of_one_le hs hF
      nlinarith

private lemma geometric_mem_l2 {f : ℕ → ℂ} {r C : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ n, ‖f n‖ ≤ C * Real.sqrt r ^ (n + 1)) : Memℓp f 2 := by
  apply memℓp_gen
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr hr1)).mul_left (C ^ 2))
  calc
    ‖f n‖ ^ 2 ≤ (C * Real.sqrt r ^ (n + 1)) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (hf n) 2
    _ = C ^ 2 * r ^ (n + 1) := by
      rw [mul_pow, ← pow_mul, mul_comm (n + 1) 2, pow_mul, Real.sq_sqrt hr]

private lemma source_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Memℓp (sourceValue r) 2 :=
  geometric_mem_l2 (C := 1) hr hr1 (by simpa using sourceValue_bound r)

private lemma column_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Memℓp (columnValue r) 2 :=
  geometric_mem_l2 (C := (1 - r)⁻¹) hr hr1 (columnValue_bound hr hr1)

def source (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : H := ⟨sourceValue r, source_mem hr hr1⟩

def column (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : H := ⟨columnValue r, column_mem hr hr1⟩

private lemma weighted_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Memℓp (fun n : ℕ => (n + 1 : ℂ) * sourceValue r n) 2 := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one 2 (r := r)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)
  apply memℓp_gen
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_)
    ((summable_nat_add_iff 1).mpr hg)
  have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    exact_mod_cast (Complex.norm_natCast (n + 1))
  rw [norm_mul, hn]
  calc
    _ ≤ ((n + 1 : ℝ) * Real.sqrt r ^ (n + 1)) ^ 2 := by
      gcongr
      exact sourceValue_bound r n
    _ = _ := by
      rw [mul_pow, ← pow_mul, mul_comm (n + 1) 2, pow_mul, Real.sq_sqrt hr]
      norm_cast

/-- Frequency multiplication is applied only to this proved square-summable vector. -/
def weightedSource (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : H :=
  ⟨fun n : ℕ => (n + 1 : ℂ) * sourceValue r n, weighted_mem hr hr1⟩

def resolvent (z : ℂ) : H →L[ℂ] H := ∑' k : ℕ, operator z ^ k

private lemma resolvent_mul {z : ℂ} (hz : ‖z‖ < 1) :
    resolvent z * (1 - operator z) = 1 := by
  apply geom_series_mul_neg
  exact (operator_norm_le hz).trans_lt (pow_lt_one₀ (norm_nonneg z) hz (by norm_num : (2 : ℕ) ≠ 0))

private def B (r : ℝ) : ℝ := ∑' k : ℕ, centralWeight k * r ^ k

private lemma B_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => centralWeight k * r ^ k) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (centralWeight_nonneg k) (pow_nonneg hr k))
    (fun k => ?_) (summable_geometric_of_lt_one hr hr1)
  simpa using mul_le_mul_of_nonneg_right (weight_le_one k) (pow_nonneg hr k)

private lemma B_ge_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : 1 ≤ B r := by
  have h := (B_summable hr hr1).le_tsum 0
    (fun k hk => mul_nonneg (centralWeight_nonneg k) (pow_nonneg hr k))
  simpa [B, centralWeight_zero] using h

private lemma B_eq {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    B r = (Real.sqrt (1 - r))⁻¹ := by
  have hf := B_summable hr hr1
  have hn : Summable (fun k : ℕ => ‖centralWeight k * r ^ k‖) := by
    convert hf using 1
    ext k
    exact Real.norm_of_nonneg (mul_nonneg (centralWeight_nonneg k) (pow_nonneg hr k))
  have hsq : (B r) ^ 2 = (1 - r)⁻¹ := by
    rw [pow_two, B, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn hn]
    rw [← tsum_geometric_of_lt_one hr hr1]
    apply tsum_congr
    intro n
    calc
      _ = (∑ t ∈ Finset.range (n + 1), centralWeight t * centralWeight (n - t)) * r ^ n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t ht
        have htn : t + (n - t) = n := by have := Finset.mem_range.mp ht; omega
        calc
          _ = centralWeight t * centralWeight (n - t) * (r ^ t * r ^ (n - t)) := by ring
          _ = _ := by rw [← pow_add, htn]
      _ = r ^ n := by rw [weight_convolution, one_mul]
  apply (sq_eq_sq₀ (by linarith [B_ge_one hr hr1]) (by positivity)).mp
  rw [hsq, inv_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - r)]

private def scalarTerm (r : ℝ) (p : ℕ × ℕ) : ℝ :=
  centralWeight p.1 * centralWeight p.2 * centralWeight (p.1 + p.2) *
    r ^ (p.1 + p.2)

private lemma scalarTerm_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (scalarTerm r) := by
  have hg := summable_geometric_of_lt_one hr hr1
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity))
  · exact mul_nonneg (mul_nonneg (mul_nonneg (centralWeight_nonneg _) (centralWeight_nonneg _))
      (centralWeight_nonneg _)) (pow_nonneg hr _)
  · have hp : centralWeight p.1 * centralWeight p.2 ≤ 1 := by
      simpa using mul_le_mul (weight_le_one p.1) (weight_le_one p.2)
        (centralWeight_nonneg _) zero_le_one
    have hp' : centralWeight p.1 * centralWeight p.2 * centralWeight (p.1 + p.2) ≤ 1 := by
      simpa using mul_le_mul hp (weight_le_one (p.1 + p.2))
        (centralWeight_nonneg _) zero_le_one
    simpa [scalarTerm, pow_add] using mul_le_mul_of_nonneg_right hp' (pow_nonneg hr (p.1 + p.2))

private lemma scalarTerm_row (r : ℝ) (t : ℕ) :
    (∑' k : ℕ, scalarTerm r (t, k)) = centralWeight t * r ^ t * L r t := by
  calc
    _ = ∑' k : ℕ, (centralWeight t * r ^ t) *
        (centralWeight k * centralWeight (k + t) * r ^ k) := by
      apply tsum_congr
      intro k
      simp only [scalarTerm, pow_add, Nat.add_comm t k]
      ring
    _ = _ := by rw [tsum_mul_left]; rfl

private lemma scalar_shifted_sum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' t : ℕ, centralWeight (t + 1) * r ^ (t + 1) * L r (t + 1)) = B r - F r := by
  have hf := scalarTerm_summable hr hr1
  have hsum : Summable (fun t : ℕ => centralWeight t * r ^ t * L r t) := by
    simpa only [scalarTerm_row] using hf.prod
  have he : (∑' t : ℕ, centralWeight t * r ^ t * L r t) = B r := by
    trans ∑' p : ℕ × ℕ, scalarTerm r p
    · exact (tsum_congr (fun t => (scalarTerm_row r t).symm)).trans hf.tsum_prod.symm
    rw [pair_tsum_antidiagonal _ hf]
    apply tsum_congr
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc
      _ = (centralWeight n * r ^ n) *
          (∑ t ∈ Finset.range (n + 1), centralWeight t * centralWeight (n - t)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hn : t + (n - t) = n := by have := Finset.mem_range.mp ht; omega
        simp only [scalarTerm, hn]
        ring
      _ = centralWeight n * r ^ n := by rw [weight_convolution, mul_one]
  rw [hsum.tsum_eq_zero_add] at he
  have hL0 : L r 0 = F r := by simp [L, F_eq, pow_two]
  simp only [centralWeight_zero, pow_zero, one_mul, hL0] at he
  linarith

private lemma entry_sqrt (z : ℂ) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    matrixEntry z s t =
      (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (t : ℝ) : ℂ) *
        halfBinomial s * halfBinomial t * z ^ (s + t) / ((s : ℂ) + t) := by
  have hs2 : (Real.sqrt (s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ s)
  have ht2 : (Real.sqrt (t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ t)
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (s : ℝ) ≠ 0)
  have ht0 : (Real.sqrt (t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (t : ℝ) ≠ 0)
  simp only [matrixEntry, pairScalar]
  rw [← hs2, ← ht2]
  field_simp

private lemma entry_column_product {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (s t : ℕ)
    (hs : 0 < s) :
    matrixEntry (Real.sqrt r : ℂ) s (t + 1) * columnValue r t =
      ((-1 : ℂ) ^ s * (Real.sqrt r : ℂ) ^ s /
        ((Real.sqrt (s : ℝ) : ℂ) * (F r : ℂ))) *
        (((s : ℝ) * centralWeight s *
          (centralWeight (t + 1) * r ^ (t + 1) * L r (t + 1) /
            ((s : ℝ) + (t + 1 : ℕ))) : ℝ) : ℂ) := by
  have hs2 : (Real.sqrt (s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ s)
  have hq : (Real.sqrt r : ℂ) ^ (t + 1) * (Real.sqrt r : ℂ) ^ (t + 1) =
      (r : ℂ) ^ (t + 1) := by
    rw [← mul_pow]
    congr 1
    exact_mod_cast Real.mul_self_sqrt hr
  have hsign : (-1 : ℂ) ^ (t + 1) * (-1 : ℂ) ^ (t + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (s : ℝ) ≠ 0)
  have ht0 : (Real.sqrt (t + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (t + 1 : ℝ) ≠ 0)
  have hF : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr hr1)))
  calc
    _ = ((-1 : ℂ) ^ s * (Real.sqrt r : ℂ) ^ s /
        ((Real.sqrt (s : ℝ) : ℂ) * (F r : ℂ))) *
        ((Real.sqrt (s : ℝ) : ℂ) ^ 2 * (centralWeight s : ℂ) *
          ((-1 : ℂ) ^ (t + 1) * (-1 : ℂ) ^ (t + 1)) *
          ((Real.sqrt r : ℂ) ^ (t + 1) * (Real.sqrt r : ℂ) ^ (t + 1)) *
          (centralWeight (t + 1) : ℂ) * (L r (t + 1) : ℂ) /
          ((s : ℂ) + (t + 1 : ℕ))) := by
      rw [entry_sqrt _ _ _ hs (by omega), halfBinomial_eq_signed_centralWeight,
        halfBinomial_eq_signed_centralWeight]
      simp only [columnValue, pow_add (Real.sqrt r : ℂ) s (t + 1)]
      push_cast
      field_simp [hs0, ht0, hF]
    _ = _ := by
      rw [hs2, hsign, hq]
      push_cast
      ring

private lemma radial_norm_lt_one {r : ℝ} (hr1 : r < 1) : ‖(Real.sqrt r : ℂ)‖ < 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg r)] using
    (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hr1)

private lemma column_equation {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (1 - operator (Real.sqrt r : ℂ)) (column r hr.le hr1) = source r hr.le hr1 := by
  ext n
  have ha : operator (Real.sqrt r : ℂ) (column r hr.le hr1) n =
      ((-1 : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * (F r : ℂ))) *
        (((n + 1 : ℝ) * centralWeight (n + 1) *
          (∑' t : ℕ, centralWeight (t + 1) * r ^ (t + 1) * L r (t + 1) /
            ((n + 1 : ℝ) + (t + 1 : ℕ))) : ℝ) : ℂ) := by
    rw [operator_apply (radial_norm_lt_one hr1)]
    change (∑' t : ℕ, matrixEntry (Real.sqrt r : ℂ) (n + 1) (t + 1) * columnValue r t) = _
    simp_rw [entry_column_product hr.le hr1 (n + 1) _ (by omega)]
    rw [tsum_mul_left, ← Complex.ofReal_tsum, tsum_mul_left]
    push_cast
    rfl
  have hres := shifted_residual hr.le hr1 (n + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hres ha
  rw [hres] at ha
  change columnValue r n - operator (Real.sqrt r : ℂ) (column r hr.le hr1) n = sourceValue r n
  rw [ha]
  simp only [columnValue, sourceValue, halfBinomial_eq_signed_centralWeight]
  push_cast
  have hF : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)))
  field_simp [hF]
  ring

/-- The shifted column solves the actual signed original infinite resolvent. -/
theorem resolvent_column {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    resolvent (Real.sqrt r : ℂ) (source r hr.le hr1) n =
      (-1 : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) * (L r (n + 1) : ℂ) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * (F r : ℂ)) := by
  have he : resolvent (Real.sqrt r : ℂ) (source r hr.le hr1) = column r hr.le hr1 := by
    calc
      _ = resolvent (Real.sqrt r : ℂ)
          ((1 - operator (Real.sqrt r : ℂ)) (column r hr.le hr1)) := by
        rw [column_equation hr hr1]
      _ = column r hr.le hr1 := by
        exact congrArg (fun T : H →L[ℂ] H => T (column r hr.le hr1))
          (resolvent_mul (radial_norm_lt_one hr1))
  exact congrArg (fun x : H => x n) he

private lemma scalar_column_product {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (n + 1 : ℂ) * sourceValue r n * columnValue r n =
      ((centralWeight (n + 1) * r ^ (n + 1) * L r (n + 1) / F r : ℝ) : ℂ) := by
  have hs2 : (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hq : (Real.sqrt r : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) =
      (r : ℂ) ^ (n + 1) := by
    rw [← mul_pow]
    congr 1
    exact_mod_cast Real.mul_self_sqrt hr
  have hsign : (-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ (n + 1) = 1 := by
    rw [← mul_pow]; norm_num
  calc
    _ = (n + 1 : ℂ) * (centralWeight (n + 1) : ℂ) *
        ((-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ (n + 1)) *
        ((Real.sqrt r : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1)) *
        (L r (n + 1) : ℂ) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 * (F r : ℂ)) := by
      simp only [sourceValue, columnValue, halfBinomial_eq_signed_centralWeight,
        div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hs2, hsign, hq]
      push_cast
      field_simp

/-- An absolutely convergent bilinear scalar contraction, with the original signs. -/
theorem bilinear_resolvent_scalar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖(n + 1 : ℂ) * sourceValue r n *
      resolvent (Real.sqrt r : ℂ) (source r hr.le hr1) n‖) ∧
    1 + (∑' n : ℕ, (n + 1 : ℂ) * sourceValue r n *
      resolvent (Real.sqrt r : ℂ) (source r hr.le hr1) n) =
      1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ)) := by
  constructor
  · have h := lp.summable_mul (p := 2) (q := 2)
      (by simpa using Real.HolderConjugate.two_two) (weightedSource r hr.le hr1)
        (resolvent (Real.sqrt r : ℂ) (source r hr.le hr1))
    change Summable (fun n : ℕ => ‖((n + 1 : ℂ) * sourceValue r n)‖ *
      ‖resolvent (Real.sqrt r : ℂ) (source r hr.le hr1) n‖) at h
    simpa only [norm_mul, mul_assoc] using h
  · have he : (∑' n : ℕ, (n + 1 : ℂ) * sourceValue r n *
        resolvent (Real.sqrt r : ℂ) (source r hr.le hr1) n) =
        (((B r - F r) / F r : ℝ) : ℂ) := by
      simp_rw [resolvent_column hr hr1]
      change (∑' n : ℕ, (n + 1 : ℂ) * sourceValue r n * columnValue r n) = _
      simp_rw [scalar_column_product hr.le]
      rw [← Complex.ofReal_tsum, tsum_div_const, scalar_shifted_sum hr.le hr1]
    rw [he, B_eq hr.le hr1]
    push_cast
    have hF : (F r : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)))
    field_simp [hF]
    ring

private lemma weightedColumn_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Memℓp (fun n : ℕ => (n + 1 : ℂ) * columnValue r n) 2 := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one 2 (r := r)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)
  apply memℓp_gen
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr hg).mul_left ((1 - r)⁻¹ ^ 2))
  have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    exact_mod_cast (Complex.norm_natCast (n + 1))
  rw [norm_mul, hn]
  calc
    _ ≤ ((n + 1 : ℝ) * ((1 - r)⁻¹ * Real.sqrt r ^ (n + 1))) ^ 2 := by
      gcongr
      exact columnValue_bound hr hr1 n
    _ = (1 - r)⁻¹ ^ 2 * ((n + 1 : ℝ) ^ 2 * r ^ (n + 1)) := by
      rw [mul_pow, mul_pow, ← pow_mul, mul_comm (n + 1) 2,
        pow_mul, Real.sq_sqrt hr]
      ring
    _ = _ := by push_cast; rfl

/-- The actual signed shifted column multiplied by its positive frequency. -/
def weightedColumn (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : H :=
  ⟨fun n : ℕ => (n + 1 : ℂ) * columnValue r n, weightedColumn_mem hr hr1⟩

private lemma row_summable_norm {z : ℂ} (hz : ‖z‖ < 1) (x : H) (n : ℕ) :
    Summable (fun m : ℕ => ‖matrixEntry z (n + 1) (m + 1) * x m‖) := by
  have hg : Summable (fun m : ℕ => ‖z‖ ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg z) hz)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (hg.mul_left (‖z‖ ^ (n + 1) * ‖x‖))
  rw [norm_mul]
  calc
    _ ≤ ‖z‖ ^ ((n + 1) + (m + 1)) * ‖x‖ :=
      mul_le_mul (entry_bound z (n + 1) (m + 1) (by omega) (by omega))
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x m)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

private lemma original_coordinate_anticommutator (r : ℝ) (n m : ℕ) :
    ((n + 1 : ℂ) + (m + 1 : ℂ)) *
        matrixEntry (Real.sqrt r : ℂ) (n + 1) (m + 1) =
      ((n + 1 : ℂ) * sourceValue r n) *
        ((m + 1 : ℂ) * sourceValue r m) := by
  have hs : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (n + 1 : ℝ) ≠ 0)
  have ht : (Real.sqrt (m + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (m + 1 : ℝ) ≠ 0)
  have hst : (n + 1 : ℂ) + (m + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (n + 1 : ℝ) + (m + 1 : ℝ) ≠ 0)
  simp only [matrixEntry, pairScalar, sourceValue, pow_add]
  push_cast
  field_simp [hs, ht, hst]
  <;> ring

private lemma column_pair_normalization {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    1 + (∑' n : ℕ, weightedSource r hr.le hr1 n * column r hr.le hr1 n) =
      ((B r / F r : ℝ) : ℂ) := by
  have h := (bilinear_resolvent_scalar hr hr1).2
  simp_rw [resolvent_column hr hr1] at h
  change 1 + (∑' n : ℕ, weightedSource r hr.le hr1 n * column r hr.le hr1 n) =
    1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ)) at h
  rw [h, B_eq hr.le hr1]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The weighted equation is paid by the actual coordinate anticommutator. -/
theorem weightedColumn_equation {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (1 + operator (Real.sqrt r : ℂ)) (weightedColumn r hr.le hr1) =
      (1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ))) • weightedSource r hr.le hr1 := by
  have hcoef : 1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ)) =
      ((B r / F r : ℝ) : ℂ) := by
    rw [B_eq hr.le hr1]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [hcoef]
  let z : ℂ := (Real.sqrt r : ℂ)
  let c : H := column r hr.le hr1
  let d : H := weightedColumn r hr.le hr1
  let w : H := weightedSource r hr.le hr1
  let y : ℂ := ∑' m : ℕ, w m * c m
  have hz : ‖z‖ < 1 := radial_norm_lt_one hr1
  have hy : 1 + y = ((B r / F r : ℝ) : ℂ) := column_pair_normalization hr hr1
  ext n
  have hc : columnValue r n - operator z c n = sourceValue r n := by
    exact congrArg (fun x : H => x n) (column_equation hr hr1)
  have hf : Summable (fun m : ℕ => matrixEntry z (n + 1) (m + 1) * c m) :=
    (row_summable_norm hz c n).of_norm
  have hg : Summable (fun m : ℕ => matrixEntry z (n + 1) (m + 1) * d m) :=
    (row_summable_norm hz d n).of_norm
  have hrow : (n + 1 : ℂ) * operator z c n + operator z d n = w n * y := by
    calc
      _ = (∑' m : ℕ, (n + 1 : ℂ) *
            (matrixEntry z (n + 1) (m + 1) * c m)) +
          (∑' m : ℕ, matrixEntry z (n + 1) (m + 1) * d m) := by
        rw [operator_apply hz, operator_apply hz, tsum_mul_left]
      _ = ∑' m : ℕ, ((n + 1 : ℂ) *
            (matrixEntry z (n + 1) (m + 1) * c m) +
          matrixEntry z (n + 1) (m + 1) * d m) :=
        ((hf.mul_left (n + 1 : ℂ)).tsum_add hg).symm
      _ = ∑' m : ℕ, w n * (w m * c m) := by
        apply tsum_congr
        intro m
        change (n + 1 : ℂ) * (matrixEntry z (n + 1) (m + 1) * columnValue r m) +
            matrixEntry z (n + 1) (m + 1) * ((m + 1 : ℂ) * columnValue r m) =
          ((n + 1 : ℂ) * sourceValue r n) *
            (((m + 1 : ℂ) * sourceValue r m) * columnValue r m)
        calc
          _ = (((n + 1 : ℂ) + (m + 1 : ℂ)) *
              matrixEntry z (n + 1) (m + 1)) * columnValue r m := by ring
          _ = _ := by rw [original_coordinate_anticommutator]; ring
      _ = _ := tsum_mul_left
  change (n + 1 : ℂ) * columnValue r n + operator z d n =
    ((B r / F r : ℝ) : ℂ) * w n
  calc
    _ = (n + 1 : ℂ) * sourceValue r n +
        ((n + 1 : ℂ) * operator z c n + operator z d n) := by
      linear_combination (n + 1 : ℂ) * hc
    _ = w n + w n * y := by rw [hrow]; rfl
    _ = (1 + y) * w n := by ring
    _ = _ := by rw [hy]

/-- Opposite-sign Neumann series for the same literal signed operator. -/
def oppositeResolvent (z : ℂ) : H →L[ℂ] H := ∑' k : ℕ, (-operator z) ^ k

private lemma operator_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    ‖operator z‖ < 1 :=
  (operator_norm_le hz).trans_lt
    (pow_lt_one₀ (norm_nonneg z) hz (by norm_num : (2 : ℕ) ≠ 0))

private theorem oppositeResolvent_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => (-operator z) ^ k) := by
  exact summable_geometric_of_norm_lt_one (by simpa using operator_norm_lt_one hz)

private theorem oppositeResolvent_mul {z : ℂ} (hz : ‖z‖ < 1) :
    oppositeResolvent z * (1 + operator z) = 1 := by
  simpa only [oppositeResolvent, sub_neg_eq_add] using
    (oppositeResolvent_summable hz).tsum_pow_mul_one_sub

private theorem mul_oppositeResolvent {z : ℂ} (hz : ‖z‖ < 1) :
    (1 + operator z) * oppositeResolvent z = 1 := by
  simpa only [oppositeResolvent, sub_neg_eq_add] using
    (oppositeResolvent_summable hz).one_sub_mul_tsum_pow

/-- The opposite inverse acts on the prescribed weighted original source. -/
theorem opposite_resolvent_weighted_source {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) =
      ((Real.sqrt (1 - r) * F r : ℝ) : ℂ) • weightedColumn r hr.le hr1 := by
  have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1))
  have hB : B r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (B_ge_one hr.le hr1))
  have hz := radial_norm_lt_one hr1
  have hcoef : 1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ)) =
      ((B r / F r : ℝ) : ℂ) := by
    rw [B_eq hr.le hr1]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  have heq := weightedColumn_equation hr hr1
  rw [hcoef] at heq
  have hinj : Function.Injective (1 + operator (Real.sqrt r : ℂ) : H →L[ℂ] H) := by
    intro x y he
    calc
      x = oppositeResolvent (Real.sqrt r : ℂ)
          ((1 + operator (Real.sqrt r : ℂ)) x) :=
        (congrArg (fun T : H →L[ℂ] H => T x) (oppositeResolvent_mul hz)).symm
      _ = oppositeResolvent (Real.sqrt r : ℂ)
          ((1 + operator (Real.sqrt r : ℂ)) y) := congrArg _ he
      _ = y := congrArg (fun T : H →L[ℂ] H => T y) (oppositeResolvent_mul hz)
  have hright : (1 + operator (Real.sqrt r : ℂ))
      (oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1)) =
        weightedSource r hr.le hr1 :=
    congrArg (fun T : H →L[ℂ] H => T (weightedSource r hr.le hr1))
      (mul_oppositeResolvent hz)
  have ha : ((B r / F r : ℝ) : ℂ) •
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) =
        weightedColumn r hr.le hr1 := by
    apply hinj
    rw [map_smul, hright]
    exact heq.symm
  have hcancel : ((F r / B r : ℝ) : ℂ) * ((B r / F r : ℝ) : ℂ) = 1 := by
    norm_cast
    field_simp [hF, hB]
  calc
    _ = (((F r / B r : ℝ) : ℂ) * ((B r / F r : ℝ) : ℂ)) •
        oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) := by
      rw [hcancel, one_smul]
    _ = ((F r / B r : ℝ) : ℂ) • (((B r / F r : ℝ) : ℂ) •
        oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1)) := by
      rw [smul_smul]
    _ = ((F r / B r : ℝ) : ℂ) • weightedColumn r hr.le hr1 := by rw [ha]
    _ = _ := by rw [B_eq hr.le hr1]; simp [div_eq_mul_inv, mul_comm]

/- The next finite identity is the only additional convolution coefficient.
   Its proof is finite symmetry, not differentiation of an assumed endpoint. -/
private lemma frequency_weight_convolution (n : ℕ) :
    (∑ t ∈ Finset.range (n + 1),
      (t : ℝ) * centralWeight t * centralWeight (n - t)) = (n : ℝ) / 2 := by
  have hsym : (∑ t ∈ Finset.range (n + 1),
      (t : ℝ) * centralWeight t * centralWeight (n - t)) =
      ∑ t ∈ Finset.range (n + 1),
        ((n - t : ℕ) : ℝ) * centralWeight t * centralWeight (n - t) := by
    refine Finset.sum_bij (fun t _ => n - t) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_range] at ht ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_range] at ha hb
      omega
    · intro b hb
      refine ⟨n - b, Finset.mem_range.mpr (by omega), ?_⟩
      have hb' := Finset.mem_range.mp hb
      omega
    · intro t ht
      have hi : n - (n - t) = t := by
        have := Finset.mem_range.mp ht
        omega
      rw [hi]
      ring
  have hadd : (∑ t ∈ Finset.range (n + 1),
      (t : ℝ) * centralWeight t * centralWeight (n - t)) +
      (∑ t ∈ Finset.range (n + 1),
        ((n - t : ℕ) : ℝ) * centralWeight t * centralWeight (n - t)) = (n : ℝ) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = (n : ℝ) * (∑ t ∈ Finset.range (n + 1),
          centralWeight t * centralWeight (n - t)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : t ≤ n := by have := Finset.mem_range.mp ht; omega
        rw [Nat.cast_sub ht']
        ring
      _ = _ := by rw [weight_convolution, mul_one]
  rw [← hsym] at hadd
  linarith

private lemma weightedB_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * centralWeight n * r ^ n) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)
  apply Summable.of_nonneg_of_le (fun n => by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (centralWeight_nonneg n))
      (pow_nonneg hr n)) (fun n => ?_) hg
  calc
    _ ≤ (n : ℝ) * 1 * r ^ n := by
      gcongr
      exact weight_le_one n
    _ = _ := by ring

private lemma weightedB_coefficient_step (n : ℕ) :
    2 * (n + 1 : ℝ) * centralWeight (n + 1) =
      (2 * (n : ℝ) + 1) * centralWeight n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hcR : (n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  simp only [centralWeight, pow_succ, Nat.cast_add, Nat.cast_one,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  nlinarith [hcR]

private lemma weightedB_eq {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (n : ℝ) * centralWeight n * r ^ n) =
      r * B r / (2 * (1 - r)) := by
  let S : ℝ := ∑' n : ℕ, (n : ℝ) * centralWeight n * r ^ n
  have hs := weightedB_summable hr hr1
  have hb := B_summable hr hr1
  have hshift : (∑' n : ℕ, (n + 1 : ℝ) * centralWeight (n + 1) * r ^ (n + 1)) = S := by
    simpa only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one] using
      hs.tsum_eq_zero_add.symm
  have he : 2 * S = r * (2 * S + B r) := by
    calc
      _ = 2 * (∑' n : ℕ,
          (n + 1 : ℝ) * centralWeight (n + 1) * r ^ (n + 1)) := by rw [hshift]
      _ = ∑' n : ℕ, 2 * ((n + 1 : ℝ) * centralWeight (n + 1) * r ^ (n + 1)) :=
        (tsum_mul_left).symm
      _ = ∑' n : ℕ, r * (2 * ((n : ℝ) * centralWeight n * r ^ n) +
          centralWeight n * r ^ n) := by
        apply tsum_congr
        intro n
        have hrec := weightedB_coefficient_step n
        rw [pow_succ]
        linear_combination (r ^ n * r) * hrec
      _ = _ := by
        rw [tsum_mul_left, (hs.mul_left 2).tsum_add hb, tsum_mul_left]
        rfl
  change S = _
  apply (eq_div_iff (by linarith : 2 * (1 - r) ≠ 0)).mpr
  nlinarith [he]

private def weightedScalarTerm (r : ℝ) (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) * scalarTerm r p

private lemma weightedScalarTerm_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (weightedScalarTerm r) := by
  have hg := summable_geometric_of_lt_one hr hr1
  have hng : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (hng.mul_of_nonneg hg (fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hr n))
      (fun n => pow_nonneg hr n))
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (mul_nonneg (centralWeight_nonneg _) (centralWeight_nonneg _))
        (centralWeight_nonneg _)) (pow_nonneg hr _))
  · have hp : centralWeight p.1 * centralWeight p.2 ≤ 1 := by
      simpa using mul_le_mul (weight_le_one p.1) (weight_le_one p.2)
        (centralWeight_nonneg _) zero_le_one
    have hp' : centralWeight p.1 * centralWeight p.2 * centralWeight (p.1 + p.2) ≤ 1 := by
      simpa using mul_le_mul hp (weight_le_one (p.1 + p.2))
        (centralWeight_nonneg _) zero_le_one
    calc
      _ ≤ (p.1 : ℝ) * (1 * r ^ (p.1 + p.2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp' (pow_nonneg hr _)) (Nat.cast_nonneg _)
      _ = _ := by rw [pow_add]; ring

private lemma weightedScalarTerm_row (r : ℝ) (t : ℕ) :
    (∑' k : ℕ, weightedScalarTerm r (t, k)) =
      (t : ℝ) * centralWeight t * r ^ t * L r t := by
  change (∑' k : ℕ, (t : ℝ) * scalarTerm r (t, k)) = _
  rw [tsum_mul_left, scalarTerm_row]
  ring

private lemma weighted_scalar_shifted_sum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' t : ℕ, (t + 1 : ℝ) * centralWeight (t + 1) *
      r ^ (t + 1) * L r (t + 1)) =
      (∑' n : ℕ, (n : ℝ) * centralWeight n * r ^ n) / 2 := by
  have hf := weightedScalarTerm_summable hr hr1
  have hsum : Summable (fun t : ℕ => (t : ℝ) * centralWeight t * r ^ t * L r t) := by
    simpa only [weightedScalarTerm_row] using hf.prod
  have he : (∑' t : ℕ, (t : ℝ) * centralWeight t * r ^ t * L r t) =
      (∑' n : ℕ, (n : ℝ) * centralWeight n * r ^ n) / 2 := by
    calc
      _ = ∑' p : ℕ × ℕ, weightedScalarTerm r p :=
        (tsum_congr (fun t => (weightedScalarTerm_row r t).symm)).trans hf.tsum_prod.symm
      _ = ∑' n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          weightedScalarTerm r p := pair_tsum_antidiagonal _ hf
      _ = ∑' n : ℕ, ((n : ℝ) * centralWeight n * r ^ n) / 2 := by
        apply tsum_congr
        intro n
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        calc
          _ = (centralWeight n * r ^ n) *
              (∑ t ∈ Finset.range (n + 1),
                (t : ℝ) * centralWeight t * centralWeight (n - t)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            have hn : t + (n - t) = n := by
              have := Finset.mem_range.mp ht
              omega
            simp only [weightedScalarTerm, scalarTerm, hn]
            ring
          _ = _ := by rw [frequency_weight_convolution]; ring
      _ = _ := tsum_div_const
  rw [hsum.tsum_eq_zero_add] at he
  simpa only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one] using he

private lemma weighted_column_pair {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑' n : ℕ, weightedSource r hr.le hr1 n * weightedColumn r hr.le hr1 n) =
      ((r * B r / (4 * (1 - r) * F r) : ℝ) : ℂ) := by
  have hterm (n : ℕ) : weightedSource r hr.le hr1 n * weightedColumn r hr.le hr1 n =
      (((n + 1 : ℝ) * centralWeight (n + 1) * r ^ (n + 1) *
        L r (n + 1) / F r : ℝ) : ℂ) := by
    change ((n + 1 : ℂ) * sourceValue r n) * ((n + 1 : ℂ) * columnValue r n) = _
    calc
      _ = (n + 1 : ℂ) * ((n + 1 : ℂ) * sourceValue r n * columnValue r n) := by ring
      _ = _ := by rw [scalar_column_product hr.le]; push_cast; ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, tsum_div_const,
    weighted_scalar_shifted_sum hr.le hr1, weightedB_eq hr.le hr1]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The immediately consumed opposite-sign moment is absolutely convergent
    and bilinear, for the literal original signed kernel and weighted source. -/
theorem bilinear_opposite_resolvent_scalar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n‖) ∧
    (∑' n : ℕ, weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n) =
        ((r / (4 * (1 - r)) : ℝ) : ℂ) := by
  constructor
  · have h := lp.summable_mul (p := 2) (q := 2)
      (by simpa using Real.HolderConjugate.two_two) (weightedSource r hr.le hr1)
        (oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1))
    simpa only [norm_mul] using h
  · rw [opposite_resolvent_weighted_source hr hr1]
    have ht : (∑' n : ℕ, weightedSource r hr.le hr1 n *
        (((Real.sqrt (1 - r) * F r : ℝ) : ℂ) • weightedColumn r hr.le hr1) n) =
        ((Real.sqrt (1 - r) * F r : ℝ) : ℂ) *
          (∑' n : ℕ, weightedSource r hr.le hr1 n * weightedColumn r hr.le hr1 n) := by
      calc
        _ = ∑' n : ℕ, ((Real.sqrt (1 - r) * F r : ℝ) : ℂ) *
            (weightedSource r hr.le hr1 n * weightedColumn r hr.le hr1 n) := by
          apply tsum_congr
          intro n
          change _ * (((Real.sqrt (1 - r) * F r : ℝ) : ℂ) * _) = _
          ring
        _ = _ := tsum_mul_left
    rw [ht, weighted_column_pair hr hr1]
    have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1))
    have hr0 : 1 - r ≠ 0 := by linarith
    rw [B_eq hr.le hr1]
    have hs : Real.sqrt (1 - r) ≠ 0 := by positivity
    norm_cast
    field_simp [hF, hs, hr0]
    <;> ring


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
