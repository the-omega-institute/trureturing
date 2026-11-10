/- GID: D5/S3/ArithSums/HannaA075885FloorGrowth
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaA075885FloorGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's floor-prefix sum has the positive root limit specified by its log series. -/

/-
admission_basis: open-problem-resolution (#23630; Proved)
escape_witness: none
The source uses natural division for floor(n/k), inclusive positive finite intervals,
and the shift n + 1 for all positive root indices. The source series starts at j + 1.
The source product is inlined in a; proofs use ResidueCodeDynamicRange.prefixProduct
through prefix_correspondence, without introducing a second prefix-product definition.
The auxiliary increment and its sum are private; the public expressions retain the source formulas.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26133
Direct frozen dependencies (declaration statement_id, from the existing source-matched report):
D5/S3/ArithSums/A400361PillaiMean.hasSum_kernel_one:
sha256:f98032369bad7b5ea5ba9c5256c3d52d180ac0c48424f6f725c7d1a19dd5295b
D5/S3/ArithSums/A400361PillaiMean.quotient_ratio_limit:
sha256:1f5f094c2b2c031ab14bc98a22319f9732b6b734b100101c37d7e319007de1db
D5/S3/Arith/Coding/ResidueCodeDynamicRange.prefixProduct:
sha256:53f5561d871f569f77dbb9b8b738a53475f1e8f74e5217495778f418b0ca2ba0
The short dependency labels below refer to these three declaration identities.
prefix_correspondence: proof_shape: bind-only; consumers: prefix_pos, prefix_mono, log_product; direct frozen dependencies: ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
prefix_pos: proof_shape: bind-only; consumers: sandwich, logarithmic_limit; direct frozen dependencies: ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
prefix_mono: proof_shape: bind-only; consumers: sandwich; direct frozen dependencies: ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
sandwich: proof_shape: bind-only; consumers: logarithmic_limit; direct frozen dependencies: ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
sum_inc: proof_shape: bind-only; consumers: log_quotient; direct frozen dependencies: none; escape_witness: none.
log_quotient: proof_shape: bind-only; consumers: log_product; direct frozen dependencies: none; escape_witness: none.
count_quotient: proof_shape: bind-only; consumers: log_product; direct frozen dependencies: none; escape_witness: none.
log_product: proof_shape: bind-only; consumers: product_limit; direct frozen dependencies: ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
inc_bounds: proof_shape: bind-only; consumers: summable_inc, product_limit; direct frozen dependencies: none; escape_witness: none.
summable_inc: proof_shape: bind-only; consumers: source_hasSum; direct frozen dependencies: hasSum_kernel_one; escape_witness: none.
parts: proof_shape: bind-only; consumers: source_hasSum; direct frozen dependencies: none; escape_witness: none.
log_ratio_zero: proof_shape: bind-only; consumers: source_hasSum, correction_zero; direct frozen dependencies: none; escape_witness: none.
source_hasSum: proof_shape: bind-only; consumers: result; direct frozen dependencies: hasSum_kernel_one; escape_witness: none.
product_limit: proof_shape: bind-only; consumers: logarithmic_limit; direct frozen dependencies: hasSum_kernel_one, quotient_ratio_limit, ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
correction_zero: proof_shape: bind-only; consumers: logarithmic_limit; direct frozen dependencies: none; escape_witness: none.
logarithmic_limit: proof_shape: bind-only; consumers: result; direct frozen dependencies: hasSum_kernel_one, quotient_ratio_limit, ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
result: proof_shape: bind-only; consumers: settling conclusion; direct frozen dependencies: hasSum_kernel_one, quotient_ratio_limit, ResidueCodeDynamicRange.prefixProduct; escape_witness: none.
a: definition; consumers: claim, sandwich, logarithmic_limit, result; escape_witness: none.
logSummand: definition; consumers: claim, parts, source_hasSum, result; escape_witness: none.
claim: definition; consumers: result; escape_witness: none.
inc: definition; consumers: sum_inc, log_quotient, count_quotient, log_product, inc_bounds, summable_inc, parts, C, source_hasSum, product_limit; escape_witness: none.
C: definition; consumers: source_hasSum, product_limit, logarithmic_limit, result; escape_witness: none.
-/

import D5.S3.ArithSums.A400361PillaiMean
import D5.S3.Arith.Coding.ResidueCodeDynamicRange

namespace D5.S3.ArithSums.HannaA075885FloorGrowth

open scoped BigOperators

/-- The literal A075885 FORMULA, including a(0) = 1. -/
def a (n : ℕ) : ℕ :=
  1 + ∑ m ∈ Finset.Icc 1 n, ∏ k ∈ Finset.Icc 1 m, n / k

/-- The j-th summand of the source's series, indexed from j = 0. -/
noncomputable def logSummand (j : ℕ) : ℝ :=
  Real.log ((j : ℝ) + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))

/-- The positive limit exists, its logarithm is the stated convergent series,
and the roots are indexed over exactly the positive integers n + 1. -/
def claim : Prop :=
  ∃ L : ℝ, 0 < L ∧
    HasSum (fun j : ℕ => logSummand j) (Real.log L) ∧
    Filter.Tendsto
      (fun n : ℕ => (a (n + 1) : ℝ) ^ (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds L)

open Finset Filter Topology

private noncomputable def inc (j : ℕ) : ℝ := Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1)

private theorem prefix_correspondence (n m : ℕ) :
    D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) m =
      ∏ k ∈ Finset.Icc 1 m, n / k := by
  symm
  unfold D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct
  calc
    _ = ∏ k ∈ Finset.range m, n / (k + 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
      simp only [Nat.add_sub_cancel, add_comm]
    _ = _ := Finset.prod_range (fun k => n / (k + 1))

private theorem prefix_pos (n m : ℕ) (hm : m ≤ n) : 0 < D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) m := by
  rw [prefix_correspondence]
  apply Finset.prod_pos
  intro k hk
  have hk := Finset.mem_Icc.mp hk
  exact Nat.div_pos (hk.2.trans hm) (by omega)

private theorem prefix_mono (n m : ℕ) (hm : m ≤ n) :
    D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) m ≤ D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n := by
  simp only [prefix_correspondence]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hm⟩
  · intro k hk _
    have hk := Finset.mem_Icc.mp hk
    exact Nat.div_pos hk.2 (by omega)

private theorem sandwich (n : ℕ) (hn : 0 < n) :
    D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n ≤ a n ∧ a n ≤ (n + 1) * D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n := by
  have hp := prefix_pos n n le_rfl
  constructor
  · have h := Finset.single_le_sum (f := fun m => D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) m)
      (fun m _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
    unfold a
    simp only [← prefix_correspondence]
    exact h.trans (Nat.le_add_left _ _)
  · have h : (∑ m ∈ Icc 1 n, D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) m) ≤ n * D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n := by
      calc
        _ ≤ ∑ m ∈ Icc 1 n, D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n := sum_le_sum (fun m hm => prefix_mono n m (mem_Icc.mp hm).2)
        _ = _ := by simp
    unfold a
    simp only [← prefix_correspondence]
    nlinarith

private theorem sum_inc (q : ℕ) : (∑ j ∈ range q, inc j) = Real.log ((q : ℝ) + 1) := by
  simpa [inc, Nat.cast_add, add_assoc, one_add_one_eq_two] using
    (Finset.sum_range_sub (fun j : ℕ => Real.log ((j : ℝ) + 1)) q)

private theorem log_quotient (n k : ℕ) (hk : k ∈ Icc 1 n) :
    Real.log ((n / k : ℕ) : ℝ) =
      ∑ j ∈ range n, if j + 2 ≤ n / k then inc j else 0 := by
  have hq : 0 < n / k := Nat.div_pos (mem_Icc.mp hk).2 (by have := (mem_Icc.mp hk).1; omega)
  have hqn : n / k ≤ n := Nat.div_le_self _ _
  have hset : (range n).filter (fun j => j + 2 ≤ n / k) = range (n / k - 1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [← sum_filter, hset, sum_inc]
  congr 1
  have he : n / k - 1 + 1 = n / k := Nat.sub_add_cancel hq
  exact_mod_cast he.symm

private theorem count_quotient (n j : ℕ) :
    (∑ k ∈ Icc 1 n, if j + 2 ≤ n / k then inc j else 0) =
      ((n / (j + 2) : ℕ) : ℝ) * inc j := by
  have hset : (Icc 1 n).filter (fun k => j + 2 ≤ n / k) = Icc 1 (n / (j + 2)) := by
    ext k
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hk, hkn⟩, hjk⟩
      refine ⟨hk, (Nat.le_div_iff_mul_le (by omega : 0 < j + 2)).mpr ?_⟩
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hjk
      simpa only [mul_comm] using h
    · rintro ⟨hk, hkj⟩
      refine ⟨⟨hk, hkj.trans (Nat.div_le_self _ _)⟩, ?_⟩
      apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < j + 2)).mp hkj
      simpa only [mul_comm] using h
  rw [← sum_filter, hset]
  simp

private theorem log_product (n : ℕ) :
    Real.log ((D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℕ) : ℝ) =
      ∑ j ∈ range n, ((n / (j + 2) : ℕ) : ℝ) * inc j := by
  rw [prefix_correspondence, Nat.cast_prod, Real.log_prod]
  · rw [show (∑ k ∈ Icc 1 n, Real.log ((n / k : ℕ) : ℝ)) =
        ∑ k ∈ Icc 1 n, ∑ j ∈ range n, if j + 2 ≤ n / k then inc j else 0 from
        sum_congr rfl (fun k hk => log_quotient n k hk), sum_comm]
    exact sum_congr rfl (fun j _ => count_quotient n j)
  · intro k hk
    have hp : 0 < n / k := Nat.div_pos (mem_Icc.mp hk).2 (by have := (mem_Icc.mp hk).1; omega)
    exact_mod_cast hp.ne'


private theorem inc_bounds (j : ℕ) : 0 ≤ inc j ∧ inc j ≤ 1 / ((j : ℝ) + 1) := by
  constructor
  · dsimp [inc]
    exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
  · have h := Real.log_le_sub_one_of_pos (show 0 < ((j : ℝ) + 2) / ((j : ℝ) + 1) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have he : ((j : ℝ) + 2) / ((j : ℝ) + 1) - 1 = 1 / ((j : ℝ) + 1) := by
      field_simp
      ring
    rw [he] at h
    exact h

private theorem summable_inc : Summable (fun j : ℕ => inc j / ((j : ℝ) + 2)) := by
  apply D5.S3.ArithSums.A400361PillaiMean.hasSum_kernel_one.summable.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (inc_bounds j).1 (by positivity))]
  calc
    _ ≤ (1 / ((j : ℝ) + 1)) / ((j : ℝ) + 2) :=
      div_le_div_of_nonneg_right (inc_bounds j).2 (by positivity)
    _ = _ := by simp only [div_div]

private theorem parts (N : ℕ) :
    (∑ j ∈ range N, inc j / ((j : ℝ) + 2)) =
      (∑ j ∈ range N, logSummand j) + Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) := by
  let f : ℕ → ℝ := fun j => Real.log ((j : ℝ) + 1) / ((j : ℝ) + 1)
  calc
    _ = ∑ j ∈ range N, (logSummand j + (f (j + 1) - f j)) := by
      apply sum_congr rfl
      intro j hj
      dsimp [inc, logSummand, f]
      push_cast
      have h1 : (j : ℝ) + 1 ≠ 0 := by exact Nat.cast_add_one_ne_zero j
      have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    _ = _ := by
      rw [sum_add_distrib, Finset.sum_range_sub]
      simp [f]

private noncomputable def C : ℝ := ∑' j : ℕ, inc j / ((j : ℝ) + 2)

private theorem log_ratio_zero :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, id_eq, Nat.cast_add, Nat.cast_one] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

private theorem source_hasSum : HasSum logSummand C := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j =>
    div_nonneg (Real.log_nonneg (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)) (by positivity)) C).mpr
  have hs := summable_inc.hasSum.tendsto_sum_nat
  have ht := hs.sub log_ratio_zero
  simp only [sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun N => sub_eq_iff_eq_add.mpr (parts N)

private theorem product_limit :
    Tendsto (fun n : ℕ => Real.log (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) / (n : ℝ)) atTop (𝓝 C) := by
  let F : ℕ → ℕ → ℝ := fun n j => ((n / (j + 2) : ℕ) : ℝ) / (n : ℝ) * inc j
  have hp (j : ℕ) : Tendsto (fun n => F n j) atTop (𝓝 (inc j / ((j : ℝ) + 2))) := by
    have h := (D5.S3.ArithSums.A400361PillaiMean.quotient_ratio_limit (j + 2)).mul_const (inc j)
    convert h using 1
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hb : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ‖F n j‖ ≤ 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn j
    have hnR : 0 < (n : ℝ) := by exact Nat.cast_pos'.mpr hn
    have hq : ((n / (j + 2) : ℕ) : ℝ) * ((j : ℝ) + 2) ≤ (n : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self n (j + 2)
    have hr : ((n / (j + 2) : ℕ) : ℝ) / (n : ℝ) ≤ 1 / ((j : ℝ) + 2) := by
      apply (div_le_div_iff₀ hnR (by positivity)).mpr
      simpa using hq
    have hi := (inc_bounds j).1
    dsimp [F]
    rw [abs_of_nonneg (by positivity : 0 ≤ ((n / (j + 2) : ℕ) : ℝ) / (n : ℝ) * inc j)]
    calc
      _ ≤ (1 / ((j : ℝ) + 2)) * (1 / ((j : ℝ) + 1)) :=
        mul_le_mul hr (inc_bounds j).2 (inc_bounds j).1 (by positivity)
      _ = _ := by simp only [one_div, mul_inv_rev]
  have ht := tendsto_tsum_of_dominated_convergence
    D5.S3.ArithSums.A400361PillaiMean.hasSum_kernel_one.summable hp hb
  have hf (n : ℕ) : (∑' j : ℕ, F n j) = Real.log (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) / (n : ℝ) := by
    rw [tsum_eq_sum (s := range n)]
    · rw [log_product, sum_div]
      exact sum_congr rfl (fun j _ => by dsimp [F]; ring)
    · intro j hj
      have hnj : n < j + 2 := by simp only [mem_range, not_lt] at hj; omega
      simp [F, Nat.div_eq_of_lt hnj]
  simpa only [hf, C] using ht

private theorem correction_zero :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  have ht := log_ratio_zero.mul hr
  simp only [zero_mul] at ht
  convert ht using 1
  funext n
  have hn1 : (n : ℝ) + 1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
  field_simp

private theorem logarithmic_limit :
    Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)) atTop (𝓝 C) := by
  have hl : ∀ᶠ n : ℕ in atTop,
      Real.log (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) / (n : ℝ) ≤ Real.log (a n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by exact Nat.zero_lt_of_lt hn
    have hP : 0 < (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) := by exact_mod_cast prefix_pos n n le_rfl
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log hP (by exact_mod_cast (sandwich n hnpos).1)
  have hu : ∀ᶠ n : ℕ in atTop,
      Real.log (a n : ℝ) / (n : ℝ) ≤ Real.log (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) / (n : ℝ) +
        Real.log ((n : ℝ) + 1) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by exact Nat.zero_lt_of_lt hn
    have hP : 0 < (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) := by exact_mod_cast prefix_pos n n le_rfl
    have ha : 0 < (a n : ℝ) := lt_of_lt_of_le hP (by exact_mod_cast (sandwich n hnpos).1)
    have hle : (a n : ℝ) ≤ ((n : ℝ) + 1) * (D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct (fun k => n / (k + 1)) n : ℝ) := by
      exact_mod_cast (sandwich n hnpos).2
    have h := Real.log_le_log ha hle
    rw [Real.log_mul (by positivity) hP.ne'] at h
    have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
    simpa only [add_div, add_comm] using hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' product_limit
    (by simpa only [add_zero] using product_limit.add correction_zero) hl hu

theorem result : D5.S3.ArithSums.HannaA075885FloorGrowth.claim := by
  refine ⟨Real.exp C, Real.exp_pos C, ?_, ?_⟩
  · simpa only [Real.log_exp] using source_hasSum
  · have ht := (Real.continuous_exp.tendsto C).comp
      (logarithmic_limit.comp (tendsto_add_atTop_nat 1))
    convert ht using 1
    funext n
    have ha : 0 < (a (n + 1) : ℝ) := by
      have : 0 < a (n + 1) := by unfold a; omega
      exact_mod_cast this
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos ha]
    congr 1
    push_cast
    ring


end D5.S3.ArithSums.HannaA075885FloorGrowth
