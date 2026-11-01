/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Frequency-weighted columns and opposite-sign moments of the original Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent

/-! Frequency weighting and the opposite inverse of the original complex l2 operator. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianWeightedResolvent

open OriginalGaussianMatrix OriginalGaussianResolvent
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

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

lemma original_coordinate_anticommutator (r : ℝ) (n m : ℕ) :
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

lemma column_pair_normalization {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
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

lemma operator_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
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
        have hrec := OriginalGaussianMatrix.centralWeight_step n
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

lemma weighted_column_pair {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
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


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianWeightedResolvent
