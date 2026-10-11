/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual occurring words determine weighted pressure and its rate zero. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
import Mathlib.Analysis.Subadditive
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure

open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open Filter Topology
open scoped ENNReal

/-- Each actual occurring word is indexed once, without a choice of occurrence. -/
abbrev OccurringWord (X : Set (ℤ → CuLetter)) :=
  {w : List CuLetter // ∃ ω ∈ X, Occurs ω w}

/-- The literal length-k language, including the empty word at length zero. -/
abbrev LengthDictionary (X : Set (ℤ → CuLetter)) (k : ℕ) :=
  {w : List CuLetter // (∃ ω ∈ X, Occurs ω w) ∧ w.length = k}

instance lengthDictionary_finite (X : Set (ℤ → CuLetter)) (k : ℕ) :
    Finite (LengthDictionary X k) := by
  let f : LengthDictionary X k → (Fin k → CuLetter) :=
    fun w i => w.val[i.val]'(by rw [w.property.2]; exact i.isLt)
  apply Finite.of_injective f
  intro w v he
  apply Subtype.ext
  apply List.ext_getElem
  · exact w.property.2.trans v.property.2.symm
  · intro i hi hj
    exact congrFun he ⟨i, by simpa [w.property.2] using hi⟩

instance lengthDictionary_fintype (X : Set (ℤ → CuLetter)) (k : ℕ) :
    Fintype (LengthDictionary X k) := Fintype.ofFinite _

theorem length_dictionary_nonempty (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (k : ℕ) : Nonempty (LengthDictionary X k) := by
  rcases occupied with ⟨ω, hω⟩
  refine ⟨⟨List.ofFn (fun i : Fin k => ω (i : ℕ)), ?_, List.length_ofFn⟩⟩
  refine ⟨ω, hω, 0, ?_⟩
  intro i
  simp

/-- The binary monomial uses the original twenty/six weight. -/
def wordTerm (θ : ℝ) (w : List CuLetter) : ℝ :=
  ((2 : ℝ) ^ (-θ)) ^ wordWeight w

def partitionSum (X : Set (ℤ → CuLetter)) (k : ℕ) (θ : ℝ) : ℝ :=
  ∑ w : LengthDictionary X k, wordTerm θ w.val

def logPartition (X : Set (ℤ → CuLetter)) (θ : ℝ) (k : ℕ) : ℝ :=
  Real.logb 2 (partitionSum X k θ)

/-- Infimum over every positive letter length. The zero-length quotient is not
an index of this infimum. -/
def pressure (X : Set (ℤ → CuLetter)) (θ : ℝ) : ℝ :=
  sInf ((fun k : ℕ => logPartition X θ k / (k : ℝ)) '' Set.Ici 1)

private theorem wordTerm_pos (θ : ℝ) (w : List CuLetter) : 0 < wordTerm θ w :=
  pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _

theorem partition_positive (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (k : ℕ) (θ : ℝ) : 0 < partitionSum X k θ := by
  classical
  let := length_dictionary_nonempty X occupied k
  exact Finset.sum_pos (fun _ _ => wordTerm_pos θ _) Finset.univ_nonempty

private theorem occurs_take_drop {ω : ℤ → CuLetter} {w : List CuLetter}
    (h : Occurs ω w) (k : ℕ) : Occurs ω (w.take k) ∧ Occurs ω (w.drop k) := by
  rcases h with ⟨i, hi⟩
  constructor
  · refine ⟨i, ?_⟩
    intro q
    have bound : q.val < w.length := by
      have := q.isLt
      simp only [List.length_take] at this
      omega
    simpa using hi ⟨q.val, bound⟩
  · refine ⟨i + (k : ℤ), ?_⟩
    intro q
    have bound : k + q.val < w.length := by
      have := q.isLt
      simp only [List.length_drop] at this
      omega
    simpa [List.getElem_drop, Nat.cast_add, add_assoc] using hi ⟨k + q.val, bound⟩

/-- Splitting an occurring word keeps the same bilateral realization. -/
def splitWord (X : Set (ℤ → CuLetter)) (k j : ℕ)
    (w : LengthDictionary X (k + j)) : LengthDictionary X k × LengthDictionary X j :=
  (⟨w.val.take k, by
      rcases w.property.1 with ⟨ω, hω, hw⟩
      exact ⟨ω, hω, (occurs_take_drop hw k).1⟩,
      by simp [w.property.2]⟩,
   ⟨w.val.drop k, by
      rcases w.property.1 with ⟨ω, hω, hw⟩
      exact ⟨ω, hω, (occurs_take_drop hw k).2⟩,
      by simp [w.property.2]⟩)

theorem split_word_injective (X : Set (ℤ → CuLetter)) (k j : ℕ) :
    Function.Injective (splitWord X k j) := by
  intro w v h
  apply Subtype.ext
  have first := congrArg (fun x => x.1.val) h
  have last := congrArg (fun x => x.2.val) h
  calc
    w.val = w.val.take k ++ w.val.drop k := (List.take_append_drop k w.val).symm
    _ = v.val.take k ++ v.val.drop k := congrArg₂ List.append first last
    _ = v.val := List.take_append_drop k v.val

theorem partition_submultiplicative (X : Set (ℤ → CuLetter)) (k j : ℕ) (θ : ℝ) :
    partitionSum X (k + j) θ ≤ partitionSum X k θ * partitionSum X j θ := by
  classical
  have terms (w : LengthDictionary X (k + j)) :
      wordTerm θ w.val = wordTerm θ (splitWord X k j w).1.val *
        wordTerm θ (splitWord X k j w).2.val := by
    simp only [wordTerm, splitWord]
    rw [← pow_add, ← word_weight_geometry.1, List.take_append_drop]
  calc
    _ = ∑ w : LengthDictionary X (k + j),
        wordTerm θ (splitWord X k j w).1.val * wordTerm θ (splitWord X k j w).2.val :=
      Finset.sum_congr rfl (fun w _ => terms w)
    _ ≤ ∑ p : LengthDictionary X k × LengthDictionary X j,
        wordTerm θ p.1.val * wordTerm θ p.2.val := by
      rw [← Finset.sum_image (f := fun p : LengthDictionary X k × LengthDictionary X j =>
        wordTerm θ p.1.val * wordTerm θ p.2.val)
        (fun w _ v _ h => split_word_injective X k j h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun p _ _ => (mul_pos (wordTerm_pos θ _) (wordTerm_pos θ _)).le)
    _ = _ := by
      rw [Fintype.sum_prod_type, partitionSum, partitionSum, Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem log_partition_subadditive (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) : Subadditive (logPartition X θ) := by
  intro k j
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (partition_positive X occupied (k+j) θ) (partition_submultiplicative X k j θ)
  simpa [logPartition, Real.logb_mul (partition_positive X occupied k θ).ne'
    (partition_positive X occupied j θ).ne'] using h

private theorem wordTerm_rpow (θ : ℝ) (w : List CuLetter) :
    wordTerm θ w = (2 : ℝ) ^ (-θ * (wordWeight w : ℝ)) := by
  exact (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (-θ) _).symm

/-- A lower bound uniform in the language and length, for every real exponent. -/
theorem partition_lower_bound (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (k : ℕ) (θ : ℝ) :
    (2 : ℝ) ^ (-20 * |θ| * (k : ℝ)) ≤ partitionSum X k θ := by
  classical
  let w : LengthDictionary X k := Classical.choice (length_dictionary_nonempty X occupied k)
  have upper : (wordWeight w.val : ℝ) ≤ 20 * (k : ℝ) := by
    exact_mod_cast ((InteriorRoot.word_weight_bounds w.val).2.trans_eq
      (congrArg (20 * ·) w.property.2))
  have exponent : -20 * |θ| * (k : ℝ) ≤ -θ * (wordWeight w.val : ℝ) := by
    calc
      _ ≤ -|θ| * (wordWeight w.val : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left upper (abs_nonneg θ)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (neg_le_neg (le_abs_self θ)) (by positivity)
  calc
    _ ≤ wordTerm θ w.val := by
      rw [wordTerm_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ ≤ _ := Finset.single_le_sum
      (fun (v : LengthDictionary X k) _ => (wordTerm_pos θ v.val).le)
      (Finset.mem_univ w)

/-- The same explicit lower bound covers the zero-length quotient convention. -/
theorem log_quotient_lower_bound (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) (k : ℕ) : -20 * |θ| ≤ logPartition X θ k / (k : ℝ) := by
  by_cases hk : k = 0
  · simp only [hk, Nat.cast_zero, div_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg θ)
  have kp : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos (by norm_num) _) (partition_lower_bound X occupied k θ)
  rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
  exact (le_div_iff₀ kp).mpr h

private theorem log_quotients_bddBelow (X : Set (ℤ → CuLetter))
    (occupied : X.Nonempty) (θ : ℝ) :
    BddBelow (Set.range (fun k : ℕ => logPartition X θ k / (k : ℝ))) := by
  refine ⟨-20 * |θ|, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact log_quotient_lower_bound X occupied θ k

/-- Actual logarithmic partitions converge to the infimum over all k≥1. -/
theorem pressure_tendsto (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ) :
    Tendsto (fun k : ℕ => logPartition X θ k / (k : ℝ)) atTop (𝓝 (pressure X θ)) := by
  simpa only [Subadditive.lim, pressure] using
    (log_partition_subadditive X occupied θ).tendsto_lim
    (log_quotients_bddBelow X occupied θ)

/-- The literal twenty/six constants compare the whole finite partition. -/
theorem partition_shift_bounds (X : Set (ℤ → CuLetter)) (k : ℕ) (θ a : ℝ)
    (nonnegative : 0 ≤ a) :
    (2 : ℝ) ^ (-20 * a * (k : ℝ)) * partitionSum X k θ ≤ partitionSum X k (θ+a) ∧
    partitionSum X k (θ+a) ≤ (2 : ℝ) ^ (-6 * a * (k : ℝ)) * partitionSum X k θ := by
  classical
  have bounds (w : LengthDictionary X k) :
      (2 : ℝ) ^ (-20 * a * (k : ℝ)) * wordTerm θ w.val ≤ wordTerm (θ+a) w.val ∧
      wordTerm (θ+a) w.val ≤ (2 : ℝ) ^ (-6 * a * (k : ℝ)) * wordTerm θ w.val := by
    have low : 6 * (k : ℝ) ≤ (wordWeight w.val : ℝ) := by
      exact_mod_cast (by simpa [w.property.2] using
        (InteriorRoot.word_weight_bounds w.val).1)
    have high : (wordWeight w.val : ℝ) ≤ 20 * (k : ℝ) := by
      exact_mod_cast (by simpa [w.property.2] using
        (InteriorRoot.word_weight_bounds w.val).2)
    simp only [wordTerm_rpow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left high nonnegative]
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left low nonnegative]
  unfold partitionSum
  rw [Finset.mul_sum, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun w _ => (bounds w).1),
    Finset.sum_le_sum (fun w _ => (bounds w).2)⟩

private theorem log_quotient_shift_bounds (X : Set (ℤ → CuLetter))
    (occupied : X.Nonempty) (θ a : ℝ) (nonnegative : 0 ≤ a) (k : ℕ) (positive : 0 < k) :
    logPartition X θ k / (k : ℝ) - 20*a ≤ logPartition X (θ+a) k / (k : ℝ) ∧
    logPartition X (θ+a) k / (k : ℝ) ≤ logPartition X θ k / (k : ℝ) - 6*a := by
  have bounds := partition_shift_bounds X k θ a nonnegative
  have lower := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (partition_positive X occupied k θ))
    bounds.1
  have upper := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (partition_positive X occupied k (θ+a)) bounds.2
  rw [Real.logb_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
    (partition_positive X occupied k θ).ne',
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at lower upper
  have kp : (0 : ℝ) < (k : ℝ) := by exact_mod_cast positive
  constructor
  · have h := div_le_div_of_nonneg_right lower kp.le
    change (-20*a*(k : ℝ) + logPartition X θ k) / (k : ℝ) ≤
      logPartition X (θ+a) k / (k : ℝ) at h
    have eqn : (-20*a*(k : ℝ) + logPartition X θ k) / (k : ℝ) =
        logPartition X θ k / (k : ℝ) - 20*a := by
      field_simp
      ring
    rwa [eqn] at h
  · have h := div_le_div_of_nonneg_right upper kp.le
    change logPartition X (θ+a) k / (k : ℝ) ≤
      (-6*a*(k : ℝ) + logPartition X θ k) / (k : ℝ) at h
    have eqn : (-6*a*(k : ℝ) + logPartition X θ k) / (k : ℝ) =
        logPartition X θ k / (k : ℝ) - 6*a := by
      field_simp
      ring
    rwa [eqn] at h

theorem pressure_shift_bounds (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ a : ℝ) (nonnegative : 0 ≤ a) :
    pressure X θ - 20*a ≤ pressure X (θ+a) ∧
    pressure X (θ+a) ≤ pressure X θ - 6*a := by
  have left := (pressure_tendsto X occupied θ).sub_const (20*a)
  have right := (pressure_tendsto X occupied θ).sub_const (6*a)
  refine ⟨le_of_tendsto_of_tendsto left (pressure_tendsto X occupied (θ+a)) ?_,
    le_of_tendsto_of_tendsto (pressure_tendsto X occupied (θ+a)) right ?_⟩
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact (log_quotient_shift_bounds X occupied θ a nonnegative k (by omega)).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact (log_quotient_shift_bounds X occupied θ a nonnegative k (by omega)).2

theorem pressure_lipschitz (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) :
    LipschitzWith 20 (pressure X) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ φ
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  wlog h : θ ≤ φ generalizing θ φ
  · simpa [abs_sub_comm] using this φ θ (le_of_not_ge h)
  have bounds := pressure_shift_bounds X occupied θ (φ-θ) (sub_nonneg.mpr h)
  rw [add_sub_cancel] at bounds
  rw [abs_of_nonpos (sub_nonpos.mpr h)]
  apply abs_le.mpr
  constructor <;> linarith [bounds.1, bounds.2]

theorem pressure_strictAnti (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) :
    StrictAnti (pressure X) := by
  intro θ φ h
  have bounds := (pressure_shift_bounds X occupied θ (φ-θ) (sub_nonneg.mpr h.le)).2
  rw [add_sub_cancel] at bounds
  linarith

theorem pressure_zero_nonneg (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) :
    0 ≤ pressure X 0 := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (pressure_tendsto X occupied 0)
  filter_upwards [] with k
  simpa using log_quotient_lower_bound X occupied 0 k

/-- The zero exists even when the language has zero entropy. -/
theorem pressure_unique_zero (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) :
    ∃! η : ℝ, 0 ≤ η ∧ pressure X η = 0 := by
  have p0 := pressure_zero_nonneg X occupied
  let b := (pressure X 0 + 1) / 6
  have bp : 0 < b := by dsimp [b]; linarith
  have pb : pressure X b ≤ 0 := by
    have upper := (pressure_shift_bounds X occupied 0 b bp.le).2
    dsimp [b] at *
    norm_num at upper
    linarith
  rcases intermediate_value_Icc' bp.le (pressure_lipschitz X occupied).continuous.continuousOn
    ⟨pb, p0⟩ with ⟨η, hη, hz⟩
  refine ⟨η, ⟨hη.1, hz⟩, ?_⟩
  intro η' hη'
  exact (pressure_strictAnti X occupied).injective (hη'.2.trans hz.symm)

private def lengthFiberEquiv (X : Set (ℤ → CuLetter)) (k : ℕ) :
    {w : OccurringWord X // w.val.length = k} ≃ LengthDictionary X k where
  toFun w := ⟨w.val.val, w.val.property, w.property⟩
  invFun w := ⟨⟨w.val, w.property.1⟩, w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def weightFiberEquiv (X : Set (ℤ → CuLetter)) (T : ℕ) :
    {w : OccurringWord X // wordWeight w.val = T} ≃ FactorDictionary X T where
  toFun w := ⟨w.val.val, w.val.property, w.property⟩
  invFun w := ⟨⟨w.val, w.property.1⟩, w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The same nonnegative whole series, including infinity, is partitioned by
letter length or by the original weight. Neither an occurrence position nor a
graph path is part of its index. -/
theorem whole_series_regrouping (X : Set (ℤ → CuLetter)) (θ : ℝ) :
    ((∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) =
      ∑' k : ℕ, ENNReal.ofReal (partitionSum X k θ)) ∧
    ((∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) =
      ∑' T : ℕ, ENNReal.ofReal
        ((factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T)) := by
  classical
  have lengthSum (k : ℕ) :
      (∑' w : {w : OccurringWord X // w.val.length = k},
        ENNReal.ofReal (wordTerm θ w.val.val)) = ENNReal.ofReal (partitionSum X k θ) := by
    change (∑' w, ENNReal.ofReal (wordTerm θ ((lengthFiberEquiv X k) w).val)) = _
    rw [(lengthFiberEquiv X k).tsum_eq
      (fun w : LengthDictionary X k => ENNReal.ofReal (wordTerm θ w.val)), tsum_fintype]
    exact (ENNReal.ofReal_sum_of_nonneg
      (fun (w : LengthDictionary X k) _ => (wordTerm_pos θ w.val).le)).symm
  have weightSum (T : ℕ) :
      (∑' w : {w : OccurringWord X // wordWeight w.val = T},
        ENNReal.ofReal (wordTerm θ w.val.val)) = ENNReal.ofReal
        ((factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T) := by
    let : Finite (FactorDictionary X T) := (factor_dictionary_bound X T).1
    let : Fintype (FactorDictionary X T) := Fintype.ofFinite _
    change (∑' w, ENNReal.ofReal (wordTerm θ ((weightFiberEquiv X T) w).val)) = _
    rw [(weightFiberEquiv X T).tsum_eq
      (fun w : FactorDictionary X T => ENNReal.ofReal (wordTerm θ w.val)), tsum_fintype]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun (w : FactorDictionary X T) _ => (wordTerm_pos θ w.val).le)]
    congr 1
    have terms (w : FactorDictionary X T) :
        wordTerm θ w.val = ((2 : ℝ) ^ (-θ)) ^ T := by
      simp only [wordTerm, w.property.2]
    simp only [terms, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      factorCount, Nat.card_eq_fintype_card]
  have byLength := ENNReal.tsum_fiberwise
    (fun w : OccurringWord X => ENNReal.ofReal (wordTerm θ w.val))
    (fun w => w.val.length)
  have byWeight := ENNReal.tsum_fiberwise
    (fun w : OccurringWord X => ENNReal.ofReal (wordTerm θ w.val))
    (fun w => wordWeight w.val)
  exact ⟨byLength.symm.trans (tsum_congr lengthSum),
    byWeight.symm.trans (tsum_congr weightSum)⟩

/-- Finiteness, rather than automatic ENNReal summability, is equivalent to
real summability in each regrouping. -/
theorem whole_series_finiteness (X : Set (ℤ → CuLetter)) (θ : ℝ) :
    (Summable (fun k : ℕ => partitionSum X k θ) ↔
      (∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) < ∞) ∧
    (Summable (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T) ↔
      (∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) < ∞) := by
  have partitions : ∀ k, 0 ≤ partitionSum X k θ := by
    intro k
    exact Finset.sum_nonneg (fun w _ => (wordTerm_pos θ w.val).le)
  have factors : ∀ T, 0 ≤ (factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T := by
    intro T
    positivity
  have eqn := whole_series_regrouping X θ
  constructor
  · rw [eqn.1]
    constructor
    · exact Summable.tsum_ofReal_lt_top
    · intro h
      simpa only [ENNReal.toReal_ofReal (partitions _)] using
        ENNReal.summable_toReal h.ne
  · rw [eqn.2]
    constructor
    · exact Summable.tsum_ofReal_lt_top
    · intro h
      simpa only [ENNReal.toReal_ofReal (factors _)] using
        ENNReal.summable_toReal h.ne

private theorem occurringWord_infinite (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) :
    Infinite (OccurringWord X) := by
  let f : ℕ → OccurringWord X := fun k =>
    let w := Classical.choice (length_dictionary_nonempty X occupied k)
    ⟨w.val, w.property.1⟩
  have lengths (k : ℕ) : (f k).val.length = k :=
    (Classical.choice (length_dictionary_nonempty X occupied k)).property.2
  apply Infinite.of_injective f
  intro k j h
  have eqn := congrArg (fun w : OccurringWord X => w.val.length) h
  simpa only [lengths] using eqn

/-- Nonempty languages have infinitely many actual factors. Their monomials
are at least one at every nonpositive exponent, so the whole series diverges. -/
theorem whole_series_nonpositive (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) (nonpositive : θ ≤ 0) :
    (∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) = ∞ := by
  let := occurringWord_infinite X occupied
  have lower (w : OccurringWord X) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (wordTerm θ w.val) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact one_le_pow₀ (Real.one_le_rpow (by norm_num) (neg_nonneg.mpr nonpositive))
  apply top_unique
  calc
    ∞ = ∑' _ : OccurringWord X, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num : (1 : ℝ≥0∞) ≠ 0)).symm
    _ ≤ _ := ENNReal.tsum_le_tsum lower

private theorem summable_exponent_positive (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) (converges : Summable
      (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T)) : 0 < θ := by
  by_contra h
  have finite := (whole_series_finiteness X θ).2.mp converges
  rw [whole_series_nonpositive X occupied θ (le_of_not_gt h)] at finite
  exact (lt_irrefl _) finite

/-- Negative pressure supplies an eventual geometric majorant. -/
theorem negative_pressure_summable (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) (negative : pressure X θ < 0) :
    Summable (fun k : ℕ => partitionSum X k θ) := by
  let b := pressure X θ / 2
  have above : pressure X θ < b := by dsimp [b]; linarith
  have bn : b < 0 := by dsimp [b]; linarith
  have eventual : ∀ᶠ k : ℕ in atTop, logPartition X θ k / (k : ℝ) < b :=
    (pressure_tendsto X occupied θ).eventually (gt_mem_nhds above)
  have qp : 0 ≤ (2 : ℝ) ^ b := (Real.rpow_pos_of_pos (by norm_num) _).le
  have qsmall : (2 : ℝ) ^ b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) bn
  apply (summable_geometric_of_lt_one qp qsmall).of_norm_bounded_eventually_nat
  filter_upwards [eventual, eventually_ge_atTop (1 : ℕ)] with k hk hpos
  have kp : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have logs : logPartition X θ k < b * (k : ℝ) := (div_lt_iff₀ kp).mp hk
  have bound := ((Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2)
    (partition_positive X occupied k θ)).mp logs).le
  rw [Real.norm_eq_abs, abs_of_pos (partition_positive X occupied k θ)]
  simpa only [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] using bound

private theorem summable_pressure_nonpos (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) (converges : Summable (fun k : ℕ => partitionSum X k θ)) :
    pressure X θ ≤ 0 := by
  have eventual : ∀ᶠ k : ℕ in atTop, partitionSum X k θ ≤ 1 :=
    (converges.tendsto_atTop_zero.eventually (eventually_lt_nhds
      (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  apply le_of_tendsto (pressure_tendsto X occupied θ)
  filter_upwards [eventual] with k hk
  apply div_nonpos_of_nonpos_of_nonneg
  · exact Real.logb_nonpos (by norm_num) (partition_positive X occupied k θ).le hk
  · positivity

/-- The unique pressure zero is the very same sparse, max-one weighted factor
rate. This statement makes no assertion about summability at that zero. -/
theorem pressure_zero_iff_rate (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ) :
    pressure X θ = 0 ↔ θ = weightedFactorRate X := by
  obtain ⟨η, hη, _⟩ := pressure_unique_zero X occupied
  have bridge (s : ℝ) : Summable (fun k : ℕ => partitionSum X k s) ↔
      Summable (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-s)) ^ T) :=
    (whole_series_finiteness X s).1.trans (whole_series_finiteness X s).2.symm
  have lower : η ≤ weightedFactorRate X := by
    by_contra h
    obtain ⟨s, above, below⟩ := exists_between (lt_of_not_ge h)
    have sp : 0 < s := (factor_rate_nonneg X).trans_lt above
    have converges := (factor_rate_convergence X s sp).1 above
    have ps := summable_pressure_nonpos X occupied s ((bridge s).mpr converges)
    have strict := pressure_strictAnti X occupied below
    rw [hη.2] at strict
    linarith
  have upper : weightedFactorRate X ≤ η := by
    by_contra h
    obtain ⟨s, above, below⟩ := exists_between (lt_of_not_ge h)
    have strict := pressure_strictAnti X occupied above
    rw [hη.2] at strict
    have converges := (bridge s).mp (negative_pressure_summable X occupied s strict)
    have sp := summable_exponent_positive X occupied s converges
    have rate := (factor_rate_convergence X s sp).2 converges
    linarith
  have rate : η = weightedFactorRate X := le_antisymm lower upper
  constructor
  · intro h
    exact ((pressure_strictAnti X occupied).injective (h.trans hη.2.symm)).trans rate
  · intro h
    rw [h, ← rate]
    exact hη.2

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
