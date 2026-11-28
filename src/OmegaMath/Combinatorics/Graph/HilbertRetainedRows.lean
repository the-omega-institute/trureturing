import OmegaMath.Combinatorics.Graph.HilbertWeightedEnergy
import OmegaMath.Combinatorics.Graph.HilbertPairCharges
import Mathlib.Data.Finset.Powerset

/-! # Finite retained-curl rows

The insertion rows of C39 (17) are reduced to a finite scalar envelope.
The only old-clique input is the combined credit from (20) and (21).
All mixtures, including mixtures with zero vertex weights, are covered.
-/

compile_only_with_mathlib

open scoped BigOperators
open HilbertWeightedEnergy

namespace HilbertRetainedRows

noncomputable section

variable {ι κ E : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalized weight assigned by one nonempty subset row. -/
def rowWeight (W : Finset ι) (i : ι) : ℝ :=
  if i ∈ W then 1 / (W.card : ℝ) else 0

/-- Vertex marginals of a mixture of normalized subset rows. -/
def vertexWeight (W : κ → Finset ι) (w : κ → ℝ) (i : ι) : ℝ :=
  ∑ a, w a * rowWeight (W a) i

/-- Off-diagonal pair marginals of the same mixture. -/
def pairWeight (W : κ → Finset ι) (w : κ → ℝ) (i j : ι) : ℝ :=
  if i = j then 0 else ∑ a, if i ∈ W a ∧ j ∈ W a then w a / (W a).card else 0

/-- A sum on unordered pairs contained in a specified subset. -/
def subsetPairs (W : Finset ι) (f : ι → ι → ℝ) : ℝ :=
  sortedPairSum (fun i j => if i ∈ W ∧ j ∈ W then f i j else 0)

/-- The fixed offset in the normalized version of (17). -/
def rowOffset (W : Finset ι) (r beta : ℝ) (y : ι → ι → E) : ℝ :=
  -r + beta / W.card * subsetPairs W (fun i j => 1 - ‖y i j‖ ^ 2)

/-- The unordered second elementary symmetric polynomial. -/
def pairMass (p : ι → ℝ) : ℝ := sortedPairSum (fun i j => p i * p j)

/-- Old edge deficits, counted once per edge. -/
def deficit (p : ι → ℝ) (r : ℝ) (x : ι → ι → E) : ℝ :=
  sortedPairSum (fun i j => p i * p j * (r - ‖x i j‖ ^ 2))

/-- The old triangle curl energy, counted once per triangle. -/
def triangleEnergy (p : ι → ℝ) (x : ι → ι → E) : ℝ :=
  sortedTripleSum (fun i j k => p i * p j * p k * ‖curl x i j k‖ ^ 2)

lemma rowWeight_sum (W : Finset ι) (hW : W.Nonempty) : ∑ i, rowWeight W i = 1 := by
  have hn : (W.card : ℝ) ≠ 0 := by exact_mod_cast hW.card_ne_zero
  simp [rowWeight, hn]

omit [Fintype ι] in
lemma vertexWeight_nonneg (W : κ → Finset ι) (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (i : ι) : 0 ≤ vertexWeight W w i := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (hw a) (by unfold rowWeight; split_ifs <;> positivity)

lemma vertexWeight_sum (W : κ → Finset ι) (hW : ∀ a, (W a).Nonempty)
    (w : κ → ℝ) (hw : ∑ a, w a = 1) : ∑ i, vertexWeight W w i = 1 := by
  unfold vertexWeight
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, rowWeight_sum _ (hW _), mul_one]
  exact hw

omit [Fintype ι] in
lemma pairWeight_symm (W : κ → Finset ι) (w : κ → ℝ) (i j : ι) :
    pairWeight W w i j = pairWeight W w j i := by
  simp only [pairWeight, eq_comm, and_comm]

omit [Fintype ι] in
lemma pairWeight_diag (W : κ → Finset ι) (w : κ → ℝ) (i : ι) :
    pairWeight W w i i = 0 := by simp [pairWeight]

omit [Fintype ι] in
lemma pairWeight_nonneg (W : κ → Finset ι) (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (i j : ι) : 0 ≤ pairWeight W w i j := by
  unfold pairWeight
  split_ifs
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact div_nonneg (hw a) (Nat.cast_nonneg _)
    · exact le_rfl

omit [Fintype ι] in
lemma pairWeight_le_vertex (W : κ → Finset ι) (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (i j : ι) : pairWeight W w i j ≤ vertexWeight W w i := by
  unfold pairWeight
  split_ifs
  · exact vertexWeight_nonneg W w hw i
  · apply Finset.sum_le_sum
    intro a _
    unfold rowWeight
    by_cases hi : i ∈ W a
    · by_cases hj : j ∈ W a
      · simp [hi, hj, div_eq_mul_inv]
      · simp only [hi, hj, and_false, ite_false, ite_true]
        exact mul_nonneg (hw a) (by positivity)
    · simp [hi]

/-- The degree bound in (18), with arbitrary finite row supports. -/
theorem pairWeight_degree (s : ℕ) (W : κ → Finset ι)
    (hW : ∀ a, (W a).Nonempty) (hsize : ∀ a, (W a).card ≤ s - 1)
    (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a) (i : ι) :
    (∑ j, pairWeight W w j i) ≤ (s - 2 : ℕ) * vertexWeight W w i := by
  have hexp (j : ι) : pairWeight W w j i =
      ∑ a, if i ∈ W a ∧ j ∈ (W a).erase i then w a / (W a).card else 0 := by
    unfold pairWeight
    by_cases hji : j = i
    · subst j; simp
    · simp [hji, Finset.mem_erase, and_comm]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  unfold vertexWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases hi : i ∈ W a
  · have hn : (W a).card - 1 ≤ s - 2 := by
      have := (hW a).card_pos
      have := hsize a
      omega
    have he : ((W a).erase i).card ≤ s - 2 := by
      simpa only [Finset.card_erase_of_mem hi] using hn
    simp only [hi, true_and, rowWeight, ite_true]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have he' : (((W a).erase i).card : ℝ) ≤ (s - 2 : ℕ) := by exact_mod_cast he
    have hh := mul_le_mul_of_nonneg_right he' (div_nonneg (hw a) (Nat.cast_nonneg (W a).card))
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hh
  · simp [hi, rowWeight]

lemma pairMass_eq (p : ι → ℝ) (hp : ∑ i, p i = 1) :
    pairMass p = (1 - ∑ i, p i ^ 2) / 2 := by
  have hh := ordered_pair_eq_two_sorted (fun i j => if i = j then 0 else p i * p j)
    (by intro i j; simp only [eq_comm]; split_ifs <;> ring) (by intro i; simp)
  have he : (∑ i, ∑ j, if i = j then 0 else p i * p j) = 1 - ∑ i, p i ^ 2 := by
    have ht (i : ι) : (∑ j, if i = j then 0 else p i * p j) = p i - p i ^ 2 := by
      have he (j : ι) : (if i = j then 0 else p i * p j) =
          p i * p j - if i = j then p i ^ 2 else 0 := by
        split_ifs with h
        · subst j; ring
        · ring
      simp_rw [he, Finset.sum_sub_distrib]
      simp [← Finset.mul_sum, hp]
    simp_rw [ht, Finset.sum_sub_distrib, hp]
  have hs : sortedPairSum (fun i j => if i = j then 0 else p i * p j) = pairMass p := by
    unfold sortedPairSum pairMass
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij, ne_of_lt hij]
    · simp [hij]
  rw [he, hs] at hh
  linarith

omit [InnerProductSpace ℝ E] in
/-- Mixture offsets in (18), with no assumption on the signs of the curls. -/
theorem offset_mixture (W : κ → Finset ι) (w : κ → ℝ) (hw : ∑ a, w a = 1)
    (r beta : ℝ) (y : ι → ι → E) :
    (∑ a, w a * rowOffset (W a) r beta y) = -r + beta *
      sortedPairSum (fun i j => pairWeight W w i j * (1 - ‖y i j‖ ^ 2)) := by
  have he (i j : ι) (hij : i < j) : pairWeight W w i j * (1 - ‖y i j‖ ^ 2) =
      ∑ a, w a / (W a).card *
        (if i ∈ W a ∧ j ∈ W a then 1 - ‖y i j‖ ^ 2 else 0) := by
    simp only [pairWeight, ne_of_lt hij, ite_false, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  simp only [rowOffset, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  congr 1
  unfold subsetPairs sortedPairSum
  simp only [Finset.mul_sum]
  calc
    _ = ∑ a, ∑ i, ∑ j, if i < j then
        beta * (w a / (W a).card *
          (if i ∈ W a ∧ j ∈ W a then 1 - ‖y i j‖ ^ 2 else 0)) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ = ∑ i, ∑ j, ∑ a, if i < j then
        beta * (w a / (W a).card *
          (if i ∈ W a ∧ j ∈ W a then 1 - ‖y i j‖ ^ 2 else 0)) else 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j
      · simp only [hij, ite_true, ← Finset.mul_sum, ← he i j hij]
      · simp [hij]

/-- Young's inequality with the two coefficients used by retained-curl insertion. -/
theorem young_norm_sub (mu : ℝ) (hmu : 0 < mu) (x y : E) :
    ‖x - y‖ ^ 2 ≤ (1 + mu) * ‖x‖ ^ 2 + (1 + 1 / mu) * ‖y‖ ^ 2 := by
  let a := 1 / (1 + mu)
  let b := mu / (1 + mu)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a + b = 1 := by dsimp [a, b]; field_simp
  have hh := young_gap x y a b hab ha.ne' hb.ne'
  have hn := div_nonneg (sq_nonneg ‖b • x + a • y‖) (mul_nonneg ha.le hb.le)
  have hx : ‖x‖ ^ 2 / a = (1 + mu) * ‖x‖ ^ 2 := by simp [a, mul_comm]
  have hy : ‖y‖ ^ 2 / b = (1 + 1 / mu) * ‖y‖ ^ 2 := by
    dsimp [b]
    field_simp
    ring
  rw [hx, hy] at hh
  linarith

/-- The Hodge--Young reduction (19), before substituting edge deficits.
Only skewness, nonnegative weights of total one, and equality of curls are used. -/
theorem hodge_young (p : ι → ℝ) (hp₀ : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (x y : ι → ι → E)
    (hx : ∀ i j, x j i = -x i j) (hy : ∀ i j, y j i = -y i j)
    (hcurl : ∀ i j k, curl x i j k = curl y i j k)
    (mu : ℝ) (hmu : 0 < mu) :
    meanEnergy p (fun i j => x i j - y i j) ≤
      (1 + mu) * (sortedPairSum (fun i j => p i * p j * ‖x i j‖ ^ 2) -
        (1 + 1 / mu) * sortedTripleSum
          (fun i j k => p i * p j * p k * ‖curl x i j k‖ ^ 2)) +
      (1 + 1 / mu) * sortedPairSum (fun i j => p i * p j * ‖y i j‖ ^ 2) := by
  have hm : meanEnergy p (fun i j => x i j - y i j) ≤
      (1 + mu) * meanEnergy p x + (1 + 1 / mu) * meanEnergy p y := by
    unfold meanEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hr : rowMean p (fun i j => x i j - y i j) i = rowMean p x i - rowMean p y i := by
      simp [rowMean, smul_sub, Finset.sum_sub_distrib]
    rw [hr]
    have hh := mul_le_mul_of_nonneg_left (young_norm_sub mu hmu (rowMean p x i)
      (rowMean p y i)) (hp₀ i)
    nlinarith only [hh]
  have hX := hodge_sorted p hp x hx
  have hY := hodge_sorted p hp y hy
  simp_rw [← hcurl] at hY
  have hxe : meanEnergy p x = sortedPairSum (fun i j => p i * p j * ‖x i j‖ ^ 2) -
      sortedTripleSum (fun i j k => p i * p j * p k * ‖curl x i j k‖ ^ 2) := by linarith
  have hye : meanEnergy p y = sortedPairSum (fun i j => p i * p j * ‖y i j‖ ^ 2) -
      sortedTripleSum (fun i j k => p i * p j * p k * ‖curl x i j k‖ ^ 2) := by linarith
  rw [hxe, hye] at hm
  convert hm using 1
  field_simp
  ring

omit [LinearOrder ι] in
/-- If the difference of the fields is a gradient, its mean energy is the
weighted variance of the gradient's vertex positions. -/
theorem meanEnergy_gradient (p : ι → ℝ) (hp : ∑ i, p i = 1) (v : ι → E)
    (x y : ι → ι → E) (hxy : ∀ i j, x i j - y i j = v i - v j) :
    meanEnergy p (fun i j => x i j - y i j) = FiniteHilbertJung.variance v p := by
  have hr (i : ι) : rowMean p (fun i j => x i j - y i j) i =
      v i - FiniteHilbertJung.center v p := by
    simp only [rowMean, hxy, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hp, one_smul, FiniteHilbertJung.center]
  simp only [meanEnergy, hr]
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
    FiniteHilbertJung.weighted_sq v p hp (FiniteHilbertJung.center v p)

/-- Formula (19) for the vertex variance, with arbitrary skew fields whose
difference is the given gradient. No dimension or completeness is assumed. -/
theorem variance_hodge_young (p : ι → ℝ) (hp₀ : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (v : ι → E) (x y : ι → ι → E)
    (hx : ∀ i j, x j i = -x i j) (hy : ∀ i j, y j i = -y i j)
    (hxy : ∀ i j, x i j - y i j = v i - v j) (mu : ℝ) (hmu : 0 < mu) :
    FiniteHilbertJung.variance v p ≤
      (1 + mu) * (HilbertWeightedEnergy.sortedPairSum (fun i j => p i * p j * ‖x i j‖ ^ 2) -
        (1 + 1 / mu) * HilbertWeightedEnergy.sortedTripleSum
          (fun i j k => p i * p j * p k * ‖HilbertWeightedEnergy.curl x i j k‖ ^ 2)) +
      (1 + 1 / mu) * HilbertWeightedEnergy.sortedPairSum (fun i j => p i * p j * ‖y i j‖ ^ 2) := by
  rw [← meanEnergy_gradient p hp v x y hxy]
  apply hodge_young p hp₀ hp x y hx hy _ mu hmu
  intro i j k
  have he (a b : ι) : x a b = v a - v b + y a b := (sub_eq_iff_eq_add).mp (hxy a b)
  simp only [curl, he]
  abel


/-- Equation (19), expressed using the old edge deficit and triangle energy. -/
theorem variance_le (p : ι → ℝ) (hp₀ : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (v : ι → E) (x y : ι → ι → E) (hx : ∀ i j, x j i = -x i j)
    (hy : ∀ i j, y j i = -y i j) (hxy : ∀ i j, x i j - y i j = v i - v j)
    (r mu : ℝ) (hmu : 0 < mu) :
    FiniteHilbertJung.variance v p ≤
      (1 + mu) * (r * pairMass p - deficit p r x -
        (1 + 1 / mu) * triangleEnergy p x) +
      (1 + 1 / mu) * sortedPairSum (fun i j => p i * p j * ‖y i j‖ ^ 2) := by
  have he : r * pairMass p - deficit p r x =
      sortedPairSum (fun i j => p i * p j * ‖x i j‖ ^ 2) := by
    unfold pairMass deficit sortedPairSum
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [he]
  exact variance_hodge_young p hp₀ hp v x y hx hy hxy mu hmu

/-- The retained-curl pair inequality preceding (22).
It allows either sign of the coefficient of the curl square. -/
private theorem retained_curl_pair {c beta pi pj x b : ℝ}
    (hc : 0 ≤ c) (hi : 0 ≤ pi) (hj : 0 ≤ pj)
    (hx : 0 ≤ x) (hxi : x ≤ pi) (hxj : x ≤ pj)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    (c * pi * pj - beta * x) * b ≤
      c * pi * pj - min beta (c * max pi pj) * x := by
  have hm : max pi pj * x ≤ pi * pj := by
    rcases le_total pi pj with h | h
    · rw [max_eq_right h]
      nlinarith [mul_le_mul_of_nonneg_left hxi hj]
    · rw [max_eq_left h]
      exact mul_le_mul_of_nonneg_left hxj hi
  have hR : 0 ≤ c * pi * pj - min beta (c * max pi pj) * x := by
    have h₁ := mul_le_mul_of_nonneg_right (min_le_right beta (c * max pi pj)) hx
    have h₂ := mul_le_mul_of_nonneg_left hm hc
    nlinarith
  have hA : c * pi * pj - beta * x ≤ c * pi * pj - min beta (c * max pi pj) * x := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left beta (c * max pi pj)) hx
    linarith
  by_cases h : c * pi * pj - beta * x ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg h hb).trans hR
  · exact (mul_le_mul_of_nonneg_left hb₁ (le_of_not_ge h)).trans (by simpa using hA)

/-- The symmetric endpoint estimate used to charge the remaining pair penalty
to vertex degrees in (18). -/
private theorem pair_penalty_le {c beta pi pj : ℝ} (hc : 0 ≤ c) :
    max (beta - c * max pi pj) 0 ≤
      (max (beta - c * pi) 0 + max (beta - c * pj) 0) / 2 := by
  have hi := mul_le_mul_of_nonneg_left (le_max_left pi pj) hc
  have hj := mul_le_mul_of_nonneg_left (le_max_right pi pj) hc
  have h₁ := max_le_max (sub_le_sub_left hi beta) (le_refl (0 : ℝ))
  have h₂ := max_le_max (sub_le_sub_left hj beta) (le_refl (0 : ℝ))
  linarith

omit [InnerProductSpace ℝ E] in
/-- The retained pair penalty, charged to endpoint degrees. -/
theorem pair_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (x : ι → ι → ℝ)
    (hx : ∀ i j, x i j = x j i) (hx₀ : ∀ i j, 0 ≤ x i j) (hz : ∀ i, x i i = 0)
    (hxp : ∀ i j, x i j ≤ p i) (d : ℝ) (hd : ∀ j, (∑ i, x i j) ≤ d * p j)
    (y : ι → ι → E) (hy : ∀ i j, ‖y i j‖ ^ 2 ≤ 1)
    (c theta : ℝ) (hc : 0 ≤ c) :
    c * sortedPairSum (fun i j => p i * p j * ‖y i j‖ ^ 2) +
        (c * theta) * sortedPairSum (fun i j => x i j * (1 - ‖y i j‖ ^ 2)) ≤
      c * pairMass p + c * d / 2 * ∑ i, p i * max (theta - p i) 0 := by
  let f := fun i => max (c * theta - c * p i) 0
  have hf (i : ι) : f i = c * max (theta - p i) 0 := by
    dsimp [f]
    by_cases h : 0 ≤ theta - p i
    · rw [max_eq_left h, max_eq_left (by nlinarith : 0 ≤ c * theta - c * p i)]
      ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_right (by nlinarith : c * theta - c * p i ≤ 0)]
      ring
  have hpoint (i j : ι) :
      (c * p i * p j - c * theta * x i j) * ‖y i j‖ ^ 2 + c * theta * x i j ≤
        c * p i * p j + x i j * (f i + f j) / 2 := by
    have h₁ := retained_curl_pair hc (hp i) (hp j) (hx₀ i j) (hxp i j)
      (by rw [hx]; exact hxp j i) (sq_nonneg ‖y i j‖) (hy i j) (beta := c * theta)
    have h₂ := mul_le_mul_of_nonneg_right
      (pair_penalty_le (beta := c * theta) (pi := p i) (pj := p j) hc) (hx₀ i j)
    have hm : c * theta - min (c * theta) (c * max (p i) (p j)) =
        max (c * theta - c * max (p i) (p j)) 0 := by
      rcases le_total (c * theta) (c * max (p i) (p j)) with h | h
      · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    dsimp [f]
    nlinarith [congrArg (fun t : ℝ => t * x i j) hm]
  have he : c * sortedPairSum (fun i j => p i * p j * ‖y i j‖ ^ 2) +
      (c * theta) * sortedPairSum (fun i j => x i j * (1 - ‖y i j‖ ^ 2)) ≤
      c * pairMass p + sortedPairSum (fun i j => x i j * (f i + f j)) / 2 := by
    unfold pairMass sortedPairSum
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i < j
    · simp only [hij, ite_true]
      nlinarith only [hpoint i j]
    · simp [hij]
  have hi : sortedPairSum (fun i j => x i j * (f i + f j)) =
      ∑ j, (∑ i, x i j) * f j := by
    unfold sortedPairSum
    rw [Finset.sum_comm]
    exact HilbertPairCharges.incidence x hx hz Finset.univ f
  have hdeg : (∑ j, (∑ i, x i j) * f j) ≤ d * ∑ j, p j * f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_right (hd j) (show 0 ≤ f j from le_max_right _ _)
    dsimp [f] at *
    nlinarith only [hh]
  rw [hi] at he
  have hf' : (∑ j, p j * f j) = c * ∑ j, p j * max (theta - p j) 0 := by
    simp_rw [hf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf'] at hdeg
  linarith

/-- The right side of (22); `oldBase` and `oldSlope` encode the combined
old-credit estimate, and `u` is the reciprocal padded cardinality. -/
def envelope (s : ℕ) (r mu theta oldBase oldSlope u : ℝ) (p : ι → ℝ) : ℝ :=
  let c := 1 + 1 / mu
  let M := (1 + mu) * r + c
  M * (1 - u) / 2 - r - oldBase - (M / 2 - oldSlope) * ((∑ i, p i ^ 2) - u) +
    c * (s - 2 : ℕ) / 2 * ∑ i, p i * max (theta - p i) 0

/-- Equations (18)--(22) for every normalized mixture. The old-credit
hypothesis is precisely (20) after substituting the lower bound (21). -/
theorem mixture_le_envelope (s : ℕ) (W : κ → Finset ι)
    (hW : ∀ a, (W a).Nonempty) (hsize : ∀ a, (W a).card ≤ s - 1)
    (w : κ → ℝ) (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (v : ι → E) (x y : ι → ι → E)
    (hx : ∀ i j, x j i = -x i j) (hy : ∀ i j, y j i = -y i j)
    (hxy : ∀ i j, x i j - y i j = v i - v j)
    (hcap : ∀ i j, ‖y i j‖ ^ 2 ≤ 1)
    (r mu theta oldBase oldSlope u : ℝ) (hmu : 0 < mu)
    (hcredit : oldBase - oldSlope * ((∑ i, vertexWeight W w i ^ 2) - u) ≤
      (1 + mu) * (deficit (vertexWeight W w) r x +
        (1 + 1 / mu) * triangleEnergy (vertexWeight W w) x)) :
    FiniteHilbertJung.variance v (vertexWeight W w) +
      (∑ a, w a * rowOffset (W a) r ((1 + 1 / mu) * theta) y) ≤
        envelope s r mu theta oldBase oldSlope u (vertexWeight W w) := by
  let p := vertexWeight W w
  have hp₀ := vertexWeight_nonneg W w hw₀
  have hp := vertexWeight_sum W hW w hw
  have hV := variance_le p hp₀ hp v x y hx hy hxy r mu hmu
  have hP := pair_bound p hp₀ (pairWeight W w) (pairWeight_symm W w)
    (pairWeight_nonneg W w hw₀) (pairWeight_diag W w)
    (pairWeight_le_vertex W w hw₀) (s - 2 : ℕ)
    (pairWeight_degree s W hW hsize w hw₀) y hcap (1 + 1 / mu) theta (by positivity)
  rw [offset_mixture W w hw, pairMass_eq p hp] at *
  unfold envelope
  dsimp only
  change oldBase - oldSlope * ((∑ i, p i ^ 2) - u) ≤ _ at hcredit
  change _ ≤ _ - _ - _ - _ * ((∑ i, p i ^ 2) - u) + _
  nlinarith only [hV, hP, hcredit]


/-- A subset of cardinality `n` contains `n(n-1)/2` unordered pairs. -/
theorem subsetPairs_one (W : Finset ι) :
    subsetPairs W (fun _ _ => 1) = (W.card : ℝ) * ((W.card : ℝ) - 1) / 2 := by
  let f := fun i j => if i ∈ W ∧ j ∈ W ∧ i ≠ j then (1 : ℝ) else 0
  have hs : ∀ i j, f j i = f i j := by
    intro i j
    simp [f, and_comm, and_left_comm, ne_comm]
  have hz : ∀ i, f i i = 0 := by intro i; simp [f]
  have he (i : ι) : (∑ j, f i j) = if i ∈ W then ((W.erase i).card : ℝ) else 0 := by
    by_cases hi : i ∈ W
    · have hj (j : ι) : f i j = if j ∈ W.erase i then (1 : ℝ) else 0 := by
        simp [f, hi, Finset.mem_erase, ne_comm, and_comm]
      simp only [hj, hi, ite_true, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    · simp [f, hi]
  have ht : (∑ i, ∑ j, f i j) = (W.card : ℝ) * ((W.card : ℝ) - 1) := by
    simp_rw [he]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    calc
      _ = ∑ i ∈ W, ((W.card : ℝ) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.card_erase_of_mem hi, Nat.cast_sub (Finset.card_pos.mpr ⟨i, hi⟩), Nat.cast_one]
      _ = _ := by simp; ring
  have hsort : sortedPairSum f = subsetPairs W (fun _ _ => 1) := by
    unfold sortedPairSum subsetPairs
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [f, hij, ne_of_lt hij]
    · simp [hij]
  have hh := ordered_pair_eq_two_sorted f hs hz
  rw [ht, hsort] at hh
  linarith

omit [InnerProductSpace ℝ E] in
lemma subsetPairs_defect (W : Finset ι) (y : ι → ι → E) :
    subsetPairs W (fun i j => 1 - ‖y i j‖ ^ 2) =
      (W.card : ℝ) * ((W.card : ℝ) - 1) / 2 -
        subsetPairs W (fun i j => ‖y i j‖ ^ 2) := by
  rw [← subsetPairs_one W]
  unfold subsetPairs sortedPairSum
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

omit [InnerProductSpace ℝ E] in
/-- Normalizing a nonempty row preserves its sign. -/
lemma row_identity (W : Finset ι) (hW : W.Nonempty) (v : ι → E) (z : E)
    (r beta : ℝ) (y : ι → ι → E) :
    (∑ i, rowWeight W i * ‖v i - z‖ ^ 2) + rowOffset W r beta y =
      ((∑ i ∈ W, ‖v i - z‖ ^ 2) - W.card * r +
        beta * subsetPairs W (fun i j => 1 - ‖y i j‖ ^ 2)) / W.card := by
  have hn : (W.card : ℝ) ≠ 0 := by exact_mod_cast hW.card_ne_zero
  simp only [rowWeight, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum,
    rowOffset]
  field_simp
  ring

/-- Application-ready insertion for any finite family of nonempty subset
rows. The old-credit and scalar hypotheses are uniform over the vertex simplex. -/
theorem exists_centers (s : ℕ) (W : κ → Finset ι)
    (hW : ∀ a, (W a).Nonempty) (hsize : ∀ a, (W a).card ≤ s - 1)
    (v : ι → E) (x y : ι → ι → E)
    (hx : ∀ i j, x j i = -x i j) (hy : ∀ i j, y j i = -y i j)
    (hxy : ∀ i j, x i j - y i j = v i - v j)
    (hcap : ∀ i j, ‖y i j‖ ^ 2 ≤ 1)
    (r mu theta oldBase oldSlope u : ℝ) (hmu : 0 < mu)
    (hcredit : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      oldBase - oldSlope * ((∑ i, p i ^ 2) - u) ≤
        (1 + mu) * (deficit p r x + (1 + 1 / mu) * triangleEnergy p x))
    (hscalar : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      envelope s r mu theta oldBase oldSlope u p ≤ 0) :
    ∃ z : E, ∀ a,
      (∑ i ∈ W a, ‖v i - z‖ ^ 2) ≤ (W a).card * r -
        ((1 + 1 / mu) * theta) * subsetPairs (W a) (fun i j => 1 - ‖y i j‖ ^ 2) := by
  obtain ⟨z, hz⟩ := QuadraticRows.averaged_minimax v (fun a => rowWeight (W a))
    (fun a => rowOffset (W a) r ((1 + 1 / mu) * theta) y)
    (fun a => rowWeight_sum (W a) (hW a)) (by
      intro w hw₀ hw
      let p := vertexWeight W w
      have hp₀ := vertexWeight_nonneg W w hw₀
      have hp := vertexWeight_sum W hW w hw
      have hb := mixture_le_envelope s W hW hsize w hw₀ hw v x y hx hy hxy hcap
        r mu theta oldBase oldSlope u hmu (hcredit p hp₀ hp)
      refine ⟨FiniteHilbertJung.center v p, ?_⟩
      rw [QuadraticRows.averaged_mixture_identity v (fun a => rowWeight (W a))
        (fun a => rowOffset (W a) r ((1 + 1 / mu) * theta) y) w hw
        (fun a => rowWeight_sum (W a) (hW a))]
      change FiniteHilbertJung.variance v p + _ +
        ‖FiniteHilbertJung.center v p - FiniteHilbertJung.center v p‖ ^ 2 ≤ 0
      rw [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      exact hb.trans (hscalar p hp₀ hp))
  refine ⟨z, fun a => ?_⟩
  have hh := hz a
  rw [row_identity (W a) (hW a)] at hh
  have hn : (0 : ℝ) < (W a).card := by exact_mod_cast (hW a).card_pos
  have hh' := (div_le_iff₀ hn).mp hh
  linarith

/-- All nonempty subsets of size at most `s-1` have one common row center.
The finite index type may be the subtype of any explicit predecessor set. -/
theorem exists_predecessor_centers {α : Type*} [LinearOrder α] (S : Finset α)
    (s : ℕ) (v : S → E) (x y : S → S → E)
    (hx : ∀ i j, x j i = -x i j) (hy : ∀ i j, y j i = -y i j)
    (hxy : ∀ i j, x i j - y i j = v i - v j)
    (hcap : ∀ i j, ‖y i j‖ ^ 2 ≤ 1)
    (r mu theta oldBase oldSlope u : ℝ) (hmu : 0 < mu)
    (hcredit : ∀ p : S → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      oldBase - oldSlope * ((∑ i, p i ^ 2) - u) ≤
        (1 + mu) * (deficit p r x + (1 + 1 / mu) * triangleEnergy p x))
    (hscalar : ∀ p : S → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      envelope s r mu theta oldBase oldSlope u p ≤ 0) :
    ∃ z : E, ∀ W : Finset S, W.Nonempty → W.card ≤ s - 1 →
      (∑ i ∈ W, ‖v i - z‖ ^ 2) ≤ W.card * r -
        ((1 + 1 / mu) * theta) * ((W.card : ℝ) * ((W.card : ℝ) - 1) / 2) +
        ((1 + 1 / mu) * theta) * subsetPairs W (fun i j => ‖y i j‖ ^ 2) := by
  classical
  let Rows := {W : Finset S // W.Nonempty ∧ W.card ≤ s - 1}
  obtain ⟨z, hz⟩ := exists_centers s (fun a : Rows => a.val)
    (fun a => a.property.1) (fun a => a.property.2) v x y hx hy hxy hcap
    r mu theta oldBase oldSlope u hmu hcredit hscalar
  refine ⟨z, fun W hW hs => ?_⟩
  have hb := hz ⟨W, hW, hs⟩
  change (∑ i ∈ W, ‖v i - z‖ ^ 2) ≤ _ at hb
  rw [subsetPairs_defect] at hb
  nlinarith only [hb]

end
end HilbertRetainedRows
