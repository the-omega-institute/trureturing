import OmegaMath.Combinatorics.Graph.FiniteHilbertJung

/-!
Omega original.

# Weighted finite Hilbert energies and quadratic rows

Ordered sums keep the Hodge identities independent of an ordering of the index
set. The unnormalized identity also applies to restrictions of the weights,
including restrictions of mass zero. Quadratic rows share a common quadratic
part; maximizing their mixture minimum on a finite simplex proves minimax.
-/

open scoped BigOperators InnerProductSpace

namespace HilbertWeightedEnergy

universe u v w
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type v} [Fintype ι]

noncomputable def rowMean (p : ι → ℝ) (f : ι → ι → E) (i : ι) : E :=
  ∑ j, p j • f i j

noncomputable def orderedEnergy (p : ι → ℝ) (f : ι → ι → E) : ℝ :=
  ∑ i, ∑ j, p i * p j * ‖f i j‖ ^ 2

def curl (f : ι → ι → E) (i j k : ι) : E := f i j + f j k - f i k

noncomputable def orderedCurlEnergy (p : ι → ℝ) (f : ι → ι → E) : ℝ :=
  ∑ i, ∑ j, ∑ k, p i * p j * p k * ‖curl f i j k‖ ^ 2

noncomputable def meanEnergy (p : ι → ℝ) (f : ι → ι → E) : ℝ :=
  ∑ i, p i * ‖rowMean p f i‖ ^ 2

noncomputable def centeredField (p : ι → ℝ) (f : ι → ι → E) (i j : ι) : E :=
  f i j - rowMean p f i + rowMean p f j

omit [Fintype ι] in
lemma skew_diagonal (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) (i : ι) :
    f i i = 0 := by
  have h : (2 : ℝ) • f i i = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (hf i i)
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

omit [InnerProductSpace ℝ E] [Fintype ι] in
lemma curl_swap_left (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) (i j k : ι) :
    curl f j i k = -curl f i j k := by
  unfold curl
  rw [hf i j]
  abel

omit [InnerProductSpace ℝ E] [Fintype ι] in
lemma curl_swap_right (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) (i j k : ι) :
    curl f i k j = -curl f i j k := by
  unfold curl
  rw [hf j k]
  abel

omit [Fintype ι] in
lemma curl_repeat (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j)
    (i j k : ι) (h : i = j ∨ j = k ∨ i = k) : curl f i j k = 0 := by
  rcases h with rfl | rfl | rfl
  · simp [curl, skew_diagonal f hf]
  · simp [curl, skew_diagonal f hf]
  · rw [curl, hf i j, skew_diagonal f hf]
    abel

lemma rowMean_total (p : ι → ℝ) (f : ι → ι → E)
    (hf : ∀ i j, f j i = -f i j) : ∑ i, p i • rowMean p f i = 0 := by
  have h : (∑ i, p i • rowMean p f i) = -(∑ i, p i • rowMean p f i) := by
    unfold rowMean
    simp_rw [Finset.smul_sum, ← mul_smul]
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hf i j, smul_neg, mul_comm]
  have : (2 : ℝ) • (∑ i, p i • rowMean p f i) = 0 := by
    rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp this).resolve_left (by norm_num)

lemma centeredField_skew (p : ι → ℝ) (f : ι → ι → E)
    (hf : ∀ i j, f j i = -f i j) :
    ∀ i j, centeredField p f j i = -centeredField p f i j := by
  intro i j
  simp only [centeredField]
  rw [hf i j]
  abel

lemma curl_centeredField (p : ι → ℝ) (f : ι → ι → E) (i j k : ι) :
    curl (centeredField p f) i j k = curl f i j k := by
  unfold curl centeredField
  abel

lemma rowMean_centeredField (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) (i : ι) :
    rowMean p (centeredField p f) i = 0 := by
  simp only [rowMean, centeredField, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_smul, hp, one_smul]
  change rowMean p f i - rowMean p f i + (∑ j, p j • rowMean p f j) = 0
  rw [rowMean_total p f hf]
  simp

private lemma cross_row (p : ι → ℝ) (f : ι → ι → E) :
    (∑ i, ∑ j, ∑ k, p i * p j * p k * ⟪f i j, f i k⟫_ℝ) = meanEnergy p f := by
  simp only [meanEnergy, ← real_inner_self_eq_norm_sq, rowMean,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => by rw [real_inner_comm]; ring)))

/-- Weighted Hodge identity without a normalization or positivity assumption. -/
theorem hodge_identity (p : ι → ℝ) (f : ι → ι → E)
    (hf : ∀ i j, f j i = -f i j) :
    orderedCurlEnergy p f = 3 * (∑ i, p i) * orderedEnergy p f - 6 * meanEnergy p f := by
  have h₁ : (∑ i, ∑ j, ∑ k, p i * p j * p k * ⟪f i j, f j k⟫_ℝ) =
      -meanEnergy p f := by
    calc
      _ = ∑ j, ∑ i, ∑ k, p i * p j * p k * ⟪f i j, f j k⟫_ℝ :=
        Finset.sum_comm
      _ = -(∑ j, ∑ i, ∑ k, p j * p i * p k * ⟪f j i, f j k⟫_ℝ) := by
        simp only [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun k _ => ?_)))
        rw [hf j i, inner_neg_left]
        ring
      _ = _ := by rw [cross_row]
  have h₂ : (∑ i, ∑ j, ∑ k, p i * p j * p k * ⟪f j k, f i k⟫_ℝ) =
      meanEnergy p f := by
    calc
      _ = ∑ j, ∑ k, ∑ i, p i * p j * p k * ⟪f j k, f i k⟫_ℝ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
      _ = ∑ k, ∑ j, ∑ i, p i * p j * p k * ⟪f j k, f i k⟫_ℝ :=
        Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, p k * p j * p i * ⟪f k j, f k i⟫_ℝ := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun i _ => ?_)))
        rw [hf k j, hf k i, inner_neg_neg]
        ring
      _ = _ := cross_row p f
  have hs₁ : (∑ i, ∑ j, ∑ k, p i * p j * p k * ‖f i j‖ ^ 2) =
      (∑ i, p i) * orderedEnergy p f := by
    calc
      _ = ∑ i, ∑ j, (∑ k, p k) * (p i * p j * ‖f i j‖ ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by simp only [orderedEnergy, Finset.mul_sum]
  have hs₂ : (∑ i, ∑ j, ∑ k, p i * p j * p k * ‖f j k‖ ^ 2) =
      (∑ i, p i) * orderedEnergy p f := by
    simp [orderedEnergy, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  have hs₃ : (∑ i, ∑ j, ∑ k, p i * p j * p k * ‖f i k‖ ^ 2) =
      (∑ i, p i) * orderedEnergy p f := by
    calc
      _ = ∑ i, ∑ k, ∑ j, p i * p j * p k * ‖f i k‖ ^ 2 := by
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := by
        simpa only [mul_right_comm] using hs₁
  have hexp (i j k : ι) :
      p i * p j * p k * ‖curl f i j k‖ ^ 2 =
      p i * p j * p k * ‖f i j‖ ^ 2 + p i * p j * p k * ‖f j k‖ ^ 2 +
      p i * p j * p k * ‖f i k‖ ^ 2 +
      2 * (p i * p j * p k * ⟪f i j, f j k⟫_ℝ) -
      2 * (p i * p j * p k * ⟪f i j, f i k⟫_ℝ) -
      2 * (p i * p j * p k * ⟪f j k, f i k⟫_ℝ) := by
    rw [curl, norm_sub_sq_real, norm_add_sq_real, inner_add_left]
    ring
  simp only [orderedCurlEnergy, hexp, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hs₁, hs₂, hs₃, h₁, h₂, cross_row]
  ring

/-- The Hodge inequality is valid for arbitrary nonnegative weights. -/
theorem hodge_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (f : ι → ι → E)
    (hf : ∀ i j, f j i = -f i j) :
    orderedCurlEnergy p f ≤ 3 * (∑ i, p i) * orderedEnergy p f := by
  rw [hodge_identity p f hf]
  have : 0 ≤ meanEnergy p f :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
  linarith

/-- Restricting weights gives the prefix estimate, including zero mass. -/
theorem hodge_prefix [DecidableEq ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (S : Finset ι)
    (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) :
    orderedCurlEnergy (fun i => if i ∈ S then p i else 0) f ≤
      3 * (∑ i ∈ S, p i) * orderedEnergy p f := by
  classical
  let q := fun i => if i ∈ S then p i else 0
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    dsimp [q]
    split_ifs
    · exact hp i
    · exact le_rfl
  have hqp : ∀ i, q i ≤ p i := by
    intro i
    dsimp [q]
    split_ifs
    · exact le_rfl
    · exact hp i
  have he : orderedEnergy q f ≤ orderedEnergy p f := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hqp i) (hqp j) (hq j) (hp i)) (sq_nonneg _)
  have hm : ∑ i, q i = ∑ i ∈ S, p i := by simp [q]
  calc
    _ ≤ 3 * (∑ i, q i) * orderedEnergy q f := hodge_le q hq f hf
    _ ≤ 3 * (∑ i, q i) * orderedEnergy p f :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num)
        (Finset.sum_nonneg (fun i _ => hq i)))
    _ = _ := by rw [hm]

/-- The centered field has exactly the nongradient part of the energy. -/
theorem centered_energy (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) :
    orderedEnergy p (centeredField p f) = orderedEnergy p f - 2 * meanEnergy p f := by
  have hc := hodge_identity p (centeredField p f) (centeredField_skew p f hf)
  have ho := hodge_identity p f hf
  have hz : meanEnergy p (centeredField p f) = 0 := by
    simp [meanEnergy, rowMean_centeredField p hp f hf]
  have ht : orderedCurlEnergy p (centeredField p f) = orderedCurlEnergy p f := by
    simp only [orderedCurlEnergy, curl_centeredField]
  rw [hz, ht, hp] at hc
  rw [hp] at ho
  linarith

namespace QuadraticRows
variable {κ : Type w} [Fintype κ]

noncomputable def mixtureMinimum (c : κ → E) (b : κ → ℝ) (w : κ → ℝ) : ℝ :=
  FiniteHilbertJung.variance c w + ∑ r, w r * b r

lemma mixture_identity (c : κ → E) (b w : κ → ℝ) (hw : ∑ r, w r = 1) (z : E) :
    ∑ r, w r * (‖c r - z‖ ^ 2 + b r) =
      mixtureMinimum c b w + ‖FiniteHilbertJung.center c w - z‖ ^ 2 := by
  simp only [mul_add, Finset.sum_add_distrib, FiniteHilbertJung.weighted_sq c w hw z,
    mixtureMinimum]
  ring

lemma mixture_move [DecidableEq κ] (c : κ → E) (b w : κ → ℝ) (r : κ) (t : ℝ) :
    mixtureMinimum c b (fun s => (1 - t) * w s + t * (if s = r then 1 else 0)) =
      mixtureMinimum c b w +
        t * (‖c r - FiniteHilbertJung.center c w‖ ^ 2 + b r - mixtureMinimum c b w) -
        t ^ 2 * ‖c r - FiniteHilbertJung.center c w‖ ^ 2 := by
  classical
  unfold mixtureMinimum
  rw [FiniteHilbertJung.variance_move]
  have hs : (∑ s, ((1 - t) * w s + t * (if s = r then 1 else 0)) * b s) =
      (1 - t) * ∑ s, w s * b s + t * b r := by
    simp [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', mul_ite]
  rw [hs]
  ring

/-- A maximizing mixture supplies a simultaneous upper bound for all rows. -/
theorem exists_row_center [Nonempty κ] (c : κ → E) (b : κ → ℝ) :
    ∃ w : κ → ℝ, (∀ r, 0 ≤ w r) ∧ (∑ r, w r = 1) ∧
      ∀ r, ‖c r - FiniteHilbertJung.center c w‖ ^ 2 + b r ≤ mixtureMinimum c b w := by
  classical
  let K : Set (κ → ℝ) := {w | (∀ r, 0 ≤ w r) ∧ ∑ r, w r = 1}
  have hcont : Continuous (mixtureMinimum c b) := by
    unfold mixtureMinimum FiniteHilbertJung.variance FiniteHilbertJung.center
    fun_prop
  have hcompact : IsCompact K := by
    have he : K = Set.range (fun t : Convexity.StdSimplex ℝ κ => (t.weights : κ → ℝ)) := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext w
      simp [K]
    rw [he]
    simpa only [Set.image_univ] using
      (isCompact_univ : IsCompact (Set.univ : Set (Convexity.StdSimplex ℝ κ))).image
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ κ).continuous
  have hne : K.Nonempty := by
    refine ⟨fun s => if s = Classical.arbitrary κ then 1 else 0, ?_, ?_⟩
    · intro s; dsimp only; split_ifs <;> positivity
    · simp
  obtain ⟨w, hw, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  refine ⟨w, hw.1, hw.2, fun r => ?_⟩
  have hpoly : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * (‖c r - FiniteHilbertJung.center c w‖ ^ 2 + b r - mixtureMinimum c b w) -
        t ^ 2 * ‖c r - FiniteHilbertJung.center c w‖ ^ 2 ≤ 0 := by
    intro t ht ht1
    have hv : (fun s => (1 - t) * w s + t * (if s = r then 1 else 0)) ∈ K := by
      refine ⟨fun s => add_nonneg (mul_nonneg (by linarith) (hw.1 s))
        (mul_nonneg ht (by split_ifs <;> positivity)), ?_⟩
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, mul_ite]
    have hh := hmax hv
    change mixtureMinimum c b (fun s => (1 - t) * w s + t * (if s = r then 1 else 0)) ≤
      mixtureMinimum c b w at hh
    rw [mixture_move] at hh
    linarith
  have hh := FiniteHilbertJung.polynomial_maximum
    (sq_nonneg ‖c r - FiniteHilbertJung.center c w‖) hpoly
  linarith

/-- Finite minimax for shifted squared distances in any real Hilbert space. -/
theorem minimax (c : κ → E) (b : κ → ℝ)
    (h : ∀ w : κ → ℝ, (∀ r, 0 ≤ w r) → (∑ r, w r = 1) →
      ∃ z : E, ∑ r, w r * (‖c r - z‖ ^ 2 + b r) ≤ 0) :
    ∃ z : E, ∀ r, ‖c r - z‖ ^ 2 + b r ≤ 0 := by
  classical
  by_cases hn : Nonempty κ
  · let := hn
    obtain ⟨w, hw₀, hw₁, hb⟩ := exists_row_center c b
    obtain ⟨z, hz⟩ := h w hw₀ hw₁
    rw [mixture_identity c b w hw₁ z] at hz
    have hm : mixtureMinimum c b w ≤ 0 := by
      nlinarith [sq_nonneg ‖FiniteHilbertJung.center c w - z‖]
    exact ⟨FiniteHilbertJung.center c w, fun r => (hb r).trans hm⟩
  · exact ⟨0, fun r => (hn ⟨r⟩).elim⟩

/-- Averaged squared-distance rows reduce to shifted-square minimax. -/
theorem averaged_minimax (c : ι → E) (q : κ → ι → ℝ) (b : κ → ℝ)
    (hq : ∀ r, ∑ i, q r i = 1)
    (h : ∀ w : κ → ℝ, (∀ r, 0 ≤ w r) → (∑ r, w r = 1) →
      ∃ z : E, ∑ r, w r * ((∑ i, q r i * ‖c i - z‖ ^ 2) + b r) ≤ 0) :
    ∃ z : E, ∀ r, (∑ i, q r i * ‖c i - z‖ ^ 2) + b r ≤ 0 := by
  have he (r : κ) (z : E) : (∑ i, q r i * ‖c i - z‖ ^ 2) + b r =
      ‖FiniteHilbertJung.center c (q r) - z‖ ^ 2 +
        (FiniteHilbertJung.variance c (q r) + b r) := by
    rw [FiniteHilbertJung.weighted_sq c (q r) (hq r)]
    ring
  obtain ⟨z, hz⟩ := minimax (fun r => FiniteHilbertJung.center c (q r))
    (fun r => FiniteHilbertJung.variance c (q r) + b r) (by simpa only [← he] using h)
  exact ⟨z, fun r => by simpa only [he] using hz r⟩

/-- A mixture of averaged rows has the vertex weights obtained by summing its
row incidences. This is the minimum formula used for singleton and pair rows. -/
lemma averaged_mixture_identity (c : ι → E) (q : κ → ι → ℝ) (b w : κ → ℝ)
    (hw : ∑ r, w r = 1) (hq : ∀ r, ∑ i, q r i = 1) (z : E) :
    let p := fun i => ∑ r, w r * q r i
    (∑ r, w r * ((∑ i, q r i * ‖c i - z‖ ^ 2) + b r)) =
      FiniteHilbertJung.variance c p + (∑ r, w r * b r) +
        ‖FiniteHilbertJung.center c p - z‖ ^ 2 := by
  let p := fun i => ∑ r, w r * q r i
  have hp : ∑ i, p i = 1 := by
    dsimp [p]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hq, mul_one]
    exact hw
  have he : (∑ r, w r * (∑ i, q r i * ‖c i - z‖ ^ 2)) =
      ∑ i, p i * ‖c i - z‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [p, Finset.sum_mul, mul_assoc]
  change _ = FiniteHilbertJung.variance c p + _ + ‖FiniteHilbertJung.center c p - z‖ ^ 2
  simp only [mul_add, Finset.sum_add_distrib]
  rw [he, FiniteHilbertJung.weighted_sq c p hp]
  ring

end QuadraticRows

/-- Exact remainder in the quadratic Young inequality. -/
theorem young_gap (x y : E) (a b : ℝ) (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖x‖ ^ 2 / a + ‖y‖ ^ 2 / b - ‖x - y‖ ^ 2 =
      ‖b • x + a • y‖ ^ 2 / (a * b) := by
  have h : b = 1 - a := by linarith
  subst b
  rw [norm_sub_sq_real, norm_add_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- The pointwise variance-loss identity. The scalar equality specifies the cap. -/
theorem variance_loss_pair (x y : E) (a b cap r : ℝ)
    (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcap : cap = r / a + 1 / b) :
    cap - ‖x - y‖ ^ 2 = (r - ‖x‖ ^ 2) / a + (1 - ‖y‖ ^ 2) / b +
      ‖b • x + a • y‖ ^ 2 / (a * b) := by
  have hh := young_gap x y a b hab ha hb
  rw [hcap]
  rw [sub_div, sub_div]
  linarith

/-- The cap specialization in the pointwise identity uses only `R > 0`. -/
theorem variance_loss_pair_radius (x y : E) (R : ℝ) (hR : 0 < R) :
    (1 + R) ^ 2 - ‖x - y‖ ^ 2 =
      (R ^ 2 - ‖x‖ ^ 2) / (R / (1 + R)) +
      (1 - ‖y‖ ^ 2) / (1 / (1 + R)) +
      ‖(1 / (1 + R)) • x + (R / (1 + R)) • y‖ ^ 2 /
        ((R / (1 + R)) * (1 / (1 + R))) := by
  apply variance_loss_pair
  · field_simp
    ring
  · exact div_ne_zero hR.ne' (by linarith)
  · exact one_div_ne_zero (by linarith)
  · field_simp
    <;> ring

/-- Off-diagonal deficits use both orientations. -/
noncomputable def orderedDeficit [DecidableEq ι] (p : ι → ℝ) (r : ℝ)
    (f : ι → ι → E) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else p i * p j * (r - ‖f i j‖ ^ 2)

/-- The aggregate variance loss, with both orientations retained throughout.
Its last numerator is the centered energy plus twice the row-mean energy. -/
theorem variance_loss [DecidableEq ι] (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (c : ι → E) (x y : ι → ι → E) (hx : ∀ i j, x j i = -x i j)
    (hy : ∀ i j, y j i = -y i j) (hxy : ∀ i j, x i j - y i j = c i - c j)
    (a b cap r : ℝ) (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcap : cap = r / a + 1 / b) :
    cap / 2 - FiniteHilbertJung.variance c p =
      cap / 2 * (∑ i, p i ^ 2) + orderedDeficit p r x / (2 * a) +
      orderedDeficit p 1 y / (2 * b) +
      (orderedEnergy p (centeredField p (fun i j => b • x i j + a • y i j)) +
        2 * meanEnergy p (fun i j => b • x i j + a • y i j)) / (2 * a * b) := by
  let e := fun i j => b • x i j + a • y i j
  have he : ∀ i j, e j i = -e i j := by
    intro i j
    dsimp [e]
    rw [hx i j, hy i j, smul_neg, smul_neg, neg_add]
  have hpoint (i j : ι) :
      p i * p j * (cap - ‖c i - c j‖ ^ 2) =
      (if i = j then cap * p i ^ 2 else 0) +
      (if i = j then 0 else p i * p j * (r - ‖x i j‖ ^ 2)) / a +
      (if i = j then 0 else p i * p j * (1 - ‖y i j‖ ^ 2)) / b +
      p i * p j * ‖e i j‖ ^ 2 / (a * b) := by
    by_cases hij : i = j
    · subst j
      simp [skew_diagonal x hx, skew_diagonal y hy, e, pow_two]
      ring
    · simp only [hij, ite_false, zero_add]
      rw [← hxy, variance_loss_pair (x i j) (y i j) a b cap r hab ha hb hcap]
      dsimp [e]
      ring
  have hsum := congrArg (fun F : ι → ι → ℝ => ∑ i, ∑ j, F i j) (funext fun i => funext (hpoint i))
  have hleft : (∑ i, ∑ j, p i * p j * (cap - ‖c i - c j‖ ^ 2)) =
      cap - 2 * FiniteHilbertJung.variance c p := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [FiniteHilbertJung.pair_sq c p hp]
    simp [← Finset.sum_mul, ← Finset.mul_sum, hp, mul_assoc]
  change (∑ i, ∑ j, p i * p j * (cap - ‖c i - c j‖ ^ 2)) = _ at hsum
  rw [hleft] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
  change cap - 2 * FiniteHilbertJung.variance c p =
    cap * (∑ i, p i ^ 2) + orderedDeficit p r x / a + orderedDeficit p 1 y / b +
      orderedEnergy p e / (a * b) at hsum
  have hc := centered_energy p hp e he
  change orderedEnergy p (centeredField p e) = orderedEnergy p e - 2 * meanEnergy p e at hc
  change cap / 2 - FiniteHilbertJung.variance c p =
    cap / 2 * (∑ i, p i ^ 2) + orderedDeficit p r x / (2 * a) +
      orderedDeficit p 1 y / (2 * b) +
      (orderedEnergy p (centeredField p e) + 2 * meanEnergy p e) / (2 * a * b)
  rw [hc]
  calc
    _ = (cap - 2 * FiniteHilbertJung.variance c p) / 2 := by ring
    _ = (cap * (∑ i, p i ^ 2) + orderedDeficit p r x / a +
        orderedDeficit p 1 y / b + orderedEnergy p e / (a * b)) / 2 := by rw [hsum]
    _ = _ := by ring

noncomputable def sortedTripleSum [LinearOrder ι] (q : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j k else 0

/-- Every symmetric triple function vanishing on repetitions has six equal
ordered orientations. This bridge does not impose positivity on the function. -/
theorem ordered_triple_eq_six_sorted [LinearOrder ι] (q : ι → ι → ι → ℝ)
    (h₁₂ : ∀ i j k, q j i k = q i j k) (h₂₃ : ∀ i j k, q i k j = q i j k)
    (hzero : ∀ i j k, i = j ∨ j = k ∨ i = k → q i j k = 0) :
    (∑ i, ∑ j, ∑ k, q i j k) = 6 * sortedTripleSum q := by
  let t := fun i j k => if i < j ∧ j < k then q i j k else 0
  have hexp (i j k : ι) : q i j k =
      t i j k + t i k j + t j i k + t j k i + t k i j + t k j i := by
    by_cases hij : i = j
    · subst j
      rw [hzero i i k (Or.inl rfl)]
      simp [t, hzero]
    by_cases hjk : j = k
    · subst k
      rw [hzero i j j (Or.inr (Or.inl rfl))]
      simp [t, hzero]
    by_cases hik : i = k
    · subst k
      rw [hzero i j i (Or.inr (Or.inr rfl))]
      simp [t, hzero]
    have h₁ := h₂₃ i j k
    have h₂ := h₁₂ i j k
    have h₃ : q j k i = q i j k := (h₂₃ j i k).trans h₂
    have h₄ : q k i j = q i j k := (h₁₂ i k j).trans h₁
    have h₅ : q k j i = q i j k := (h₁₂ j k i).trans h₃
    dsimp [t]
    rw [h₁, h₂, h₃, h₄, h₅]
    rcases lt_or_gt_of_ne hij with h | h
    · rcases lt_or_gt_of_ne hjk with h' | h'
      · have h'' := lt_trans h h'
        simp [h, h', h'', not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr h''.le]
      · rcases lt_or_gt_of_ne hik with h'' | h''
        · simp [h, h', h'', not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr h''.le]
        · simp [h, h', h'', not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr h''.le]
    · rcases lt_or_gt_of_ne hik with h' | h'
      · have h'' := lt_trans h h'
        simp [h, h', h'', not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr h''.le]
      · rcases lt_or_gt_of_ne hjk with h'' | h''
        · simp [h, h', h'', not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr h''.le]
        · simp [h, h', h'', not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr h''.le]
  have hswap (F : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, F i k j) = ∑ i, ∑ j, ∑ k, F i j k := by
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have hswap' (F : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, F j i k) = ∑ i, ∑ j, ∑ k, F i j k := Finset.sum_comm
  have hcycle (F : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, F j k i) = ∑ i, ∑ j, ∑ k, F i j k := by
    calc
      _ = ∑ j, ∑ i, ∑ k, F j k i := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, F j k i :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  have hreverse (F : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, F k j i) = ∑ i, ∑ j, ∑ k, F i j k := by
    calc
      _ = ∑ i, ∑ j, ∑ k, F j k i := (hswap (fun i j k => F k j i)).symm
      _ = _ := hcycle F
  calc
    _ = ∑ i, ∑ j, ∑ k,
        (t i j k + t i k j + t j i k + t j k i + t k i j + t k j i) := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => hexp i j k)))
    _ = 6 * (∑ i, ∑ j, ∑ k, t i j k) := by
      simp only [Finset.sum_add_distrib]
      rw [hswap t, hswap' t, hcycle t, hreverse t]
      have hh : (∑ i, ∑ j, ∑ k, t k i j) = ∑ i, ∑ j, ∑ k, t i j k := by
        calc
          _ = ∑ i, ∑ j, ∑ k, t k j i := hswap' (fun i j k => t k j i)
          _ = _ := hreverse t
      rw [hh]
      ring
    _ = _ := rfl

/-- The symmetric weighted curl-square sum in increasing order. -/
theorem ordered_curl_eq_six_sorted [LinearOrder ι] (p : ι → ℝ) (f : ι → ι → E)
    (hf : ∀ i j, f j i = -f i j) :
    orderedCurlEnergy p f =
      6 * sortedTripleSum (fun i j k => p i * p j * p k * ‖curl f i j k‖ ^ 2) := by
  apply ordered_triple_eq_six_sorted
  · intro i j k
    rw [curl_swap_left f hf, norm_neg]
    ring
  · intro i j k
    rw [curl_swap_right f hf, norm_neg]
    ring
  · intro i j k h
    rw [curl_repeat f hf i j k h]
    simp

/-- Twice the increasing-triple curl energy on a prefix is at most its mass
 times the full ordered edge energy. No positive-mass premise is necessary. -/
theorem sorted_hodge_prefix [LinearOrder ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (S : Finset ι) (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) :
    2 * sortedTripleSum (fun i j k =>
      (if i ∈ S then p i else 0) * (if j ∈ S then p j else 0) *
        (if k ∈ S then p k else 0) * ‖curl f i j k‖ ^ 2) ≤
      (∑ i ∈ S, p i) * orderedEnergy p f := by
  have hh := hodge_prefix p hp S f hf
  rw [ordered_curl_eq_six_sorted _ f hf] at hh
  linarith

noncomputable def sortedPairSum [LinearOrder ι] (q : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then q i j else 0

/-- A symmetric function zero on the diagonal has two ordered orientations. -/
theorem ordered_pair_eq_two_sorted [LinearOrder ι] (q : ι → ι → ℝ)
    (hs : ∀ i j, q j i = q i j) (hz : ∀ i, q i i = 0) :
    (∑ i, ∑ j, q i j) = 2 * sortedPairSum q := by
  let t := fun i j => if i < j then q i j else 0
  have he (i j : ι) : q i j = t i j + t j i := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [t, h, not_lt.mpr h.le]
    · simp [t, hz]
    · simp [t, h, not_lt.mpr h.le, hs i j]
  calc
    _ = ∑ i, ∑ j, (t i j + t j i) := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j))
    _ = (∑ i, ∑ j, t i j) + ∑ i, ∑ j, t j i := by simp [Finset.sum_add_distrib]
    _ = 2 * sortedPairSum q := by
      rw [Finset.sum_comm (f := fun i j => t j i)]
      change (∑ i, ∑ j, t i j) + (∑ i, ∑ j, t i j) = 2 * (∑ i, ∑ j, t i j)
      ring

/-- The minimum weighted squared distance is the increasing-pair energy. -/
theorem variance_eq_sorted [LinearOrder ι] (c : ι → E) (p : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    FiniteHilbertJung.variance c p =
      sortedPairSum (fun i j => p i * p j * ‖c i - c j‖ ^ 2) := by
  have hh := ordered_pair_eq_two_sorted (fun i j => p i * p j * ‖c i - c j‖ ^ 2)
    (by intro i j; rw [norm_sub_rev]; ring) (by intro i; simp)
  rw [FiniteHilbertJung.pair_sq c p hp] at hh
  linarith

/-- The weighted Hodge identity with increasing pairs and triples. -/
theorem hodge_sorted [LinearOrder ι] (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (f : ι → ι → E) (hf : ∀ i j, f j i = -f i j) :
    sortedTripleSum (fun i j k => p i * p j * p k * ‖curl f i j k‖ ^ 2) =
      sortedPairSum (fun i j => p i * p j * ‖f i j‖ ^ 2) - meanEnergy p f := by
  have he := ordered_pair_eq_two_sorted (fun i j => p i * p j * ‖f i j‖ ^ 2)
    (by intro i j; rw [hf i j, norm_neg]; ring)
    (by intro i; rw [skew_diagonal f hf]; simp)
  have hh := hodge_identity p f hf
  rw [hp, ordered_curl_eq_six_sorted p f hf] at hh
  change (∑ i, ∑ j, p i * p j * ‖f i j‖ ^ 2) = _ at he
  unfold orderedEnergy at hh
  rw [he] at hh
  linarith

end HilbertWeightedEnergy
