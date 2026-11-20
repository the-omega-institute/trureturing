/- GID: D5/S3/QuadraticForms/SphereRatioEarlierExamples
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SphereRatioEarlierExamples
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: Sphere-ratio infima: h = 1 gives 1/√d, 0 and 1/√2; h(t) = 1/t gives 0 for d ≥ 2. -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Corollary 10 of Ma–Zhang (DOI 10.5281/zenodo.23920598): the earlier examples for the ratio
`R_h(x) = Σ xᵢ h(xᵢ) / (Σ h(xᵢ)²)^{1/2}` of Lucid's sphere question (Mathematics Stack Exchange
5146381, linked from MathOverflow 513954, revision 2), under the active-coordinate convention:
unit vectors with all coordinates positive, their number `d` being the dimension. For `h = 1`
(suggested by daw) the infimum in fixed dimension `d ≥ 1` is `1/√d`, unattained for `d ≥ 2`; over
all dimensions it is `0`, unattained; over dimensions at most two it is `1/√2`, unattained. For
`h(t) = 1/t` (used by Exodd) the infimum is `0`, unattained, already in dimension two and in
every dimension `d ≥ 2`.

admission_basis: escape-witness. Escape witnesses: sum_ge_one (`1 ≤ Σ xᵢ` for positive unit
vectors, strict in dimension at least two), near_tendsto (the near-axis sequence with `R → 1/√d`),
one_all (the choice of dimension driving the infimum to `0`), and ratio_inv with inv_all
(`R_{1/t}(x) = d / (Σ xᵢ⁻²)^{1/2} ≤ d √p` when one squared coordinate is `p`). -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.QuadraticForms.SphereRatioEarlierExamples


/-- `R_h(x) = Σ xᵢ h(xᵢ) / (Σ h(xᵢ)²)^{1/2}`. -/
def ratio (h : ℝ → ℝ) {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  (∑ i, x i * h (x i)) / Real.sqrt (∑ i, h (x i) ^ 2)

/-- Values of `R_h` on unit vectors with `d` positive coordinates (the active-coordinate
convention). -/
def values (h : ℝ → ℝ) (d : ℕ) : Set ℝ :=
  {r | ∃ x : Fin d → ℝ, (∀ i, 0 < x i) ∧ ∑ i, x i ^ 2 = 1 ∧ ratio h x = r}

private theorem ratio_one {d : ℕ} (x : Fin d → ℝ) :
    ratio (fun _ => 1) x = (∑ i, x i) / Real.sqrt d := by
  simp [ratio]

/-- For a positive unit vector, `1 ≤ Σ xᵢ`, strictly when `d ≥ 2`. -/
private theorem sum_ge_one {d : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 < x i) (hs : ∑ i, x i ^ 2 = 1) :
    1 ≤ ∑ i, x i ∧ (2 ≤ d → 1 < ∑ i, x i) := by
  have hle : ∀ i, x i ^ 2 ≤ x i := fun i => by
    have : x i ≤ 1 := by
      have := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hs] at this; nlinarith [hx i]
    nlinarith [hx i]
  refine ⟨hs ▸ Finset.sum_le_sum fun i _ => hle i, fun hd => ?_⟩
  -- strict: some coordinate is < 1
  have hlt : ∃ i, x i < 1 := by
    by_contra hcon; push Not at hcon
    have h0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
    have := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ {⟨0, by omega⟩, ⟨1, by omega⟩})
      (fun j _ _ => sq_nonneg (x j)) (f := fun j => x j ^ 2)
    rw [Finset.sum_pair h0, hs] at this
    nlinarith [hcon ⟨0, by omega⟩, hcon ⟨1, by omega⟩]
  obtain ⟨i, hi⟩ := hlt
  rw [← hs]
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, by nlinarith [hx i]⟩


/-- One large coordinate and `k` small coordinates `ε`. -/
private def near (k : ℕ) (ε : ℝ) : Fin (k + 1) → ℝ :=
  Fin.cons (Real.sqrt (1 - k * ε ^ 2)) fun _ => ε

private theorem near_pos (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hk : k * ε ^ 2 < 1) (i : Fin (k + 1)) :
    0 < near k ε i := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · simp only [near, Fin.cons_zero]; exact Real.sqrt_pos.mpr (by linarith)
  · simpa [near] using hε

private theorem near_unit (k : ℕ) (ε : ℝ) (hk : k * ε ^ 2 < 1) : ∑ i, near k ε i ^ 2 = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [near, Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - k * ε ^ 2)]
  ring

private theorem near_sum (k : ℕ) (ε : ℝ) : ∑ i, near k ε i = Real.sqrt (1 - k * ε ^ 2) + k * ε := by
  rw [Fin.sum_univ_succ]
  simp [near]

/-- `ε_m = 1/((k+1)(m+1))`. -/
private def eps (k m : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * ((m : ℝ) + 1))

private theorem eps_pos (k m : ℕ) : 0 < eps k m := by unfold eps; positivity

private theorem eps_small (k m : ℕ) : (k : ℝ) * eps k m ^ 2 < 1 := by
  unfold eps
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
  nlinarith [mul_nonneg hk hm, mul_nonneg (mul_nonneg hk hm) hm, mul_nonneg hk hk,
    mul_nonneg (mul_nonneg hk hk) hm, mul_nonneg (mul_nonneg (mul_nonneg hk hk) hm) hm]

private theorem eps_tendsto (k : ℕ) : Filter.Tendsto (eps k) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := h.const_mul (1 / ((k : ℝ) + 1))
  rw [mul_zero] at this
  refine this.congr fun m => ?_
  unfold eps; field_simp

private theorem near_tendsto (k : ℕ) :
    Filter.Tendsto (fun m => ratio (fun _ => 1) (near k (eps k m))) Filter.atTop
      (nhds (1 / Real.sqrt (k + 1))) := by
  have he := eps_tendsto k
  have hs : Filter.Tendsto (fun m => Real.sqrt (1 - k * eps k m ^ 2) + k * eps k m)
      Filter.atTop (nhds (Real.sqrt (1 - k * 0 ^ 2) + k * 0)) :=
    ((Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (he.pow 2)))).add (tendsto_const_nhds.mul he)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
    Real.sqrt_one, add_zero] at hs
  have := hs.div_const (Real.sqrt (k + 1))
  refine this.congr fun m => ?_
  rw [ratio_one, near_sum]; push_cast; ring

/-- `h = 1`, fixed dimension `k + 1`: the infimum is `1/√(k+1)`, unattained when `k ≥ 1`. -/
private theorem one_fixed (k : ℕ) :
    IsGLB (values (fun _ => 1) (k + 1)) (1 / Real.sqrt (k + 1)) ∧
      (1 ≤ k → ∀ r ∈ values (fun _ => 1) (k + 1), 1 / Real.sqrt (k + 1) < r) := by
  have hsq : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨⟨?_, fun b hb => ?_⟩, fun hk r hr => ?_⟩
  · rintro r ⟨x, hx, hs, rfl⟩
    rw [ratio_one]; push_cast
    exact div_le_div_of_nonneg_right (sum_ge_one x hx hs).1 hsq.le
  · refine ge_of_tendsto (near_tendsto k) (Filter.Eventually.of_forall fun m => hb ?_)
    exact ⟨near k (eps k m), near_pos k _ (eps_pos k m) (eps_small k m),
      near_unit k _ (eps_small k m), rfl⟩
  · obtain ⟨x, hx, hs, rfl⟩ := hr
    rw [ratio_one]; push_cast
    exact div_lt_div_of_pos_right ((sum_ge_one x hx hs).2 (by omega)) hsq


private theorem values_one_pos {d : ℕ} {r : ℝ} (hr : r ∈ values (fun _ => 1) d) : 0 < r := by
  obtain ⟨x, hx, hs, rfl⟩ := hr
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at hs
  rw [ratio_one]
  exact div_pos (lt_of_lt_of_le zero_lt_one (sum_ge_one x hx hs).1)
    (Real.sqrt_pos.mpr (by exact_mod_cast hd))

/-- `h = 1` over all dimensions: the infimum is `0`, unattained. -/
private theorem one_all :
    IsGLB {r | ∃ d, r ∈ values (fun _ => 1) d} 0 ∧ ∀ d, ∀ r ∈ values (fun _ => 1) d, 0 < r := by
  refine ⟨⟨?_, fun b hb => ?_⟩, fun d r hr => values_one_pos hr⟩
  · rintro r ⟨d, hr⟩; exact (values_one_pos hr).le
  · by_contra hbpos; push Not at hbpos
    -- choose k with 2/√(k+1) < b
    obtain ⟨k, hk⟩ := exists_nat_gt (4 / b ^ 2)
    have hsq : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hkb : 4 < (k : ℝ) * b ^ 2 := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < b ^ 2)).mp hk; linarith
    have hprod : 2 < b * Real.sqrt (k + 1) := by
      have hsq2 : (b * Real.sqrt (k + 1)) ^ 2 = b ^ 2 * (k + 1) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith [mul_pos hbpos hsq, sq_nonneg b]
    have h2 : 1 / Real.sqrt (k + 1) < b / 2 := by
      rw [div_lt_div_iff₀ hsq two_pos]; linarith
    obtain ⟨r, hr, -, hrb⟩ := (one_fixed k).1.exists_between (lt_trans h2 (by linarith : b / 2 < b))
    exact absurd (hb ⟨k + 1, hr⟩) (not_le.mpr hrb)

/-- `h = 1` with at most two coordinates: the infimum is `1/√2`, unattained. -/
private theorem one_two :
    IsGLB {r | ∃ d ≤ 2, r ∈ values (fun _ => 1) d} (1 / Real.sqrt 2) ∧
      ∀ d ≤ 2, ∀ r ∈ values (fun _ => 1) d, 1 / Real.sqrt 2 < r := by
  have hlt : ∀ d ≤ 2, ∀ r ∈ values (fun _ => 1) d, 1 / Real.sqrt 2 < r := by
    intro d hd r hr
    interval_cases d
    · obtain ⟨x, -, hs, -⟩ := hr; simp at hs
    · obtain ⟨x, hx, hs, rfl⟩ := hr
      rw [ratio_one]
      have : ∑ i, x i = 1 := by
        simp only [Fin.sum_univ_one] at hs ⊢
        nlinarith [hx 0, sq_nonneg (x 0 - 1)]
      rw [this]; simp only [Nat.cast_one, Real.sqrt_one]
      exact one_div_lt_one_div_of_lt zero_lt_one ((Real.lt_sqrt zero_le_one).2 (by norm_num))
    · have := (one_fixed 1).2 le_rfl r (by norm_num at hr ⊢; exact hr)
      norm_num at this; rw [one_div]; exact this
  refine ⟨⟨fun r ⟨d, hd, hr⟩ => (hlt d hd r hr).le, fun b hb => ?_⟩, hlt⟩
  have := (one_fixed 1).1.2 (fun r hr => hb ⟨2, le_rfl, by norm_num at hr ⊢; exact hr⟩)
  norm_num at this ⊢; exact this

/-- For positive coordinates, `R_{1/t}(x) = d / (Σ xᵢ⁻²)^{1/2}`. -/
private theorem ratio_inv {d : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 < x i) :
    ratio (fun t => 1 / t) x = d / Real.sqrt (∑ i, (1 / x i) ^ 2) := by
  unfold ratio
  congr 1
  rw [Finset.sum_congr rfl fun i _ => by rw [mul_one_div_cancel (hx i).ne']]
  simp

/-- One small squared coordinate `p` and `k + 1` equal ones. -/
private def tiny (k : ℕ) (p : ℝ) : Fin (k + 2) → ℝ :=
  Fin.cons (Real.sqrt p) fun _ => Real.sqrt ((1 - p) / (k + 1))

/-- `h(t) = 1/t` in dimension `k + 2`: the infimum is `0`, unattained. -/
private theorem inv_all (k : ℕ) :
    IsGLB (values (fun t => 1 / t) (k + 2)) 0 ∧
      ∀ r ∈ values (fun t => 1 / t) (k + 2), 0 < r := by
  have hpos : ∀ r ∈ values (fun t => 1 / t) (k + 2), 0 < r := by
    rintro r ⟨x, hx, -, rfl⟩
    rw [ratio_inv x hx]
    refine div_pos (by positivity) (Real.sqrt_pos.mpr ?_)
    exact lt_of_lt_of_le (by have := hx 0; positivity)
      (Finset.single_le_sum (fun i _ => sq_nonneg (1 / x i)) (Finset.mem_univ 0))
  refine ⟨⟨fun r hr => (hpos r hr).le, fun b hb => ?_⟩, hpos⟩
  by_contra hbpos; push Not at hbpos
  have hK : (0:ℝ) < ((k : ℝ) + 2) ^ 2 := by positivity
  set p : ℝ := min (1 / 2) (b ^ 2 / (2 * ((k : ℝ) + 2) ^ 2)) with hp
  have hp0 : 0 < p := lt_min (by norm_num) (by positivity)
  have hp1 : p ≤ 1 / 2 := min_le_left _ _
  have hpb : p ≤ b ^ 2 / (2 * ((k : ℝ) + 2) ^ 2) := min_le_right _ _
  have hq : 0 < (1 - p) / ((k : ℝ) + 1) := div_pos (by linarith) (by positivity)
  have hx : ∀ i, 0 < tiny k p i := fun i => by
    refine Fin.cases ?_ (fun _ => ?_) i
    · simp only [tiny, Fin.cons_zero]; exact Real.sqrt_pos.mpr hp0
    · simp only [tiny, Fin.cons_succ]; exact Real.sqrt_pos.mpr hq
  have hs : ∑ i, tiny k p i ^ 2 = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [tiny, Fin.cons_zero, Fin.cons_succ, Real.sq_sqrt hp0.le, Real.sq_sqrt hq.le,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; field_simp; ring
  have hmem := hb ⟨tiny k p, hx, hs, rfl⟩
  rw [ratio_inv _ hx] at hmem
  have hS : 1 / p ≤ ∑ i, (1 / tiny k p i) ^ 2 := by
    have h0 : (1 / tiny k p 0) ^ 2 = 1 / p := by
      simp only [tiny, Fin.cons_zero, div_pow, one_pow, Real.sq_sqrt hp0.le]
    rw [← h0]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (1 / tiny k p i)) (Finset.mem_univ 0)
  have hsqS : Real.sqrt (1 / p) ≤ Real.sqrt (∑ i, (1 / tiny k p i) ^ 2) := Real.sqrt_le_sqrt hS
  have hsp : Real.sqrt (1 / p) = 1 / Real.sqrt p := by
    rw [Real.sqrt_div' _ hp0.le, Real.sqrt_one]
  have hsqp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hR : ((k + 2 : ℕ) : ℝ) / Real.sqrt (∑ i, (1 / tiny k p i) ^ 2) ≤
      ((k : ℝ) + 2) * Real.sqrt p := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by rw [hsp]; positivity) hsqS)]
    push_cast
    calc (k : ℝ) + 2 = ((k : ℝ) + 2) * Real.sqrt p * (1 / Real.sqrt p) := by field_simp
      _ ≤ ((k : ℝ) + 2) * Real.sqrt p * Real.sqrt (∑ i, (1 / tiny k p i) ^ 2) := by
        rw [← hsp]; exact mul_le_mul_of_nonneg_left hsqS (by positivity)
  have hlt : ((k : ℝ) + 2) * Real.sqrt p < b := by
    have hsq : (((k : ℝ) + 2) * Real.sqrt p) ^ 2 < b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp0.le]
      calc ((k : ℝ) + 2) ^ 2 * p ≤ ((k : ℝ) + 2) ^ 2 * (b ^ 2 / (2 * ((k : ℝ) + 2) ^ 2)) :=
            mul_le_mul_of_nonneg_left hpb hK.le
        _ = b ^ 2 / 2 := by field_simp
        _ < b ^ 2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k : ℝ) + 2) hsqp.le]
  linarith

/-- Corollary 10 of Ma–Zhang (DOI 10.5281/zenodo.23920598) for `h = 1` and `h(t) = 1/t`. -/
theorem result :
    (∀ d : ℕ, 1 ≤ d → IsGLB (values (fun _ => 1) d) (1 / Real.sqrt d) ∧
      (2 ≤ d → ∀ r ∈ values (fun _ => 1) d, 1 / Real.sqrt d < r)) ∧
      (IsGLB {r | ∃ d, r ∈ values (fun _ => 1) d} 0 ∧
        ∀ d, ∀ r ∈ values (fun _ => 1) d, 0 < r) ∧
      (IsGLB {r | ∃ d ≤ 2, r ∈ values (fun _ => 1) d} (1 / Real.sqrt 2) ∧
        ∀ d ≤ 2, ∀ r ∈ values (fun _ => 1) d, 1 / Real.sqrt 2 < r) ∧
      (∀ d : ℕ, 2 ≤ d → IsGLB (values (fun t => 1 / t) d) 0 ∧
        ∀ r ∈ values (fun t => 1 / t) d, 0 < r) := by
  refine ⟨fun d hd => ?_, one_all, one_two, fun d hd => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have := one_fixed k
    push_cast
    exact ⟨this.1, fun hd2 => this.2 (by omega)⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    exact inv_all k

end D5.S3.QuadraticForms.SphereRatioEarlierExamples
