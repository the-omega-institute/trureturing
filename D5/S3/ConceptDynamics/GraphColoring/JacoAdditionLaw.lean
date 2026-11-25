/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree]
   utility: none
   digest: Finite linear Jaco maximum degrees add up to an exact golden fractional-part correction. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree

/-! The corrected addition law for maximum degrees of finite linear Jaco graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

/-
proof_shape:
  delta_eq_floor: content
  sum_law: content
  result: content
escape_witness: the real identity delta n = (n + 2) / phi - frac n - 1, summed over the
  family and reduced through 2 / phi = sqrt 5 - 1, places the integer correction within one of
  the real number sum frac - (card - 1) * alpha; the trichotomy bounds that floor.
admission_basis: escape-witness
-/

universe u

open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation

/-- The maximum degree of the order-`n` linear Jaco graph, as an integer. -/
noncomputable def delta (n : ℕ) : ℤ := (jaco n).maxDegree

/-- The fractional part `x_n` of `(n + 2) / φ`. -/
noncomputable def frac (n : ℕ) : ℝ := Int.fract (((n : ℝ) + 2) / Real.goldenRatio)

/-- The constant `alpha = √5 - 2`. -/
noncomputable def alpha : ℝ := Real.sqrt 5 - 2

private theorem two_div_phi : 2 / Real.goldenRatio = Real.sqrt 5 - 1 := by
  rw [div_eq_mul_inv, Real.inv_goldenRatio, Real.goldenConj]
  ring

/-- The maximum degree of every finite linear Jaco graph, order zero included. -/
theorem delta_eq_floor (n : ℕ) :
    delta n = ⌊((n : ℝ) + 2) / Real.goldenRatio⌋ - 1 := by
  have hp := Real.goldenRatio_pos
  have hpos : (0 : ℝ) ≤ ((n : ℝ) + 2) / Real.goldenRatio := by positivity
  rw [← Int.natCast_floor_eq_floor hpos]
  by_cases h1 : n ≤ 1
  · have : Subsingleton (Vertex n) := ⟨by
      intro a b
      apply Subtype.ext
      have ha := Finset.mem_Icc.mp a.2
      have hb := Finset.mem_Icc.mp b.2
      omega⟩
    have hf : ⌊((n : ℝ) + 2) / Real.goldenRatio⌋₊ = 1 := by
      rw [Nat.floor_eq_iff hpos]
      have hlo := Real.one_lt_goldenRatio
      have hn : (n : ℝ) ≤ 1 := by exact_mod_cast h1
      norm_num
      constructor
      · rw [le_div_iff₀ hp]; linarith [Real.goldenRatio_lt_two, Nat.cast_nonneg (α := ℝ) n]
      · rw [div_lt_iff₀ hp]
        nlinarith [Real.goldenRatio_sq]
    rw [hf, delta, SimpleGraph.maxDegree_of_subsingleton]
    norm_num
  · have h := (JacoMaximumDegree.result.1 n (by omega)).1
    have he : 2 * ((n : ℝ) + 2) / (1 + Real.sqrt 5) =
        ((n : ℝ) + 2) / Real.goldenRatio := by
      simp only [Real.goldenRatio, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    rw [he] at h
    have hge : 1 ≤ ⌊((n : ℝ) + 2) / Real.goldenRatio⌋₊ := by
      apply (Nat.le_floor_iff hpos).2
      rw [le_div_iff₀ hp]
      have := Real.goldenRatio_lt_two
      push_cast
      linarith
    rw [delta, h]
    omega

private theorem delta_real (n : ℕ) :
    (delta n : ℝ) = ((n : ℝ) + 2) / Real.goldenRatio - frac n - 1 := by
  rw [delta_eq_floor n, frac, Int.fract]
  push_cast
  ring

/-- The universal correction law for every finite family of orders. -/
theorem sum_law {ι : Type u} (s : Finset ι) (n : ι → ℕ) :
    delta (∑ j ∈ s, n j) - ∑ j ∈ s, delta (n j) =
      ⌊∑ j ∈ s, frac (n j) - ((s.card : ℝ) - 1) * alpha⌋ := by
  symm
  rw [Int.floor_eq_iff]
  have hsum : (∑ j ∈ s, (delta (n j) : ℝ)) =
      ∑ j ∈ s, (((n j : ℝ) + 2) / Real.goldenRatio - frac (n j) - 1) :=
    Finset.sum_congr rfl fun j _ => delta_real (n j)
  have hD := delta_real (∑ j ∈ s, n j)
  have hx0 : 0 ≤ frac (∑ j ∈ s, n j) := Int.fract_nonneg _
  have hx1 : frac (∑ j ∈ s, n j) < 1 := Int.fract_lt_one _
  have key : ((delta (∑ j ∈ s, n j) - ∑ j ∈ s, delta (n j) : ℤ) : ℝ) =
      ∑ j ∈ s, frac (n j) - ((s.card : ℝ) - 1) * alpha - frac (∑ j ∈ s, n j) := by
    push_cast
    rw [hsum, hD, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    push_cast
    have h2 := two_div_phi
    have hp := Real.goldenRatio_pos.ne'
    rw [alpha]
    field_simp
    field_simp at h2
    linear_combination (1 - (s.card : ℝ)) * h2
  rw [key]
  constructor <;> linarith

private theorem alpha_bounds : 0 < alpha ∧ alpha < 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 5
  constructor <;> (rw [alpha]; nlinarith)

private theorem delta_at (n k : ℕ)
    (hl : (k : ℝ) * Real.goldenRatio ≤ (n : ℝ) + 2)
    (hh : (n : ℝ) + 2 < (k + 1 : ℝ) * Real.goldenRatio) : delta n = k - 1 := by
  have hp := Real.goldenRatio_pos
  rw [delta_eq_floor n]
  congr 1
  rw [Int.floor_eq_iff]
  push_cast
  exact ⟨(le_div_iff₀ hp).mpr hl, (div_lt_iff₀ hp).mpr hh⟩

/-- The two-summand law, its three exact regimes, and three witnesses
attaining the values `-1`, `0` and `1` at distinct orders. -/
theorem result :
    (∀ {ι : Type u} (s : Finset ι) (n : ι → ℕ),
      delta (∑ j ∈ s, n j) - ∑ j ∈ s, delta (n j) =
        ⌊∑ j ∈ s, frac (n j) - ((s.card : ℝ) - 1) * alpha⌋) ∧
    (∀ n m : ℕ,
      delta (n + m) - delta n - delta m = ⌊frac n + frac m - alpha⌋ ∧
      (delta (n + m) - delta n - delta m = -1 ↔ frac n + frac m < alpha) ∧
      (delta (n + m) - delta n - delta m = 0 ↔ alpha ≤ frac n + frac m ∧ frac n + frac m < 1 + alpha) ∧
      (delta (n + m) - delta n - delta m = 1 ↔ 1 + alpha ≤ frac n + frac m)) ∧
    delta (3 + 11) - delta 3 - delta 11 = -1 ∧
    delta (3 + 4) - delta 3 - delta 4 = 0 ∧
    delta (4 + 6) - delta 4 - delta 6 = 1 := by
  refine ⟨fun s n => sum_law s n, ?_, ?_⟩
  · intro n m
    have h := sum_law (Finset.univ : Finset (Fin 2)) ![n, m]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Finset.card_univ, Fintype.card_fin] at h
    norm_num at h
    have he : delta (n + m) - delta n - delta m = ⌊frac n + frac m - alpha⌋ := by rw [← h]; ring
    obtain ⟨ha0, ha1⟩ := alpha_bounds
    have hx0 : 0 ≤ frac n := Int.fract_nonneg _
    have hx1 : frac n < 1 := Int.fract_lt_one _
    have hy0 : 0 ≤ frac m := Int.fract_nonneg _
    have hy1 : frac m < 1 := Int.fract_lt_one _
    rw [he]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [Int.floor_eq_iff]
      push_cast
      constructor
      · intro h1; linarith [h1.2]
      · intro h1; constructor <;> linarith
    · rw [Int.floor_eq_iff]
      push_cast
      constructor
      · intro h1; constructor <;> linarith [h1.1, h1.2]
      · intro h1; constructor <;> linarith [h1.1, h1.2]
    · rw [Int.floor_eq_iff]
      push_cast
      constructor
      · intro h1; linarith [h1.1]
      · intro h1; constructor <;> linarith
  · have hlo : (8 : ℝ) / 5 < Real.goldenRatio := by
      rw [Real.goldenRatio]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have hhi : Real.goldenRatio < (13 : ℝ) / 8 := by
      rw [Real.goldenRatio]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have d3 : delta 3 = 2 := by
      have := delta_at 3 3 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    have d4 : delta 4 = 2 := by
      have := delta_at 4 3 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    have d6 : delta 6 = 3 := by
      have := delta_at 6 4 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    have d7 : delta 7 = 4 := by
      have := delta_at 7 5 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    have d10 : delta 10 = 6 := by
      have := delta_at 10 7 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    have d11 : delta 11 = 7 := by
      have := delta_at 11 8 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    have d14 : delta 14 = 8 := by
      have := delta_at 14 9 (by norm_num; linarith) (by norm_num; linarith)
      simpa using this
    norm_num [d3, d4, d6, d7, d10, d11, d14]


#print axioms sum_law
#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw
