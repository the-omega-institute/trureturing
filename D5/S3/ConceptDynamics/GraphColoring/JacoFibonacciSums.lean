/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet]
   utility: none
   digest: Maximum degrees and maximum sets of the finite Jaco graphs at Fibonacci orders and sums of two Fibonacci orders, with the exact exceptions. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-! Finite linear Jaco graphs at Fibonacci orders and their pairwise sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoFibonacciSums

/-
proof_shape:
  eps: definition
  g_pos, g_quad, g_fine, g3, g4, g5, g6, g7: bind-only (consumers: eps_three, eps_four,
    eps_five, eps_even, eps_odd, single_cases, sum_cases)
  eps_pow, eps_three, eps_four, eps_five, eps_even, eps_odd, eps_class: bind-only (consumers:
    eps_class, single_cases, sum_cases)
  fib_ge_two: bind-only (consumers: single_cases, sum_cases)
  criterion: content (consumers: single_cases, sum_cases)
  single_cases, sum_cases: content (consumer: result)
  result: content
escape_witness: the Binet error F_r / phi = F_(r-1) + eps_r with eps_r = -(-1/phi)^r, the
  criterion that an order n with (n + 2)/phi = p + 2/phi + E has maximum degree p exactly when
  2/phi + E >= 1 and the singleton maximum set {p} exactly when moreover E < 2 - 3/phi, and the
  classification of the sign and size of eps_r for r = 3, 4, 5, even r >= 6 and odd r >= 7.
admission_basis: escape-witness
-/

open Nat (fib)
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-- The Binet error `ε_r = F_r / φ - F_(r-1)`. -/
noncomputable def eps (r : ℕ) : ℝ := (fib r : ℝ) * Real.goldenRatio⁻¹ - fib (r - 1)

private theorem g_pos : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos

private theorem g_quad : Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]; ring

private theorem g_fine : (618 : ℝ) / 1000 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < 619 / 1000 := by
  have hq := g_quad
  have hg0 := g_pos
  constructor <;> nlinarith

private theorem g3 : Real.goldenRatio⁻¹ ^ 3 = 2 * Real.goldenRatio⁻¹ - 1 := by
  linear_combination (Real.goldenRatio⁻¹ - 1) * g_quad

private theorem g4 : Real.goldenRatio⁻¹ ^ 4 = 2 - 3 * Real.goldenRatio⁻¹ := by
  linear_combination (Real.goldenRatio⁻¹ ^ 2 - Real.goldenRatio⁻¹ + 2) * g_quad

private theorem g5 : Real.goldenRatio⁻¹ ^ 5 = 5 * Real.goldenRatio⁻¹ - 3 := by
  linear_combination (Real.goldenRatio⁻¹ ^ 3 - Real.goldenRatio⁻¹ ^ 2 + 2 * Real.goldenRatio⁻¹ - 3) *
    g_quad

private theorem g6 : Real.goldenRatio⁻¹ ^ 6 = 5 - 8 * Real.goldenRatio⁻¹ := by
  linear_combination (Real.goldenRatio⁻¹ ^ 4 - Real.goldenRatio⁻¹ ^ 3 + 2 * Real.goldenRatio⁻¹ ^ 2 -
    3 * Real.goldenRatio⁻¹ + 5) * g_quad

private theorem g7 : Real.goldenRatio⁻¹ ^ 7 = 13 * Real.goldenRatio⁻¹ - 8 := by
  linear_combination (Real.goldenRatio⁻¹ ^ 5 - Real.goldenRatio⁻¹ ^ 4 + 2 * Real.goldenRatio⁻¹ ^ 3 -
    3 * Real.goldenRatio⁻¹ ^ 2 + 5 * Real.goldenRatio⁻¹ - 8) * g_quad

/-- Binet: `ε_r = -(-1/φ)^r` for `r ≥ 1`. -/
private theorem eps_pow (r : ℕ) (hr : 1 ≤ r) : eps r = -(-Real.goldenRatio⁻¹) ^ r := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have h := Real.fib_succ_sub_goldenRatio_mul_fib m
  rw [show Real.goldenConj = -Real.goldenRatio⁻¹ by rw [Real.inv_goldenRatio, neg_neg]] at h
  have hφg : Real.goldenRatio * Real.goldenRatio⁻¹ = 1 :=
    mul_inv_cancel₀ Real.goldenRatio_pos.ne'
  rw [eps, Nat.add_sub_cancel]
  linear_combination Real.goldenRatio⁻¹ * h + (Nat.fib m : ℝ) * hφg

private theorem eps_three : eps 3 = 2 * Real.goldenRatio⁻¹ - 1 := by
  rw [eps_pow 3 (by omega), ← g3]; ring

private theorem eps_four : eps 4 = -(2 - 3 * Real.goldenRatio⁻¹) := by
  rw [eps_pow 4 (by omega), ← g4]; ring

private theorem eps_five : eps 5 = 5 * Real.goldenRatio⁻¹ - 3 := by
  rw [eps_pow 5 (by omega), ← g5]; ring

private theorem eps_even (r : ℕ) (hr : 6 ≤ r) (he : Even r) :
    -(5 - 8 * Real.goldenRatio⁻¹) ≤ eps r ∧ eps r < 0 := by
  rw [eps_pow r (by omega), he.neg_pow, ← g6]
  have hg0 := g_pos
  have hg1 : Real.goldenRatio⁻¹ ≤ 1 := by have := g_fine; linarith
  refine ⟨neg_le_neg (pow_le_pow_of_le_one hg0.le hg1 hr), neg_neg_of_pos (pow_pos hg0 r)⟩

private theorem eps_odd (r : ℕ) (hr : 7 ≤ r) (ho : Odd r) :
    0 < eps r ∧ eps r ≤ 13 * Real.goldenRatio⁻¹ - 8 := by
  rw [eps_pow r (by omega), ho.neg_pow, neg_neg, ← g7]
  have hg0 := g_pos
  have hg1 : Real.goldenRatio⁻¹ ≤ 1 := by have := g_fine; linarith
  exact ⟨pow_pos hg0 r, pow_le_pow_of_le_one hg0.le hg1 hr⟩

/-- The five classes of `ε_r` for `r ≥ 3`. -/
private theorem eps_class (r : ℕ) (hr : 3 ≤ r) :
    (r = 3 ∧ eps r = 2 * Real.goldenRatio⁻¹ - 1) ∨
    (r = 4 ∧ eps r = -(2 - 3 * Real.goldenRatio⁻¹)) ∨
    (r = 5 ∧ eps r = 5 * Real.goldenRatio⁻¹ - 3) ∨
    (6 ≤ r ∧ -(5 - 8 * Real.goldenRatio⁻¹) ≤ eps r ∧ eps r < 0) ∨
    (7 ≤ r ∧ 0 < eps r ∧ eps r ≤ 13 * Real.goldenRatio⁻¹ - 8) := by
  rcases (show r = 3 ∨ r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with rfl | rfl | rfl | h6
  · exact Or.inl ⟨rfl, eps_three⟩
  · exact Or.inr (Or.inl ⟨rfl, eps_four⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, eps_five⟩))
  · rcases Nat.even_or_odd r with he | ho
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, eps_even r h6 he⟩)))
    · have h7 : 7 ≤ r := by
        rcases ho with ⟨k, hk⟩; omega
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h7, eps_odd r h7 ho⟩)))

/-- An order `n` with `(n + 2)/φ = p + 2/φ + E` and `0 ≤ 2/φ + E < 2` has maximum degree `p`
exactly when `2/φ + E ≥ 1`, and maximum set `{p}` exactly when moreover `E < 2 - 3/φ`. -/
private theorem criterion (n p : ℕ) (E : ℝ) (hn : 2 ≤ n)
    (h : ((n : ℝ) + 2) * Real.goldenRatio⁻¹ = p + 2 * Real.goldenRatio⁻¹ + E)
    (h0 : 0 ≤ 2 * Real.goldenRatio⁻¹ + E) (h2 : 2 * Real.goldenRatio⁻¹ + E < 2) :
    ((jaco n).maxDegree = p ↔ 1 ≤ 2 * Real.goldenRatio⁻¹ + E) ∧
      (jaconian n = {p} ↔ 1 ≤ 2 * Real.goldenRatio⁻¹ + E ∧ E < 2 - 3 * Real.goldenRatio⁻¹) := by
  obtain ⟨-, hset, hsing, -⟩ := JacoMaximumSet.result
  have hdel := delta_eq_floor n
  rw [delta, div_eq_mul_inv, h] at hdel
  have hmem : (jaco n).maxDegree ∈ jaconian n := by
    have hne : (jaconian n).Nonempty := by
      rw [← Finset.card_pos]; rcases (hset n hn).2.2.2 with h | h | h <;> omega
    rw [(hset n hn).2.1] at hne ⊢
    exact Finset.mem_Icc.mpr ⟨le_rfl, Finset.nonempty_Icc.mp hne⟩
  have hdeg : (jaco n).maxDegree = p ↔ 1 ≤ 2 * Real.goldenRatio⁻¹ + E := by
    constructor
    · intro hp
      by_contra hlt
      push Not at hlt
      have hf : ⌊(p : ℝ) + 2 * Real.goldenRatio⁻¹ + E⌋ = p := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [hf, hp] at hdel
      omega
    · intro h1
      have hf : ⌊(p : ℝ) + 2 * Real.goldenRatio⁻¹ + E⌋ = p + 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [hf] at hdel
      omega
  refine ⟨hdeg, ?_⟩
  constructor
  · intro hJ
    have hp : (jaco n).maxDegree = p := by
      rw [hJ, Finset.mem_singleton] at hmem; exact hmem
    have h1 := hdeg.mp hp
    refine ⟨h1, ?_⟩
    have hs := ((hsing n hn).1).mp (by rw [hp]; exact hJ)
    have hfr : frac n = 2 * Real.goldenRatio⁻¹ + E - 1 := by
      rw [frac, Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, p + 1, ?_⟩
      rw [div_eq_mul_inv, h]; push_cast; ring
    rw [hfr] at hs
    linarith
  · rintro ⟨h1, hE⟩
    have hp := hdeg.mpr h1
    have hfr : frac n = 2 * Real.goldenRatio⁻¹ + E - 1 := by
      rw [frac, Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, p + 1, ?_⟩
      rw [div_eq_mul_inv, h]; push_cast; ring
    have hs : frac n < 1 - Real.goldenRatio⁻¹ := by rw [hfr]; linarith
    have := ((hsing n hn).1).mpr hs
    rw [hp] at this
    exact this

private theorem fib_ge_two (r : ℕ) (hr : 3 ≤ r) : 2 ≤ fib r := by
  have h3 : fib 3 = 2 := by decide
  have := Nat.fib_mono hr
  omega

/-- Single Fibonacci orders. -/
private theorem single_cases (r : ℕ) (hr : 3 ≤ r) :
    (jaco (fib r)).maxDegree = fib (r - 1) ∧ (jaconian (fib r) = {fib (r - 1)} ↔ 4 ≤ r) := by
  have hc := criterion (fib r) (fib (r - 1)) (eps r) (fib_ge_two r hr)
    (by rw [eps]; ring)
  have hg := g_fine
  rcases eps_class r hr with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨h6, he1, he2⟩ | ⟨h7, he1, he2⟩ <;>
  · obtain ⟨hd, hs⟩ := hc (by linarith) (by linarith)
    refine ⟨hd.mpr (by linarith), ?_⟩
    rw [hs]
    constructor
    · rintro ⟨-, hE⟩
      first | omega | (exfalso; linarith)
    · intro h4
      first | (exfalso; omega) | exact ⟨by linarith, by linarith⟩

/-- Sums of two Fibonacci orders. -/
private theorem sum_cases (r s : ℕ) (hr : 3 ≤ r) (hs : 3 ≤ s) :
    ((jaco (fib r + fib s)).maxDegree = fib (r - 1) + fib (s - 1) ↔ ¬(r = 4 ∧ s = 4)) ∧
      (jaconian (fib r + fib s) = {fib (r - 1) + fib (s - 1)} ↔
        ¬(r = 4 ∧ s = 4) ∧ ¬(r = 5 ∧ s = 5) ∧ (r = 3 → s = 4) ∧ (s = 3 → r = 4)) := by
  have hc := criterion (fib r + fib s) (fib (r - 1) + fib (s - 1)) (eps r + eps s)
    (by have := fib_ge_two r hr; omega) (by rw [eps, eps]; push_cast; ring)
  have hg := g_fine
  rcases eps_class r hr with ⟨rfl, hr'⟩ | ⟨rfl, hr'⟩ | ⟨rfl, hr'⟩ | ⟨hr6, hr1, hr2⟩ | ⟨hr7, hr1, hr2⟩ <;>
  rcases eps_class s hs with ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨hs6, hs1, hs2⟩ | ⟨hs7, hs1, hs2⟩ <;>
  · obtain ⟨hd, hJ⟩ := hc (by linarith) (by linarith)
    rw [hd, hJ]
    constructor
    · constructor
      · intro h
        first | omega | (exfalso; linarith)
      · intro h
        first | linarith | (exfalso; omega)
    · constructor
      · rintro ⟨h1, h2⟩
        first | omega | (exfalso; linarith)
      · intro h
        first | exact ⟨by linarith, by linarith⟩ | (exfalso; omega)

/-- Fibonacci orders and pairwise sums of Fibonacci orders in the finite linear Jaco graphs.
For `r ≥ 3`, `Δ_(F_r) = F_(r-1)`, with maximum set `{F_(r-1)}` exactly when `r ≥ 4`. For
`r, s ≥ 3`, `Δ_(F_r + F_s) = F_(r-1) + F_(s-1)` except at `r = s = 4`, and the maximum set is
`{F_(r-1) + F_(s-1)}` except at `r = s = 4`, `r = s = 5` and the pairs with a `3` other than
`{3, 4}`. For distinct Fibonacci orders with `r, s ≥ 4` both additive assertions hold. -/
theorem result :
    (∀ r, 3 ≤ r → (jaco (fib r)).maxDegree = fib (r - 1) ∧
      (jaconian (fib r) = {fib (r - 1)} ↔ 4 ≤ r)) ∧
    (∀ r s, 3 ≤ r → 3 ≤ s →
      ((jaco (fib r + fib s)).maxDegree = fib (r - 1) + fib (s - 1) ↔ ¬(r = 4 ∧ s = 4))) ∧
    (∀ r s, 3 ≤ r → 3 ≤ s →
      (jaconian (fib r + fib s) = {fib (r - 1) + fib (s - 1)} ↔
        ¬(r = 4 ∧ s = 4) ∧ ¬(r = 5 ∧ s = 5) ∧ (r = 3 → s = 4) ∧ (s = 3 → r = 4))) ∧
    (∀ r s, 4 ≤ r → 4 ≤ s → fib r ≠ fib s →
      (jaco (fib r + fib s)).maxDegree = (jaco (fib r)).maxDegree + (jaco (fib s)).maxDegree ∧
      jaconian (fib r + fib s) = {(jaco (fib r)).maxDegree + (jaco (fib s)).maxDegree}) := by
  refine ⟨single_cases, fun r s hr hs => (sum_cases r s hr hs).1,
    fun r s hr hs => (sum_cases r s hr hs).2, ?_⟩
  intro r s hr hs hne
  have hrs : r ≠ s := fun h => hne (h ▸ rfl)
  rw [(single_cases r (by omega)).1, (single_cases s (by omega)).1]
  obtain ⟨hd, hJ⟩ := sum_cases r s (by omega) (by omega)
  exact ⟨hd.mpr (by omega), hJ.mpr ⟨by omega, by omega, by omega, by omega⟩⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoFibonacciSums
