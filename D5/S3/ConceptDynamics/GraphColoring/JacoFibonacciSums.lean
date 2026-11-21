/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet, lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw]
   utility: none
   digest: Exact maximum degrees and maximum sets of the finite Jaco graphs at Fibonacci orders and at sums of two Fibonacci orders. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-! Finite linear Jaco graphs at Fibonacci orders and their pairwise sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoFibonacciSums

/-
proof_shape:
  eps: definition
  g_pos: bind-only (consumers: g_fine, eps_even, eps_odd)
  g_quad: bind-only (consumers: g_fine, g3, g4, g5, g6, g7, core)
  g_fine: bind-only (consumers: eps_even, eps_odd, core, single_exact, sum_exact)
  g3, g4, g5, g6, g7: bind-only (consumers: eps_three, eps_four, eps_five, eps_even, eps_odd)
  eps_pow: bind-only (consumers: eps_three, eps_four, eps_five, eps_even, eps_odd)
  eps_three, eps_four, eps_five, eps_even, eps_odd: bind-only (consumers: eps_class, sum_exact)
  eps_class: bind-only (consumers: single_exact, sum_exact)
  fib_ge_two: bind-only (consumers: single_exact, sum_exact)
  core: content (consumers: single_exact, sum_exact)
  single_exact, sum_exact: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.delta_eq_floor (statement_id
    sha256:289669fd9ce5e9c638eb5eb4c27e641b00d3b68fa3cf9720a425b277073d78ff)
  D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.result (statement_id
    sha256:d31cfe56216a7368dfd3700d57fd0f68ca52816f38e6d48739b538a93e32a20f)
escape_witness: the Binet error F_r / phi = F_(r-1) + eps_r with eps_r = -(-1/phi)^r and the
  classification of eps_r for r = 3, 4, 5, even r >= 6 and odd r >= 7; and the exact reading
  in core: (n + 2)/phi = (q + 1) + x with c (1 - 1/phi) <= x < (c + 1)(1 - 1/phi) forces
  Delta_n = q and J_n = [q, q + c], because (x - c/phi^2) phi^2 = x phi^2 - c.
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

/-- An order `n ≥ 2` with `(n + 2)/φ = (q + 1) + x`, `0 ≤ x < 1` and
`c (1 - 1/φ) ≤ x < (c + 1)(1 - 1/φ)` has `Δ_n = q` and `J_n = [q, q + c]`. -/
private theorem core (n q c : ℕ) (x : ℝ) (hn : 2 ≤ n)
    (h : ((n : ℝ) + 2) * Real.goldenRatio⁻¹ = ((q : ℝ) + 1) + x) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hc0 : (c : ℝ) * (1 - Real.goldenRatio⁻¹) ≤ x)
    (hc1 : x < ((c : ℝ) + 1) * (1 - Real.goldenRatio⁻¹)) :
    (jaco n).maxDegree = q ∧ jaconian n = Finset.Icc q (q + c) := by
  obtain ⟨-, hset, -, -⟩ := JacoMaximumSet.result
  have hq := g_quad
  have hg := g_fine
  set g := Real.goldenRatio⁻¹ with hgdef
  have hdel := delta_eq_floor n
  have hf : ⌊((n : ℝ) + 2) / Real.goldenRatio⌋ = q + 1 := by
    rw [Int.floor_eq_iff, div_eq_mul_inv, ← hgdef, h]; push_cast; constructor <;> linarith
  rw [delta, hf] at hdel
  have hP : (jaco n).maxDegree = q := by omega
  have hfr : frac n = x := by
    rw [frac, Int.fract_eq_iff]
    refine ⟨hx0, hx1, q + 1, ?_⟩
    rw [div_eq_mul_inv, ← hgdef, h]; push_cast; ring
  have hphi : Real.goldenRatio = 1 + g := by
    rw [hgdef, Real.inv_goldenRatio]; linarith [Real.one_sub_goldenConj]
  have hsq : Real.goldenRatio ^ 2 = 2 + g := by rw [hphi]; nlinarith
  have key : x * (2 + g) - c = (x - c * (1 - g)) * (2 + g) := by
    linear_combination (-(c : ℝ)) * hq
  have hfl : ⌊x * Real.goldenRatio ^ 2⌋ = c := by
    rw [hsq, Int.floor_eq_iff]
    have hlo : 0 ≤ (x - c * (1 - g)) * (2 + g) := mul_nonneg (by linarith) (by linarith)
    have hhi : (x - c * (1 - g)) * (2 + g) < 1 := by
      have : x - c * (1 - g) < 1 - g := by linarith
      nlinarith
    push_cast
    constructor <;> linarith
  obtain ⟨-, hJ, hcard, -⟩ := hset n hn
  rw [hfr, hfl, hJ, Nat.card_Icc, hP] at hcard
  rw [hJ, hP]
  refine ⟨rfl, ?_⟩
  congr 1
  omega

private theorem fib_ge_two (r : ℕ) (hr : 3 ≤ r) : 2 ≤ fib r := by
  have h3 : fib 3 = 2 := by decide
  have := Nat.fib_mono hr
  omega

/-- Single Fibonacci orders: `Δ_(F_r) = F_(r-1)` and `J_(F_r) = [F_(r-1), F_(r-1) + [r = 3]]`. -/
private theorem single_exact (r : ℕ) (hr : 3 ≤ r) :
    (jaco (fib r)).maxDegree = fib (r - 1) ∧
      jaconian (fib r) = Finset.Icc (fib (r - 1)) (fib (r - 1) + if r = 3 then 1 else 0) := by
  have hg := g_fine
  have hh : ((fib r : ℕ) + 2 : ℝ) * Real.goldenRatio⁻¹ =
      ((fib (r - 1) : ℕ) + 1 : ℝ) + (2 * Real.goldenRatio⁻¹ + eps r - 1) := by
    rw [eps]; ring
  rcases eps_class r hr with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨h6, he1, he2⟩ | ⟨h7, he1, he2⟩
  · simpa using core _ _ 1 _ (fib_ge_two 3 le_rfl) hh (by linarith) (by linarith)
      (by push_cast; linarith) (by push_cast; linarith)
  all_goals
    have hc := core _ _ 0 _ (fib_ge_two _ hr) hh (by linarith) (by linarith)
      (by push_cast; linarith) (by push_cast; linarith)
    first | simpa using hc | simpa [show ¬r = 3 by omega] using hc

/-- The correction `c(r, s)` of the maximum set at `F_r + F_s`. -/
private theorem sum_exact (r s : ℕ) (hr : 3 ≤ r) (hs : 3 ≤ s) :
    (jaco (fib r + fib s)).maxDegree = fib (r - 1) + fib (s - 1) - (if r = 4 ∧ s = 4 then 1 else 0) ∧
      jaconian (fib r + fib s) = Finset.Icc (jaco (fib r + fib s)).maxDegree
        ((jaco (fib r + fib s)).maxDegree + if r = 4 ∧ s = 4 then 2 else
          if (r = 5 ∧ s = 5) ∨ (r = 3 ∧ s ≠ 4) ∨ (s = 3 ∧ r ≠ 4) then 1 else 0) := by
  have hg := g_fine
  have hn : 2 ≤ fib r + fib s := by have := fib_ge_two r hr; omega
  have hh : ((fib r + fib s : ℕ) + 2 : ℝ) * Real.goldenRatio⁻¹ =
      ((fib (r - 1) + fib (s - 1) : ℕ) + 1 : ℝ) + (2 * Real.goldenRatio⁻¹ + (eps r + eps s) - 1) := by
    rw [eps, eps]; push_cast; ring
  by_cases h44 : r = 4 ∧ s = 4
  · obtain ⟨rfl, rfl⟩ := h44
    have hf3 : fib (4 - 1) = 2 := by decide
    have hh' : ((fib 4 + fib 4 : ℕ) + 2 : ℝ) * Real.goldenRatio⁻¹ =
        ((3 : ℕ) + 1 : ℝ) + (2 * Real.goldenRatio⁻¹ + (eps 4 + eps 4)) := by
      rw [hh, hf3]; push_cast; ring
    have hc := core _ 3 2 _ hn hh' (by rw [eps_four]; linarith) (by rw [eps_four]; linarith)
      (by rw [eps_four]; push_cast; linarith) (by rw [eps_four]; push_cast; linarith)
    simp only [and_self, ↓reduceIte, hf3]
    rw [hc.1, hc.2]
    exact ⟨rfl, rfl⟩
  · by_cases h1 : (r = 5 ∧ s = 5) ∨ (r = 3 ∧ s ≠ 4) ∨ (s = 3 ∧ r ≠ 4)
    · simp only [h44, h1, ↓reduceIte, Nat.sub_zero]
      have hb : 2 - 3 * Real.goldenRatio⁻¹ ≤ eps r + eps s ∧
          eps r + eps s < 3 - 4 * Real.goldenRatio⁻¹ := by
        rcases eps_class r hr with ⟨rfl, hr'⟩ | ⟨rfl, hr'⟩ | ⟨rfl, hr'⟩ | ⟨hr6, hr1, hr2⟩ |
            ⟨hr7, hr1, hr2⟩ <;>
        rcases eps_class s hs with ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨hs6, hs1, hs2⟩ |
            ⟨hs7, hs1, hs2⟩ <;>
        first | (exfalso; omega) | (constructor <;> linarith)
      have hc := core _ _ 1 _ hn hh (by linarith) (by linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      rw [hc.1, hc.2]
      exact ⟨rfl, rfl⟩
    · simp only [h44, h1, ↓reduceIte, Nat.sub_zero, Nat.add_zero]
      have hb : -(2 * Real.goldenRatio⁻¹ - 1) ≤ eps r + eps s ∧
          eps r + eps s < 2 - 3 * Real.goldenRatio⁻¹ := by
        rcases eps_class r hr with ⟨rfl, hr'⟩ | ⟨rfl, hr'⟩ | ⟨rfl, hr'⟩ | ⟨hr6, hr1, hr2⟩ |
            ⟨hr7, hr1, hr2⟩ <;>
        rcases eps_class s hs with ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨hs6, hs1, hs2⟩ |
            ⟨hs7, hs1, hs2⟩ <;>
        first | (exfalso; omega) | (constructor <;> linarith)
      have hc := core _ _ 0 _ hn hh (by linarith) (by linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      rw [hc.1, hc.2]
      exact ⟨rfl, by simp⟩

/-- Fibonacci orders and pairwise sums of Fibonacci orders in the finite linear Jaco graphs.
For `r ≥ 3`, `Δ_(F_r) = F_(r-1)` and `J_(F_r) = [F_(r-1), F_(r-1) + [r = 3]]`. For `r, s ≥ 3`,
`Δ_(F_r + F_s) = F_(r-1) + F_(s-1) - [r = s = 4]` and `J_(F_r + F_s) = [Δ, Δ + c]` with `c = 2`
at `r = s = 4`, `c = 1` at `r = s = 5` and at the pairs containing a `3` other than `{3, 4}`,
and `c = 0` otherwise. For distinct Fibonacci orders with `r, s ≥ 4`,
`Δ_(F_r + F_s) = Δ_(F_r) + Δ_(F_s)` and `J_(F_r + F_s) = {Δ_(F_r) + Δ_(F_s)}`. -/
theorem result :
    (∀ r, 3 ≤ r → (jaco (fib r)).maxDegree = fib (r - 1) ∧
      jaconian (fib r) = Finset.Icc (fib (r - 1)) (fib (r - 1) + if r = 3 then 1 else 0)) ∧
    (∀ r s, 3 ≤ r → 3 ≤ s →
      (jaco (fib r + fib s)).maxDegree = fib (r - 1) + fib (s - 1) - (if r = 4 ∧ s = 4 then 1 else 0) ∧
      jaconian (fib r + fib s) = Finset.Icc (jaco (fib r + fib s)).maxDegree
        ((jaco (fib r + fib s)).maxDegree + if r = 4 ∧ s = 4 then 2 else
          if (r = 5 ∧ s = 5) ∨ (r = 3 ∧ s ≠ 4) ∨ (s = 3 ∧ r ≠ 4) then 1 else 0)) ∧
    (∀ r s, 4 ≤ r → 4 ≤ s → fib r ≠ fib s →
      (jaco (fib r + fib s)).maxDegree = (jaco (fib r)).maxDegree + (jaco (fib s)).maxDegree ∧
      jaconian (fib r + fib s) = {(jaco (fib r)).maxDegree + (jaco (fib s)).maxDegree}) := by
  refine ⟨single_exact, sum_exact, ?_⟩
  intro r s hr hs hne
  have hrs : r ≠ s := fun h => hne (h ▸ rfl)
  rw [(single_exact r (by omega)).1, (single_exact s (by omega)).1]
  obtain ⟨hd, hJ⟩ := sum_exact r s (by omega) (by omega)
  have h44 : ¬(r = 4 ∧ s = 4) := by omega
  have h1 : ¬((r = 5 ∧ s = 5) ∨ (r = 3 ∧ s ≠ 4) ∨ (s = 3 ∧ r ≠ 4)) := by omega
  simp only [h44, h1, ↓reduceIte, Nat.sub_zero, Nat.add_zero] at hd hJ
  rw [hJ, hd]
  exact ⟨rfl, by simp⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoFibonacciSums
