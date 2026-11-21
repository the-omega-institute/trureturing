/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet]
   utility: none
   digest: The finite Jaco graphs with three maximum-degree vertices are exactly the orders 3j + 1 + 2 b_j, j >= 1, with gaps 3 or 5. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-! Orders of the finite linear Jaco graphs with three maximum-degree vertices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoTripleMaximizers

/-
proof_shape:
  orders: definition
  g_pos, g_quad, g_fine, g_ne: bind-only (consumers: bo_le, bo_eq_iff, bo_zero, card_three_iff,
    shape, frac_bounds, gap, e_bounds, orders_three, between, result)
  bo_le, bo_eq_iff, bo_mono, bo_zero: bind-only (consumers: closed_form, card_three_iff,
    shape_floor, frac_bounds, gap, between, result)
  shape, shape_floor, frac_bounds, gap, e_bounds: bind-only (consumers: orders_three, between,
    increments)
  closed_form: content (consumers: shape, between, increments, enumerate, result)
  card_three_iff: content (consumers: enumerate, result)
  orders_three, between: content (consumer: enumerate)
  increments, strictMono_orders, bracket: content (consumers: bracket, enumerate, result)
  enumerate: content (consumer: result)
  result: content
escape_witness: the golden identity (p_j + 2 + i) / phi = (b_j + 2j + 1) + (1 - f_j (2/phi - 1))
  + i / phi with f_j = fract((j + 1) / phi), which places every order between p_j and
  p_(j+1) at an exact floor pattern; the criterion card J_n = 3 iff b_(n+3) = b_(n+1) + 2
  from x_n phi^2 - 2 = (x_n - 2/phi^2) phi^2; and the bracketing induction that turns the
  pattern into the exact enumeration.
admission_basis: escape-witness
-/

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-- The source recurrence `p_0 = 1`,
`p_(j+1) = p_j + 3 + 2 (⌊(j + 2)/φ⌋ - ⌊(j + 1)/φ⌋)`. -/
noncomputable def orders : ℕ → ℕ
  | 0 => 1
  | j + 1 => orders j + 3 + 2 * (beattyOut (j + 1) - beattyOut j)

private theorem g_pos : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos

private theorem g_quad : Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]; ring

private theorem g_fine : (61 : ℝ) / 100 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < 5 / 8 := by
  have hq := g_quad
  have hg0 := g_pos
  constructor <;> nlinarith

private theorem g_ne (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : (k : ℝ) * Real.goldenRatio⁻¹ ≠ m :=
  (Real.goldenRatio_irrational.inv.natCast_mul (by omega)).ne_int m

private theorem bo_le (k : ℕ) :
    (beattyOut k : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ ∧
      ((k : ℝ) + 1) * Real.goldenRatio⁻¹ < beattyOut k + 1 := by
  have hpos : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ := by have := g_pos; positivity
  rw [beattyOut, ← div_eq_mul_inv]
  rw [← div_eq_mul_inv] at hpos
  exact ⟨Nat.floor_le hpos, Nat.lt_floor_add_one _⟩

private theorem bo_eq_iff (k N : ℕ) :
    beattyOut k = N ↔
      (N : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ ∧
        ((k : ℝ) + 1) * Real.goldenRatio⁻¹ < N + 1 := by
  have hpos : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ := by have := g_pos; positivity
  rw [beattyOut, ← div_eq_mul_inv]
  rw [← div_eq_mul_inv] at hpos
  exact Nat.floor_eq_iff hpos

private theorem bo_mono (k : ℕ) : beattyOut k ≤ beattyOut (k + 1) := by
  apply Nat.floor_le_floor
  have := Real.goldenRatio_pos
  push_cast
  gcongr
  linarith

private theorem bo_zero : beattyOut 0 = 0 := by
  rw [bo_eq_iff]
  have := g_fine
  push_cast
  constructor <;> linarith

/-- Closed form `p_j = 3j + 1 + 2 b_j`. -/
private theorem closed_form (j : ℕ) : orders j = 3 * j + 1 + 2 * beattyOut j := by
  induction j with
  | zero => simp [orders, bo_zero]
  | succ j ih =>
    have := bo_mono j
    rw [orders, ih]
    omega

/-- For `n ≥ 2`, `J_n` has three vertices exactly when `b_(n+3) = b_(n+1) + 2`. -/
private theorem card_three_iff (n : ℕ) (hn : 2 ≤ n) :
    (jaconian n).card = 3 ↔ beattyOut (n + 3) = beattyOut (n + 1) + 2 := by
  obtain ⟨-, hcard, -, -⟩ := JacoMaximumSet.result
  have hc := (hcard n hn).2.2.1
  have hq := g_quad
  have hg := g_fine
  set g := Real.goldenRatio⁻¹ with hgdef
  obtain ⟨hB1, hB2⟩ := bo_le (n + 1)
  set B := beattyOut (n + 1)
  set x := ((n : ℝ) + 2) * g - B with hx
  have hx0 : 0 ≤ x := by push_cast at hB1; linarith
  have hx1 : x < 1 := by push_cast at hB2; linarith
  have hfrac : frac n = x := by
    rw [frac, Int.fract_eq_iff]
    refine ⟨hx0, hx1, B, ?_⟩
    rw [hx, div_eq_mul_inv]; push_cast; ring
  have hphi : Real.goldenRatio = 1 + g := by
    rw [hgdef, Real.inv_goldenRatio]; linarith [Real.one_sub_goldenConj]
  have hsq : Real.goldenRatio ^ 2 = 2 + g := by rw [hphi]; nlinarith
  rw [hfrac, hsq] at hc
  have key : x * (2 + g) - 2 = (x - (2 - 2 * g)) * (2 + g) := by
    linear_combination (-2 : ℝ) * hq
  rw [bo_eq_iff]
  push_cast
  constructor
  · intro h3
    have hfl : ⌊x * (2 + g)⌋ = 2 := by
      have : ((jaconian n).card : ℤ) = 3 := by exact_mod_cast h3
      omega
    rw [Int.floor_eq_iff] at hfl
    push_cast at hfl
    have hge : 0 ≤ (x - (2 - 2 * g)) * (2 + g) := by linarith [hfl.1]
    have hx2 : 2 - 2 * g ≤ x := by
      by_contra hlt
      push Not at hlt
      have : (x - (2 - 2 * g)) * (2 + g) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith
    constructor <;> linarith
  · intro hD
    have hx2 : 2 - 2 * g ≤ x := by linarith [hD.1]
    have hfl : ⌊x * (2 + g)⌋ = 2 := by
      rw [Int.floor_eq_iff]
      push_cast
      have : 0 ≤ (x - (2 - 2 * g)) * (2 + g) := mul_nonneg (by linarith) (by linarith)
      constructor
      · linarith
      · nlinarith
    have : ((jaconian n).card : ℤ) = 3 := by omega
    exact_mod_cast this

/-- The golden identity behind the enumeration. -/
private theorem shape (j i : ℕ) :
    (((orders j + 1 + i : ℕ) : ℝ) + 1) * Real.goldenRatio⁻¹ =
      ((beattyOut j + 2 * j + 1 : ℕ) : ℝ) +
        (1 - (((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j) * (2 * Real.goldenRatio⁻¹ - 1)) +
        (i : ℝ) * Real.goldenRatio⁻¹ := by
  rw [closed_form]
  push_cast
  linear_combination (2 * ((j : ℝ) + 1)) * g_quad

private theorem shape_floor (j i k : ℕ)
    (h : (k : ℝ) ≤ (1 - (((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j) *
        (2 * Real.goldenRatio⁻¹ - 1)) + (i : ℝ) * Real.goldenRatio⁻¹ ∧
      (1 - (((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j) *
        (2 * Real.goldenRatio⁻¹ - 1)) + (i : ℝ) * Real.goldenRatio⁻¹ < k + 1) :
    beattyOut (orders j + 1 + i) = beattyOut j + 2 * j + 1 + k := by
  rw [bo_eq_iff, shape]
  push_cast at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `f_j = fract((j + 1)/φ)` lies strictly inside `(0, 1)`, and decides the next gap. -/
private theorem frac_bounds (j : ℕ) :
    0 < ((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j ∧
      ((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j < 1 ∧
      ((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j ≠ 1 - Real.goldenRatio⁻¹ := by
  obtain ⟨h1, h2⟩ := bo_le j
  refine ⟨?_, by linarith, ?_⟩
  · have hne := g_ne (j + 1) (by omega) (beattyOut j)
    push_cast at hne
    exact lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
  · intro h
    have hne := g_ne (j + 2) (by omega) (beattyOut j + 1)
    push_cast at hne
    exact hne (by linarith)

/-- The next gap: `b_(j+1) = b_j` when `f_j < 1 - 1/φ`, and `b_(j+1) = b_j + 1` otherwise. -/
private theorem gap (j : ℕ) :
    (((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j < 1 - Real.goldenRatio⁻¹ →
        beattyOut (j + 1) = beattyOut j) ∧
      (1 - Real.goldenRatio⁻¹ < ((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j →
        beattyOut (j + 1) = beattyOut j + 1) := by
  obtain ⟨h0, h1, -⟩ := frac_bounds j
  have hg := g_fine
  constructor
  · intro h
    rw [bo_eq_iff]; push_cast
    constructor <;> nlinarith
  · intro h
    rw [bo_eq_iff]; push_cast
    constructor <;> nlinarith

private theorem e_bounds (j : ℕ) :
    0 < (((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j) * (2 * Real.goldenRatio⁻¹ - 1) ∧
      (((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j) * (2 * Real.goldenRatio⁻¹ - 1) <
        2 * Real.goldenRatio⁻¹ - 1 := by
  obtain ⟨h0, h1, -⟩ := frac_bounds j
  have hg := g_fine
  have ha : 0 < 2 * Real.goldenRatio⁻¹ - 1 := by linarith
  exact ⟨mul_pos h0 ha, by nlinarith⟩

/-- Every `p_j` satisfies the three-vertex criterion. -/
private theorem orders_three (j : ℕ) :
    beattyOut (orders j + 3) = beattyOut (orders j + 1) + 2 := by
  obtain ⟨he0, he1⟩ := e_bounds j
  have hg := g_fine
  have h0 := shape_floor j 0 0 (by push_cast; constructor <;> linarith)
  have h2 := shape_floor j 2 2 (by push_cast; constructor <;> linarith)
  rw [Nat.add_zero] at h0
  rw [show orders j + 3 = orders j + 1 + 2 by omega, h2, h0]

/-- No order strictly between `p_j` and `p_(j+1)` satisfies the criterion. -/
private theorem between (j i : ℕ) (hi : 1 ≤ i) (hlt : orders j + i < orders (j + 1)) :
    beattyOut (orders j + i + 3) ≠ beattyOut (orders j + i + 1) + 2 := by
  obtain ⟨he0, he1⟩ := e_bounds j
  obtain ⟨hf0, hf1, hfne⟩ := frac_bounds j
  have hg := g_fine
  have hq := g_quad
  obtain ⟨gap0, gap1⟩ := gap j
  have hc := closed_form j
  have hc1 := closed_form (j + 1)
  have hmono := bo_mono j
  rw [show orders j + i + 3 = orders j + 1 + (i + 2) by omega,
    show orders j + i + 1 = orders j + 1 + i by omega]
  set f := ((j : ℝ) + 1) * Real.goldenRatio⁻¹ - beattyOut j
  set g := Real.goldenRatio⁻¹
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by
    rcases lt_or_gt_of_ne hfne with h | h
    · have := gap0 h; omega
    · have := gap1 h; omega) with rfl | rfl | rfl | rfl
  · rw [shape_floor j 1 1 (by push_cast; constructor <;> linarith),
      shape_floor j (1 + 2) 2 (by push_cast; constructor <;> linarith)]
    omega
  · rw [shape_floor j 2 2 (by push_cast; constructor <;> linarith),
      shape_floor j (2 + 2) 3 (by push_cast; constructor <;> linarith)]
    omega
  · have hf : 1 - g < f := by
      rcases lt_or_gt_of_ne hfne with h | h
      · have := gap0 h; omega
      · exact h
    have hk : (1 - g) * (2 * g - 1) = 5 * g - 3 := by linear_combination (-2 : ℝ) * hq
    have hfe : (1 - g) * (2 * g - 1) < f * (2 * g - 1) :=
      mul_lt_mul_of_pos_right hf (by linarith)
    rw [shape_floor j 3 2 (by push_cast; constructor <;> linarith),
      shape_floor j (3 + 2) 3 (by push_cast; constructor <;> linarith)]
    omega
  · have hf : 1 - g < f := by
      rcases lt_or_gt_of_ne hfne with h | h
      · have := gap0 h; omega
      · exact h
    rw [shape_floor j 4 3 (by push_cast; constructor <;> linarith),
      shape_floor j (4 + 2) 4 (by push_cast; constructor <;> linarith)]
    omega

/-- The gaps are `3` or `5`. -/
private theorem increments (j : ℕ) :
    orders (j + 1) = orders j + 3 ∨ orders (j + 1) = orders j + 5 := by
  have hc := closed_form j
  have hc1 := closed_form (j + 1)
  obtain ⟨-, -, hfne⟩ := frac_bounds j
  obtain ⟨gap0, gap1⟩ := gap j
  rcases lt_or_gt_of_ne hfne with h | h
  · have := gap0 h; omega
  · have := gap1 h; omega

private theorem strictMono_orders : StrictMono orders :=
  strictMono_nat_of_lt_succ fun j => by rcases increments j with h | h <;> omega

/-- Every order `n ≥ 1` lies in some `[p_j, p_(j+1))`. -/
private theorem bracket (n : ℕ) (hn : 1 ≤ n) : ∃ j, orders j ≤ n ∧ n < orders (j + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have h0 := closed_form 0
      have h1 := closed_form 1
      rw [bo_zero] at h0
      exact ⟨0, by omega, by simp only [Nat.zero_add]; omega⟩
    · obtain ⟨j, hj1, hj2⟩ := ih hpos
      by_cases h : n + 1 < orders (j + 1)
      · exact ⟨j, by omega, h⟩
      · have hs : orders (j + 1) < orders (j + 1 + 1) := strictMono_orders (by omega)
        exact ⟨j + 1, by omega, by omega⟩

/-- The exact enumeration. -/
private theorem enumerate (n : ℕ) : (jaconian n).card = 3 ↔ ∃ j, 1 ≤ j ∧ orders j = n := by
  constructor
  · intro h3
    have hn2 : 2 ≤ n := by
      rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h
      · exfalso
        have : (jaconian 0).card = 0 := by
          unfold jaconian
          rw [Finset.card_map]
          apply Nat.eq_zero_of_le_zero
          calc _ ≤ (Finset.univ : Finset (Vertex 0)).card := Finset.card_filter_le _ _
            _ = 0 := by simp
        omega
      · exfalso
        obtain ⟨h1, -⟩ := JacoMaximumSet.result
        rw [h1] at h3
        simp at h3
      · exact h
    have hD := (card_three_iff n hn2).mp h3
    obtain ⟨j, hj1, hj2⟩ := bracket n (by omega)
    by_cases heq : orders j = n
    · refine ⟨j, ?_, heq⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [orders] at heq; omega
      · exact hj
    · exfalso
      obtain ⟨i, rfl⟩ : ∃ i, n = orders j + i := ⟨n - orders j, by omega⟩
      exact between j i (by omega) hj2 hD
  · rintro ⟨j, hj, rfl⟩
    have hc := closed_form j
    exact (card_three_iff _ (by omega)).mpr (orders_three j)

/-- The orders `n` with `|J_n| = 3` are exactly `p_1, p_2, … = 6, 9, 14, 19, 22, …`, where
`p_j = 3j + 1 + 2 b_j` solves the source recurrence; the gaps are `3` or `5`, a `3` is always
followed by a `5`, and two consecutive `5`s are always followed by a `3`. -/
theorem result :
    (∀ j, orders j = 3 * j + 1 + 2 * beattyOut j) ∧
    (∀ n, 2 ≤ n → ((jaconian n).card = 3 ↔ beattyOut (n + 3) = beattyOut (n + 1) + 2)) ∧
    (∀ n, (jaconian n).card = 3 ↔ ∃ j, 1 ≤ j ∧ orders j = n) ∧
    StrictMono orders ∧
    (∀ j, orders (j + 1) = orders j + 3 ∨ orders (j + 1) = orders j + 5) ∧
    (∀ j, orders (j + 1) = orders j + 3 → orders (j + 2) = orders (j + 1) + 5) ∧
    (∀ j, orders (j + 1) = orders j + 5 → orders (j + 2) = orders (j + 1) + 5 →
      orders (j + 3) = orders (j + 2) + 3) := by
  refine ⟨closed_form, card_three_iff, enumerate, strictMono_orders, increments, ?_, ?_⟩
  · intro j h3
    have hc := closed_form j
    have hc1 := closed_form (j + 1)
    have hc2 := closed_form (j + 2)
    obtain ⟨h1, h2⟩ := bo_le j
    have hb2 : beattyOut j + 1 ≤ beattyOut (j + 2) := by
      by_contra hlt
      have hle : (beattyOut (j + 2) : ℝ) ≤ beattyOut j := by
        exact_mod_cast (by omega : beattyOut (j + 2) ≤ beattyOut j)
      have := (bo_le (j + 2)).2
      have := g_fine
      push_cast at *
      linarith
    have inc := increments (j + 1)
    rw [show j + 1 + 1 = j + 2 by omega] at inc
    rcases inc with h | h
    · have := bo_mono (j + 1)
      rw [show j + 1 + 1 = j + 2 by omega] at this
      omega
    · exact h
  · intro j h5 h5'
    have hc := closed_form j
    have hc3 := closed_form (j + 3)
    have hc2 := closed_form (j + 2)
    have hc1 := closed_form (j + 1)
    have hb : beattyOut (j + 3) < beattyOut j + 3 := by
      rw [beattyOut, Nat.floor_lt (by have := Real.goldenRatio_pos; positivity)]
      obtain ⟨-, h2⟩ := bo_le j
      have := g_fine
      rw [div_eq_mul_inv]
      push_cast at *
      linarith
    have inc := increments (j + 2)
    rw [show j + 2 + 1 = j + 3 by omega] at inc
    rcases inc with h | h
    · exact h
    · omega

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoTripleMaximizers
