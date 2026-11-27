import OmegaBuild.Commands
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

An invariant polygon for residuals on the faces of an ordered tetrahedron. -/

namespace Omega.ThreeTreePolygon

open scoped BigOperators

/-- The positive defect layer of the residual polytope. -/
def InP (x y : ℝ) : Prop :=
  (-1) * x + (-1) * y ≤ 45074 / 100000 ∧
  (-2) * x + (-3) * y ≤ 78776 / 100000 ∧
  (-1) * x + (-2) * y ≤ 70886 / 100000 ∧
  (-1) * x + (-3) * y ≤ 141847 / 100000 ∧
  (0) * x + (-1) * y ≤ 76377 / 100000 ∧
  (6) * x + (-7) * y ≤ 1265119 / 100000 ∧
  (1) * x + (0) * y ≤ 145074 / 100000 ∧
  (1) * x + (1) * y ≤ 215959 / 100000 ∧
  (5) * x + (8) * y ≤ 1300019 / 100000 ∧
  (3) * x + (8) * y ≤ 1100015 / 100000 ∧
  (1) * x + (5) * y ≤ 663554 / 100000 ∧
  (0) * x + (1) * y ≤ 145072 / 100000 ∧
  (-1) * x + (0) * y ≤ 145074 / 100000

noncomputable section

/-- The prescribed middle edge residual for one attachment. -/
def middle {E : Type*} [AddCommGroup E] [Module ℝ E] (A C t u v : E) : E :=
  (-(1513 / 5000) : ℝ) • A + (177 / 500 : ℝ) • C +
    (50948 / 100000 : ℝ) • u - (14557 / 100000 : ℝ) • v - (15689 / 100000 : ℝ) • t

private theorem middle_real (x y t u v : ℝ) :
    middle x y t u v = -(1513 / 5000) * x + (177 / 500) * y +
      (50948 / 100000) * u - (14557 / 100000) * v - (15689 / 100000) * t := rfl

private theorem root : InP (1 / 3) (1 / 3) := by norm_num [InP]

-- Each image facet follows from two parent inequalities.
private theorem transition00 {x y : ℝ} (h : InP x y) :
    InP (x) (middle x y 1 (1) (1)) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h0, h12]
  · linarith only [h1, h11]
  · linarith only [h4, h12]
  · linarith only [h0, h6]
  · linarith only [h1, h6]
  · linarith only [h4, h6]
  · linarith only [h0, h6]
  · linarith only [h5, h9]
  · linarith only [h3, h8]
  · linarith only [h1, h9]
  · linarith only [h3, h11]
  · linarith only [h9, h12]
  · linarith only [h0, h12]

-- Each image facet follows from two parent inequalities.
private theorem transition01 {x y : ℝ} (h : InP x y) :
    InP (x + y - 1) (middle x y 1 (1) (1) - y + (1)) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h0, h12]
  · linarith only [h0, h10]
  · linarith only [h1, h10]
  · linarith only [h1, h9]
  · linarith only [h7, h12]
  · linarith only [h6, h11]
  · linarith only [h6, h9]
  · linarith only [h5, h9]
  · linarith only [h4, h7]
  · linarith only [h4, h8]
  · linarith only [h1, h5]
  · linarith only [h2, h3]
  · linarith only [h0, h1]

-- Each image facet follows from two parent inequalities.
private theorem transition02 {x y : ℝ} (h : InP x y) :
    InP (y) (middle x y 1 (1) (1) - y + (1)) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h4, h8]
  · linarith only [h3, h7]
  · linarith only [h1, h7]
  · linarith only [h5, h11]
  · linarith only [h7, h12]
  · linarith only [h0, h9]
  · linarith only [h0, h11]
  · linarith only [h11, h12]
  · linarith only [h0, h12]
  · linarith only [h0, h12]
  · linarith only [h0, h1]
  · linarith only [h2, h3]
  · linarith only [h1, h6]

-- Each image facet follows from two parent inequalities.
private theorem transition10 {x y : ℝ} (h : InP x y) :
    InP (x) (middle x y 1 (1) (-1)) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h0, h10]
  · linarith only [h1, h10]
  · linarith only [h3, h11]
  · linarith only [h2, h7]
  · linarith only [h4, h7]
  · linarith only [h1, h6]
  · linarith only [h0, h6]
  · linarith only [h6, h11]
  · linarith only [h6, h11]
  · linarith only [h1, h9]
  · linarith only [h9, h12]
  · linarith only [h11, h12]
  · linarith only [h0, h12]

-- Each image facet follows from two parent inequalities.
private theorem transition11 {x y : ℝ} (h : InP x y) :
    InP (-(x + y - 1)) (-(middle x y 1 (1) (-1) - y + (-1))) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h5, h9]
  · linarith only [h5, h11]
  · linarith only [h4, h9]
  · linarith only [h3, h8]
  · linarith only [h1, h7]
  · linarith only [h1, h9]
  · linarith only [h0, h1]
  · linarith only [h0, h12]
  · linarith only [h11, h12]
  · linarith only [h11, h12]
  · linarith only [h6, h10]
  · linarith only [h8, h9]
  · linarith only [h6, h9]

-- Each image facet follows from two parent inequalities.
private theorem transition12 {x y : ℝ} (h : InP x y) :
    InP (-(y)) (-(middle x y 1 (1) (-1) - y + (-1))) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h11, h12]
  · linarith only [h0, h10]
  · linarith only [h1, h10]
  · linarith only [h2, h10]
  · linarith only [h1, h7]
  · linarith only [h3, h8]
  · linarith only [h1, h6]
  · linarith only [h4, h8]
  · linarith only [h5, h10]
  · linarith only [h6, h11]
  · linarith only [h4, h8]
  · linarith only [h8, h9]
  · linarith only [h0, h11]

-- Each image facet follows from two parent inequalities.
private theorem transition20 {x y : ℝ} (h : InP x y) :
    InP (-(x)) (-(middle x y 1 (-1) (1))) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h6, h7]
  · linarith only [h6, h11]
  · linarith only [h7, h12]
  · linarith only [h7, h12]
  · linarith only [h8, h12]
  · linarith only [h8, h12]
  · linarith only [h0, h12]
  · linarith only [h4, h12]
  · linarith only [h4, h12]
  · linarith only [h3, h8]
  · linarith only [h0, h5]
  · linarith only [h4, h5]
  · linarith only [h0, h6]

-- Each image facet follows from two parent inequalities.
private theorem transition21 {x y : ℝ} (h : InP x y) :
    InP (-(x + y - 1)) (-(middle x y 1 (-1) (1) - y + (1))) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h6, h7]
  · linarith only [h6, h11]
  · linarith only [h0, h6]
  · linarith only [h4, h10]
  · linarith only [h2, h8]
  · linarith only [h0, h3]
  · linarith only [h0, h1]
  · linarith only [h4, h12]
  · linarith only [h1, h10]
  · linarith only [h7, h12]
  · linarith only [h5, h11]
  · linarith only [h0, h8]
  · linarith only [h6, h9]

-- Each image facet follows from two parent inequalities.
private theorem transition22 {x y : ℝ} (h : InP x y) :
    InP (y) (middle x y 1 (-1) (1) - y + (1)) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  unfold InP
  rw [middle_real]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h4, h5]
  · linarith only [h5, h6]
  · linarith only [h6, h7]
  · linarith only [h7, h8]
  · linarith only [h8, h9]
  · linarith only [h9, h10]
  · linarith only [h0, h11]
  · linarith only [h0, h9]
  · linarith only [h2, h11]
  · linarith only [h2, h10]
  · linarith only [h3, h11]
  · linarith only [h1, h7]
  · linarith only [h1, h6]

/-- A convex mixture of the positive defect layer and its negative. -/
def InPolytope (A C t : ℝ) : Prop :=
  ∃ p x₁ y₁ x₂ y₂ : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ InP x₁ y₁ ∧ InP x₂ y₂ ∧
    A = p * x₁ - (1 - p) * x₂ ∧ C = p * y₁ - (1 - p) * y₂ ∧ t = 2 * p - 1

private abbrev Point := ℝ × ℝ × ℝ

private def layer (s : ℝ) : Set Point :=
  {a | InP (s * a.1) (s * a.2.1) ∧ a.2.2 = s}

private theorem convex_layer (s : ℝ) : Convex ℝ (layer s) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx, hxt⟩
  rcases hy with ⟨hy, hyt⟩
  change InP (s * (a * x.1 + b * y.1)) (s * (a * x.2.1 + b * y.2.1)) ∧
    a * x.2.2 + b * y.2.2 = s
  rcases hx with ⟨hx₀, hx₁, hx₂, hx₃, hx₄, hx₅, hx₆, hx₇, hx₈, hx₉, hx₁₀, hx₁₁, hx₁₂⟩
  rcases hy with ⟨hy₀, hy₁, hy₂, hy₃, hy₄, hy₅, hy₆, hy₇, hy₈, hy₉, hy₁₀, hy₁₁, hy₁₂⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left hx₀ ha, mul_le_mul_of_nonneg_left hy₀ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₁ ha, mul_le_mul_of_nonneg_left hy₁ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₂ ha, mul_le_mul_of_nonneg_left hy₂ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₃ ha, mul_le_mul_of_nonneg_left hy₃ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₄ ha, mul_le_mul_of_nonneg_left hy₄ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₅ ha, mul_le_mul_of_nonneg_left hy₅ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₆ ha, mul_le_mul_of_nonneg_left hy₆ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₇ ha, mul_le_mul_of_nonneg_left hy₇ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₈ ha, mul_le_mul_of_nonneg_left hy₈ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₉ ha, mul_le_mul_of_nonneg_left hy₉ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₁₀ ha, mul_le_mul_of_nonneg_left hy₁₀ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₁₁ ha, mul_le_mul_of_nonneg_left hy₁₁ hb, hab]
  · nlinarith only [mul_le_mul_of_nonneg_left hx₁₂ ha, mul_le_mul_of_nonneg_left hy₁₂ hb, hab]
  · rw [hxt, hyt, ← add_mul, hab, one_mul]

private theorem mem_join {A C t : ℝ} :
    (A, C, t) ∈ convexJoin ℝ (layer 1) (layer (-1)) ↔ InPolytope A C t := by
  rw [mem_convexJoin]
  constructor
  · rintro ⟨⟨x₁, y₁, s₁⟩, h₁, ⟨x₂, y₂, s₂⟩, h₂, p, q, hp, hq, hs, he⟩
    change InP (1 * x₁) (1 * y₁) ∧ s₁ = 1 at h₁
    change InP (-1 * x₂) (-1 * y₂) ∧ s₂ = -1 at h₂
    rcases h₁ with ⟨h₁, rfl⟩
    rcases h₂ with ⟨h₂, rfl⟩
    have eq : p * x₁ + q * x₂ = A := congrArg Prod.fst he
    have eq' : p * y₁ + q * y₂ = C := congrArg (fun r : Point => r.2.1) he
    refine ⟨p, x₁, y₁, -x₂, -y₂, hp, by linarith, by simpa using h₁,
      by simpa using h₂, ?_, ?_, ?_⟩
    · rw [show 1 - p = q by linarith]
      linarith only [eq]
    · rw [show 1 - p = q by linarith]
      linarith only [eq']
    · have ht : p * 1 + q * (-1) = t := congrArg (fun r : Point => r.2.2) he
      linarith
  · rintro ⟨p, x₁, y₁, x₂, y₂, hp, hq, h₁, h₂, rfl, rfl, rfl⟩
    refine ⟨(x₁, y₁, 1), ⟨by simpa using h₁, rfl⟩,
      (-x₂, -y₂, -1), ⟨by simpa using h₂, rfl⟩, p, 1 - p, hp, by linarith, by ring, ?_⟩
    ext <;> change _ * _ + _ * _ = _ <;> ring

/-- A zero-defect parent obtained by adjoining a copy of the second vertex.
The residual on the cloned edge is set by the potential of the virtual copy. -/
theorem padded {x : ℝ} (hx : |x| ≤ 72537/50000) :
    InPolytope x (-(25000/72537) * x) 0 := by
  rcases abs_le.mp hx with ⟨hl, hr⟩
  refine ⟨1/2, x, 1/2-(25000/72537)*x, -x, 1/2+(25000/72537)*x,
    by norm_num, by norm_num, ?_, ?_, by ring, by ring, by ring⟩
  all_goals
    unfold InP
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hl, hr]

private theorem pos_mem {x y : ℝ} (h : InP x y) : InPolytope x y 1 :=
  ⟨1, x, y, 1/3, 1/3, by norm_num, le_rfl, h, root, by ring, by ring, by ring⟩

private theorem neg_mem {x y t : ℝ} : InPolytope x y t → InPolytope (-x) (-y) (-t) := by
  rintro ⟨p, x₁, y₁, x₂, y₂, hp, hq, h₁, h₂, rfl, rfl, rfl⟩
  exact ⟨1-p, x₂, y₂, x₁, y₁, by linarith, by linarith, h₂, h₁, by ring, by ring, by ring⟩

private theorem layer_bounds {x y : ℝ} (h : InP x y) :
    |x| ≤ 72537/50000 ∧ |y| ≤ 72537/50000 ∧ |x+y-1| ≤ 72537/50000 := by
  rcases h with ⟨h₀, _, _, _, h₄, _, h₆, h₇, _, _, _, h₁₁, h₁₂⟩
  simp only [abs_le]
  exact ⟨⟨by linarith only [h₁₂], by linarith only [h₆]⟩,
    ⟨by linarith only [h₄], by linarith only [h₁₁]⟩,
    ⟨by linarith only [h₀], by linarith only [h₇]⟩⟩

/-- The state bounds all three oriented edge residuals. -/
theorem bounds {A C t : ℝ} (h : InPolytope A C t) :
    |A| ≤ 72537/50000 ∧ |C| ≤ 72537/50000 ∧ |A+C-t| ≤ 72537/50000 := by
  rcases h with ⟨p, x₁, y₁, x₂, y₂, hp, hq, h₁, h₂, rfl, rfl, rfl⟩
  have weight (x y : ℝ) (hx : |x| ≤ (72537/50000 : ℝ)) (hy : |y| ≤ (72537/50000 : ℝ)) :
      |p * x - (1-p) * y| ≤ 72537/50000 := by
    calc
      _ ≤ |p * x| + |(1-p) * y| := by
        simpa using abs_sub_le (p * x) 0 ((1-p) * y)
      _ = p * |x| + (1-p) * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg hp,
        abs_of_nonneg (sub_nonneg.mpr hq)]
      _ ≤ 72537/50000 := by
        nlinarith only [mul_le_mul_of_nonneg_left hx hp,
          mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hq)]
  have ⟨hx₁, hy₁, hz₁⟩ := layer_bounds h₁
  have ⟨hx₂, hy₂, hz₂⟩ := layer_bounds h₂
  refine ⟨weight _ _ hx₁ hx₂, weight _ _ hy₁ hy₂, ?_⟩
  convert weight _ _ hz₁ hz₂ using 2
  ring

private abbrev Input := ℝ × ℝ × ℝ × ℝ × ℝ

private def child (k : Fin 3) (z : Input) : Point :=
  let (A, C, t, u, v) := z
  let B := middle A C t u v
  if k = 0 then (A, B, u)
  else if k = 1 then (A+C-t, B-C+v, u+v-t)
  else (C, B-C+v, v)

private theorem child_neg (k : Fin 3) (z : Input) : child k (-z) = -child k z := by
  rcases z with ⟨A, C, t, u, v⟩
  fin_cases k <;> norm_num [child, middle_real] <;> (repeat' apply And.intro) <;> ring

private theorem child_add (k : Fin 3) (x y : Input) : child k (x+y) = child k x + child k y := by
  rcases x with ⟨A, C, t, u, v⟩
  rcases y with ⟨A', C', t', u', v'⟩
  fin_cases k <;> norm_num [child, middle_real] <;> (repeat' apply And.intro) <;> ring

private theorem child_smul (k : Fin 3) (r : ℝ) (x : Input) : child k (r • x) = r • child k x := by
  rcases x with ⟨A, C, t, u, v⟩
  fin_cases k <;> norm_num [child, middle_real] <;> (repeat' apply And.intro) <;> ring

private def childLinear (k : Fin 3) : Input →ₗ[ℝ] Point where
  toFun := child k
  map_add' := child_add k
  map_smul' := child_smul k

private def admissible (a : Point) : Prop := InPolytope a.1 a.2.1 a.2.2

private theorem convex_admissible : Convex ℝ {a : Point | admissible a} := by
  have h : {a : Point | admissible a} = convexJoin ℝ (layer 1) (layer (-1)) := by
    ext ⟨A, C, t⟩
    exact mem_join.symm
  rw [h]
  exact (convex_layer 1).convexJoin (convex_layer (-1))

private def signInput (x y : ℝ) (i : Fin 3) : Input :=
  (x, y, 1, if i = 2 then -1 else 1, if i = 1 then -1 else 1)

private theorem sign_child {x y : ℝ} (h : InP x y) (i k : Fin 3) :
    admissible (child k (signInput x y i)) := by
  fin_cases i <;> fin_cases k <;> simp [admissible, signInput, child] at *
  · exact pos_mem (transition00 h)
  · exact pos_mem (transition01 h)
  · exact pos_mem (transition02 h)
  · exact pos_mem (transition10 h)
  · convert neg_mem (pos_mem (transition11 h)) using 1 <;> ring
  · convert neg_mem (pos_mem (transition12 h)) using 1 <;> ring
  · convert neg_mem (pos_mem (transition20 h)) using 1 <;> ring
  · convert neg_mem (pos_mem (transition21 h)) using 1 <;> ring
  · exact pos_mem (transition22 h)

private theorem abs_budget {t u v w : ℝ} (ht : |t| ≤ 1) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hw : |w| ≤ 1) (he : t+w = u+v) :
    |(u+v)/2| + |(t-v)/2| + |(t-u)/2| ≤ 1 := by
  rw [abs_le] at ht hu hv hw
  rcases ht with ⟨_, _⟩
  rcases hu with ⟨_, _⟩
  rcases hv with ⟨_, _⟩
  rcases hw with ⟨_, _⟩
  by_cases h₀ : 0 ≤ (u+v)/2 <;> by_cases h₁ : 0 ≤ (t-v)/2 <;>
    by_cases h₂ : 0 ≤ (t-u)/2 <;>
    simp_all only [abs_of_nonneg, abs_of_neg, not_le] <;> linarith

private theorem blend (k : Fin 3) {A C t u v w : ℝ}
    (h : InPolytope A C t) (ht : |t| ≤ 1) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hw : |w| ≤ 1) (he : t+w = u+v) : admissible (child k (A,C,t,u,v)) := by
  rcases h with ⟨p, x₁, y₁, x₂, y₂, hp, hq, h₁, h₂, rfl, rfl, hp_eq⟩
  let d₀ := (u+v)/2
  let d₁ := (t-v)/2
  let d₂ := (t-u)/2
  let spare := (1 - (|d₀| + |d₁| + |d₂|)) / 2
  have hs : 0 ≤ spare := by
    dsimp [spare, d₀, d₁, d₂]
    linarith only [abs_budget ht hu hv hw he]
  let a (d : ℝ) := (|d| + d)/2
  let b (d : ℝ) := (|d| - d)/2
  have ha (d : ℝ) : 0 ≤ a d := by dsimp [a]; linarith only [neg_abs_le d]
  have hb (d : ℝ) : 0 ≤ b d := by dsimp [b]; linarith only [le_abs_self d]
  let μ : Fin 6 → ℝ := ![a d₀ + spare, a d₁, a d₂, b d₀ + spare, b d₁, b d₂]
  let X : Fin 6 → Input := ![signInput x₁ y₁ 0, signInput x₁ y₁ 1, signInput x₁ y₁ 2,
    -signInput x₂ y₂ 0, -signInput x₂ y₂ 1, -signInput x₂ y₂ 2]
  have hμ : ∑ i, μ i = 1 := by simp [Fin.sum_univ_succ, μ, a, b, spare]; ring
  have hX : ∑ i, μ i • X i = (p*x₁-(1-p)*x₂, p*y₁-(1-p)*y₂, t, u, v) := by
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    ext <;> norm_num [μ, X, signInput, a, b, spare, d₀, d₁, d₂, smul_eq_mul] <;>
      rw [hp_eq] <;> ring
  have hμi (i : Fin 6) : 0 ≤ μ i := by
    fin_cases i
    · exact add_nonneg (ha d₀) hs
    · exact ha d₁
    · exact ha d₂
    · exact add_nonneg (hb d₀) hs
    · exact hb d₁
    · exact hb d₂
  have hXi (i : Fin 6) : admissible (child k (X i)) := by
    fin_cases i
    · exact sign_child h₁ 0 k
    · exact sign_child h₁ 1 k
    · exact sign_child h₁ 2 k
    · change admissible (child k (-signInput x₂ y₂ 0))
      rw [child_neg]
      exact neg_mem (sign_child h₂ 0 k)
    · change admissible (child k (-signInput x₂ y₂ 1))
      rw [child_neg]
      exact neg_mem (sign_child h₂ 1 k)
    · change admissible (child k (-signInput x₂ y₂ 2))
      rw [child_neg]
      exact neg_mem (sign_child h₂ 2 k)
  have hc := convex_admissible.sum_mem (t := Finset.univ) (fun i _ => hμi i) hμ
    (fun i _ => hXi i)
  change admissible (∑ i, μ i • childLinear k (X i)) at hc
  simp only [← map_smul, ← map_sum, hX] at hc
  exact hc

/-- Inserting a new vertex preserves the invariant on each of the three child faces. -/
theorem step {A C t u v : ℝ} (h : InPolytope A C t) (ht : |t| ≤ 1)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |u+v-t| ≤ 1) :
    let B := middle A C t u v
    InPolytope A B u ∧ InPolytope (A+C-t) (B-C+v) (u+v-t) ∧ InPolytope C (B-C+v) v := by
  have hh (k : Fin 3) := blend k h ht hu hv hw (by ring)
  exact ⟨hh 0, hh 1, hh 2⟩

end

end Omega.ThreeTreePolygon
