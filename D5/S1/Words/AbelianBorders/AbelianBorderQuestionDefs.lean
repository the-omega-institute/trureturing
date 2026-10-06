/- GID: D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs
   generality: G
   mirror-B: D5/B/S1/Words/AbelianBorders/AbelianBorderQuestionDefs
   mirror-E: none(waiver:abelian-border-periodicity-question-definition)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2, mathlib/module/Mathlib.Analysis.Convex.Segment, mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDistance]
   utility: none
   digest: Charlier, Harju, Puzynina and Zamboni's question whether geometric weak abelian periodicity forces finitely many weakly abelian unbordered factors. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs

/-! Fixed public statement: É. Charlier, T. Harju, S. Puzynina and L. Q. Zamboni, *Abelian
    bordered factors and periodicity*, arXiv:1501.07464v1, Section 7, Question 2: "Let w be an
    infinite bounded weakly abelian periodic word over a k-letter alphabet such that its graph
    G_w belongs to a k-dimensional cylinder with axis with rational coefficients, and each
    tangential line to G_w has points of G_w on it with bounded gaps. Does it follow that w has
    only finitely many weakly abelian unbordered factors?"  Two nonempty words are weakly
    abelian equivalent when they have the same letter frequencies; a finite word is weakly
    abelian bordered when a nonempty proper prefix and a nonempty suffix have the same letter
    frequencies (the suffix may be the whole word, the most permissive reading, so the claim
    below is implied by the question's positive answer).  The graph is the polygonal path of
    prefix Parikh vectors, drawn with the standard unit vectors (Section 2).  The cylinder is
    the set of points at Euclidean distance at most `M` from a line with rational direction;
    a tangential hyperplane has normal orthogonal to the axis, supports the graph and meets
    it; a tangential line is an axis-parallel line inside such a hyperplane containing every
    point of the graph on that hyperplane (Section 4).  Gaps are measured by the indices of the
    graph's cut points; the bounded-gap hypothesis is taken in its uniform form. -/

/-- Number of occurrences of the letter `a` in `u`. -/
def letterCount {k : ℕ} (u : List (Fin k)) (a : Fin k) : ℕ :=
  u.count a

/-- Weak abelian equivalence of nonempty words: equal letter frequencies. -/
def WeakAbelianEquiv {k : ℕ} (u v : List (Fin k)) : Prop :=
  u ≠ [] ∧ v ≠ [] ∧ ∀ a, v.length * letterCount u a = u.length * letterCount v a

/-- A finite word is weakly abelian bordered when some nonempty proper prefix and some
    nonempty suffix have the same letter frequencies. -/
def WeakAbelianBordered {k : ℕ} (u : List (Fin k)) : Prop :=
  ∃ r s : ℕ, 1 ≤ r ∧ r < u.length ∧ 1 ≤ s ∧ s ≤ u.length ∧
    WeakAbelianEquiv (u.take r) (u.drop (u.length - s))

/-- The factor of length `n` of `w` starting at `i`. -/
def factor {k : ℕ} (w : ℕ → Fin k) (i n : ℕ) : List (Fin k) :=
  (List.range n).map fun j => w (i + j)

/-- Bounded weak abelian periodicity: after a finite prefix, `w` is cut into consecutive
    nonempty blocks of bounded length, all with the same letter frequencies. -/
def BoundedWeakAbelianPeriodic {k : ℕ} (w : ℕ → Fin k) : Prop :=
  ∃ (t : ℕ → ℕ) (C : ℕ), StrictMono t ∧ (∀ i, t (i + 1) - t i ≤ C) ∧
    ∀ i, WeakAbelianEquiv (factor w (t i) (t (i + 1) - t i)) (factor w (t 0) (t 1 - t 0))

/-- The prefix Parikh vector of length `n`, as a point of `ℝ^k`. -/
noncomputable def parikhPoint {k : ℕ} (w : ℕ → Fin k) (n : ℕ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun a => (letterCount (factor w 0 n) a : ℝ)

/-- The graph `G_w`: the union of the segments joining consecutive prefix Parikh vectors. -/
def graph {k : ℕ} (w : ℕ → Fin k) : Set (EuclideanSpace ℝ (Fin k)) :=
  ⋃ n, segment ℝ (parikhPoint w n) (parikhPoint w (n + 1))

/-- The line through `x₀` with direction `a`. -/
def line {k : ℕ} (x₀ a : EuclideanSpace ℝ (Fin k)) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∃ t : ℝ, x = x₀ + t • a}

/-- A direction with rational coordinates. -/
def RationalDirection {k : ℕ} (a : EuclideanSpace ℝ (Fin k)) : Prop :=
  a ≠ 0 ∧ ∀ i, ∃ q : ℚ, a i = q

/-- A tangential line to the graph for the axis direction `a`. -/
def IsTangentialLine {k : ℕ} (w : ℕ → Fin k) (a y : EuclideanSpace ℝ (Fin k)) : Prop :=
  ∃ (b : EuclideanSpace ℝ (Fin k)) (d : ℝ), b ≠ 0 ∧ inner ℝ b a = 0 ∧
    (∀ x ∈ graph w, d ≤ inner ℝ b x) ∧ (∃ x ∈ graph w, inner ℝ b x = d) ∧
    line y a ⊆ {x | inner ℝ b x = d} ∧
    ∀ x ∈ graph w, inner ℝ b x = d → x ∈ line y a

/-- The geometric hypotheses of Question 2 for the axis through `x₀` with direction `a`:
    the graph lies in a cylinder around the axis, and every tangential line has cut points of
    the graph on it in every window of `D` consecutive indices. -/
def GeometricHypotheses {k : ℕ} (w : ℕ → Fin k) : Prop :=
  ∃ (x₀ a : EuclideanSpace ℝ (Fin k)) (M : ℝ), RationalDirection a ∧
    (∀ x ∈ graph w, Metric.infDist x (line x₀ a) ≤ M) ∧
    ∀ y, IsTangentialLine w a y →
      ∃ D : ℕ, ∀ n, ∃ m, n ≤ m ∧ m ≤ n + D ∧ parikhPoint w m ∈ line y a

/-- The positive answer to Question 2 (with the permissive border convention). -/
def claim : Prop :=
  ∀ (k : ℕ) (w : ℕ → Fin k), BoundedWeakAbelianPeriodic w → GeometricHypotheses w →
    {u : List (Fin k) | (∃ i n, u = factor w i n) ∧ u ≠ [] ∧ ¬ WeakAbelianBordered u}.Finite

end D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs
