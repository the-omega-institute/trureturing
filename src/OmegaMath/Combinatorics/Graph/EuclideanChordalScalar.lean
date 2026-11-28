import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.ScalarCycleReconstruction
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Positivity

compile_only_with_mathlib

/-! Omega original.

 # Continuous scalar reconstruction on finite chordal graphs

The minimum over all simple paths ending at a vertex supplies a canonical continuous
selection. Allowing every starting vertex handles disconnected graphs without choices of roots.
The finite-order coefficient is `(n - 2) / n` for `n ≥ 3`.
-/

open scoped RealInnerProductSpace

namespace SimpleGraph.EuclideanChordal

variable {V : Type*} {G : SimpleGraph V}

private theorem triangleProduct_bound (g : V → V → ℝ) {δ : ℝ}
    (_hδ : 0 ≤ δ) (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      |g a b + g b c - g a c| ≤ δ)
    {n : ℕ} {x : Multiplicative ℝ}
    (h : TriangleProduct G (fun a b => Multiplicative.ofAdd (g a b)) n x) :
    |Multiplicative.toAdd x| ≤ (n : ℝ) * δ := by
  induction h with
  | one => simp
  | triangle a b c hab hbc hca =>
    simp only [Nat.cast_one]
    change |g a b + g b c + g c a| ≤ (1 : ℝ) * δ
    rw [hrev a c hca.symm, ← sub_eq_add_neg, one_mul]
    exact htri a b c hab hbc hca.symm
  | @mul m n x y _ _ hx hy =>
    change |Multiplicative.toAdd x + Multiplicative.toAdd y| ≤ _
    exact (abs_add_le _ _).trans (by simpa [Nat.cast_add, add_mul] using add_le_add hx hy)
  | @conj n x z _ hx =>
    change |Multiplicative.toAdd z + Multiplicative.toAdd x + -Multiplicative.toAdd z| ≤ _
    convert hx using 1; congr 1; ring

private theorem gain_eq_weight (g : V → V → ℝ) {a b : V} (p : G.Walk a b) :
    Multiplicative.toAdd (p.gain (fun v w => Multiplicative.ofAdd (g v w))) =
      p.scalarWeight g := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [Walk.gain_cons, Walk.scalarWeight_cons]
    change g _ _ + Multiplicative.toAdd (p.gain _) = _
    rw [ih]

/-- A dimension-free scalar cycle estimate, with arbitrary nonnegative defect. -/
theorem cycle_bound [Finite V] (hG : G.IsChordal) (g : V → V → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      |g a b + g b c - g a c| ≤ δ)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    |p.scalarWeight g| ≤ ((p.length : ℝ) - 2) * δ := by
  obtain ⟨n, hn, hprod⟩ := hG.closed_walk_triangle_product
    (fun a b => Multiplicative.ofAdd (g a b)) (fun a b h => hrev a b h) p
  have hs := triangleProduct_bound g hδ hrev htri hprod
  rw [gain_eq_weight] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ hδ
  have hn' : (n : ℝ) ≤ ((p.length - 2 : ℕ) : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_sub (by have := hp.three_le_length; omega)] at hn'
  exact hn'

/-- The scalar finite-order factor. -/
noncomputable def orderFactor (n : ℕ) : ℝ := ((n : ℝ) - 2) / n

theorem orderFactor_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ orderFactor n := by
  unfold orderFactor
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith) (Nat.cast_nonneg _)

theorem orderFactor_le_one {n : ℕ} (hn : 3 ≤ n) : orderFactor n ≤ 1 := by
  unfold orderFactor
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_le_one this).2 (by linarith)

/-- With the finite-order additive slack every closed walk has nonnegative weight. -/
theorem closed_cost_nonneg [Fintype V] (hG : G.IsChordal) (hn : 3 ≤ Fintype.card V)
    (g : V → V → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      |g a b + g b c - g a c| ≤ δ)
    {a : V} (p : G.Walk a a) :
    0 ≤ p.scalarWeight (fun v w => g v w + orderFactor (Fintype.card V) * δ) := by
  apply Walk.scalarWeight_nonneg_of_cycles
  · intro a b hab
    rw [hrev a b hab]
    have := mul_nonneg (orderFactor_nonneg hn) hδ
    linarith
  · intro a c hc
    rw [ScalarCycleReconstruction.scalarWeight_shift]
    have hb := (abs_le.mp (cycle_bound hG g hδ hrev htri c hc)).1
    have hm : c.length ≤ Fintype.card V := by
      have := hc.isPath_dropLast.length_lt
      have he := c.length_dropLast_add_one hc.not_nil
      omega
    have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
    have hm' : (c.length : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
    have hcoef : (c.length : ℝ) - 2 ≤ (c.length : ℝ) * orderFactor (Fintype.card V) := by
      unfold orderFactor
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hn0).2
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoef hδ
    nlinarith

/-- Removing nonnegative closed subwalks gives a simple path of no greater cost. -/
theorem exists_path_le (w : V → V → ℝ)
    (hclosed : ∀ (a : V) (p : G.Walk a a), 0 ≤ p.scalarWeight w)
    {a b : V} (p : G.Walk a b) :
    ∃ q : G.Path a b, q.val.scalarWeight w ≤ p.scalarWeight w := by
  classical
  suffices ∀ n (a b : V) (p : G.Walk a b), p.length = n →
      ∃ q : G.Path a b, q.val.scalarWeight w ≤ p.scalarWeight w by
    exact this p.length a b p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b p hp
    by_cases hpath : p.IsPath
    · exact ⟨⟨p, hpath⟩, le_rfl⟩
    · obtain ⟨x, c, q, hc, hlen, hw⟩ := p.exists_shorter_of_not_isPath w hpath
      obtain ⟨r, hr⟩ := ih q.length (by omega) a b q rfl
      exact ⟨r, hr.trans (by rw [hw]; linarith [hclosed x c])⟩

section Selection

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev EndingPaths (v : V) := Σ a : V, G.Path a v

private instance (v : V) : Nonempty (EndingPaths (G := G) v) :=
  ⟨⟨v, ⟨Walk.nil, by simp⟩⟩⟩

/-- Minimum path cost, allowing an arbitrary starting vertex. -/
noncomputable def shortestPotential (w : V → V → ℝ) (v : V) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun p : EndingPaths (G := G) v => p.2.val.scalarWeight w)

private theorem shortestPotential_le (w : V → V → ℝ) {a b : V} (p : G.Path a b) :
    shortestPotential (G := G) w b ≤ p.val.scalarWeight w :=
  Finset.inf'_le (fun q : EndingPaths (G := G) b => q.2.val.scalarWeight w)
    (Finset.mem_univ (⟨a, p⟩ : EndingPaths (G := G) b))

private theorem shortestPotential_attained (w : V → V → ℝ) (v : V) :
    ∃ (a : V) (p : G.Path a v), shortestPotential (G := G) w v = p.val.scalarWeight w := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun p : EndingPaths (G := G) v => p.2.val.scalarWeight w)
  exact ⟨p.1, p.2, hp⟩

theorem shortestPotential_edge (w : V → V → ℝ)
    (hclosed : ∀ (a : V) (p : G.Walk a a), 0 ≤ p.scalarWeight w)
    {a b : V} (hab : G.Adj a b) :
    shortestPotential (G := G) w b ≤ shortestPotential (G := G) w a + w a b := by
  obtain ⟨s, p, hp⟩ := shortestPotential_attained (G := G) w a
  obtain ⟨q, hq⟩ := exists_path_le w hclosed (p.val.append hab.toWalk)
  exact (shortestPotential_le w q).trans (by simpa [hp, Adj.toWalk] using hq)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem continuous_weight {X : Type*} [TopologicalSpace X]
    (w : X → V → V → ℝ) (hw : ∀ a b, Continuous fun x => w x a b)
    {a b : V} (p : G.Walk a b) : Continuous fun x => p.scalarWeight (w x) := by
  induction p with
  | nil => exact continuous_const
  | @cons a b c h p ih => exact (hw a b).add ih

/-- The canonical scalar selection is continuous in every continuous edge-cost parameter. -/
theorem continuous_shortestPotential {X : Type*} [TopologicalSpace X]
    (w : X → V → V → ℝ) (hw : ∀ a b, Continuous fun x => w x a b) (v : V) :
    Continuous fun x => shortestPotential (G := G) (w x) v := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun p _ => continuous_weight w hw p.2.val)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem weight_abs_bound (w : V → V → ℝ) {A : ℝ} (_hA : 0 ≤ A)
    (hw : ∀ a b, G.Adj a b → |w a b| ≤ A) {a b : V} (p : G.Walk a b) :
    |p.scalarWeight w| ≤ (p.length : ℝ) * A := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    simp only [Walk.scalarWeight_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    exact (abs_add_le _ _).trans (by nlinarith [hw a b hab])

/-- A uniform bound for the shortest-path selection. -/
theorem shortestPotential_abs_le (w : V → V → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hw : ∀ a b, G.Adj a b → |w a b| ≤ A) (v : V) :
    |shortestPotential (G := G) w v| ≤ (Fintype.card V : ℝ) * A := by
  obtain ⟨a, p, hp⟩ := shortestPotential_attained (G := G) w v
  rw [hp]
  exact (weight_abs_bound w hA hw p.val).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast p.prop.length_lt.le) hA)

end Selection

/-- A continuous scalar reconstruction for every direction in a real inner product space.
This includes the origin and uses homogeneous costs, so the selection is suitable for
both spherical and Gaussian averaging. -/
theorem exists_continuous_directional_potential [Fintype V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hG : G.IsChordal) (hn : 3 ≤ Fintype.card V) (g : V → V → E)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ f : E → V → ℝ, (∀ v, Continuous fun x => f x v) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x v, |f x v| ≤ B * ‖x‖) ∧
      ∀ x a b, G.Adj a b →
        |f x b - f x a - ⟪g a b, x⟫| ≤ orderFactor (Fintype.card V) * δ * ‖x‖ := by
  classical
  let w (x : E) (a b : V) := ⟪g a b, x⟫ + orderFactor (Fintype.card V) * (δ * ‖x‖)
  have hclosed (x : E) (a : V) (p : G.Walk a a) : 0 ≤ p.scalarWeight (w x) := by
    apply closed_cost_nonneg hG hn (fun a b => ⟪g a b, x⟫) (mul_nonneg hδ (norm_nonneg x))
    · intro a b hab
      simp [hrev a b hab]
    · intro a b c hab hbc hac
      rw [← inner_add_left, ← inner_sub_left]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (htri a b c hab hbc hac) (norm_nonneg x))
  refine ⟨fun x v => shortestPotential (G := G) (w x) v, ?_, ?_, ?_⟩
  · intro v
    exact continuous_shortestPotential (G := G) w (fun a b => by dsimp [w]; fun_prop) v
  · obtain ⟨A, hA⟩ := (Set.finite_range (fun p : V × V => ‖g p.1 p.2‖)).bddAbove
    let C := max A 0 + orderFactor (Fintype.card V) * δ
    have hC : 0 ≤ C := add_nonneg (le_max_right _ _) (mul_nonneg (orderFactor_nonneg hn) hδ)
    refine ⟨(Fintype.card V : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
    intro x v
    have hw (a b : V) (_ : G.Adj a b) : |w x a b| ≤ C * ‖x‖ := by
      dsimp [w]
      calc
        _ ≤ |⟪g a b, x⟫| + |orderFactor (Fintype.card V) * (δ * ‖x‖)| := abs_add_le _ _
        _ ≤ (max A 0) * ‖x‖ + orderFactor (Fintype.card V) * (δ * ‖x‖) := by
          rw [abs_of_nonneg (mul_nonneg (orderFactor_nonneg hn) (mul_nonneg hδ (norm_nonneg _)))]
          exact add_le_add ((abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right ((hA (Set.mem_range_self (a, b))).trans (le_max_left _ _))
              (norm_nonneg _))) le_rfl
        _ = C * ‖x‖ := by dsimp [C]; ring
    simpa [mul_assoc] using shortestPotential_abs_le (w x) (mul_nonneg hC (norm_nonneg x)) hw v
  · intro x a b hab
    have hf := shortestPotential_edge (w x) (hclosed x) hab
    have hr := shortestPotential_edge (w x) (hclosed x) hab.symm
    dsimp [w] at hf hr
    rw [hrev a b hab, inner_neg_left] at hr
    rw [abs_le]
    constructor <;> nlinarith

end SimpleGraph.EuclideanChordal
