/- GID: D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.claim; result=D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result; claim=D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.claim
   digest: An edge-triangle Gibbs law has marginals above one half and positive third cumulant. -/

import D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Sym.Card

/-! The homomorphism-density Hamiltonian and GHS condition are those of
Bianchi, Collet and Magnanini, arXiv:2107.08889v2, Sections 2.1, 3 and 4.
The counterexample concerns the conjecture in the final paragraph of Section 4.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/22390
Admission basis: open-problem-resolution. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation

open scoped BigOperators
open D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit (homCount)

/-- The fraction of vertex maps that preserve adjacency. -/
def homDensity {m n : ℕ} (h : SimpleGraph (Fin m)) (g : SimpleGraph (Fin n)) : ℝ :=
  (homCount h g : ℝ) / (n : ℝ) ^ m

/-- The homomorphism-density Hamiltonian for an arbitrary finite graph family. -/
def hamiltonian {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m))
    (β : Fin k → ℝ) (g : SimpleGraph (Fin n)) : ℝ :=
  (n : ℝ) ^ 2 * dotProduct β (fun j => homDensity (h j).2 g)

/-- The Gibbs probability of a labeled graph, normalized over all simple graphs. -/
def gibbsWeight {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m))
    (β : Fin k → ℝ) (g : SimpleGraph (Fin n)) : ℝ :=
  Real.exp (hamiltonian h β g) / ∑ g : SimpleGraph (Fin n), Real.exp (hamiltonian h β g)

/-- Expectation under the graph Gibbs law. -/
def expectation {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m))
    (β : Fin k → ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  dotProduct (gibbsWeight h β) f

/-- The indicator of an edge of the complete labeled graph. -/
def edgeIndicator {n : ℕ} (e : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (g : SimpleGraph (Fin n)) : ℝ :=
  g.edgeSet.indicator (fun _ => 1) e.val

/-- The third Ursell function, including triples with repeated edges. -/
def u3 {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m)) (β : Fin k → ℝ)
    (e f g : (⊤ : SimpleGraph (Fin n)).edgeSet) : ℝ :=
  expectation h β (fun a => edgeIndicator e a * edgeIndicator f a * edgeIndicator g a) -
  expectation h β (edgeIndicator e) *
    expectation h β (fun a => edgeIndicator f a * edgeIndicator g a) -
  expectation h β (edgeIndicator f) *
    expectation h β (fun a => edgeIndicator e a * edgeIndicator g a) -
  expectation h β (edgeIndicator g) *
    expectation h β (fun a => edgeIndicator e a * edgeIndicator f a) +
  2 * expectation h β (edgeIndicator e) * expectation h β (edgeIndicator f) *
    expectation h β (edgeIndicator g)

/-- The marginal criterion conjectured for general exponential random graphs.
`Fin (k + 1)` indexes every nonempty finite family, with its first graph an edge. -/
def claim : Prop :=
  ∀ (n k : ℕ) (h : Fin (k + 1) → Σ m, SimpleGraph (Fin m)) (β : Fin (k + 1) → ℝ),
    h 0 = ⟨2, (⊤ : SimpleGraph (Fin 2))⟩ →
    (∀ j, j ≠ 0 → 0 ≤ β j) →
    ((∀ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      (1 / 2 : ℝ) ≤ expectation h β (edgeIndicator e)) ↔
     ∀ e f g : (⊤ : SimpleGraph (Fin n)).edgeSet, u3 h β e f g ≤ 0)

private def models : Fin 2 → Σ m, SimpleGraph (Fin m) :=
  ![⟨2, ⊤⟩, ⟨3, ⊤⟩]

private def parameters : Fin 2 → ℝ := ![0, Real.log 2 / 2]

private def edge01 : (⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(0, 1), by decide⟩
private def edge02 : (⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(0, 2), by decide⟩
private def edge12 : (⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(1, 2), by decide⟩

open Classical in
private lemma triangle_count (g : SimpleGraph (Fin 3)) :
    homCount (⊤ : SimpleGraph (Fin 3)) g = if g = ⊤ then 6 else 0 := by
  classical
  unfold homCount
  split_ifs with hg
  · subst g
    rw [Nat.card_eq_fintype_card]
    decide
  · have he : IsEmpty {f : Fin 3 → Fin 3 // ∀ i j,
        (⊤ : SimpleGraph (Fin 3)).Adj i j → g.Adj (f i) (f j)} := by
      refine ⟨fun φ => hg ?_⟩
      let ψ : (⊤ : SimpleGraph (Fin 3)) →g g :=
        ⟨φ.val, fun {i j} hij => φ.property i j hij⟩
      have hs := Finite.surjective_of_injective ψ.injective_of_top_hom
      apply top_unique
      intro v w hvw
      obtain ⟨a, rfl⟩ := hs v
      obtain ⟨b, rfl⟩ := hs w
      exact ψ.map_rel (show a ≠ b from fun hab => hvw (congrArg ψ hab))
    exact Nat.card_eq_zero.mpr (Or.inl he)

open Classical in
private lemma hamiltonian_value (g : SimpleGraph (Fin 3)) :
    hamiltonian models parameters g = if g = ⊤ then Real.log 2 else 0 := by
  unfold hamiltonian dotProduct
  delta models parameters homDensity
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_mul, zero_add]
  rw [triangle_count]
  split_ifs <;> ring

private def graphOfBits (b : Bool × Bool × Bool) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet {e | (e = s(0, 1) ∧ b.1 = true) ∨
    (e = s(0, 2) ∧ b.2.1 = true) ∨ (e = s(1, 2) ∧ b.2.2 = true)}

private lemma graph_bijective : Function.Bijective graphOfBits := by
  constructor
  · intro a b hab
    have h01 := congrArg (fun g : SimpleGraph (Fin 3) => g.Adj 0 1) hab
    have h02 := congrArg (fun g : SimpleGraph (Fin 3) => g.Adj 0 2) hab
    have h12 := congrArg (fun g : SimpleGraph (Fin 3) => g.Adj 1 2) hab
    dsimp only [graphOfBits, SimpleGraph.fromEdgeSet] at h01 h02 h12
    rcases a with ⟨a, c, d⟩
    rcases b with ⟨b, e, f⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
      simp_all
  · intro g
    classical
    refine ⟨(decide (g.Adj 0 1), decide (g.Adj 0 2), decide (g.Adj 1 2)), ?_⟩
    delta graphOfBits
    ext v w
    fin_cases v <;> fin_cases w <;>
      simp <;> exact g.adj_comm _ _

private lemma graph_top (b : Bool × Bool × Bool) :
    graphOfBits b = ⊤ ↔ b = (true, true, true) := by
  have ht : graphOfBits (true, true, true) = ⊤ := by
    delta graphOfBits
    ext v w
    fin_cases v <;> fin_cases w <;> simp
  rw [← ht, graph_bijective.injective.eq_iff]

private lemma sum_graphs (f : SimpleGraph (Fin 3) → ℝ) :
    ∑ g, f g = ∑ b : Bool × Bool × Bool, f (graphOfBits b) :=
  (graph_bijective.sum_comp f).symm

open Classical in
private lemma weight_value (g : SimpleGraph (Fin 3)) :
    gibbsWeight models parameters g = if g = ⊤ then 2 / 9 else 1 / 9 := by
  classical
  have hw (a : SimpleGraph (Fin 3)) :
      Real.exp (hamiltonian models parameters a) = if a = ⊤ then 2 else 1 := by
    rw [hamiltonian_value]
    split_ifs
    · exact Real.exp_log (by norm_num)
    · exact Real.exp_zero
  unfold gibbsWeight
  simp_rw [hw]
  have hz : (∑ a : SimpleGraph (Fin 3), (if a = ⊤ then 2 else 1 : ℝ)) = 9 := by
    rw [sum_graphs]
    norm_num [graph_top, Fintype.sum_prod_type]
  rw [hz]
  split_ifs <;> norm_num

private lemma marginal_value (e : (⊤ : SimpleGraph (Fin 3)).edgeSet) :
    expectation models parameters (edgeIndicator e) = 5 / 9 := by
  classical
  unfold expectation dotProduct
  simp_rw [weight_value]
  rw [sum_graphs]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, graph_top]
  delta edgeIndicator graphOfBits Set.indicator
  fin_cases e <;> norm_num

private lemma joint_values :
    expectation models parameters (fun a => edgeIndicator edge01 a * edgeIndicator edge02 a) =
      1 / 3 ∧
    expectation models parameters (fun a => edgeIndicator edge01 a * edgeIndicator edge12 a) =
      1 / 3 ∧
    expectation models parameters (fun a => edgeIndicator edge02 a * edgeIndicator edge12 a) =
      1 / 3 ∧
    expectation models parameters (fun a =>
      edgeIndicator edge01 a * edgeIndicator edge02 a * edgeIndicator edge12 a) = 2 / 9 := by
  classical
  unfold expectation dotProduct
  simp_rw [weight_value]
  simp only [sum_graphs, Fintype.sum_prod_type, Fintype.sum_bool, graph_top]
  delta edgeIndicator edge01 edge02 edge12 graphOfBits Set.indicator
  norm_num

private lemma ursell_value : u3 models parameters edge01 edge02 edge12 = 7 / 729 := by
  delta u3
  rw [marginal_value, marginal_value, marginal_value,
    joint_values.1, joint_values.2.1, joint_values.2.2.1, joint_values.2.2.2]
  norm_num

/-- All three edge marginals exceed one half, but their third Ursell function is positive. -/
theorem result : ¬ claim := by
  intro h
  have hβ : ∀ j : Fin 2, j ≠ 0 → 0 ≤ parameters j := by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hm : ∀ e : (⊤ : SimpleGraph (Fin 3)).edgeSet,
      (1 / 2 : ℝ) ≤ expectation models parameters (edgeIndicator e) := by
    intro e
    rw [marginal_value]
    norm_num
  have hu := (h 3 1 models parameters rfl hβ).mp hm edge01 edge02 edge12
  rw [ursell_value] at hu
  norm_num at hu

end D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation
