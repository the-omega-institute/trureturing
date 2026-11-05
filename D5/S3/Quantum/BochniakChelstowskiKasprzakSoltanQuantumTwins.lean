/- GID: D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins
   generality: I
   mirror-B: D5/B/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Adjacency determines algebra homomorphisms for finite twin-free graphs. -/

/-
proof_shape: adjacency_single = bind-only (consumer: separating_product_eq_single).
proof_shape: separating_product_eq_single = content (consumer: algHom_eq_of_adjacency_eq).
proof_shape: algHom_eq_of_adjacency_eq = content (consumer: no_twins_of_twin_free).
proof_shape: no_twins_of_twin_free = content after same-delivery inlining (consumer: result).
proof_shape: tesseract_eq_hypercube = bind-only (consumer: result).
proof_shape: result = content after same-delivery inlining; the three local graph checks are bind-only.
escape_witness: algHom_eq_of_adjacency_eq, through separating_product_eq_single.
admission_basis: open-problem-resolution (#19959; Proved).
Direct frozen dependencies: algHom_eq_of_adjacency_eq = none; result and
  tesseract_eq_hypercube use D5/S3/Combinatorics/Graph/Hypercube.hypercube,
  declaration statement_id sha256:e70c1ce92111881fa6bcced6ddb8eeb908912e4c390ec989d4c1880ebc362345;
  all other declarations = none.
The tesseract graph expression is inlined in claim; the proof uses the existing
hypercube owner through the consumed equality tesseract_eq_hypercube.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19959
-/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Basic.Complex.Basic
import D5.S3.Combinatorics.Graph.Hypercube

/-! Binding conventions for A. Bochniak, I. Chełstowski, P. Kasprzak and P. M. Sołtan, "Quantum Mycielskians:
symmetries, twin vertices and distinguishing labelings", arXiv:2502.10521v2 (Question 3.16 in v1).

* A classical graph `G` on the finite vertex set `V` is the quantum graph `(C(V), ψ, A_G)` with `C(V) = V → ℂ` and
  the adjacency operator `(A_G f)(w) = Σ_{v ~ w} f(v)`.
* Definition 3.8: "`G` has `H`-twin vertices ... if there exists a pair of different actions of `H` on `G`
  `ρ₁, ρ₂ : C(G) → C(G) ⊗ C(H)` such that `ρ₁ ∘ A_G = ρ₂ ∘ A_G`. We say that `G` has quantum twin vertices if there
  exists a quantum group `H` such that `G` has `H`-twins."
* Section 3.2: "The other potential candidate is the Tesseract graph with 16 vertices. ... Question 3.17. Do the
  above-mentioned graphs possess quantum twin vertices?", the graphs being `K₂ □ K₅`, `C₄ □ C₃` and the tesseract.

An action of a compact quantum group is in particular a unital algebra homomorphism `C(G) → C(G) ⊗ C(H)`. The claim
states the negative answer for every pair of unital algebra homomorphisms into every complex algebra `B`. -/

namespace D5.S3.Quantum.BochniakChelstowskiKasprzakSoltanQuantumTwins

open SimpleGraph

open Classical in
/-- The adjacency operator `A_G` on `C(V) = V → ℂ`. -/
noncomputable def adjacencyOperator {V : Type} [Fintype V] (G : SimpleGraph V) :
    (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  Matrix.toLin' (G.adjMatrix ℂ)

/-- Definition 3.8 with target algebra `B`: two different unital algebra homomorphisms `ρ₁, ρ₂ : C(V) → B` with
`ρ₁ ∘ A_G = ρ₂ ∘ A_G`. -/
def HasTwinsIn {V : Type} [Fintype V] (G : SimpleGraph V) (B : Type) [Ring B] [Algebra ℂ B] : Prop :=
  ∃ ρ₁ ρ₂ : (V → ℂ) →ₐ[ℂ] B, ρ₁ ≠ ρ₂ ∧ ∀ f, ρ₁ (adjacencyOperator G f) = ρ₂ (adjacencyOperator G f)

/-- The prism `K₂ □ K₅`. -/
abbrev prism : SimpleGraph (Fin 2 × Fin 5) := completeGraph (Fin 2) □ completeGraph (Fin 5)

/-- `C₄ □ C₃`. -/
abbrev cycleProduct : SimpleGraph (Fin 4 × Fin 3) := cycleGraph 4 □ cycleGraph 3

/-- Question 3.17, answered in the negative for all three graphs and every target algebra. -/
def claim : Prop :=
  ∀ (B : Type) [Ring B] [Algebra ℂ B], ¬ HasTwinsIn prism B ∧ ¬ HasTwinsIn cycleProduct B ∧ ¬ HasTwinsIn
      ({
        Adj u v := hammingDist u v = 1
        symm := ⟨fun _ _ h => by rwa [hammingDist_comm]⟩
        loopless := ⟨fun _ h => by simp at h⟩ } : SimpleGraph (Fin 4 → Bool)) B


open Classical

private lemma adjacency_single {V : Type} [Fintype V] (G : SimpleGraph V) (v w : V) :
    adjacencyOperator G (Pi.single v 1) w = if G.Adj w v then 1 else 0 := by
  classical
  change Matrix.mulVec (G.adjMatrix ℂ) (Pi.single v 1) w = _
  rw [Matrix.mulVec_single_one]
  rfl

private noncomputable def separatingProduct {V : Type} [Fintype V] (G : SimpleGraph V) (x : V) : V → ℂ :=
  (∏ v ∈ Finset.univ.filter (G.Adj x), adjacencyOperator G (Pi.single v 1)) *
    (∏ v ∈ Finset.univ.filter (fun v => ¬ G.Adj x v),
      (1 - adjacencyOperator G (Pi.single v 1)))

private lemma separating_product_eq_single {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : ∀ x y, (∀ v, G.Adj x v ↔ G.Adj y v) → x = y) (x : V) :
    separatingProduct G x = Pi.single x 1 := by
  classical
  ext y
  by_cases hxy : y = x
  · subst y
    simp only [separatingProduct, Pi.mul_apply, Finset.prod_apply, Pi.single_eq_same]
    have h₁ : (∏ v ∈ Finset.univ.filter (G.Adj x),
        adjacencyOperator G (Pi.single v 1) x) = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      simp [adjacency_single, (Finset.mem_filter.mp hv).2]
    have h₂ : (∏ v ∈ Finset.univ.filter (fun v => ¬ G.Adj x v),
        ((1 : V → ℂ) - adjacencyOperator G (Pi.single v 1)) x) = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      simp [adjacency_single, (Finset.mem_filter.mp hv).2]
    rw [h₁, h₂, one_mul]
  · have hw : ∃ v, ¬ (G.Adj x v ↔ G.Adj y v) := by
      by_contra! h
      exact hxy (hG x y h).symm
    obtain ⟨v, hv⟩ := hw
    by_cases hxv : G.Adj x v
    · have hyv : ¬ G.Adj y v := fun h => hv (iff_of_true hxv h)
      have hp : (∏ v ∈ Finset.univ.filter (G.Adj x),
          adjacencyOperator G (Pi.single v 1) y) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hxv⟩)
        simp [adjacency_single, hyv]
      simp only [separatingProduct, Pi.mul_apply, Finset.prod_apply]
      rw [hp]
      simp [Pi.single_eq_of_ne hxy]
    · have hyv : G.Adj y v := by
        by_contra h
        exact hv (iff_of_false hxv h)
      have hp : (∏ v ∈ Finset.univ.filter (fun v => ¬ G.Adj x v),
          ((1 : V → ℂ) - adjacencyOperator G (Pi.single v 1)) y) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hxv⟩)
        simp [adjacency_single, hyv]
      simp only [separatingProduct, Pi.mul_apply, Finset.prod_apply]
      rw [hp]
      simp [Pi.single_eq_of_ne hxy]

lemma algHom_eq_of_adjacency_eq {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : ∀ x y, (∀ v, G.Adj x v ↔ G.Adj y v) → x = y)
    {B : Type} [Ring B] [Algebra ℂ B]
    (φ ψ : (V → ℂ) →ₐ[ℂ] B)
    (h : ∀ f, φ (adjacencyOperator G f) = ψ (adjacencyOperator G f)) : φ = ψ := by
  classical
  let S := AlgHom.equalizer φ ψ
  have hh (v : V) : adjacencyOperator G (Pi.single v 1) ∈ S := h _
  have hs (x : V) : Pi.single x 1 ∈ S := by
    rw [← separating_product_eq_single G hG x]
    exact S.mul_mem (S.prod_mem fun v _ => hh v)
      (S.prod_mem fun v _ => S.sub_mem S.one_mem (hh v))
  apply AlgHom.ext
  intro f
  have hdecomp : f = ∑ x, f x • Pi.single x 1 := pi_eq_sum_univ' f
  have hf : f ∈ S := by
    rw [hdecomp]
    exact S.sum_mem fun x _ => S.smul_mem (hs x) (f x)
  exact hf

private lemma no_twins_of_twin_free {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : ∀ x y, (∀ v, G.Adj x v ↔ G.Adj y v) → x = y)
    (B : Type) [Ring B] [Algebra ℂ B] : ¬ HasTwinsIn G B := by
  rintro ⟨φ, ψ, hne, h⟩
  exact hne (algHom_eq_of_adjacency_eq G hG φ ψ h)

private theorem tesseract_eq_hypercube :
    ({
        Adj u v := hammingDist u v = 1
        symm := ⟨fun _ _ h => by rwa [hammingDist_comm]⟩
        loopless := ⟨fun _ h => by simp at h⟩ } : SimpleGraph (Fin 4 → Bool)) =
      D5.S3.Combinatorics.Graph.Hypercube.hypercube 4 := rfl

theorem result : claim := by
  have hp : ∀ x y, (∀ v, prism.Adj x v ↔ prism.Adj y v) → x = y := by
    simp only [prism, boxProd_adj, completeGraph, top_adj]
    decide
  have hc : ∀ x y, (∀ v, cycleProduct.Adj x v ↔ cycleProduct.Adj y v) → x = y := by
    simp only [cycleProduct, boxProd_adj, cycleGraph_adj]
    decide
  have ht : ∀ x y, (∀ v, (D5.S3.Combinatorics.Graph.Hypercube.hypercube 4).Adj x v ↔
      (D5.S3.Combinatorics.Graph.Hypercube.hypercube 4).Adj y v) → x = y := by
    letI : DecidableRel (D5.S3.Combinatorics.Graph.Hypercube.hypercube 4).Adj := fun u v =>
      inferInstanceAs (Decidable (hammingDist u v = 1))
    decide
  intro B _ _
  refine ⟨no_twins_of_twin_free prism hp B, no_twins_of_twin_free cycleProduct hc B, ?_⟩
  change ¬ HasTwinsIn _ B
  rw [tesseract_eq_hypercube]
  exact no_twins_of_twin_free _ ht B

end D5.S3.Quantum.BochniakChelstowskiKasprzakSoltanQuantumTwins
