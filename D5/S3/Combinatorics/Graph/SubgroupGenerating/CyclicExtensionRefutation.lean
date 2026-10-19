/- GID: D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.claim; result=D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.result; claim=D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.claim
   digest: The order-one cyclic group refutes the whole Section 5 SGB extension. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false

open Matrix Finset Polynomial

namespace D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

/-- The two parts are distinguished even when their underlying sets overlap. -/
abbrev Vertex (G : Type) [Group G] := (G × G) ⊕ Subgroup G

/-- All ordered pairs and all subgroups, with precisely the source cross edges. -/
def sgbGraph (G : Type) [Group G] : SimpleGraph (Vertex G) where
  Adj x y := match x, y with
    | .inl p, .inr H => Subgroup.closure ({p.1, p.2} : Set G) = H
    | .inr H, .inl p => Subgroup.closure ({p.1, p.2} : Set G) = H
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

noncomputable local instance subgroupFintype (G : Type) [Group G] [Fintype G] :
    Fintype (Subgroup G) := by
  classical
  exact Fintype.ofInjective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

inductive MatrixKind
  | adjacency | laplacian | signless | commonNeighbour

/-- The literal off-diagonal common-neighbour count, with zero diagonal. -/
noncomputable def commonNeighbourMatrix {V : Type} [Fintype V] (g : SimpleGraph V) :
    Matrix V V ℝ := by
  classical
  exact fun i j => if i = j then 0 else
    ((Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧ g.Adj i k ∧ g.Adj j k)).card : ℝ)

/-- The adjacency, Laplacian, signless Laplacian and common-neighbour matrices. -/
noncomputable def sourceMatrix {V : Type} [Fintype V] (g : SimpleGraph V)
    (kind : MatrixKind) : Matrix V V ℝ := by
  classical
  exact match kind with
    | .adjacency => g.adjMatrix ℝ
    | .laplacian => g.lapMatrix ℝ
    | .signless => g.degMatrix ℝ + g.adjMatrix ℝ
    | .commonNeighbour => commonNeighbourMatrix g

private theorem source_matrix_isHermitian {V : Type} [Fintype V]
    (g : SimpleGraph V) (kind : MatrixKind) : (sourceMatrix g kind).IsHermitian := by
  classical
  cases kind with
  | adjacency => exact g.isHermitian_adjMatrix ℝ
  | laplacian => exact g.isHermitian_lapMatrix ℝ
  | signless => exact (g.isHermitian_degMatrix ℝ).add (g.isHermitian_adjMatrix ℝ)
  | commonNeighbour =>
    apply Matrix.IsHermitian.ext
    intro i j
    simp [sourceMatrix, commonNeighbourMatrix, eq_comm, and_comm, and_left_comm]

/-- Actual real symmetric eigenvalues, retaining algebraic multiplicities. -/
noncomputable def graphSpectrum {V : Type} [Fintype V] (g : SimpleGraph V)
    (kind : MatrixKind) : Multiset ℝ := by
  classical
  exact Finset.univ.val.map (RCLike.ofReal ∘ (source_matrix_isHermitian g kind).eigenvalues)

/-- Integer-valued eigenvalues, rather than integer characteristic coefficients. -/
def IntegralSpectrum (s : Multiset ℝ) : Prop := ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ)

/-- The center uses the edge count and vertex count of the entire graph. -/
noncomputable def averageDegree {V : Type} [Fintype V] (g : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (g.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- Absolute energy, centered only in the L and Q cases. -/
noncomputable def graphEnergy {V : Type} [Fintype V] (g : SimpleGraph V)
    (kind : MatrixKind) : ℝ :=
  let center := match kind with
    | .laplacian | .signless => averageDegree g
    | _ => 0
  ((graphSpectrum g kind).map (fun x => |x - center|)).sum

/-- The entire ten-clause list; the benchmarks are actual complete graphs on the same carrier. -/
def sourceBundle {V : Type} [Fintype V] (g : SimpleGraph V) : Prop :=
  ¬ IntegralSpectrum (graphSpectrum g .adjacency) ∧
  IntegralSpectrum (graphSpectrum g .laplacian) ∧
  IntegralSpectrum (graphSpectrum g .signless) ∧
  IntegralSpectrum (graphSpectrum g .commonNeighbour) ∧
  graphEnergy g .adjacency < (Fintype.card V : ℝ) ∧
  graphEnergy g .adjacency ≤ graphEnergy (⊤ : SimpleGraph V) .adjacency ∧
  graphEnergy g .laplacian ≤ graphEnergy (⊤ : SimpleGraph V) .laplacian ∧
  graphEnergy g .signless ≤ graphEnergy (⊤ : SimpleGraph V) .signless ∧
  graphEnergy g .commonNeighbour ≤ graphEnergy (⊤ : SimpleGraph V) .commonNeighbour ∧
  graphEnergy g .adjacency ≤ graphEnergy g .laplacian

/-- The unlabelled closing extension in Das–Erfanian–Nath, Section 5. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [IsCyclic G], sourceBundle (sgbGraph G)

/-- The order-one group has integral adjacency spectrum, contradicting the first conjunct. -/
theorem result : ¬ claim := by
  classical
  let e : Vertex PUnit ≃ Fin 2 :=
    { toFun := Sum.elim (fun _ => 0) (fun _ => 1)
      invFun := fun i => if i = 0 then .inl (PUnit.unit, PUnit.unit) else .inr ⊥
      left_inv := by
        intro x
        cases x with
        | inl p => simp
        | inr H =>
          simp only [Fin.isValue, Sum.elim_inr, one_ne_zero, ↓reduceIte, Sum.inr.injEq]
          exact Subsingleton.elim _ _
      right_inv := by intro i; fin_cases i <;> rfl }
  let g := sgbGraph PUnit
  have hmatrix : Matrix.reindex e e (sourceMatrix g .adjacency) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.reindex_apply, e, sourceMatrix, g, sgbGraph, SimpleGraph.adjMatrix]
  have hchar : (sourceMatrix g .adjacency).charpoly =
      (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) := by
    rw [← Matrix.charpoly_reindex e, hmatrix, Matrix.charpoly_fin_two]
    norm_num [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ]
    ring
  have hspectrum : graphSpectrum g .adjacency = {1} + {-1} := by
    have hr : (sourceMatrix g .adjacency).charpoly.roots = graphSpectrum g .adjacency := by
      exact
        (source_matrix_isHermitian g .adjacency).roots_charpoly_eq_eigenvalues
    rw [← hr, hchar]
    rw [Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  have hint : IntegralSpectrum (graphSpectrum g .adjacency) := by
    rw [hspectrum]
    intro x hx
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
  intro h
  exact (h PUnit).1 hint

end D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
