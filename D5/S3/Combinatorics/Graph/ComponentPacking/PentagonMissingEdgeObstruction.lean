/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.no_small_surjective_map; premises=D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.slack_1_impossible,D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.slack_3_impossible
   digest: Small pentagon degree slack violates missing-edge incidence. -/

/-
admission_basis: escape-witness: PentagonSurjectiveLower.no_small_surjective_map
escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map
Direct frozen dependencies:
  none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20094
OrderArithmetic.threshold_or_exception: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.lower_or_exception; Direct frozen dependencies: none
OrderArithmetic.class_size_floor: proof_shape: bind-only; escape_witness: none; consumers: PentagonSurjectiveLower.large_classes; Direct frozen dependencies: none
OrderArithmetic.slack_regimes: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassObstruction.no_small_class_data; Direct frozen dependencies: none
PentagonSlack.MissingDegree: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassObstruction.no_small_class_data, PentagonSlack.slack_1_impossible, PentagonSlack.slack_3_impossible; Direct frozen dependencies: none
PentagonSlack.Feasible: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassDegrees.almost_regular_feasible, PentagonClassMass.feasible_class_mass, PentagonClassObstruction.no_small_class_data, PentagonDefectCounting.missing_degrees_feasible, PentagonIncidence.feasible_of_symmetric_matrix, PentagonSlack.incidence_inequalities, PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonSlack.ConeCondition: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassObstruction.no_small_class_data, PentagonSlack.incidence_inequalities, PentagonSlack.slack_1_impossible, PentagonSlack.slack_3_impossible; Direct frozen dependencies: none
PentagonSlack.incidence_inequalities: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassObstruction.no_small_class_data; Direct frozen dependencies: none
PentagonSlack.slack_1_impossible: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassObstruction.no_small_class_data; Direct frozen dependencies: none
PentagonSlack.slack_3_impossible: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassObstruction.no_small_class_data; Direct frozen dependencies: none
PentagonIncidence.feasible_of_symmetric_matrix: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassMass.feasible_class_mass; Direct frozen dependencies: none
PentagonClassMass.ClassMass: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassMass.feasible_class_mass, PentagonClassMass.mass_row, PentagonClassMass.mass_symmetric; Direct frozen dependencies: none
PentagonClassMass.mass_symmetric: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassMass.feasible_class_mass; Direct frozen dependencies: none
PentagonClassMass.mass_row: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassMass.feasible_class_mass; Direct frozen dependencies: none
PentagonClassMass.feasible_class_mass: proof_shape: bind-only; escape_witness: none; consumers: PentagonDefectCounting.missing_degrees_feasible; Direct frozen dependencies: none
PentagonDefectCounting.cycle_five_adjacency: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalHomExtension.extension, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.PentagonIndependentSubset.adjacent_counts_le_defect, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAbstract.factor_critical, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.ConstructionRows.degree_large, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.ConstructionRows.degree_small, PentagonDefectCounting.defect_row, PentagonDefectCounting.missing_degrees_feasible; Direct frozen dependencies: none
PentagonDefectCounting.ClassSize: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalHomExtension.extension, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.PentagonIndependentSubset.adjacent_counts_le_defect, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYConstructionProperties.class_size, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYConstructionProperties.deleted_class_size, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAbstract.allowed_le_degree_add_two, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAbstract.class_omissions, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAbstract.factor_critical, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.GraphOmissionBound.class_missing_le, PentagonClassDegrees.almost_regular_feasible, PentagonClassDegrees.class_deficit, PentagonClassDegrees.degree_le_permitted, PentagonClassDegrees.sum_class_sizes, PentagonDefectCounting.defect_row, PentagonDefectCounting.missing_degrees_feasible, PentagonSurjectiveLower.large_classes, PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonDefectCounting.DefectWeight: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.PentagonIndependentSubset.adjacent_counts_le_defect, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.GraphOmissionBound.class_missing_le, PentagonClassDegrees.degree_le_permitted, PentagonDefectCounting.defect_row, PentagonDefectCounting.defect_symmetric, PentagonDefectCounting.missing_degrees_feasible; Direct frozen dependencies: none
PentagonDefectCounting.defect_symmetric: proof_shape: bind-only; escape_witness: none; consumers: PentagonDefectCounting.missing_degrees_feasible; Direct frozen dependencies: none
PentagonDefectCounting.defect_row: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.PentagonIndependentSubset.adjacent_counts_le_defect, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.GraphOmissionBound.class_missing_le, PentagonClassDegrees.degree_le_permitted, PentagonDefectCounting.missing_degrees_feasible; Direct frozen dependencies: none
PentagonDefectCounting.missing_degrees_feasible: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassDegrees.almost_regular_feasible; Direct frozen dependencies: none
PentagonClassDegrees.sum_class_sizes: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalHomExtension.extension, PentagonSurjectiveLower.large_classes, PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonClassDegrees.degree_le_permitted: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalHomExtension.extension, PentagonSurjectiveLower.large_classes, PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonClassDegrees.class_deficit: proof_shape: bind-only; escape_witness: none; consumers: PentagonClassDegrees.almost_regular_feasible; Direct frozen dependencies: none
PentagonClassDegrees.almost_regular_feasible: proof_shape: bind-only; escape_witness: none; consumers: PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonClassObstruction.NeighborTotal: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalHomExtension.extension, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.PentagonIndependentSubset.adjacent_counts_le_defect, PentagonClassObstruction.no_small_class_data, PentagonSurjectiveLower.large_classes, PentagonSurjectiveLower.no_small_surjective_map, PentagonSurjectiveLower.three_totals; Direct frozen dependencies: none
PentagonClassObstruction.no_small_class_data: proof_shape: bind-only; escape_witness: none; consumers: PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonSurjectiveLower.three_totals: proof_shape: bind-only; escape_witness: none; consumers: PentagonSurjectiveLower.large_classes; Direct frozen dependencies: none
PentagonSurjectiveLower.large_classes: proof_shape: bind-only; escape_witness: none; consumers: PentagonSurjectiveLower.no_small_surjective_map; Direct frozen dependencies: none
PentagonSurjectiveLower.no_small_surjective_map: proof_shape: content; escape_witness: PentagonSurjectiveLower.no_small_surjective_map; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.no_order_59; Direct frozen dependencies: none
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction


namespace OrderArithmetic
open Finset

/-- Below the proposed extremal order, only degree 23 and order 59 miss the density threshold. -/
theorem threshold_or_exception (d N : ℕ) (hd : 21 ≤ d) (hod : Odd d)
    (hN : N ≤ 2 * (5 * (d + 1) / 4) - 1) :
    3 * N < 8 * (d - 1) ∨ (d = 23 ∧ N = 59) := by
  all_goals
    rcases hod with ⟨k, rfl⟩
    have hk : 10 ≤ k := by omega
    by_cases hlarge : 12 ≤ k
    · omega
    · interval_cases k <;> norm_num at * <;> omega

/-- Every class-size lower bound in the proposed proof is at least seven. -/
private theorem class_size_floor (d N : ℕ) (hd : 21 ≤ d) (hod : Odd d)
    (hN : N ≤ 2 * (5 * (d + 1) / 4) - 1) :
    7 ≤ 3 * (d - 1) - N := by
  all_goals
    rcases hod with ⟨k, rfl⟩
    omega

/-- Nonnegative total slack and parity force exactly the two obstruction regimes. -/
private theorem slack_regimes (d N U : ℕ) (hd : 21 ≤ d) (hod : Odd d) (hon : Odd N)
    (hN : N ≤ 2 * (5 * (d + 1) / 4) - 1) (hU : 2 * N = 5 * d + U) :
    (U = 1 ∧ 11 ≤ (N : ℤ) - 2 * d) ∨
    (U = 3 ∧ 13 ≤ (N : ℤ) - 2 * d) := by
  all_goals
    rcases hod with ⟨k, rfl⟩
    rcases hon with ⟨l, rfl⟩
    omega

end OrderArithmetic


set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-! Cyclic missing-edge obstruction with a distributed deficient-degree budget. -/
namespace PentagonSlack
open Finset
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private def MissingDegree (C : ℤ) (u : Fin 5 → ℕ) (ε : Fin 5 → ℤ) (i : Fin 5) : ℤ :=
  (C - u (i + 2) - u (i + 3)) * u i + ε i

private def Feasible (D : Fin 5 → ℤ) : Prop :=
  ∃ m : Fin 5 → ℤ, (∀ i, 0 ≤ m i) ∧ ∀ i, D i = m (i + 4) + m i

private def ConeCondition (D : Fin 5 → ℤ) : Prop :=
  (∀ i, D i ≤ D (i + 4) + D (i + 1)) ∧
  (∀ i, D i + D (i + 2) ≤ D (i + 1) + D (i + 3) + D (i + 4))

/-- The incidence equations imply the five singleton and five nonadjacent-pair inequalities. -/
private theorem incidence_inequalities (D : Fin 5 → ℤ) (h : Feasible D) :
    ConeCondition D := by
  all_goals
    obtain ⟨m, hm, hD⟩ := h
    have h0 := hm 0; have h1 := hm 1; have h2 := hm 2
    have h3 := hm 3; have h4 := hm 4
    constructor <;> intro i <;> fin_cases i <;>
      simp only [hD] <;> norm_num <;> linarith

/-- Total slack 1 is impossible for every integer C ≥ 2. -/
private theorem slack_1_impossible (C : ℤ) (hC : 2 ≤ C)
    (u : Fin 5 → ℕ) (hu : ∑ i, u i = 1)
    (ε : Fin 5 → ℤ) (hε : ∀ i, 0 ≤ ε i) (hεsum : ∑ i, ε i = 1) :
    ¬ ConeCondition (MissingDegree C u ε) := by
  all_goals
    intro h
    obtain ⟨hs, hp⟩ := h
    have hs0 := hs 0; have hs1 := hs 1; have hs2 := hs 2
    have hs3 := hs 3; have hs4 := hs 4
    have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2
    have hp3 := hp 3; have hp4 := hp 4
    have he0 := hε 0; have he1 := hε 1; have he2 := hε 2
    have he3 := hε 3; have he4 := hε 4
    simp only [Fin.sum_univ_succ] at hu hεsum
    norm_num at hu hεsum
    have ub0 : u 0 ≤ 1 := by exact Nat.le.intro hu
    have ub1 : u 1 ≤ 1 := by omega
    have ub2 : u 2 ≤ 1 := by omega
    have ub3 : u 3 ≤ 1 := by omega
    have ub4 : u 4 ≤ 1 := by omega
    interval_cases a0 : u 0 <;> interval_cases a1 : u 1 <;> try omega
    all_goals interval_cases a2 : u 2 <;> try omega
    all_goals interval_cases a3 : u 3 <;> try omega
    all_goals interval_cases a4 : u 4 <;> try omega
    all_goals
      norm_num [MissingDegree, a0, a1, a2, a3, a4] at hs0 hs1 hs2 hs3 hs4 hp0 hp1 hp2 hp3 hp4
      linarith

/-- Total slack 3 is impossible for every integer C ≥ 4. -/
private theorem slack_3_impossible (C : ℤ) (hC : 4 ≤ C)
    (u : Fin 5 → ℕ) (hu : ∑ i, u i = 3)
    (ε : Fin 5 → ℤ) (hε : ∀ i, 0 ≤ ε i) (hεsum : ∑ i, ε i = 1) :
    ¬ ConeCondition (MissingDegree C u ε) := by
  all_goals
    intro h
    obtain ⟨hs, hp⟩ := h
    have hs0 := hs 0; have hs1 := hs 1; have hs2 := hs 2
    have hs3 := hs 3; have hs4 := hs 4
    have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2
    have hp3 := hp 3; have hp4 := hp 4
    have he0 := hε 0; have he1 := hε 1; have he2 := hε 2
    have he3 := hε 3; have he4 := hε 4
    simp only [Fin.sum_univ_succ] at hu hεsum
    norm_num at hu hεsum
    have ub0 : u 0 ≤ 3 := by exact Nat.le.intro hu
    have ub1 : u 1 ≤ 3 := by omega
    have ub2 : u 2 ≤ 3 := by omega
    have ub3 : u 3 ≤ 3 := by omega
    have ub4 : u 4 ≤ 3 := by omega
    interval_cases a0 : u 0 <;> interval_cases a1 : u 1 <;> try omega
    all_goals interval_cases a2 : u 2 <;> try omega
    all_goals interval_cases a3 : u 3 <;> try omega
    all_goals interval_cases a4 : u 4 <;> try omega
    all_goals
      norm_num [MissingDegree, a0, a1, a2, a3, a4] at hs0 hs1 hs2 hs3 hs4 hp0 hp1 hp2 hp3 hp4
      linarith

end PentagonSlack

namespace PentagonIncidence
open Finset PentagonSlack

/-- Symmetric nonnegative class-edge weights supported on the pentagon have its incidence form. -/
private theorem feasible_of_symmetric_matrix (E : Fin 5 → Fin 5 → ℤ)
    (hpos : ∀ i j, 0 ≤ E i j) (hsymm : ∀ i j, E i j = E j i)
    (hsupp : ∀ i j, j ≠ i + 4 → j ≠ i + 1 → E i j = 0) :
    Feasible (fun i => ∑ j, E i j) := by
  all_goals
    refine ⟨fun i => E i (i + 1), fun i => hpos _ _, ?_⟩
    intro i
    have row (i : Fin 5) : ∑ j, E i j = E i (i + 4) + E i (i + 1) := by
      fin_cases i
      · norm_num [Fin.sum_univ_succ]
        rw [hsupp 0 0 (by decide) (by decide)]
        rw [hsupp 0 2 (by decide) (by decide)]
        rw [hsupp 0 3 (by decide) (by decide)]
        ring
      · norm_num [Fin.sum_univ_succ]
        rw [hsupp 1 1 (by decide) (by decide)]
        rw [hsupp 1 3 (by decide) (by decide)]
        rw [hsupp 1 4 (by decide) (by decide)]
        ring
      · norm_num [Fin.sum_univ_succ]
        rw [hsupp 2 0 (by decide) (by decide)]
        rw [hsupp 2 2 (by decide) (by decide)]
        rw [hsupp 2 4 (by decide) (by decide)]
        ring
      · norm_num [Fin.sum_univ_succ]
        rw [hsupp 3 0 (by decide) (by decide)]
        rw [hsupp 3 1 (by decide) (by decide)]
        rw [hsupp 3 3 (by decide) (by decide)]
        ring
      · norm_num [Fin.sum_univ_succ]
        rw [hsupp 4 1 (by decide) (by decide)]
        rw [hsupp 4 2 (by decide) (by decide)]
        rw [hsupp 4 4 (by decide) (by decide)]
        ring
    change (∑ j, E i j) = E (i + 4) (i + 4 + 1) + E i (i + 1)
    rw [row i, hsymm i (i + 4)]
    congr 2
    fin_cases i <;> rfl


end PentagonIncidence

namespace PentagonClassMass
open Finset PentagonSlack PentagonIncidence
variable {V : Type*} [Fintype V]

private def ClassMass (f : V → Fin 5) (W : V → V → ℤ) (i j : Fin 5) : ℤ :=
  ∑ x, ∑ y, if f x = i ∧ f y = j then W x y else 0

/-- Grouping a symmetric vertex-pair weight by its endpoint classes preserves symmetry. -/
private theorem mass_symmetric (f : V → Fin 5) (W : V → V → ℤ)
    (hW : ∀ x y, W x y = W y x) (i j : Fin 5) :
    ClassMass f W i j = ClassMass f W j i := by
  all_goals
    classical
    unfold ClassMass
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro x _
    rw [hW x y]
    simp only [and_comm]

/-- Summing the class-edge matrix row counts all incident weights in that class. -/
private theorem mass_row (f : V → Fin 5) (W : V → V → ℤ) (i : Fin 5) :
    ∑ j, ClassMass f W i j = ∑ x, if f x = i then ∑ y, W x y else 0 := by
  classical
  simpa [ClassMass, Finset.sum_filter, Fintype.sum_prod_type, ← ite_and, and_comm,
    Finset.sum_ite_irrel] using
    (Finset.sum_fiberwise_eq_sum_filter (univ : Finset (V × V)) univ
      (fun p : V × V => f p.2) (fun p => if f p.1 = i then W p.1 p.2 else 0))

/-- Nonnegative symmetric pair weights supported on cyclic neighboring classes satisfy the incidence equations. -/
private theorem feasible_class_mass (f : V → Fin 5) (W : V → V → ℤ)
    (hpos : ∀ x y, 0 ≤ W x y) (hsym : ∀ x y, W x y = W y x)
    (hsup : ∀ x y, f y ≠ f x + 4 → f y ≠ f x + 1 → W x y = 0) :
    Feasible (fun i => ∑ x, if f x = i then ∑ y, W x y else 0) := by
  all_goals
    classical
    have h := feasible_of_symmetric_matrix (ClassMass f W)
      (by intro i j; apply sum_nonneg; intro x _; apply sum_nonneg; intro y _
          split_ifs <;> first | exact hpos _ _ | rfl)
      (mass_symmetric f W hsym)
      (by
        intro i j hj4 hj1
        unfold ClassMass
        apply sum_eq_zero
        intro x _
        apply sum_eq_zero
        intro y _
        split_ifs with hxy
        · exact hsup x y (by simpa [hxy.1, hxy.2] using hj4)
            (by simpa [hxy.1, hxy.2] using hj1)
        · rfl)
    simpa only [mass_row] using h

end PentagonClassMass

namespace PentagonDefectCounting
open Finset PentagonSlack PentagonClassMass
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency in the five-cycle is one step in either cyclic direction. -/
theorem cycle_five_adjacency (i j : Fin 5) :
    (SimpleGraph.cycleGraph 5).Adj i j ↔ j = i + 4 ∨ j = i + 1 := by
  revert i j
  decide

def ClassSize (f : V → Fin 5) (i : Fin 5) : ℕ := (univ.filter fun x => f x = i).card

def DefectWeight (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5) (x y : V) : ℤ :=
  if (SimpleGraph.cycleGraph 5).Adj (f x) (f y) ∧ ¬ G.Adj x y then 1 else 0

/-- The missing-edge indicator is a nonnegative symmetric pair weight. -/
private theorem defect_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (x y : V) : DefectWeight G f x y = DefectWeight G f y x := by
  all_goals
    simp only [DefectWeight, (SimpleGraph.cycleGraph 5).adj_comm, G.adj_comm]

/-- A vertex's total missing incidence is its permitted class total minus its degree. -/
theorem defect_row (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y)) (x : V) :
    ∑ y, DefectWeight G f x y =
      (ClassSize f (f x + 4) : ℤ) + ClassSize f (f x + 1) - G.degree x := by
  all_goals
    classical
    have hne : f x + 4 ≠ f x + 1 := by exact (by decide : ∀ i : Fin 5, i + 4 ≠ i + 1) (f x)
    have hind (y : V) : DefectWeight G f x y =
        (if f y = f x + 4 then (1 : ℤ) else 0) +
        (if f y = f x + 1 then 1 else 0) - (if G.Adj x y then 1 else 0) := by
      by_cases h4 : f y = f x + 4 <;> by_cases h1 : f y = f x + 1 <;>
        by_cases hxy : G.Adj x y
      all_goals solve
        | exact False.elim (hne (h4.symm.trans h1))
        | (have hh := hf hxy; simp [cycle_five_adjacency, h4, h1] at hh)
        | simp [DefectWeight, cycle_five_adjacency, h4, h1, hxy]
    have hd : (G.degree x : ℤ) = ∑ y : V, if G.Adj x y then 1 else 0 := by
      exact_mod_cast (show G.degree x = ∑ y : V, if G.Adj x y then 1 else 0 from
        (G.card_neighborFinset_eq_degree x).symm.trans
          (by simpa only [SimpleGraph.neighborFinset_eq_filter] using
            (Finset.card_filter (fun y => G.Adj x y) univ)))
    simp_rw [hind]
    rw [sum_sub_distrib, sum_add_distrib, ← hd]
    simp [ClassSize, Finset.sum_filter]

/-- Grouped missing degrees satisfy the nonnegative pentagon incidence equations. -/
private theorem missing_degrees_feasible (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y)) :
    Feasible (fun i => ∑ x, if f x = i then
      ((ClassSize f (i + 4) : ℤ) + ClassSize f (i + 1) - G.degree x) else 0) := by
  all_goals
    classical
    have h := feasible_class_mass f (DefectWeight G f)
      (by intro x y; unfold DefectWeight; split_ifs <;> norm_num)
      (defect_symmetric G f)
      (by intro x y h4 h1; simp [DefectWeight, cycle_five_adjacency, h4, h1])
    convert h using 1
    funext i
    apply sum_congr rfl
    intro x _
    split_ifs with hx
    · simpa only [defect_row G f hf x, hx]
    · rfl

end PentagonDefectCounting

namespace PentagonClassDegrees
open Finset PentagonDefectCounting PentagonSlack
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class cardinalities sum to the graph order. -/
theorem sum_class_sizes (f : V → Fin 5) : ∑ i, ClassSize f i = Fintype.card V := by
  classical
  simpa [PentagonDefectCounting.ClassSize] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V) Finset.univ f)

/-- A pentagon map bounds each vertex degree by the sizes of its two permitted classes. -/
theorem degree_le_permitted (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y)) (x : V) :
    G.degree x ≤ ClassSize f (f x + 4) + ClassSize f (f x + 1) := by
  all_goals
    classical
    have hp : 0 ≤ ∑ y, DefectWeight G f x y := by
      apply sum_nonneg
      intro y _
      unfold DefectWeight
      split_ifs <;> norm_num
    rw [defect_row G f hf x] at hp
    omega

/-- The almost-regular deficiency contributes one unit to its vertex's class. -/
private theorem class_deficit (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (d : ℤ) (w : V) (hdeg : ∀ x, (G.degree x : ℤ) = d - if x = w then 1 else 0)
    (i : Fin 5) :
    (∑ x, if f x = i then
      ((ClassSize f (i + 4) : ℤ) + ClassSize f (i + 1) - G.degree x) else 0) =
      (ClassSize f i : ℤ) * ((ClassSize f (i + 4) : ℤ) + ClassSize f (i + 1) - d) +
      if f w = i then 1 else 0 := by
  all_goals
    classical
    let T : ℤ := ClassSize f (i + 4) + ClassSize f (i + 1) - d
    have hind (x : V) :
        (if f x = i then ((ClassSize f (i + 4) : ℤ) + ClassSize f (i + 1) - G.degree x) else 0) =
        (if f x = i then T else 0) + (if x = w then if f w = i then 1 else 0 else 0) := by
      rw [hdeg x]
      by_cases hx : x = w <;> by_cases hfx : f x = i
      all_goals simp_all [T] <;> ring
    simp_rw [hind]
    rw [sum_add_distrib]
    have hsumT : (∑ x : V, if f x = i then T else 0) = (ClassSize f i : ℤ) * T := by
      rw [← Finset.sum_filter]
      simpa only [ClassSize, nsmul_eq_mul] using
        (Finset.sum_const (s := univ.filter fun x : V => f x = i) T)
    rw [hsumT]
    simp [T]

/-- Every almost-regular pentagon map has the missing-edge incidence form of the lower-bound obstruction. -/
private theorem almost_regular_feasible (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y))
    (d : ℤ) (w : V) (hdeg : ∀ x, (G.degree x : ℤ) = d - if x = w then 1 else 0) :
    Feasible (fun i => (ClassSize f i : ℤ) *
      ((ClassSize f (i + 4) : ℤ) + ClassSize f (i + 1) - d) + if f w = i then 1 else 0) := by
  all_goals
    convert missing_degrees_feasible G f hf using 1
    funext i
    exact (class_deficit G f d w hdeg i).symm

end PentagonClassDegrees

namespace PentagonClassObstruction
open Finset PentagonSlack

def NeighborTotal (s : Fin 5 → ℕ) (i : Fin 5) : ℕ := s (i + 4) + s (i + 1)

/-- Odd order below the conjectured threshold cannot realize the almost-regular missing-edge equations. -/
private theorem no_small_class_data (d N : ℕ) (hd : 21 ≤ d) (hod : Odd d) (hon : Odd N)
    (hN : N ≤ 2 * (5 * (d + 1) / 4) - 1)
    (s : Fin 5 → ℕ) (hsum : ∑ i, s i = N)
    (ht : ∀ i, d ≤ NeighborTotal s i)
    (ε : Fin 5 → ℤ) (hε : ∀ i, 0 ≤ ε i) (hεsum : ∑ i, ε i = 1) :
    ¬ Feasible (fun i => (s i : ℤ) * (NeighborTotal s i - d : ℕ) + ε i) := by
  all_goals
    intro hfeas
    let u : Fin 5 → ℕ := fun i => NeighborTotal s i - d
    have hu (i : Fin 5) : NeighborTotal s i = d + u i := by
      have hi := ht i
      dsimp [u]
      omega
    have h0 := hu 0; have h1 := hu 1; have h2 := hu 2
    have h3 := hu 3; have h4 := hu 4
    have hsum' := hsum
    norm_num [Fin.sum_univ_succ, NeighborTotal] at h0 h1 h2 h3 h4 hsum'
    have hU : 2 * N = 5 * d + ∑ i, u i := by
      norm_num [Fin.sum_univ_succ]
      omega
    have hsize (i : Fin 5) :
        (s i : ℤ) = (N : ℤ) - 2 * d - u (i + 2) - u (i + 3) := by
      have hh2 := hu (i + 2)
      have hh3 := hu (i + 3)
      fin_cases i <;> norm_num [NeighborTotal] at hh2 hh3 ⊢ <;> omega
    have hD : (fun i => (s i : ℤ) * (NeighborTotal s i - d : ℕ) + ε i) =
        MissingDegree ((N : ℤ) - 2 * d) u ε := by
      funext i
      dsimp [MissingDegree]
      rw [← hsize]
    rw [hD] at hfeas
    have hcone := incidence_inequalities _ hfeas
    rcases OrderArithmetic.slack_regimes d N (∑ i, u i) hd hod hon hN hU with h | h
    · exact slack_1_impossible _ (by omega) u h.1 ε hε hεsum hcone
    · exact slack_3_impossible _ (by omega) u h.1 ε hε hεsum hcone

end PentagonClassObstruction

namespace PentagonSurjectiveLower
open Finset PentagonSlack PentagonDefectCounting PentagonClassDegrees PentagonClassObstruction
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Three consecutive permitted-degree totals equal order plus the middle class size. -/
private theorem three_totals (s : Fin 5 → ℕ) (i : Fin 5) :
    NeighborTotal s (i + 4) + NeighborTotal s i + NeighborTotal s (i + 1) =
      (∑ j, s j) + s i := by
  all_goals
    fin_cases i <;> norm_num [NeighborTotal, Fin.sum_univ_succ] <;> omega

/-- Below the conjectured order, every surjective pentagon class has at least seven vertices. -/
private theorem large_classes (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y)) (honto : Function.Surjective f)
    (d : ℕ) (hd : 21 ≤ d) (hod : Odd d)
    (hN : Fintype.card V ≤ 2 * (5 * (d + 1) / 4) - 1)
    (hmin : ∀ x, d - 1 ≤ G.degree x) : ∀ i, 7 ≤ ClassSize f i := by
  all_goals
    have ht (i : Fin 5) : d - 1 ≤ NeighborTotal (ClassSize f) i := by
      obtain ⟨x, hx⟩ := honto i
      have hle := degree_le_permitted G f hf x
      simpa only [hx, NeighborTotal] using (hmin x).trans hle
    have hsum := sum_class_sizes f
    intro i
    have hi := ht i
    have hp := ht (i + 4)
    have hn := ht (i + 1)
    have hthree := three_totals (ClassSize f) i
    have hfloor := OrderArithmetic.class_size_floor d (Fintype.card V) hd hod hN
    omega

/-- The missing-edge obstruction rules out every almost-regular surjective pentagon map below the proposed order. -/
theorem no_small_surjective_map (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y)) (honto : Function.Surjective f)
    (d : ℕ) (hd : 21 ≤ d) (hod : Odd d) (hon : Odd (Fintype.card V))
    (hN : Fintype.card V ≤ 2 * (5 * (d + 1) / 4) - 1)
    (w : V) (hdeg : ∀ x, (G.degree x : ℤ) = d - if x = w then 1 else 0) : False := by
  all_goals
    classical
    have hmin (x : V) : d - 1 ≤ G.degree x := by
      have hx := hdeg x
      split_ifs at hx <;> omega
    have hlarge := large_classes G f hf honto d hd hod hN hmin
    have ht (i : Fin 5) : d ≤ NeighborTotal (ClassSize f) i := by
      obtain ⟨x, hx, hxw⟩ := Finset.exists_mem_ne (s := univ.filter fun x => f x = i)
        (by have hi := hlarge i; dsimp [ClassSize] at hi; omega) w
      have hle := degree_le_permitted G f hf x
      have hdx := hdeg x
      simp only [if_neg hxw, sub_zero] at hdx
      have hlabel := (mem_filter.mp hx).2
      simp only [hlabel] at hle
      dsimp [NeighborTotal]
      omega
    let ε : Fin 5 → ℤ := fun i => if f w = i then 1 else 0
    have hepos : ∀ i, 0 ≤ ε i := by intro i; dsimp [ε]; split_ifs <;> norm_num
    have hesum : ∑ i, ε i = 1 := by exact Fintype.sum_ite_eq (f w) (fun _ => 1)
    apply no_small_class_data d (Fintype.card V) hd hod hon hN (ClassSize f)
      (sum_class_sizes f) ht ε hepos hesum
    have hfeas := almost_regular_feasible G f hf (d : ℤ) w hdeg
    convert hfeas using 1
    funext i
    dsimp [ε, NeighborTotal]
    rw [Nat.cast_sub (show d ≤ ClassSize f (i + 4) + ClassSize f (i + 1) from ht i),
      Nat.cast_add]

end PentagonSurjectiveLower

end D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction
