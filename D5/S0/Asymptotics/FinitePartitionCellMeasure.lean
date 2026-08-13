/- GID: D5/S0/Asymptotics/FinitePartitionCellMeasure
   generality: G
   mirror-B: D5/B/S0/Asymptotics/FinitePartitionCellMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite measurable probability partition has a cell of at least reciprocal-cardinality measure; only this clause is closed. -/

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace D5.S0.Asymptotics.FinitePartitionCellMeasure

open MeasureTheory

/-- In a nonempty finite measurable partition of a probability space, some cell
has at least the uniform share of the total measure. -/
theorem exists_cell_measure_ge_reciprocal
    {X I : Type*} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (cell : I -> Set X)
    (measurable : forall i, MeasurableSet (cell i))
    (disjoint : Pairwise (Function.onFun Disjoint cell))
    (covers : Set.iUnion cell = Set.univ) :
    exists i, (Fintype.card I : ENNReal)⁻¹ <= mu (cell i) := by
  have hsum : Finset.univ.sum (fun i => mu (cell i)) = 1 := by
    calc
      Finset.univ.sum (fun i => mu (cell i)) = tsum (fun i : I => mu (cell i)) :=
        (tsum_fintype (fun i : I => mu (cell i))).symm
      _ = mu (Set.iUnion cell) := (measure_iUnion disjoint measurable).symm
      _ = 1 := by rw [covers, measure_univ]
  have havg : Finset.univ.sum (fun _i : I => (Fintype.card I : ENNReal)⁻¹) <=
      Finset.univ.sum (fun i => mu (cell i)) := by
    rw [hsum]
    simp
  obtain ⟨i, _, hi⟩ := ENNReal.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨i, hi⟩

end D5.S0.Asymptotics.FinitePartitionCellMeasure
