/- GID: D5/S3/Observer/MeasureSeparation/FiniteExpectationTableSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/FiniteExpectationTableSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An unrealizable complete affine expectation table has a finite linear certificate. -/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.ContinuousAffineMap

/- Library-search audit trail (2026-08-28):
   * Repository searches for finite expectation-table witnesses, finite linear
     certificates, and compact-convex coordinate separation found no exact D5
     theorem. `FiniteInformationalEffectCertificate` is a near hit for a
     realizable injective quantum readout, not an unrealizable table.
   * Exact pinned-Mathlib hits `IsCompact.elim_finite_subcover` and
     `geometric_hahn_banach_closed_point` are applied directly. The first
     extracts finitely many effects; the second supplies the linear inequality
     on their finite real coordinate space.
-/

noncomputable section

open Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MeasureSeparation.FiniteExpectationTableSeparation

/-- Let the density matrices form a compact convex subset of a real normed
state carrier, and let every effect expectation be continuous affine. If a
complete formal table is not the expectation table of any density matrix,
then finitely many effects admit a continuous linear functional and threshold
that strictly separate the table from every realizable finite readout. -/
theorem finite_expectation_table_separation
    {State Protocol : Type*}
    [NormedAddCommGroup State] [NormedSpace Real State]
    (densityMatrices : Set State)
    (effectExpectation : Protocol -> State →ᴬ[Real] Real)
    (table : Protocol -> Real)
    (densityCompact : IsCompact densityMatrices)
    (densityConvex : Convex Real densityMatrices)
    (notRealizable :
      ¬ exists rho, rho ∈ densityMatrices /\
        forall effect, effectExpectation effect rho = table effect) :
    exists selected : Finset Protocol,
      exists witness : (selected -> Real) →L[Real] Real,
        exists threshold : Real,
          (forall rho, rho ∈ densityMatrices ->
            witness (fun effect : selected =>
              effectExpectation effect.1 rho) < threshold) /\
          threshold < witness (fun effect : selected => table effect.1) := by
  classical
  let disagreement : Protocol -> Set State := fun effect =>
    {rho | effectExpectation effect rho ≠ table effect}
  have disagreementOpen : forall effect, IsOpen (disagreement effect) := by
    intro effect
    exact (isClosed_eq (effectExpectation effect).continuous continuous_const).isOpen_compl
  have disagreementCover :
      densityMatrices ⊆ ⋃ effect, disagreement effect := by
    intro rho rhoDensity
    by_contra uncovered
    apply notRealizable
    refine ⟨rho, rhoDensity, ?_⟩
    intro effect
    have rhoNotDisagree : rho ∉ disagreement effect := by
      intro rhoDisagrees
      exact uncovered (Set.mem_iUnion.mpr ⟨effect, rhoDisagrees⟩)
    simpa [disagreement] using rhoNotDisagree
  obtain ⟨selected, selectedCover⟩ :=
    densityCompact.elim_finite_subcover disagreement disagreementOpen disagreementCover
  let finiteReadout : State →ᴬ[Real] (selected -> Real) :=
    { toAffineMap := AffineMap.pi
        (fun effect : selected => (effectExpectation effect.1).toAffineMap)
      cont := continuous_pi fun effect => (effectExpectation effect.1).continuous }
  let selectedTable : selected -> Real := fun effect => table effect.1
  have imageCompact : IsCompact (finiteReadout '' densityMatrices) :=
    densityCompact.image finiteReadout.continuous
  have imageConvex : Convex Real (finiteReadout '' densityMatrices) :=
    densityConvex.affine_image finiteReadout.toAffineMap
  have tableNotInImage : selectedTable ∉ finiteReadout '' densityMatrices := by
    rintro ⟨rho, rhoDensity, readoutEquals⟩
    have rhoCovered := selectedCover rhoDensity
    rcases Set.mem_iUnion.mp rhoCovered with ⟨effect, rhoCovered⟩
    rcases Set.mem_iUnion.mp rhoCovered with ⟨effectSelected, rhoDisagrees⟩
    have coordinateEqual := congrFun readoutEquals ⟨effect, effectSelected⟩
    exact rhoDisagrees coordinateEqual
  obtain ⟨witness, threshold, imageBelow, tableAbove⟩ :=
    geometric_hahn_banach_closed_point imageConvex imageCompact.isClosed tableNotInImage
  refine ⟨selected, witness, threshold, ?_, tableAbove⟩
  intro rho rhoDensity
  exact imageBelow (finiteReadout rho) ⟨rho, rhoDensity, rfl⟩

#print axioms finite_expectation_table_separation

end D5.S3.Observer.MeasureSeparation.FiniteExpectationTableSeparation
