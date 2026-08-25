/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/CommonSourceCaptureCollapse
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/CommonSourceCaptureCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A common source channel reduces the all-branch capture minimum to one. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

/- Library-search audit trail (2026-08-21):
   * Searches of D5 and the active frozen ledger for branch compromise,
     capture numbers, and common-source capture found no exact theorem or
     canonical institutional-capture type.
   * The canonical family `Concept` function alias is imported from
     `ConceptFiberDecomposition`; no sibling readout type is redeclared.
   * Pinned Mathlib exact hit `Function.FactorsThrough` is used directly to
     express that a source channel controls a branch output.
   * Pinned Mathlib exact hits `Nat.sInf_le`, `Nat.sInf_mem`,
     `Set.ncard_singleton`, and `Set.ncard_eq_zero` are applied directly to
     the source-defined minimum over finite capturing sets.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.CommonSourceCaptureCollapse

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A controlled source set compromises a branch when one of its source
channels carries enough information to determine that branch's output. -/
def branchCompromised
    {Source State Signal Branch Result : Type*}
    (channel : Source -> Concept State Signal)
    (output : Branch -> Concept State Result)
    (controlled : Set Source) (branch : Branch) : Prop :=
  exists source, source ∈ controlled ∧
    (output branch).FactorsThrough (channel source)

/-- A source set captures the institution when it compromises every branch. -/
def capturesAllBranches
    {Source State Signal Branch Result : Type*}
    (channel : Source -> Concept State Signal)
    (output : Branch -> Concept State Result)
    (controlled : Set Source) : Prop :=
  forall branch, branchCompromised channel output controlled branch

/-- The institutional capture number is the least cardinality of a finite
source set that captures every branch. -/
noncomputable def captureNumber
    {Source State Signal Branch Result : Type*}
    (channel : Source -> Concept State Signal)
    (output : Branch -> Concept State Result) : Nat :=
  sInf {size | exists controlled : Set Source,
    controlled.Finite ∧ controlled.ncard = size ∧
      capturesAllBranches channel output controlled}

/-- If every branch output factors through one common source channel, the
minimum number of controlled sources needed to capture all branches is one. -/
theorem common_source_capture_number_eq_one
    {Source State Signal Branch Result : Type*}
    [Nonempty Branch]
    (channel : Source -> Concept State Signal)
    (output : Branch -> Concept State Result)
    (source : Source)
    (commonSource : forall branch,
      (output branch).FactorsThrough (channel source)) :
    captureNumber channel output = 1 := by
  let candidateSizes : Set Nat :=
    {size | exists controlled : Set Source,
      controlled.Finite ∧ controlled.ncard = size ∧
        capturesAllBranches channel output controlled}
  have singletonCaptures :
      capturesAllBranches channel output ({source} : Set Source) := by
    intro branch
    exact ⟨source, Set.mem_singleton source, commonSource branch⟩
  have singletonCandidate : 1 ∈ candidateSizes := by
    exact ⟨{source}, Set.finite_singleton source,
      Set.ncard_singleton source, singletonCaptures⟩
  change sInf candidateSizes = 1
  apply le_antisymm (Nat.sInf_le singletonCandidate)
  rw [Nat.one_le_iff_ne_zero]
  intro minimumZero
  have minimumCandidate : sInf candidateSizes ∈ candidateSizes :=
    Nat.sInf_mem ⟨1, singletonCandidate⟩
  rw [minimumZero] at minimumCandidate
  rcases minimumCandidate with
    ⟨controlled, controlledFinite, controlledCard, captures⟩
  have controlledEmpty : controlled = ∅ :=
    (Set.ncard_eq_zero controlledFinite).mp controlledCard
  obtain ⟨branch⟩ := (inferInstance : Nonempty Branch)
  rcases captures branch with ⟨controlledSource, membership, _⟩
  rw [controlledEmpty] at membership
  exact Set.notMem_empty controlledSource membership

/-- Two nonempty branches and the identity channel realize the public
common-source hypothesis. -/
example :
    captureNumber
      (fun _ : Unit => (id : Concept Bool Bool))
      (fun _ : Fin 2 => (id : Concept Bool Bool)) = 1 := by
  apply common_source_capture_number_eq_one _ _ ()
  intro branch
  exact Function.FactorsThrough.rfl

/-- With no sources, a nonempty branch cannot be captured, so the conclusion
is not true independently of the common-source hypothesis. -/
example :
    captureNumber
      (fun source : Empty => (nomatch source : Concept Bool Unit))
      (fun _ : Unit => (id : Concept Bool Bool)) = 0 := by
  unfold captureNumber
  rw [Nat.sInf_eq_zero]
  right
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro size
  rintro ⟨controlled, _, _, captures⟩
  rcases captures () with ⟨source, _, _⟩
  exact Empty.elim source

#print axioms common_source_capture_number_eq_one

end D5.S3.ConceptDynamics.InstitutionalCapture.CommonSourceCaptureCollapse
