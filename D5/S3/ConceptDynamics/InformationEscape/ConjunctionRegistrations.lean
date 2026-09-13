/- GID: D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrations.partition_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrations.partitionRealization
   digest: One typed conjunction template registers three frozen statements with checked slot support. -/

import D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S3.Arith.IcosahedralAxisDecomposition
import D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
import D5.S3.Fourier.FinitePoisson
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrations

open ConjunctionRegistrationTemplates LeanInformationAudit

section Partition
open D5.S3.Arith.IcosahedralAxisDecomposition

def partitionClauses : ConjunctionClause 3 0 :=
  .and (.cover 0 1 2) (.and (.disjoint 0 1) (.and (.disjoint 0 2) (.disjoint 1 2)))
def partitionArena := conjunctionArena (Arena.ofFintype FiniteProjectivePlane) partitionClauses
def partitionRealization := conjunctionRealization
  (fun i p => p ∈ ![projectiveAxisPointSet .fivefold, projectiveAxisPointSet .threefold,
    projectiveAxisPointSet .twofold] i) (Fin.elim0 : Fin 0 → FiniteProjectivePlane)
theorem partition_bridge : LegacyPrimitiveRealization partitionArena
    (projectiveAxisPointSet .fivefold ∪ projectiveAxisPointSet .threefold ∪
        projectiveAxisPointSet .twofold = Finset.univ ∧
      Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .threefold) ∧
      Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .twofold) ∧
      Disjoint (projectiveAxisPointSet .threefold) (projectiveAxisPointSet .twofold))
    partitionRealization := by
  refine ⟨Iff.trans ?_
    (conjunctionLegacy (Arena.ofFintype FiniteProjectivePlane) partitionClauses
      (fun (i : Fin 3) (p : FiniteProjectivePlane) =>
        p ∈ ![projectiveAxisPointSet .fivefold, projectiveAxisPointSet .threefold,
        projectiveAxisPointSet .twofold] i) Fin.elim0).equivalence⟩
  change _ ↔ conjunctionStatement
    (fun (i : Fin 3) (p : FiniteProjectivePlane) =>
      p ∈ ![projectiveAxisPointSet .fivefold, projectiveAxisPointSet .threefold,
        projectiveAxisPointSet .twofold] i) (Fin.elim0 : Fin 0 → FiniteProjectivePlane)
    partitionClauses
  dsimp only [partitionClauses, conjunctionStatement]
  simp only [Finset.filter_univ_mem]
  rfl
theorem partition_lawSensitive : partitionArena.Law partitionRealization ∧
    ¬ partitionArena.Law (replaceConjunctionReadout partitionRealization 0 (fun _ => false)) :=
  ⟨partition_bridge.equivalence.mp finite_projective_axis_partition, by
    dsimp only [partitionArena, conjunctionArena, Arena.ofFintype]; decide⟩
theorem partition_slotSensitive : FiniteSlotSensitivity partitionArena :=
  conjunction_sensitivity _ _ partitionRealization (fun _ _ => false) Fin.elim0
    partition_lawSensitive.1
    (by intro i; fin_cases i <;> (dsimp only [conjunctionArena, Arena.ofFintype]; decide))
    (by intro i; exact Fin.elim0 i)
register_information_theorem finite_projective_axis_partition in partitionArena
  primitives partitionRealization.toPrimitiveBundle realization partition_bridge
  variation partition_lawSensitive sensitivity partition_slotSensitive
example : finite_projective_axis_partition.__information_unit.Statement =
    (projectiveAxisPointSet .fivefold ∪ projectiveAxisPointSet .threefold ∪
        projectiveAxisPointSet .twofold = Finset.univ ∧
      Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .threefold) ∧
      Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .twofold) ∧
      Disjoint (projectiveAxisPointSet .threefold) (projectiveAxisPointSet .twofold)) := rfl
#print axioms partition_bridge
#print axioms partition_lawSensitive
#print axioms partition_slotSensitive
expect_information_occurrence finite_projective_axis_partition in partitionArena
  from "D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrations"
end Partition

section Counts
open D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder

def countsClauses : ConjunctionClause 3 0 :=
  .and (.countEq 0 2) (.and (.countEq 1 2) (.countEq 2 2))
def countsArena := conjunctionArena (Arena.ofFintype (Fin 3)) countsClauses
def countsRealization := conjunctionRealization
  (fun i v : Fin 3 => prefers v i (i + 1)) (Fin.elim0 : Fin 0 → Fin 3)
theorem counts_bridge : LegacyPrimitiveRealization countsArena
    ((Finset.univ.filter fun v => prefers v 0 1).card = 2 ∧
      (Finset.univ.filter fun v => prefers v 1 2).card = 2 ∧
        (Finset.univ.filter fun v => prefers v 2 0).card = 2) countsRealization :=
  conjunctionLegacy (Arena.ofFintype (Fin 3)) countsClauses
    (fun i v : Fin 3 => prefers v i (i + 1)) Fin.elim0
theorem counts_lawSensitive : countsArena.Law countsRealization ∧
    ¬ countsArena.Law (replaceConjunctionReadout countsRealization 0 (fun _ => false)) :=
  ⟨counts_bridge.equivalence.mp condorcet_cycle_vote_counts, by
    dsimp only [countsArena, conjunctionArena, Arena.ofFintype]; decide⟩
theorem counts_slotSensitive : FiniteSlotSensitivity countsArena :=
  conjunction_sensitivity _ _ countsRealization (fun _ _ => false) Fin.elim0
    counts_lawSensitive.1
    (by intro i; fin_cases i <;> (dsimp only [conjunctionArena, Arena.ofFintype]; decide))
    (by intro i; exact Fin.elim0 i)
register_information_theorem condorcet_cycle_vote_counts in countsArena
  primitives countsRealization.toPrimitiveBundle realization counts_bridge
  variation counts_lawSensitive sensitivity counts_slotSensitive
example : condorcet_cycle_vote_counts.__information_unit.Statement =
    ((Finset.univ.filter fun v => prefers v 0 1).card = 2 ∧
      (Finset.univ.filter fun v => prefers v 1 2).card = 2 ∧
        (Finset.univ.filter fun v => prefers v 2 0).card = 2) := rfl
#print axioms counts_bridge
#print axioms counts_lawSensitive
#print axioms counts_slotSensitive
expect_information_occurrence condorcet_cycle_vote_counts in countsArena
  from "D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrations"
end Counts

section Membership
open D5.S3.Fourier.FinitePoisson

local instance (x : ZMod 4) : Decidable (x ∈ evenSubgroupFour) := by
  change Decidable ((ZMod.cast x : ZMod 2) = 0)
  infer_instance

def membershipClauses : ConjunctionClause 1 2 := .and (.member 0 0) (.notMember 0 1)
def membershipArena := conjunctionArena (Arena.ofFintype (ZMod 4)) membershipClauses
def membershipRealization := conjunctionRealization
  (fun (_ : Fin 1) (x : ZMod 4) => x ∈ evenSubgroupFour) ![2, 1]
theorem membership_bridge : LegacyPrimitiveRealization membershipArena
    ((2 : ZMod 4) ∈ evenSubgroupFour ∧ (1 : ZMod 4) ∉ evenSubgroupFour)
    membershipRealization := conjunctionLegacy (Arena.ofFintype (ZMod 4)) membershipClauses
      (fun (_ : Fin 1) (x : ZMod 4) => x ∈ evenSubgroupFour) (![2, 1] : Fin 2 → ZMod 4)
theorem membership_lawSensitive : membershipArena.Law membershipRealization ∧
    ¬ membershipArena.Law (replaceConjunctionReadout membershipRealization 0 (fun _ => false)) :=
  ⟨membership_bridge.equivalence.mp evenSubgroupFour_nontrivial, by
    dsimp only [membershipArena, conjunctionArena, Arena.ofFintype]; decide⟩
theorem membership_slotSensitive : FiniteSlotSensitivity membershipArena :=
  conjunction_sensitivity _ _ membershipRealization (fun _ _ => false) (![1, 2] : Fin 2 → ZMod 4)
    membership_lawSensitive.1
    (by intro i; fin_cases i; dsimp only [conjunctionArena, Arena.ofFintype]; decide)
    (by intro i; fin_cases i <;> (dsimp only [conjunctionArena, Arena.ofFintype]; decide))
register_information_theorem evenSubgroupFour_nontrivial in membershipArena
  primitives membershipRealization.toPrimitiveBundle realization membership_bridge
  variation membership_lawSensitive sensitivity membership_slotSensitive
example : evenSubgroupFour_nontrivial.__information_unit.Statement =
    ((2 : ZMod 4) ∈ evenSubgroupFour ∧ (1 : ZMod 4) ∉ evenSubgroupFour) := rfl
#print axioms membership_bridge
#print axioms membership_lawSensitive
#print axioms membership_slotSensitive
expect_information_occurrence evenSubgroupFour_nontrivial in membershipArena
  from "D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrations"
end Membership

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The seal computes the primitive kernel on all pairs of the 31 projective states.
#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let diagnosticName := RegistrationGates.diagnosticName entry.unitName env.header.mainModule
      let info ← getConstInfo diagnosticName
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        let support := if entry.theoremName ==
            ``D5.S3.Fourier.FinitePoisson.evenSubgroupFour_nontrivial then
          "[readout[0],anchor[0],anchor[1]]" else "[readout[0],readout[1],readout[2]]"
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support={support}"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrations
