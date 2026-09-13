/- GID: D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ImplicationRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrations.orbit_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrations.orbitRealization
   digest: Three frozen implications retain their exact statements through one template with state-dependent predicates. -/

import D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S1.Recurrence.SkolemOrderFiveModularExclusion
import D5.S3.Arith.Lattices.ThinCheckerboardNoThreeInLineSeventeen
import D5.S3.ConceptDynamics.GraphIrregularity.RegularLinkIrregularEleven
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations

open ImplicationRegistrationTemplates LeanInformationAudit

section Orbit
open D5.S1.Recurrence.SkolemOrderFiveModularExclusion

def orbitObjectArena : Arena := Arena.ofFintype (Fin 31)
def orbitObjectArena.__state_enumeration : Arena.StateEnumeration orbitObjectArena where
  states := List.finRange 31
  nodup := List.nodup_finRange 31
  complete := by
    change (List.finRange 31).toFinset = (Finset.univ : Finset (Fin 31))
    ext x; simp
def orbitArena := implicationArena orbitObjectArena Unit
theorem orbit_slotSensitive : FiniteSlotSensitivity orbitArena :=
  implication_sensitivity _ (0 : Fin 31) ()

def orbitRealization := implicationRealization
  (fun (r : Fin 31) (_ : Unit) => r.val ∉ possibleZeroResidues)
  (fun r _ => (orbitState r.val).x0 = 1)
theorem orbit_bridge : LegacyPrimitiveRealization orbitArena
    (∀ r : Fin 31, r.val ∉ possibleZeroResidues → (orbitState r.val).x0 = 1) orbitRealization := by
  refine ⟨Iff.trans ?_ (implicationLegacy orbitObjectArena _ _).equivalence⟩
  exact ⟨fun h r _ => h r, fun h r => h r ()⟩
theorem orbit_lawSensitive : orbitArena.Law orbitRealization ∧
    ¬ orbitArena.Law (implicationRealization (fun (_ : Fin 31) (_ : Unit) => True) (fun _ _ => False)) :=
  ⟨orbit_bridge.equivalence.mp orbit_nonzero_readoff,
    fun h => Bool.noConfusion (h (0 : Fin 31) () rfl)⟩
register_information_theorem orbit_nonzero_readoff in orbitArena
  object_arena orbitObjectArena catalog implications
  primitives orbitRealization.toPrimitiveBundle realization orbit_bridge
  variation orbit_lawSensitive sensitivity orbit_slotSensitive
example : orbit_nonzero_readoff.«D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations/D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations.orbitObjectArena/implications».__information_unit.Statement =
    (∀ r : Fin 31, r.val ∉ possibleZeroResidues → (orbitState r.val).x0 = 1) := rfl
#print axioms orbit_bridge
#print axioms orbit_lawSensitive
#print axioms orbit_slotSensitive
expect_information_occurrence orbit_nonzero_readoff in orbitObjectArena
  from "D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations"
end Orbit

section Grid
open D5.S3.Arith.Lattices.ThinCheckerboardNoThreeInLineSeventeen

def gridObjectArena : Arena := Arena.ofFintype (Fin 17)
def gridObjectArena.__state_enumeration : Arena.StateEnumeration gridObjectArena where
  states := List.finRange 17
  nodup := List.nodup_finRange 17
  complete := by
    change (List.finRange 17).toFinset = (Finset.univ : Finset (Fin 17))
    ext x; simp
def gridArena := implicationArena gridObjectArena (Fin 17)
theorem grid_slotSensitive : FiniteSlotSensitivity gridArena :=
  implication_sensitivity _ (0 : Fin 17) (0 : Fin 17)

def gridRealization := implicationRealization
  (fun x y : Fin 17 => (x.val + y.val) % 2 = 1) (fun x y => 24 ≤ cover (x.val, y.val))
theorem grid_bridge : LegacyPrimitiveRealization gridArena
    (∀ x y : Fin 17, (x.val + y.val) % 2 = 1 → 24 ≤ cover (x.val, y.val)) gridRealization := implicationLegacy _ _ _
theorem grid_lawSensitive : gridArena.Law gridRealization ∧
    ¬ gridArena.Law (implicationRealization (fun _ _ : Fin 17 => True) (fun _ _ => False)) :=
  ⟨grid_bridge.equivalence.mp cover_grid, fun h => Bool.noConfusion (h (0 : Fin 17) (0 : Fin 17) rfl)⟩
register_information_theorem cover_grid in gridArena
  object_arena gridObjectArena catalog implications
  primitives gridRealization.toPrimitiveBundle realization grid_bridge
  variation grid_lawSensitive sensitivity grid_slotSensitive
example : cover_grid.«D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations/D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations.gridObjectArena/implications».__information_unit.Statement =
    (∀ x y : Fin 17, (x.val + y.val) % 2 = 1 → 24 ≤ cover (x.val, y.val)) := rfl
#print axioms grid_bridge
#print axioms grid_lawSensitive
#print axioms grid_slotSensitive
expect_information_occurrence cover_grid in gridObjectArena
  from "D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations"
end Grid

section Profiles
open D5.S3.ConceptDynamics.GraphIrregularity.RegularLinkIrregularEleven

def profilesObjectArena : Arena := Arena.ofFintype (Fin 11)
def profilesObjectArena.__state_enumeration : Arena.StateEnumeration profilesObjectArena where
  states := List.finRange 11
  nodup := List.nodup_finRange 11
  complete := by
    change (List.finRange 11).toFinset = (Finset.univ : Finset (Fin 11))
    ext x; simp
def profilesArena := implicationArena profilesObjectArena (Fin 11)
theorem profiles_slotSensitive : FiniteSlotSensitivity profilesArena :=
  implication_sensitivity _ (0 : Fin 11) (0 : Fin 11)

def profilesRealization := implicationRealization
  (fun u v : Fin 11 => u ≠ v) (fun u v => linkProfile u ≠ linkProfile v)
theorem profiles_bridge : LegacyPrimitiveRealization profilesArena
    (∀ u v : Fin 11, u ≠ v → linkProfile u ≠ linkProfile v) profilesRealization := implicationLegacy _ _ _
theorem profiles_lawSensitive : profilesArena.Law profilesRealization ∧
    ¬ profilesArena.Law (implicationRealization (fun _ _ : Fin 11 => True) (fun _ _ => False)) :=
  ⟨profiles_bridge.equivalence.mp witness_profiles_pairwise_ne, fun h => Bool.noConfusion (h (0 : Fin 11) (0 : Fin 11) rfl)⟩
register_information_theorem witness_profiles_pairwise_ne in profilesArena
  object_arena profilesObjectArena catalog implications
  primitives profilesRealization.toPrimitiveBundle realization profiles_bridge
  variation profiles_lawSensitive sensitivity profiles_slotSensitive
example : witness_profiles_pairwise_ne.«D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations/D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations.profilesObjectArena/implications».__information_unit.Statement =
    (∀ u v : Fin 11, u ≠ v → linkProfile u ≠ linkProfile v) := rfl
#print axioms profiles_bridge
#print axioms profiles_lawSensitive
#print axioms profiles_slotSensitive
expect_information_occurrence witness_profiles_pairwise_ne in profilesObjectArena
  from "D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations"
end Profiles

set_option maxRecDepth 100000 in
#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrations
