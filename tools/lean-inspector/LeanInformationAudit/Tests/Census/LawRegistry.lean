import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.LawRegistry

-- An imported canonical binding cannot be replaced by the census caller.
/-- error: structural law already registered: LeanInformationAudit.Tests.Census.Evidence.structuralRegistration -/
#guard_msgs in
register_structural_law Evidence.structuralRegistration in Evidence.structuralLawArena
  nondegeneracy Evidence.structuralLawNondegenerate

def lawAlias : StructuralPrimitiveLawArena Evidence.infiniteArena := Evidence.structuralLawArena

theorem aliasBridge : StructuralLegacyPrimitiveRealization lawAlias
    (∀ n : Nat, n % 2 < 2) Evidence.structuralReadouts := ⟨Iff.rfl⟩

def aliasInventory : DispositionInventory := { Evidence.inventory with
  entries := Evidence.inventory.entries.filterMap fun ⟨key, row⟩ => match row with
    | .structuralOccurrence p => some ⟨key, .structuralOccurrence { p with
        «realization» := ``aliasBridge }⟩
    | _ => none }

-- Definitional equality of law arenas is weaker than their canonical identity.
/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem class=structural_occurrence invalid=realization.canonical_law_arena
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``aliasInventory
    `aliasCoverage aliasInventory
    (classError ``Evidence.structuralTheorem "structural_occurrence"
      "realization.canonical_law_arena")

abbrev unboundArena : StructuralArena := ⟨Nat⟩
theorem unboundTheorem : ∀ n : Nat, n % 2 < 2 := Evidence.structuralTheorem
def unboundCatalog : StructuralCatalog unboundArena := Evidence.structuralCatalog

theorem unboundRegistration : StructuralRegistrationEvidence ``unboundTheorem
    unboundArena Evidence.structuralUnit unboundCatalog () (∀ n : Nat, n % 2 < 2) :=
  ⟨rfl, rfl⟩

def unboundInventory : DispositionInventory := ⟨"fixture-head", #[
  ⟨⟨``unboundTheorem, "unbound"⟩, .structuralOccurrence {
    canonicalArena := ``unboundArena
    registration := ``unboundRegistration
    «realization» := ``Evidence.structuralRealization
    strictnessCertificate := ``Evidence.structuralStrictness
    witnessCertificate := ``Evidence.structuralWitness }⟩]⟩

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.LawRegistry.unboundTheorem class=structural_occurrence invalid=realization.law_registration
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``unboundInventory
    `unboundCoverage unboundInventory
    (classError ``unboundTheorem "structural_occurrence" "realization.law_registration")

end LeanInformationAudit.Tests.Census.LawRegistry
