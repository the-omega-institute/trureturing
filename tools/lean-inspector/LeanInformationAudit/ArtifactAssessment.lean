import LeanInformationAudit.ArtifactRegistration
import LeanInformationAudit.CompiledSeal

namespace LeanInformationAudit.ArtifactAssessment
open Lean Contract

/-- Canonical compiled module addresses determine structural requirements.
No source text or discovery result can change a module's obligation. -/
def requirements (owners : Array Name) : Array RootStructure.Requirement :=
  owners.map fun owner => {
    owner, rootId := owner
    kind := RootStructure.kindFromPath
      (System.FilePath.mk (owner.toString.replace "." "/" ++ ".lean")) }

def discover (store : RawArtifacts.Store) (target : Name) : IO Discovery.Snapshot := do
  let reachable := reachableModules (ArtifactRegistration.importsOf store) target
  let owners := store.moduleOrder.filter (fun owner =>
    reachable.contains owner && ((`Reg).isPrefixOf owner ||
      (store.modules.find? owner).any RawArtifacts.hasTypedInputs))
  let context : Literal.Context := {
    find := (store.constants[·]?), owner := (store.owners[·]?),
    external := fun name => store.metadata.externs.contains name || store.metadata.implementedBy.contains name }
  let axioms ← IO.mkRef ({ closure := store.metadata.axioms } : CompiledAxioms.AxiomClosureState)
  Discovery.discoverCompiled (requirements owners) owners context
    (fun owner => return (← store.getModule owner).constants)
    (CompiledAxioms.collectAxiomsShared (store.constants[·]?) axioms)
    (fun owner => pure (System.FilePath.mk (TemplateBinding.sourcePath owner)))

/-- A fresh target assessment rebuilds plans, registrations, all reachable
seals and the complete binding join from the compiler snapshot. -/
unsafe def assess (store : RawArtifacts.Store) (target : Name)
    : IO (ArtifactRegistration.State × Array SealArenaRecord) := do
  let snapshot ← discover store target
  let action : ArtifactRegistration.M (Array SealArenaRecord) := do
    ArtifactRegistration.prepareSnapshot snapshot
    let mut seals := #[]
    for (owner, input) in snapshot.seals do
      seals := seals ++ (← CompiledSeal.consume snapshot owner input)
    let records ← ArtifactRegistration.assessJoined target
    modify fun state => { state with records }
    return seals
  let (seals, state) ← action.run { store }
  return (state, seals)

end LeanInformationAudit.ArtifactAssessment
