import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Meta Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.NameIdentity

def rowFor (name : Name) (id : String) : Sigma fun key : StatementKey => CensusAssessment key :=
  ⟨⟨name, id⟩, .certified <| .boundedFiniteTruncation {
    truncationFamily := ``Evidence.truncation
    bound := 12
    comparisonStatement := ``Evidence.comparison
    certification := .reportOnly }⟩

def collision : DispositionInventory := ⟨"head", #[
  rowFor (Name.str (Name.mkSimple "#a") "b") "sha256:000000000000000000000000000000000000000000000000000000000000001a",
  rowFor (Name.mkSimple "#a.b") "sha256:000000000000000000000000000000000000000000000000000000000000001b"]⟩

run_cmd liftTermElabM do
  for key in collision.keys do
    addDecl <| .thmDecl {
      name := key.theoremName
      levelParams := []
      type := (← getConstInfo ``Evidence.boundedTheorem).type
      value := mkConst ``Evidence.boundedTheorem }
  validateEvidence (← getEnv).header.mainModule collision
  checkWithKernel (← coverageProof ⟨"head", "digest", collision.keys.toArray⟩ collision)

/-- info: (false, true, true, false) -/
#guard_msgs in
#eval let a := collision.entries[0]!.1; let b := collision.entries[1]!.1
  (a.theoremName == b.theoremName, a.theoremName.toString == b.theoremName.toString,
    a.lt b, b.lt a)

/-- info: true -/
#guard_msgs in
#eval parseInventory (toJson collision) == .ok collision

/-- info: true -/
#guard_msgs in
#eval let report : FrozenReport := ⟨"head", "digest", collision.keys.toArray⟩
  (artifact report collision).map Json.compress ==
    (artifact report { collision with entries := collision.entries.reverse }).map Json.compress

-- All payload names, including numeric and anonymous components, retain identity.
/-- info: true -/
#guard_msgs in
#eval [Name.mkSimple "#a.b", Name.str (Name.mkSimple "#a") "b",
    Name.num `A 3, Name.str `A "3", Name.anonymous].all fun name =>
  let key : StatementKey :=
    ⟨`T, "sha256:0000000000000000000000000000000000000000000000000000000000000019"⟩
  let rows : Array (Sigma fun key : StatementKey => CensusAssessment key) := #[
    ⟨key, .certified <| .finiteOccurrence ⟨name, name, name, name, name⟩⟩,
    ⟨key, .certified <| .structuralOccurrence ⟨name, name, name, name, name⟩⟩,
    ⟨key, .certified <| .boundedFiniteTruncation ⟨name, 1, name, .transferred name⟩⟩,
    ⟨key, .certified <| .unreachable ⟨.noFinitePrimitiveBundle, name⟩⟩]
  rows.all fun row => parseRow (dispositionRowJson row) == .ok row

end LeanInformationAudit.Tests.Census.NameIdentity
