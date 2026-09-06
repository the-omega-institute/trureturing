import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
import LeanInformationAudit.Tests.Projection.FixtureState

/-!
T-041 real-seal mutation fixture. The runner supplies IE_EXPECT_SEAL_REJECTION
and an isolated IE_PROJECTION_OUTPUT_DIR for negative production mutations.
An unmodified run must publish and write all three artifacts.

Audit boundary: direct references in publication definitions owned by
LeanInformationAudit modules, recursively through those modules only. Scanned
namespaces are IO, System, Lean.FS; type-valued constants ending in Sort are not
runtime capabilities. Other Lean-core helpers (including module-data
loaders), dynamic evaluation and callbacks inside opaque external modules are
outside this audit. Reachable own unsafe/extern/implemented_by declarations are
rejected outright. This is not an OS sandbox. Attempt 6's full-core closure
counterexamples remain valid; this fixture makes no full-core purity claim.
-/

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer
open LeanInformationAudit.Tests.Projection

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let expected ← liftIO <| IO.getEnv "IE_EXPECT_SEAL_REJECTION"
  let paths ← #["real-v2.json", "real-v3.json", "real-ascii.txt"].mapM fixturePath
  for path in paths do
    if ← liftIO <| System.FilePath.pathExists path then
      throwError "fixture requires absent artifacts: {path}"
  let before ← getEnv
  let root := before.header.mainModule
  let v2 := Syntax.mkStrLit paths[0]!
  let v3 := Syntax.mkStrLit paths[1]!
  let ascii := Syntax.mkStrLit paths[2]!
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  elabCommand (← `(command| #seal_information_theory output $v2:str
    analysis_output $v3:str ascii_output $ascii:str))
  let errors := (← get).messages.toArray.filter (·.severity == .error)
  let errorMessages ← errors.mapM (·.data.toString)
  modify fun state => { state with messages := savedMessages }
  match expected with
  | some expected =>
    unless errorMessages == #[expected] do
      throwError "RealSeal expected rejection {expected}; actual={errorMessages}"
    let after ← getEnv
    unless (SealRecords.forRoot after root).isEmpty do
      throwError "RealSeal rejected but published seal records"
    for (name, _) in after.constants.toList do
      unless before.contains name do
        throwError "RealSeal rejected but published declaration {name}"
    for path in paths do
      if ← liftIO <| System.FilePath.pathExists path then
        throwError "RealSeal rejected but wrote artifact {path}"
    logInfo s!"RealSeal rejected before publication and writes: {expected}"
  | none =>
    unless errorMessages.isEmpty do throwError "RealSeal failed: {errorMessages}"
    unless (← getEnv).contains (root.str "__system_catalog_irredundant") &&
        SealRecords.systemCatalogIrredundant (← getEnv) root do
      throwError "RealSeal publication missing"
    for path in paths do
      let contents ← liftIO <| IO.FS.readFile path
      if contents.isEmpty then throwError "RealSeal empty artifact {path}"
    logInfo "RealSeal published and wrote all three artifacts"
