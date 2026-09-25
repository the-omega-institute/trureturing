import D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import D5.S3.Quantum.Information.InfiniteCalibrationControl
import D5.S3.Quantum.Information.ActualQubitChordObstruction
import D5.S1.Words.Patterns.CyclicStackPreimages
import LeanInformationAudit.Registry.Evidence

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

-- Raw ConstantInfo.type only. Proof implementations are never expanded.
private def measureSourceType (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  let mut pending : List (Expr × Nat) := [(info.type, 0)]
  let mut unique : Std.HashSet Expr := {}
  let mut visits : Nat := 0
  let mut nameBytes : Nat := 0
  let mut metadata : Nat := 0
  let mut maxDepth : Nat := 0
  while let (e, depth) :: rest := pending do
    pending := rest
    visits := visits + 1
    maxDepth := max maxDepth depth
    unique := unique.insert e
    match e with
    | .const n _ => nameBytes := nameBytes + n.toString.utf8ByteSize
    | .app f a => pending := (f, depth + 1) :: (a, depth + 1) :: pending
    | .lam _ t b _ | .forallE _ t b _ =>
      pending := (t, depth + 1) :: (b, depth + 1) :: pending
    | .letE _ t v b _ =>
      pending := (t, depth + 1) :: (v, depth + 1) :: (b, depth + 1) :: pending
    | .mdata m b =>
      metadata := metadata + m.entries.length
      pending := (b, depth + 1) :: pending
    | .proj n _ b =>
      nameBytes := nameBytes + n.toString.utf8ByteSize
      pending := (b, depth + 1) :: pending
    | _ => pure ()
  let raw := TemplateAudit.rawStatementIdentity info.levelParams info.type
  let compact := TemplateAudit.compactRawIdentity info.levelParams info.type
  let compactBytes := (TemplateAudit.compactRawEncoding info.levelParams info.type).map (·.1.size)
  let start ← IO.monoMsNow
  let erased ← liftTermElabM <| TemplateAudit.rawIdentity info.levelParams info.type
  let elapsed := (← IO.monoMsNow) - start
  logInfo m!"SOURCE_COST {name}: raw_visits={visits} unique={unique.size} repeated={visits-unique.size} depth={maxDepth} name_bytes={nameBytes} metadata_entries={metadata} raw_identity={repr raw} erased_identity={repr erased} erased_ms={elapsed} compact_identity={repr compact} compact_bytes={repr compactBytes} proof_body_expansions=0"

run_cmd measureSourceType ``D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation
run_cmd measureSourceType ``D5.S3.Quantum.Information.InfiniteCalibrationControl.result
run_cmd measureSourceType ``D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi
run_cmd measureSourceType ``D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run

private partial def sourceReadoutPaths (e : Expr) (path : Array String := #[])
    (scope : Nat := 0) : Array (Array String × Nat) := Id.run do
  if e.isAppOfArity ``Prod.snd 3 && e.appArg!.isBVar then
    return #[(path, scope - 1 - e.appArg!.bvarIdx!)]
  if let .proj ``Prod 1 (.bvar i) := e then return #[(path, scope - 1 - i)]
  match e with
  | .app f a => return sourceReadoutPaths f (path.push "fn") scope ++
      sourceReadoutPaths a (path.push "arg") scope
  | .forallE _ d b _ | .lam _ d b _ =>
    return sourceReadoutPaths d (path.push "domain") scope ++
      sourceReadoutPaths b (path.push "body") (scope + 1)
  | .letE _ t v b _ => return sourceReadoutPaths t (path.push "type") scope ++
      sourceReadoutPaths v (path.push "value") scope ++
      sourceReadoutPaths b (path.push "body") (scope + 1)
  | .mdata _ b | .proj _ _ b => return sourceReadoutPaths b (path.push "body") scope
  | _ => return #[]

run_cmd do
  let info ← getConstInfo ``D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation
  logInfo m!"SOURCE_READOUT_PATHS {repr (sourceReadoutPaths info.type)}"
