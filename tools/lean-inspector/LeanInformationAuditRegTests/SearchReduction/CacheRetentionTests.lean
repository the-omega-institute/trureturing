import LeanInformationAuditRegAnalysis.SearchReduction.Commands

/-! Cache input mappings are released after exact identity validation. Only the
result graph remains mapped, and its proof is checked after the release. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
set_option Elab.async false
set_option maxHeartbeats 0 in
run_cmd do
  enableInitializersExecution
  liftTermElabM do
    IO.FS.withTempFile fun _ path => do
      let identity := String.ofList (List.replicate (4 * 1024 * 1024) 'x')
      let proof := mkConst ``True.intro
      let entry : DiskLookup.Entry := {
        module := "Init.Prelude", name := "True.intro", parts := #[("True", 0), ("intro", 0)]}
      let before := (← lookupPayloadRegions.get).size
      for _ in [:16] do
        pickle path ({
          identity, result := {
          cost := .zero, proof? := some proof, detail := "retained-proof",
          lookup := {source? := some ``True.intro, complete := true},
          certificate? := some (.lookup ``True.intro), query := .hit (.lookup ``True.intro)}} : LocalMemoAnswer)
        let result ← readLocalMemoResult path identity
        unless result.cost == .zero && result.detail == "retained-proof" &&
            result.lookup.source? == some ``True.intro &&
            result.query == .hit (.lookup ``True.intro) do
          throwError "memo payload changed after releasing its identity mapping"
        checkLocalProof (mkConst ``True) result.proof?.get!
      let retained := (← lookupPayloadRegions.get).extract before
      let bytes := retained.foldl (fun total region => total + region.size.toNat) 0
      unless retained.size == 16 && bytes < 1024 * 1024 do
        throwError "memo retained full context: regions={retained.size} bytes={bytes}"
      let count := (← lookupPayloadRegions.get).size
      let mut rejected := false
      try discard <| readLocalMemoResult path "wrong-identity"
      catch _ => rejected := true
      unless rejected && (← lookupPayloadRegions.get).size == count do
        throwError "mismatched memo identity was accepted or retained"
      pickle path ({
        identity, query := mkConst ``True, entry,
        trace := {complete := true, source? := some ``True.intro},
        proof? := some proof, search := 12345, preparation := 678} : LookupCheckpoint)
      for _ in [:32] do
        unless (← readLookupCheckpoint path "wrong-identity" (mkConst ``True) entry).isNone do
          throwError "mismatched checkpoint identity was accepted"
        unless (← readLookupCheckpoint path identity (mkConst ``False) entry).isNone do
          throwError "mismatched checkpoint query was accepted"
        unless (← readLookupCheckpoint path identity (mkConst ``True)
            {entry with name := "False.elim"}).isNone do
          throwError "mismatched checkpoint candidate was accepted"
      unless (← lookupPayloadRegions.get).size == count do
        throwError "mismatched checkpoint mapping was retained"
      let some result ← readLookupCheckpoint path identity (mkConst ``True) entry
        | throwError "matching checkpoint was rejected"
      unless result.search == 12345 && result.preparation == 678 &&
          result.trace.complete && result.trace.source? == some ``True.intro do
        throwError "checkpoint payload changed after input release"
      checkLocalProof (mkConst ``True) result.proof?.get!
      IO.eprintln s!"CACHE_RETENTION accepted=true memo_regions={retained.size} memo_payload_bytes={bytes} input_context_bytes={identity.utf8ByteSize} mismatched_checkpoints_retained=0 proof_rechecked=true"
