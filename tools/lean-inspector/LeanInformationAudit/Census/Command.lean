import LeanInformationAudit.Census.Receipt
import LeanInformationAudit.Census.Membership

namespace LeanInformationAudit.CensusQuery

open Lean Meta Elab Command DispositionCensus

/-- One Environment imports only candidate owners and discovered evidence. Each
key retains its original root scope, supplied by the streamed header closure. -/
elab "#census_validate " requestPath:str " using " membershipPath:str
    " output " destination:str : command => do
  let result ← liftTermElabM do
    let (input, _) ← CensusReceipt.readRequest requestPath.getString
    let head ← ofExcept <| stringField input "head"
    let requested ← ofExcept <| input.getObjValAs? (Array (Array String)) "keys"
    let metadata ← ofExcept <| Json.parse (← IO.FS.readFile membershipPath.getString)
    let requests ← ofExcept <| metadata.getObjValAs? (Array (Array String)) "candidate_keys"
    let scopes ← ofExcept <| metadata.getObjValAs? (Array (String × Array String)) "scopes"
    let assignment ← ofExcept <| metadata.getObjVal? "assignment"
    let named ← ofExcept <| metadata.getObjValAs? (Array Json) "named"
    let env ← getEnv
    let bound ← ofExcept <| metadata.getObjValAs? Nat "batch_module_bound"
    unless env.header.moduleNames.size ≤ bound do
      throwError "IE-C044 candidate batch exceeds module bound: {env.header.moduleNames.size} > {bound}"
    let keyBound ← ofExcept <| metadata.getObjValAs? Nat "batch_key_bound"
    unless requests.size ≤ keyBound do
      throwError "IE-C044 candidate batch exceeds key bound: {requests.size} > {keyBound}"
    let mut entries := #[]
    let mut sources : Array ProvenanceSource := #[]
    let mut keySources : Array (String × Array ProvenanceSource) := #[]
    for request in requests do
      unless requested.contains request && request.size == 3 do
        throwError "IE-C044 candidate key is outside the immutable request"
      let owner := request[0]!
      let key := StatementKey.mk (← ofExcept <| parseNameKey request[1]!) request[2]!
      let root ← ofExcept <| assignment.getObjValAs? String owner
      let some (_, scope) := scopes.find? (·.1 == root)
        | throwError "IE-C044 candidate root scope is missing"
      let modules := scope.map String.toName
      let members := Std.HashSet.ofArray scope
      let mut names : Std.HashMap Name (Array Name) := {}
      for entry in named do
        unless members.contains (← ofExcept <| stringField entry "module") do continue
        let name ← ofExcept <| parseNameJson (← ofExcept <| entry.getObjVal? "name")
        let head := (← ofExcept <| stringField entry "head").toName
        let some info := env.find? name
          | throwError "IE-C044 indexed evidence absent from candidate Environment: {name}"
        unless CensusStream.indexedHead info == some head do
          throwError "IE-C036 indexed evidence type changed: {name}"
        names := names.insert head ((names.getD head #[]).push name)
      for head in CensusStream.evidenceTypes.push CensusStream.approximationHead do
        names := names.insert head ((names.getD head #[]).toList.eraseDups.toArray.qsort Name.quickLt)
      let index : Index := {
        root := root.toName, modules, named := names
        finite := (InformationRegistry.entries env).filter
          (fun e => members.contains e.registrationModuleName.toString)
          |>.qsort (fun a b => Name.quickLt a.unitName b.unitName)
        structural := (structuralProvenanceEntries env).filter
          (fun e => members.contains e.registrationModule.toString)
          |>.qsort (fun a b => Name.quickLt a.unitConst b.unitConst)}
      let mut rowSources : Array ProvenanceSource := #[]
      try
        let row ← assess index head key (some owner.toName)
        -- assess already validates every certified disposition. Only structural
        -- occurrences can return source inputs; the other branches return #[]
        -- and would repeat the same completed validation just to collect it.
        if let .certified (.structuralOccurrence _) := row then
          rowSources ← validateEvidenceSources index.root
            ⟨head, #[⟨key, row⟩]⟩ (some modules)
        let json := dispositionRowJson ⟨key, row⟩
        let json := if let .observed _ := row then
          json.setObjVal! "payload" ((← ofExcept <| json.getObjVal? "payload").setObjVal!
            "import_scope" Json.null) else json
        entries := entries.push json
      catch error =>
        rowSources := #[]
        entries := entries.push (CensusStream.observation owner key.theoremName key.statementId
          root (some (← error.toMessageData.toString)))
      sources := sources ++ rowSources
      keySources := keySources.push (key.statementId, rowSources)
    return Json.mkObj [("head", toJson head),
      ("report_sha256", ← ofExcept <| input.getObjVal? "report_sha256"), ("entries", Json.arr entries),
      ("source_inputs", toJson sources),
      ("key_source_inputs", toJson keySources),
      ("environment_modules", toJson env.header.moduleNames.size),
      ("direct_imports", toJson (env.header.imports.map (·.module.toString)))]
  CensusReceipt.write destination.getString result

end LeanInformationAudit.CensusQuery
