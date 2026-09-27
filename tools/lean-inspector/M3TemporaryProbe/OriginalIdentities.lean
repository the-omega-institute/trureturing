import LeanInformationAudit.Tests.Seal.M3
namespace M3IdentityCapture
open Lean
structure DagState where
  seen : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def visit (e : Expr) : StateM DagState Nat := do
  if let some id := (← get).seen[ExprStructEq.mk e]? then return id
  let node : Json ← match e with
    | .bvar n => pure <| Json.arr #[toJson "bvar", toJson n]
    | .fvar n => pure <| Json.arr #[toJson "fvar", toJson (reprStr n)]
    | .mvar n => pure <| Json.arr #[toJson "mvar", toJson (reprStr n)]
    | .sort l => pure <| Json.arr #[toJson "sort", toJson (reprStr l)]
    | .const n ls => pure <| Json.arr #[toJson "const", toJson (reprStr n), toJson (reprStr ls)]
    | .app f a => pure <| Json.arr #[toJson "app", toJson (← visit f), toJson (← visit a)]
    | .lam n t b bi => pure <| Json.arr #[toJson "lam", toJson (reprStr n),
        toJson (← visit t), toJson (← visit b), toJson (reprStr bi)]
    | .forallE n t b bi => pure <| Json.arr #[toJson "forallE", toJson (reprStr n),
        toJson (← visit t), toJson (← visit b), toJson (reprStr bi)]
    | .letE n t v b nondep => pure <| Json.arr #[toJson "letE", toJson (reprStr n),
        toJson (← visit t), toJson (← visit v), toJson (← visit b), toJson nondep]
    | .lit l => pure <| Json.arr #[toJson "lit", toJson (reprStr l)]
    | .mdata d b => pure <| Json.arr #[toJson "mdata", toJson (reprStr d), toJson (← visit b)]
    | .proj n i b => pure <| Json.arr #[toJson "proj", toJson (reprStr n),
        toJson i, toJson (← visit b)]
  let id := (← get).nodes.size
  modify fun s => { seen := s.seen.insert ⟨e⟩ id, nodes := s.nodes.push node }
  return id
def encode (e : Expr) : Json :=
  let (id, state) := (visit e).run {}
  Json.mkObj [("root", toJson id), ("nodes", toJson state.nodes)]
end M3IdentityCapture

open Lean Meta LeanInformationAudit
run_cmd do
  let rootId := `LeanInformationAudit.Tests.Seal.M3
  let env ← getEnv
  let records := SealRecords.forRoot env rootId
  let some staged := SealRecords.analysisForRoot? env rootId
    | throwError "missing compiled original M3 analysis"
  let current ← getEnv
  let localNames := current.constants.toList.toArray.filterMap fun (name, _) =>
    if rootId.isPrefixOf name then some name else none
  let names := (localNames ++ staged.declarationNames ++ records.flatMap (fun r =>
    r.theorems.map (·.theoremName))).toList.eraseDups.toArray.qsort (fun a b => a.toString < b.toString)
  let mut identities := #[]
  for name in names do
    let some info := current.find? name | throwError "missing captured declaration {name}"
    let axioms ← collectAxioms name
    identities := identities.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levelParams", toJson (info.levelParams.map Name.toString)),
      ("type_dag", M3IdentityCapture.encode info.type),
      ("value_dag", (info.value? true |>.map M3IdentityCapture.encode).getD Json.null),
      ("axioms", toJson (axioms.map Name.toString |>.qsort (· < ·)))]
  if let some path ← IO.getEnv "M3_IDENTITIES_PATH" then
    IO.FS.writeFile path (Json.arr identities).pretty
  IO.println s!"M3CAPTURE declarations={identities.size}"
