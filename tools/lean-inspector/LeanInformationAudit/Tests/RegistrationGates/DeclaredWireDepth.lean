import LeanInformationAudit.Registry

namespace LeanInformationAudit.Tests.DeclaredWireDepth
open Lean Meta TemplateAudit

private def nestedName (count : Nat) : Name :=
  (List.range count).foldl (fun parent _ => .str parent "p") .anonymous

private def nestedLevel (count : Nat) : Level :=
  (List.range count).foldl (fun level _ => .succ level) .zero

run_meta do
  let positiveName := rawIdentity [] (.const (nestedName 32) [])
  let positiveLevel := rawIdentity [] (.sort (nestedLevel 32))
  let deepName := rawIdentity [] (.const (nestedName 300) [])
  let deepLevel := rawIdentity [] (.sort (nestedLevel 300))
  let nameRejected := match deepName with
    | .error "incomplete_closure:E8.name_depth" => true
    | _ => false
  let levelRejected := match deepLevel with
    | .error "incomplete_closure:E8.level_depth" => true
    | _ => false
  for (label, ok) in #[
      ("bounded_raw_name_and_level_accepted", positiveName.isOk && positiveLevel.isOk),
      ("raw_name_depth_incomplete", nameRejected),
      ("raw_level_depth_incomplete", levelRejected)] do
    logInfo m!"[{if ok then "PASS" else "FAIL"}] {label}"

end LeanInformationAudit.Tests.DeclaredWireDepth
