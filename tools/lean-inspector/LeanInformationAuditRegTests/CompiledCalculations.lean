import LeanInformationAudit.ArtifactAssessment

namespace LeanInformationAuditRegTests.CompiledCalculations
open Lean LeanInformationAudit

unsafe def check (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
  let store ← reader.get
  let value := mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3)
  let fingerprint := fun e => IO.ofExcept (TemplateAudit.compactRawIdentity [] e)
  let repeated := (List.range 18).foldl
    (fun term _ => mkApp2 (mkConst ``Nat.add) term term) value
  let .ok (_, repeatedWork) := TemplateAudit.compactRawIdentity [] repeated 4096
    | throw <| IO.userError "compiled.identity:shared_dag_work"
  unless repeatedWork < 4096 do throw <| IO.userError "compiled.identity:shared_dag_limit"
  let (original, _) ← fingerprint value
  let (changed, _) ← fingerprint (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 4))
  unless original != changed do
    throw <| IO.userError "compiled.identity:changed_argument"
  let lambda := Expr.lam `a (mkConst ``Nat) (.bvar 0) .default
  let (renamed, _) ← fingerprint (.lam `b (mkConst ``Nat) (.bvar 0) .default)
  let (explicit, _) ← fingerprint lambda
  let (implicit, _) ← fingerprint (.lam `a (mkConst ``Nat) (.bvar 0) .implicit)
  unless renamed == explicit && explicit != implicit do
    throw <| IO.userError "compiled.identity:binder_annotation"
  let deep := (List.range 257).foldl (fun body _ => Expr.lam `a (mkConst ``Nat) body .default)
    (mkNatLit 0)
  unless (match TemplateAudit.compactRawIdentity [] deep with
      | .error _ => true | .ok _ => false) do
    throw <| IO.userError "compiled.identity:depth_limit"
  let enrollment ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store
    `LeanInformationAudit.TemplateEnrollment {} {}
  unless !enrollment.pins.isEmpty && enrollment.pins.all (fun pin =>
      (store.owners[pin.identity.name]?) == some pin.identity.owner) do
    throw <| IO.userError "compiled.dictionary:owner_identity"
  IO.println "[PASS] compiled identities: shared DAG, arguments, binder modes, depth and owners"

end LeanInformationAuditRegTests.CompiledCalculations
