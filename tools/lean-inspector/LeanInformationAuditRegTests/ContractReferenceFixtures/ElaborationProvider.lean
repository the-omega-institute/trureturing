import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures
syntax (name := emitEquation) "emit_equation" : term
elab_rules : term
  | `(emit_equation) => do
    let parent := `ContractReferenceFixtures.ImportedElaboration.entry
    let lhs := mkConst parent
    addDecl (.thmDecl {
      name := parent.str "eq_def"
      levelParams := []
      type := ← Meta.mkEq lhs lhs
      value := ← Meta.mkEqRefl lhs })
    return mkConst ``Unit.unit
end ContractReferenceFixtures
