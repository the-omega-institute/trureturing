module

public import Lean
import all Lean.Environment

public meta section

namespace LeanInformationAuditRegTests.ContractControl
open Lean Meta

/-- Borrow the compiler's imported objects for a temporary trust-zero kernel.
The compiler retains ownership of every compacted region. -/
def kernelEnvironment (env : Environment) : Environment :=
  env.modifyCheckedAsync fun kernel =>
    { kernel with header := { kernel.header with trustLevel := 0 } }

/-- Retain only serialized test output across independent compiler environments. -/
def publish (name : Name) (value : Json) : MetaM Unit :=
  addAndCompile <| .defnDecl {
    name, levelParams := [], type := mkConst ``String,
    value := mkStrLit value.compress, hints := .opaque, safety := .safe }

def read (value : String) : MetaM Json :=
  match Json.parse value with
  | .ok result => pure result
  | .error error => throwError "control:result_json:{error}"

end LeanInformationAuditRegTests.ContractControl
