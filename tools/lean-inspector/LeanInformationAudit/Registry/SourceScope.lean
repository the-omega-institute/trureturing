import LeanInformationAudit.Registry.Enrollment
import LeanInformationAudit.CompiledSourceScope

namespace LeanInformationAudit.SourceScope
open Lean

abbrev M := StateT Nat Meta.MetaM
abbrev ReadoutScope := CompiledSourceScope.ReadoutScope
abbrev DefinitionEntry := CompiledSourceScope.DefinitionEntry
abbrev Scope := CompiledSourceScope.Scope

private def runCompiled (action : CompiledSourceScope.M α) : M α := fun fuel =>
  TemplateAudit.runCompiled (action.run fuel)

def debit (n : Nat := 1) : M Unit := runCompiled (CompiledSourceScope.debit n)
def project (slots : Array Nat) (scope : Nat) (e : Expr)
    (inverse : Bool := false) (localDepth : Nat := 0) (depth : Nat := 0) : M Expr :=
  runCompiled (CompiledSourceScope.project slots scope e inverse localDepth depth)
def expandLets (context : Array SourceBinder) (scope : Nat) (e : Expr)
    (localDepth : Nat := 0) (extraDepth : Nat := 0) (depth : Nat := 0) : M Expr :=
  runCompiled (CompiledSourceScope.expandLets context scope e localDepth extraDepth depth)
def transport (context : Array SourceBinder) (slots : Array Nat) (e : Expr) : M Expr :=
  runCompiled (CompiledSourceScope.transport context slots e)
def atPath (source : Expr) (path : Array String) : M (Array SourceBinder × Expr) :=
  runCompiled (CompiledSourceScope.atPath source path)
def replaceAt (e : Expr) (path : List String) (value : Expr) : M Expr :=
  runCompiled (CompiledSourceScope.replaceAt e path value)
def resolve (info : ConstantInfo) (selection : SourceSelection) : M Scope :=
  runCompiled (CompiledSourceScope.resolve info selection)
def validateFields (scope : Scope) (signature actual : Expr) : M Unit :=
  runCompiled (CompiledSourceScope.validateFields scope signature actual)
def reconstruct (source law : Expr) (depth : Nat := 0) : M Unit :=
  runCompiled (CompiledSourceScope.reconstruct source law depth)

/-- Compiler callers keep lexical locals in their compilation state. -/
partial def inContext (context : Array SourceBinder) (k : Array Expr → M α)
    (i : Nat := 0) (locals : Array Expr := #[]) : M α := do
  debit
  if i == context.size then return ← k locals
  let b := context[i]!
  let domain := b.domain.instantiateRev locals
  fun fuel => do
    let enter := fun x => (inContext context k (i + 1) (locals.push x)).run fuel
    if let some v := b.value then Meta.withLetDecl b.name domain (v.instantiateRev locals) enter
    else Meta.withLocalDecl b.name b.info domain enter

end LeanInformationAudit.SourceScope
