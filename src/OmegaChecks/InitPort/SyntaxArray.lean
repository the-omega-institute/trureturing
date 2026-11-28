module
public import Lean
public import OmegaChecks.InitPort.Alternatives.SyntaxArray
import all OmegaChecks.InitPort.Alternatives.SyntaxArray
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.ToImpureType

open Lean

namespace OmegaChecks.InitPort.SyntaxArray

/-- Per-index agreement includes the end of the array and each stored syntax tree. -/
private def represents {ks : SyntaxNodeKinds} (typed : TSyntaxArray ks) (raw : Array Syntax) : Prop :=
  ∀ i : Nat, typed.toList[i]?.map TSyntax.raw = raw.toList[i]?

private theorem rawElements (ks : SyntaxNodeKinds) (xs : TSyntaxArray ks) :
    represents xs (Alternatives.Lean.TSyntaxArray.rawImpl xs) := by
  intro i
  exact (List.getElem?_map (f := TSyntax.raw) (l := xs.toList) (i := i)).symm

private theorem mkElements (ks : SyntaxNodeKinds) (xs : Array Syntax) :
    represents (Alternatives.Lean.TSyntaxArray.mkImpl (ks := ks) xs) xs := by
  intro i
  change ((xs.toList.map (TSyntax.mk (ks := ks)))[i]?).map TSyntax.raw = xs.toList[i]?
  rw [List.getElem?_map]
  cases xs.toList[i]? <;> rfl

public def supported (n : Name) : Bool :=
  n == `Lean.TSyntaxArray.rawImpl || n == `Lean.TSyntaxArray.mkImpl

/-- The pinned compiler returns the same array after retaining its borrowed pointer.
Both compiler phases erase the single syntax wrapper to its raw field. -/
public def checkRuntimeCast (env : Environment) (native : DefinitionVal) : IO Unit := do
  let raw := native.name == `Lean.TSyntaxArray.rawImpl
  let api := if raw then `Lean.TSyntaxArray.raw else `Lean.TSyntaxArray.mk
  let owner := env.getModuleIdx? `Init.Prelude
  unless supported native.name && native.safety == .unsafe && native.levelParams.isEmpty && owner.isSome &&
      [native.name, api, `Lean.TSyntax, `Lean.TSyntax.mk, `Lean.TSyntax.raw, `Lean.TSyntaxArray].all
        (fun n => env.getModuleIdxFor? n == owner) &&
      Compiler.getImplementedBy? env api == some native.name do
    throw <| IO.userError "invalid native syntax array conversion"
  let some (.fdecl name params .object (.inc retained 1 false false (.ret (.var returned))) _) :=
      IR.findEnvDecl env native.name | throw <| IO.userError s!"unexpected native IR for {native.name}"
  let #[kinds, buffer] := params | throw <| IO.userError "unexpected syntax array parameters"
  unless name == native.name && kinds.ty == .tobject && buffer.ty == .object && kinds.borrow && buffer.borrow &&
      kinds.x != buffer.x && retained == buffer.x && returned == buffer.x do
    throw <| IO.userError "syntax array cast does not return its borrowed input"
  let some field := env.getProjectionFnInfo? `Lean.TSyntax.raw | throw <| IO.userError "missing syntax projection"
  unless field.ctorName == `Lean.TSyntax.mk && field.numParams == 1 && field.i == 0 do
    throw <| IO.userError "syntax projection does not read the erased wrapper field"
/-- Validate the constructive conversion at every typed/raw array index. -/
public def check (env : Environment) (native : DefinitionVal) (candidate : Expr) : IO Unit := do
  checkRuntimeCast env native
  let raw := native.name == `Lean.TSyntaxArray.rawImpl
  let verify : MetaM Unit := do
    for layout in [← Compiler.LCNF.hasTrivialStructure? `Lean.TSyntax,
        ← Compiler.LCNF.hasTrivialImpureStructure? `Lean.TSyntax] do
      unless layout.any (fun info => info.ctorName == `Lean.TSyntax.mk && info.numParams == 1 && info.fieldIdx == 0) do
        throwError "TSyntax does not erase to its raw field"
    Meta.forallTelescope native.type fun args out => do
      let #[ks, xs] := args | throwError "unexpected syntax array signature"
      let input ← Meta.inferType xs
      let actual ← Meta.mkLambdaFVars args (native.value.beta args)
      let cast ← Meta.mkAppOptM `unsafeCast #[some input, some out, some xs]
      let expected ← Meta.mkLambdaFVars args cast
      unless Kernel.isDefEqGuarded env {} actual expected do throwError "unexpected native cast operation"
      let result := mkAppN candidate args
      let arrays := if raw then #[ks, xs, result] else #[ks, result, xs]
      let claim ← Meta.mkAppOptM ``represents (arrays.map some)
      let statement ← Meta.mkForallFVars args claim
      let proof := mkConst (if raw then ``rawElements else ``mkElements)
      let .ok inferred := Kernel.check env {} proof | throwError "invalid syntax array correspondence"
      unless Kernel.isDefEqGuarded env {} inferred statement do throwError "syntax array representation mismatch"
  verify.run' |>.toIO' {fileName := "<syntax array representation>", fileMap := default} {env}

end OmegaChecks.InitPort.SyntaxArray
