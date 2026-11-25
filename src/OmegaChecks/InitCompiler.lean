import Lean
import OmegaChecks.InitCompiler.Layout
import OmegaChecks.InitCompiler.Proofs

/-! Elaborate pinned Init declarations in strict prelude modules. -/

open Lean Parser Elab Command
namespace OmegaChecks.InitCompiler

private def omegaName (n : Name) := `Omega ++ n

private partial def translate (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const (omegaName n) us)
    | .proj n i x => some (.proj (omegaName n) i (translate x))
    | _ => none

private def sourceGroup (src : Environment) (owner name : Name) : CoreM (Declaration × Array Name) := do
  let some (.inductInfo target) := src.find? name | throwError "{name} is not an official inductive"
  let mut types := []
  let mut ctors := #[]
  for n in target.all do
    let some idx := src.getModuleIdxFor? n | throwError "missing owner for {n}"
    unless src.header.moduleNames[idx]! == owner do throwError "{n} does not belong to {owner}"
    let some (.inductInfo i) := src.find? n | throwError "invalid inductive group"
    if i.isUnsafe || i.numNested != 0 then throwError "unsupported unsafe or nested inductive {n}"
    let fields ← i.ctors.mapM fun c => do
      let some (.ctorInfo val) := src.find? c | throwError "missing constructor {c}"
      return {name := omegaName c, type := translate val.type : Constructor}
    ctors := ctors ++ fields.toArray.map (·.name)
    types := {name := omegaName n, type := translate i.type, ctors := fields} :: types
  return (.inductDecl target.levelParams target.numParams types.reverse false, ctors)

private def officialDeclaration (stx : Syntax) : CommandElabM (Environment × ConstantInfo) := do
  let moduleName ← getMainModule
  unless moduleName.getRoot == `OmegaInit do throwError "expected an OmegaInit module"
  let owner := moduleName.replacePrefix `OmegaInit `Init
  let src ← officialEnvironment owner
  let name := stx.getId
  if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then
    throwErrorAt stx "expected a public declaration"
  let some idx := src.getModuleIdxFor? name | throwErrorAt stx "unknown upstream declaration"
  unless src.header.moduleNames[idx]! == owner do throwErrorAt stx "expected a declaration from {owner}"
  let some info := src.find? name | throwErrorAt stx "missing upstream declaration"
  if info.isAxiom || info.isUnsafe || info.isPartial then throwErrorAt stx "inadmissible declaration"
  return (src, info)

@[command_parser, builtin_command_parser] def portProof := leading_parser
  "port_proof " >> ident >> optional (" using " >> ident) >> optional " by_reflexivity"

@[builtin_command_elab portProof] def elabPortProof : CommandElab := fun stx => do
  let (src, info) ← officialDeclaration stx[1]
  let type ← ofExcept (translateProofTerm src info.type)
  let target := {info.toConstantVal with name := omegaName info.name, type}
  let levels := target.levelParams.map Level.param
  let implementation ← if stx[2].isNone then pure none
    else some <$> liftTermElabM (realizeGlobalConstNoOverloadWithInfo stx[2][1])
  liftCoreM <| withExporting do
    unless ← Meta.MetaM.run' (Meta.isProp target.type) do throwError "expected a proof interface"
    if !stx[3].isNone then
      if implementation.isSome then throwError "specify only one proof implementation"
      let some term := elementaryProof? (← getEnv) type | throwError "no reflexivity or assumption proof"
      Lean.addDecl (.thmDecl {target with value := term, all := [target.name]})
    else if let some proof := implementation then
      Lean.addDecl (.thmDecl {target with value := mkConst proof levels, all := [target.name]})
    else
      match info with
      | .thmInfo proof =>
        Lean.addDecl (.thmDecl {target with value := ← ofExcept (translateProofTerm src proof.value), all := [target.name]})
      | .defnInfo proof =>
        let definition := {proof with
          toConstantVal := target
          value := ← ofExcept (translateProofTerm src proof.value)
          all := proof.all.map omegaName}
        Lean.addDecl (.defnDecl definition) (forceExpose := proof.hints == .abbrev)
        setReducibilityStatus target.name (getReducibilityStatusCore src info.name)
      | _ => throwError "this proof needs a constructive implementation"
    if isProtected src info.name then modifyEnv (addProtected · target.name)

@[command_parser, builtin_command_parser] def portInductive := leading_parser "port_inductive " >> ident

@[builtin_command_elab portInductive] def elabPortInductive : CommandElab := fun stx => do
  let (src, info) ← officialDeclaration stx[1]
  let name := info.name
  let owner := (← getMainModule).replacePrefix `OmegaInit `Init
  liftCoreM <| withExporting do
    if (getStructureInfo? src name).isSome then throwError "expected an inductive datatype, got structure {name}"
    let (decl, ctors) ← sourceGroup src owner name
    let .inductDecl _ _ types _ := decl | unreachable!
    Lean.addDecl decl
    compilerLayouts (types.toArray.map (·.name)) ctors
    for typ in types do
      Meta.MetaM.run' <| mkCasesOn typ.name
      Meta.MetaM.run' <| mkRecOn typ.name

end OmegaChecks.InitCompiler
