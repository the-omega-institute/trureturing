import LeanInformationAuditRegTests.ContractMapping
import Reg.ContractPrototype.CompilerMetadata

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

set_option maxHeartbeats 0

run_cmd do
  let original := (← getEnv).setExporting false
  setEnv original
  liftTermElabM do
    let name := `Reg.ContractPrototype.CompilerMetadata.localLeaf
    let proofName := `Reg.ContractPrototype.CompilerMetadata.localReplacementEq
    GeneratedDeclarations.withOwner `Reg.ContractPrototype.CompilerMetadata do
      let .defnInfo leaf ← getConstInfo `Reg.ContractPrototype.CompilerMetadata.leaf
        | throwError "metadata_leaf_shape"
      addDecl <| .defnDecl { leaf with name := name }
      modifyEnv fun env => GeneratedDeclarations.record env name
      let .thmInfo proof ← getConstInfo `Reg.ContractPrototype.CompilerMetadata.replacement_eq
        | throwError "metadata_proof_shape"
      let mapping := #[(`Reg.ContractPrototype.CompilerMetadata.leaf, name)]
      addDecl <| .thmDecl { proof with
        name := proofName
        type := renameExpr mapping proof.type, value := renameExpr mapping proof.value }
      modifyEnv fun env => GeneratedDeclarations.record env proofName
    let saved ← getEnv
    let event : TemplateOccurrenceEvent := {
      key := {
        root := `Reg.ContractPrototype.CompilerMetadata
        registrationModule := `Reg.ContractPrototype.CompilerMetadata
        theoremName := ``True, objectArena := ``Unit, catalog := ``Unit }
      unitName := name, realizationName := name, statement := mkConst ``True
      levelParams := [], statementIdentity := "", arena := mkConst ``Unit
      registrationSource := "", registrationSourceIdentity := "" }
    let compare (label : String) (a b : Environment) : MetaM Unit := do
      discard <| rejected ("implementation_metadata_" ++ label) "implementation|dependency" <|
        (do verifyActualDependencies label a b #[] event event false; pure Json.null)
    let a := Compiler.implementedByAttr.ext.addEntry saved (name, `Reg.ContractPrototype.CompilerMetadata.targetA)
    let b := Compiler.implementedByAttr.ext.addEntry saved (name, `Reg.ContractPrototype.CompilerMetadata.targetB)
    compare "implemented_by_target" a b
    compare "implemented_by_presence_old" a saved
    compare "implemented_by_presence_new" saved a
    let foreign (entries : List ExternEntry) : MetaM Environment :=
      pure <| externAttr.ext.addEntry saved (name, { entries })
    let externA ← foreign [.standard `all "lean_nat_dec_eq"]
    let externB ← foreign [.standard `all "lean_nat_dec_lt"]
    compare "extern_symbol" externA externB
    compare "extern_presence_old" externA saved
    compare "extern_presence_new" saved externA
    let inlineA ← foreign [.inline `c "((uint8_t)0)"]
    let inlineB ← foreign [.inline `c "((uint8_t)1)"]
    compare "extern_inline" inlineA inlineB
    let tagged := ContractPrototype.CompilerAttributes.taggedReturnAttribute.ext.addEntry saved name
    compare "tagged_return" tagged saved
    let csimp ← inEnvironment saved do
      Compiler.CSimp.add proofName .global
      getEnv
    compare "csimp_presence_old" csimp saved
    compare "csimp_presence_new" saved csimp
    let initializer := `Reg.ContractPrototype.CompilerMetadata.initializer
    let initialized := regularInitAttr.ext.addEntry saved (name, initializer)
    let builtin := builtinInitAttr.ext.addEntry saved (name, initializer)
    compare "init_presence_old" initialized saved
    compare "init_presence_new" saved initialized
    compare "builtin_init_presence_old" builtin saved
    compare "builtin_init_presence_new" saved builtin
    for (label, entries) in #[("extern_adhoc", [.adhoc `all]),
        ("extern_opaque", [ExternEntry.opaque]), ("extern_empty", []),
        ("extern_backend", [.standard `unknown "symbol"])] do
      let env ← foreign entries
      discard <| rejected ("implementation_shape_" ++ label) "implementation_shape" <| inEnvironment env do
        let info ← getConstInfo name
        discard <| implementationIdentity env info `Reg.ContractPrototype.CompilerMetadata
        pure Json.null
    let missing := Compiler.implementedByAttr.ext.addEntry saved
      (name, `Reg.ContractPrototype.CompilerMetadata.missing)
    discard <| rejected "implementation_shape_missing_target" "implementation_target_missing" <| inEnvironment missing do
      let info ← getConstInfo name
      discard <| implementationIdentity missing info `Reg.ContractPrototype.CompilerMetadata
      pure Json.null
    let anonymous := regularInitAttr.ext.addEntry saved (name, Name.anonymous)
    discard <| rejected "implementation_shape_init_anonymous" "implementation_shape" <| inEnvironment anonymous do
      let info ← getConstInfo name
      discard <| implementationIdentity anonymous info `Reg.ContractPrototype.CompilerMetadata
      pure Json.null
    let malformed ← inEnvironment saved do
      let .defnInfo leaf ← getConstInfo name | throwError "metadata_leaf_shape"
      addDecl <| .defnDecl { leaf with name := Compiler.mkUnsafeRecName name }
      getEnv
    discard <| rejected "implementation_shape_unsafe_rec" "implementation_shape:unsafe_rec" <| inEnvironment malformed do
      let info ← getConstInfo name
      discard <| implementationIdentity malformed info `Reg.ContractPrototype.CompilerMetadata
      pure Json.null
    let custom := Compiler.LCNF.passManagerExt.addEntry saved
      (name, Compiler.LCNF.builtinPassManager)
    discard <| rejected "implementation_shape_cpass" "implementation_shape:cpass" <| do
      discard <| verifyCompilerPasses custom
      pure Json.null
    verifyActualDependencies "metadata_equal" saved saved #[] event event false
    logInfo "[PASS] implementation_metadata_equal_control"
    setEnv original
