import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.CatalogBuilder
import LeanInformationAudit.Sha256
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
-- Enumerations is imported only to expose the production `__state_enumeration` witnesses.
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command
open Lean.Meta
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

-- Triviality and analysis constants are resolved in their consuming Environment,
-- as in ProjectionProof; their libraries are imported by those consumers.
universe u v w

structure PreparedProofs where
  declarations : Array Declaration
  records : Array SealArenaRecord

/-- Check catalog/index before reducing a proposition that may be definitionally trivial. -/
def occurrenceTypeMatches (actual : Expr) (head : Name) (catalog index : Expr) : MetaM Bool := do
  let equality := head == `D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog && actual.isAppOfArity ``Eq 3
  let occurrence := if equality then actual.getAppArgs[1]! else actual
  unless occurrence.isAppOfArity (if equality then ``Catalog.uniqueCapturePairs else head) 3 do
    return false
  return (← isDefEq occurrence.getAppArgs[1]! catalog) &&
    (← isDefEq occurrence.getAppArgs[2]! index) &&
    (← isDefEq actual (← mkAppM head #[catalog, index]))

/-- Bind the report method to a retained projection of compiled Reg evidence. -/
def validateCountingRoute (root catalogId : Name) (catalog : Expr) (method : String) : MetaM Unit := do
  let env ← getEnv
  let compiled := if catalog.isConst then compiledSealEvidence? env catalog.constName! else none
  if compiled.isSome && method == "reg-kernel" then return
  throwError "IE-C028 AnalysisCertificateMismatch root={root} catalog={catalogId} component=proof-method expected=certified-catalog actual=different"

private def finValue (index size : Nat) : MetaM Expr := do
  let bound ← mkLT (mkNatLit index) (mkNatLit size)
  let boundProof ← mkDecideProof bound
  mkAppM ``Fin.mk #[mkNatLit index, boundProof]

private def primitiveCount {X : Type u} (bundle : PrimitiveBundle X) : Nat :=
  @Fintype.card bundle.Index bundle.indexFintype

private def primitiveAxisCount {X : Type u} (bundle : PrimitiveBundle X)
    (axis : PrimitiveAxis) : Nat := by
  letI := bundle.indexFintype
  letI := bundle.indexDecidableEq
  exact (Finset.univ.filter fun index => (bundle.atom index).axis = axis).card

/--
Serialize classes in first-representative order as
`class_count;class_1_ordinals;...`, then SHA-256 those ASCII bytes. The address is
an output-only projection and is never read as seal decision input.
-/
def primitiveKernelAddress (stateFintype bundle : Expr) : MetaM String := do
  let elems ← mkAppOptM ``Fintype.elems #[none, some stateFintype]
  let multiset ← whnf (← mkAppM ``Finset.val #[elems])
  unless multiset.isAppOfArity ``Quot.mk 3 do
    throwError "cannot reflect primitive kernel state enumeration"
  let mut remaining := multiset.getArg! 2
  let mut states := #[]
  repeat
    remaining ← whnf remaining
    if remaining.isAppOfArity ``List.nil 1 then break
    unless remaining.isAppOfArity ``List.cons 3 do
      throwError "cannot reflect primitive kernel state list"
    states := states.push (remaining.getArg! 1)
    remaining := remaining.getArg! 2
  let ordinals := List.range states.size
  let mut classes : Array (Array Nat) := #[]
  for ordinal in ordinals do
    let mut found := none
    for index in [:classes.size] do
      let representative := (classes[index]!)[0]!
      let same ← (reduceEval (← mkAppM ``PrimitiveBundle.agreesB
        #[bundle, states[ordinal]!, states[representative]!]) : MetaM Bool)
      if same then
        found := some index
        break
    classes := match found with
      | some index => classes.modify index fun candidate => candidate.push ordinal
      | none => classes.push #[ordinal]
  let encodedClasses := classes.toList.map fun candidate =>
    String.intercalate "," (candidate.toList.map toString)
  let serialization := String.intercalate ";" (toString classes.size :: encodedClasses)
  pure ("sha256:" ++ Sha256.hex serialization.toUTF8)

private def signatureBit (mask coordinate : Nat) : Bool :=
  mask / (2 ^ (3 - coordinate)) % 2 == 1

private def signatureLabel (mask : Nat) : String :=
  String.ofList <| (List.range 4).map fun coordinate =>
    if signatureBit mask coordinate then '1' else '0'

/-- Bind the raw compiled vector to the independently reconstructed catalog,
then read its kernel-checked fields. No seal proof is constructed or rechecked. -/
private def compiledTheoremProofs (prepared : PreparedCatalog) (input : CompiledSealCatalog) :
    Lean.Elab.Term.TermElabM SealArenaRecord := do
  let fs ← Contract.Decoder.fields ``Contract.SealCatalog input.value 15
  let record := prepared.record
  let size ← Contract.Decoder.liftLiteral (Contract.Literal.nat "seal.size" fs[3]!)
  unless size == record.units.size && input.arenaName == record.arenaName &&
      input.catalogId == record.catalogId do
    throwError "IE-C028 AnalysisCertificateMismatch root={record.rootId} catalog={record.catalogId} component=reg-membership expected=raw-catalog actual=different"
  let compiledCatalog ← mkAppM ``Catalog.ofVector #[fs[4]!]
  unless ← isDefEq compiledCatalog prepared.value do
    throwError "IE-C028 AnalysisCertificateMismatch root={record.rootId} catalog={record.catalogId} component=reg-vector expected=raw-catalog actual=different"
  let stateCard ← Contract.Decoder.liftLiteral (Contract.Literal.nat "seal.stateCard" fs[7]!)
  let full ← Contract.Decoder.liftLiteral (Contract.Literal.nat "seal.full" fs[9]!)
  let keep (name : Name) (proof : Expr) : Lean.Elab.Term.TermElabM Unit :=
    modifyEnv fun env => retainCompiledSealEvidence env name input.source proof
  keep record.catalogName compiledCatalog
  keep (record.catalogName.str "__reg_nondegenerate") fs[5]!
  let env ← getEnv
  let nameFor (name : Name) (suffix : String) := if record.localSealNames then
      localCompanionName env record.rootId name suffix
    else catalogQualifiedName record.rootId record.arenaName record.catalogId name suffix
  let mut theorems : Array SealTheoremRecord := #[]
  for unit in record.units do
    let index ← finValue unit.index size
    let row ← whnf (mkApp fs[11]! index)
    let rs ← Contract.Decoder.fields ``Contract.SealRow row 8
    let unique ← Contract.Decoder.liftLiteral (Contract.Literal.nat "seal.unique" rs[0]!)
    let without ← Contract.Decoder.liftLiteral (Contract.Literal.nat "seal.without" rs[2]!)
    let conclusion ← whnf rs[7]!
    let positive := conclusion.isAppOf ``Contract.SealRowConclusion.positive
    let suffix := if positive then "__lowers_escape" else "__trivial_in_catalog"
    let name := nameFor unit.theoremName suffix
    let args := conclusion.getAppArgs
    let proof := args[args.size - (if positive then 1 else 2)]!
    keep name proof
    let closureCertificate ← if positive then pure none else do
      let closureName := name.str "closure"
      keep closureName args.back!
      pure (some closureName)
    let mut roles := #[]
    for bucket in [:15] do
      let count : Nat ← reduceEval (mkApp rs[4]! (← finValue bucket 15))
      if count > 0 then roles := roles.push (signatureLabel (bucket + 1), count)
    let bundle ← mkAppM ``TheoremUnit.primitives #[mkConst unit.unitName]
    let count : Nat ← reduceEval (← mkAppM ``primitiveCount #[bundle])
    let mut axes := #[]
    for (axis, label) in #[( ``PrimitiveAxis.cut, "cut"), (``PrimitiveAxis.flow, "flow"),
        (``PrimitiveAxis.admit, "admit"), (``PrimitiveAxis.anchor, "anchor")] do
      let axisCount : Nat ← reduceEval (← mkAppM ``primitiveAxisCount #[bundle, mkConst axis])
      axes := axes ++ Array.replicate axisCount label
    let fintype ← mkAppM ``Arena.stateFintype #[prepared.arenaValue]
    theorems := theorems.push {
      theoremName := unit.theoremName, unitName := unit.unitName, realizationName := unit.realizationName,
      registrationModuleName := unit.registrationModuleName, index := unit.index,
      certificate := if positive then .positive name else .trivial name, closureCertificate,
      primitiveCount := count, primitiveAxes := axes,
      primitiveKernelAddress := ← primitiveKernelAddress fintype bundle,
      uniqueCaptureCount := unique, fullEscapeCount := full, withoutEscapeCount := without,
      roleSignatureHistogram := roles, proofMethod := "reg-kernel" }
  let pairs ← Contract.Decoder.liftLiteral (Contract.Literal.array "seal.collisions" fs[12]!)
  let mut classes : Array (Array Name × Array Name) := #[]
  for pair in pairs do
    let args := pair.getAppArgs
    let left := args[args.size - 2]!
    let nested := args.back!.getAppArgs
    let right := nested[nested.size - 2]!
    let i : Nat ← reduceEval (← mkAppM ``Fin.val #[left])
    let j : Nat ← reduceEval (← mkAppM ``Fin.val #[right])
    let proof := nested.back!.getAppArgs.back!
    let name := catalogQualifiedName record.rootId record.arenaName record.catalogId
      record.arenaName s!"__kernel_collision_{i}_{j}"
    keep name proof
    let leftName := record.units[i]!.theoremName
    let rightName := record.units[j]!.theoremName
    if let some classIndex := classes.findIdx? (fun c => c.1[0]? == some leftName) then
      classes := classes.modify classIndex fun c => (c.1.push rightName, c.2.push name)
    else classes := classes.push (#[leftName, rightName], #[name])
  let conclusion ← whnf fs[13]!
  let redundant := conclusion.isAppOf ``Contract.SealCatalogConclusion.redundant
  let verdictName := nameFor record.arenaName
    (if redundant then "__catalog_redundant" else "__catalog_irredundant")
  keep verdictName conclusion.getAppArgs.back!
  let stateEnumeration ← do
    let name := record.catalogName.str "__zero_state_enumeration"
    keep name fs[14]!
    pure (some name)
  let result : SealArenaRecord := {
    catalog := record, compiledEvidence := true, collisionClasses := classes,
    stateEnumeration,
    verdict := if redundant then .redundant verdictName else .irredundant verdictName,
    proofMethod := "reg-kernel", stateCard, offDiagonalPairCount := stateCard * (stateCard - 1),
    fullEscapeCount := full, theorems }

  modifyEnv (retainCompiledSealRecord · result)
  return result

/-- Consume only a complete compiled catalog family; raw membership and order
are reconstructed independently before this function is called. -/
def consumeCompiledSeal (catalogs : Array PreparedCatalog) (inputs : Array CompiledSealCatalog) :
    CommandElabM PreparedProofs := do
  unless inputs.size == catalogs.size do
    throwError "IE-C028 AnalysisCertificateMismatch component=reg-catalog-domain expected={catalogs.size} actual={inputs.size}"
  let records ← liftTermElabM <| catalogs.mapM fun catalog => do
    let matchingInputs := inputs.filter fun input => input.arenaName == catalog.record.arenaName &&
      input.catalogId == catalog.record.catalogId
    unless matchingInputs.size == 1 do
      throwError "IE-C028 AnalysisCertificateMismatch component=reg-catalog-identity"
    let some matching := matchingInputs[0]?
      | throwError "IE-C028 AnalysisCertificateMismatch component=reg-catalog-identity"
    compiledTheoremProofs catalog matching
  return { declarations := #[], records }

end LeanInformationAudit
