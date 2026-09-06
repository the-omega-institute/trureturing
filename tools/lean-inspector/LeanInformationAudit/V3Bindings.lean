import LeanInformationAudit.ProofBuilder
import LeanInformationAudit.KernelProjection

namespace LeanInformationAudit
open Lean Lean.Meta
open D5.S3.ConceptDynamics.CIRPT D5.S3.ConceptDynamics.InformationEscape

private def mismatch (root catalog : Name) (component : String) : MetaM Unit :=
  throwError "IE-C028 AnalysisCertificateMismatch root={root} catalog={catalog} \
component={component} expected=certified-catalog actual=different"

private def certificateType (name : Name) : MetaM Expr := do
  let some (.thmInfo info) := (← getEnv).find? name
    | throwError "missing theorem certificate: {name}"
  return info.type

/-- Bind occurrence identities and numerals to the suite's actual catalog and its
kernel-certified readout reflection, independently of the output record. -/
def validateV3Bindings (root : Name) (original reflected arena : Expr)
    (counts : SealArenaRecord) (projection : KernelProjectionRecord) : MetaM Unit :=
    withTransparency .all do
  let metadata := counts.catalog
  let fail := mismatch root metadata.catalogId
  let expectedName (name : Name) (suffix : String) :=
    catalogQualifiedName root metadata.arenaName metadata.catalogId name suffix
  let stateCard : Nat ← reduceEval (← mkAppM ``Arena.card #[arena])
  unless counts.stateCard == stateCard && counts.offDiagonalPairCount == projection.denominator do
    fail "arena-counts"
  let indices := counts.theorems.map (·.index) |>.qsort (· < ·)
  unless indices == Array.range counts.theorems.size do fail "occurrence-index-domain"
  let some verdict := projection.certificates.find? (·.1 == "verdict")
    | fail "verdict-certificate"
  let actualVerdict ← certificateType counts.irredundantCertificateName
  let expectedVerdict ← mkAppM
    (if projection.verdict == "irredundant" then ``CatalogIrredundant else ``Catalog.CatalogRedundant)
    #[original]
  unless (← isDefEq actualVerdict expectedVerdict) ||
      (← isDefEq actualVerdict (← certificateType verdict.2)) do fail "verdict-proposition"
  unless counts.irredundantCertificateName ==
      expectedName metadata.arenaName "__catalog_irredundant" do fail "verdict-qualification"
  for row in counts.theorems do
    unless row.unitName == expectedName row.theoremName theoremUnitSuffix &&
        row.realizationName == expectedName row.theoremName primitiveRealizationSuffix &&
        row.certificateName == expectedName row.theoremName "__lowers_escape" do
      fail "occurrence-qualification"
    let unit ← mkConstWithFreshMVarLevels row.unitName
    let index ← ProjectionProof.fin row.index counts.theorems.size
    unless ← isDefEq unit (← mkAppM ``Catalog.theoremAt #[original, index]) do
      fail "occurrence-unit"
    unless ← isDefEq (← mkAppM ``TheoremUnit.Statement #[unit])
        (← inferType (← mkConstWithFreshMVarLevels row.theoremName)) do
      fail "occurrence-statement"
    let some loo := projection.leaveOneOut.find? (·.theoremName == row.unitName)
      | fail "occurrence-leave-one-out"
    let some node := projection.nodes.find? (·.key == loo.node)
      | fail "occurrence-without-node"
    unless row.uniqueCaptureCount == loo.uniqueCaptureCount &&
        row.withoutEscapeCount == node.escapeCount &&
        row.fullEscapeCount + row.uniqueCaptureCount == row.withoutEscapeCount &&
        row.fullEscapeCount == counts.fullEscapeCount do fail "occurrence-counts"
    let expectedLowering ← mkAppM ``Catalog.LowersEscape #[original, index]
    let expectedLowering ← if row.uniqueCaptureCount > 0 then pure expectedLowering else
      mkAppM ``Not #[expectedLowering]
    let actualLowering ← certificateType row.certificateName
    unless (← isDefEq actualLowering expectedLowering) ||
        (← isDefEq actualLowering (← certificateType loo.certificate)) do
      fail "occurrence-certificate-proposition"
    let bundle ← mkAppM ``TheoremUnit.primitives #[unit]
    let bundleIndex ← mkAppM ``PrimitiveBundle.Index #[bundle]
    let bundleFintype ← mkAppM ``PrimitiveBundle.indexFintype #[bundle]
    let primitiveCount : Nat ← reduceEval
      (← mkAppOptM ``Fintype.card #[some bundleIndex, some bundleFintype])
    unless row.primitiveCount == primitiveCount && row.primitiveAxes.size == primitiveCount do
      fail "primitive-count"
    let declared ← mkConstWithFreshMVarLevels row.realizationName
    let declaredType ← whnf (← inferType declared)
    let realized ← if declaredType.isAppOf ``LegacyPrimitiveRealization then
        pure declaredType.appArg!
      else if declaredType.isAppOf ``PrimitiveRealization then pure declared
      else do fail "realization-type"; pure declared
    let decEq ← mkAppM ``Arena.stateDecidableEq #[arena]
    let realizedBundle ← mkAppOptM ``PrimitiveRealization.toPrimitiveBundle
      #[none, none, some decEq, some realized]
    unless ← isDefEq bundle realizedBundle do fail "realization-bundle"
    let members ← whnf (← mkAppOptM ``Fintype.elems #[some bundleIndex, some bundleFintype])
    let list ← whnf (← mkAppM ``Finset.val #[members])
    unless list.isAppOfArity ``Quot.mk 3 do fail "primitive-enumeration"
    let axisFunction ← withLocalDeclD `primitive bundleIndex fun i => do
      mkLambdaFVars #[i] (← mkAppM ``PrimitiveAtom.axis #[← mkAppM ``PrimitiveBundle.atom #[bundle, i]])
    let mut axes := #[]
    for (axis, label) in #[(``PrimitiveAxis.cut, "cut"), (``PrimitiveAxis.flow, "flow"),
        (``PrimitiveAxis.admit, "admit"), (``PrimitiveAxis.anchor, "anchor")] do
      let predicate ← withLocalDeclD `primitive bundleIndex fun i => do
        mkLambdaFVars #[i] (← mkDecide (← mkEq (mkApp axisFunction i) (mkConst axis)))
      let filtered ← mkAppM ``List.filter #[predicate, list.getArg! 2]
      let count : Nat ← reduceEval (← mkAppM ``List.length #[filtered])
      axes := axes ++ Array.replicate count label
    unless row.primitiveAxes == axes do fail "primitive-axes"
    let mut roles := #[]
    for mask in [1:16] do
      let bits := (Array.range 4).map fun bit => mask / 2 ^ (3 - bit) % 2 == 1
      let signature ← ProjectionProof.vector
        (bits.map fun bit => mkConst (if bit then ``Bool.true else ``Bool.false))
      let count : Nat ← reduceEval (← mkAppM ``Catalog.roleHistogram #[reflected, index, signature])
      if count > 0 then
        roles := roles.push
          (String.ofList (bits.toList.map fun bit => if bit then '1' else '0'), count)
    unless row.roleSignatureHistogram.qsort (fun a b => a.1 < b.1) == roles do fail "role-histogram"

end LeanInformationAudit
