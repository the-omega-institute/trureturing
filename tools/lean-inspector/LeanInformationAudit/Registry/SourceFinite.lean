import LeanInformationAudit.Registry.SourceScope

namespace LeanInformationAudit.SourceFinite
open Lean Meta SourceScope

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
private def finite := `D5.S3.ConceptDynamics.InformationEscape

/-- A Unit-indexed family may audit an existing finite catalog only through the
same signature, all realizations, full Law, actual readouts and anchors. -/
def validate (event : TemplateOccurrenceEvent) (arena signature actual : Expr)
    (bridgeName : Name) : M Unit := do
  debit
  let bridge ← mkConstWithLevelParams bridgeName
  let bridgeType ← inferType bridge
  unless bridgeType.isAppOfArity (finite ++ `LegacyPrimitiveRealization) 3 do
    throwError "unclassified_form:source.finite_bridge"
  let objectArena := event.arena
  unless ← isDefEq bridgeType.getAppArgs[0]! objectArena do
    throwError "unclassified_form:source.finite_arena"
  unless ← isDefEq bridgeType.getAppArgs[1]! event.statement do
    throwError "unclassified_form:source.finite_statement"
  let finiteActual := bridgeType.getAppArgs[2]!
  let finiteSignature ← mkAppM (finite ++ `PrimitiveLawArena.signature) #[objectArena]
  let finiteType ← inferType finiteActual
  unless ← isDefEq (← mkAppM (family ++ `Signature.Params) #[signature]) (mkConst ``Unit) do
    throwError "unclassified_form:source.finite_params"
  let liftRealization : Expr → MetaM Expr := fun r => do
    let roleType ← mkAppM (finite ++ `PrimitiveSignature.Index) #[finiteSignature]
    let anchorType ← mkAppM (finite ++ `PrimitiveSignature.AnchorIndex) #[finiteSignature]
    unless (← isDefEq roleType (← mkAppM (family ++ `Signature.Role) #[signature])) &&
        (← isDefEq anchorType (← mkAppM (family ++ `Signature.Anchor) #[signature])) do
      throwError "unclassified_form:source.finite_signature"
    let readout ← withLocalDeclD `role roleType fun role =>
      withLocalDeclD `parameter (mkConst ``Unit) fun parameter => do
        mkLambdaFVars #[role, parameter]
          (← mkAppM (finite ++ `PrimitiveRealization.readout) #[r, role])
    let anchor ← withLocalDeclD `anchor anchorType fun role =>
      withLocalDeclD `parameter (mkConst ``Unit) fun parameter => do
        mkLambdaFVars #[role, parameter]
          (← mkAppM (finite ++ `PrimitiveRealization.anchor) #[r, role])
    let lifted ← mkAppM (family ++ `realize) #[signature, readout, anchor]
    checkWithKernel lifted
    pure lifted
  -- Compare whole state functions at every role, not a sample of states.
  -- Empty anchor types have no inhabitants to compare.
  for role in ← RegistrationGates.indices
      (← mkAppM (family ++ `Signature.Role) #[signature])
      (← mkAppM (family ++ `Signature.finiteRole) #[signature]) do
    debit
    unless ← isDefEq
        (← mkAppM (family ++ `Realization.readout) #[actual, role, mkConst ``Unit.unit])
        (← mkAppM (finite ++ `PrimitiveRealization.readout) #[finiteActual, role]) do
      throwError "unclassified_form:source.finite_actual"
  for anchor in ← RegistrationGates.indices
      (← mkAppM (family ++ `Signature.Anchor) #[signature])
      (← mkAppM (family ++ `Signature.finiteAnchor) #[signature]) do
    debit
    unless ← isDefEq
        (← mkAppM (family ++ `Realization.anchor) #[actual, anchor, mkConst ``Unit.unit])
        (← mkAppM (finite ++ `PrimitiveRealization.anchor) #[finiteActual, anchor]) do
      throwError "unclassified_form:source.finite_anchor"
  let check : MetaM Unit := withLocalDeclD `realization finiteType fun r => do
    let left ← mkAppM (family ++ `Arena.Law) #[arena, ← liftRealization r]
    let right ← mkAppM (finite ++ `PrimitiveLawArena.Law) #[objectArena, r]
    unless ← isDefEq left right do throwError "unclassified_form:source.finite_full_law"
    let unit ← mkConstWithLevelParams event.unitName
    let expected ← mkAppM (finite ++ `LegacyPrimitiveRealization.toTheoremUnit)
      #[bridge, ← mkConstWithLevelParams event.key.theoremName]
    unless ← isDefEq unit expected do throwError "unclassified_form:source.finite_unit"
    checkWithKernel bridge
  liftM check

end LeanInformationAudit.SourceFinite
