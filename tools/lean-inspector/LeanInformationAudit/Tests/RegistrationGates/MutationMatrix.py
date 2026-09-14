def specification(label, original):
    TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistRules'
    kind=label.removeprefix('a11-')
    source=original.decode()

    composite=['DirectIndexBare','CompositeIdentityBare','CompositeIdentityEta','CompositeSuccessorBare','CompositeSuccessorEta','NominalIndexedProofField','NominalRecursiveIndexedProofField','NominalLetIndexProofField']
    if kind=='erase-level-instantiation':
        needle='  let some type ← boundedMeta (Meta.inferType e) `infer_type | return none'
        replacement='''  let some type ← boundedMeta (do
    let occurrence ← match e with
      | .const n _ => do
        let declaration ← getConstInfo n
        match declaration with
        | .defnInfo _ => pure (mkConst n (declaration.levelParams.map Level.param))
        | _ => pure e
      | _ => pure e
    Meta.inferType occurrence) `infer_type | return none'''
        predicted=['NominalUniverseField']
        description='Erase explicit universe instantiations only for definition constants before inference. Retain kernel constructor occurrences, isolating the nominal-return diagnostic boundary.'
    elif kind in ['reconstruct-constructor-type','generic-inferred-telescope']:
        needle='  let mut branches := #[]\n  for ctor in family.ctors do'
        ty='declaration.type' if kind=='reconstruct-constructor-type' else '(← Meta.inferType (mkConst ctorName levels))'
        replacement='''  if family.numParams == 0 && family.numIndices > 0 then
    let mut contexts := #[]
    for ctorName in family.ctors do
      let declaration ← getConstInfo ctorName
      let some fields ← boundedMeta (Meta.forallTelescope '''+ty+''' fun fields _ => do
        return (← getLCtx, ← Meta.getLocalInstances, fields)) `mutant_generic_fields | return none
      contexts := contexts.push fields
    return some contexts
  let mut branches := #[]
  for ctor in family.ctors do'''
        predicted=composite
        description=('Classify fields from raw ConstantInfo.type for indexed constructors with no parameters, bypassing occurrence instantiation.' if kind=='reconstruct-constructor-type' else 'Classify the generic inferred constructor telescope with correct occurrence universes but without resolving the result indices.')
    elif kind=='drop-list-relation-fence':
        needle='let relationAllowed := args[1]! == relation || match args[1]! with'
        replacement='let relationAllowed := true || args[1]! == relation || match args[1]! with'
        predicted=['PairwisePredicatePayload']
        description='Admit arbitrary Pairwise predicates through the equality-only primitive instead of inferring their specialized case fields.'
    elif kind=='drop-list-carrier-fence':
        needle='if carrierEvidence.isSome &&'
        replacement='if true &&'
        predicted=['PropositionNodupPayload','IndexedPropositionNodupPayload','LetPropositionNodupPayload','PropositionMemPayload']
        description='Admit proposition-valued list elements through the natural-number uniqueness primitive.'
    elif kind=='drop-list-statement-fence':
        needle='          if disjoint.isSome then return ← checkedType .listMetadata reduced mentions unclassified'
        replacement='          return ← checkedType .listMetadata reduced mentions unclassified'
        predicted=['NodupFunctionPayload']
        description='Admit the uniqueness primitive even when a proof field can match the registered function statement.'
    elif kind=='drop-order-statement-fence':
        needle='if natOrder reduced && natOrder statement then return ← checkedType .nominalFields type mentions true'
        replacement='if false && natOrder reduced && natOrder statement then return ← checkedType .nominalFields type mentions true'
        source=source.replace('return ← checkedType .naturalOrder reduced mentions (unclassified || order)', 'return ← checkedType .naturalOrder reduced mentions unclassified')
        predicted=['NatLeStatementFence','NatLtStatementFence']
        description='Admit primitive Nat.le even when the normalized registered statement belongs to its recursive proof family.'
    elif kind=='resume-proof-implementations':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  if proof == some true then return'
        replacement='  if false && proof == some true then return'
        source=source.replace('let summary ← if proof then summarise', 'let summary ← if false && proof then summarise')
        predicted=['InternalTargetProofErased','InternalCompanionProofErased','ProofImplementationInvariance']
        description='Re-enter erased proof implementations after checking the occurrence boundary.'
    elif kind=='normalization-api':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='private def compareCanonical (a b : Expr) : WalkM Bool := do'
        replacement=needle+'\n  let _ ← Meta.isDefEq (mkConst ``True) (mkConst ``True)'
        predicted=['NoSemanticNormalization']
        description='Call explicit definitional equality on the actual admission path; the API control must reject even a cheap comparison.'
    elif kind=='remove-algebra-families':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='if Lean.isClass env name && !listedTypeClasses.contains name then'
        replacement='if Lean.isClass env name && (!listedTypeClasses.contains name || #[`AddMonoidWithOne, `AddCommMonoid, `Semiring, `Distrib, `LinearOrder, `Field, `DivisionRing, `Fact, `CharP, `NonUnitalNonAssocCommRing, `NonUnitalCommRing].contains name) then'
        predicted=['UniformMonoidHeads','UniformRingHeads','UniformOrderHeads','UniformFieldHeads','UniformCommutativeRingHeads']
        description='Remove algebra/order class heads uniformly, regardless of instance names.'
    elif kind=='incomplete-as-unsupported':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='let reason := if result.incomplete then "incomplete_closure"'
        replacement='let reason := if result.incomplete then "unclassified_form"'
        predicted=['NativeExhaustionRouting']
        description='Mislabel incomplete work as unsupported form while retaining the null payload.'
    elif kind=='erase-applied-identity':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  if let .const n _ := e.getAppFn then directConstant env n\n  if let .proj n _ _ := e then directProjection env n'
        replacement='  if let .const n _ := e then directConstant env n\n  if let .proj n _ _ := e then directProjection env n'
        predicted=['AppliedTargetIdentity','AppliedCompanionIdentity']
        description='Erase an applied proof before checking the identity of its application head.'
    elif kind=='remove-named-carrier-alias':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='let some carrier ← namedCarrier env args[0]! | return ← checkedType .nominalFields type mentions true'
        replacement='let some carrier ← representationType args[0]! | return ← checkedType .nominalFields type mentions true'
        source=source.replace('    if let some (.defnInfo info) := env.find? name then\n      let value ← Core.instantiateValueLevelParams (.defnInfo info) levels\n      let some body ← aliasBody value args | return none\n      -- admission-exit: dataCarrier.6 rule=retained-witness.rule\n      return ← dataCarrier env body (active.push type)', '    if (env.find? name).any (fun i => i.hasValue) then return none')
        predicted=['FiniteFunctionRange']
        description='Remove named carrier alias forwarding from both collection-boundary sites.'
    elif kind=='remove-statement-projection':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  | .proj structureName index receiver =>\n    let (record, work) := ReadoutFamily.carrier env receiver (← get).exprFuel'
        replacement='  | .proj structureName index receiver =>\n    return ← statementUnknown (.proj structureName index receiver)\n    let (record, work) := ReadoutFamily.carrier env receiver (← get).exprFuel'
        predicted=['ProjectedStatementAlias']
        description='Treat explicit record projection aliases as opaque when retaining statement rejection witnesses.'
    elif kind=='resume-proposition-operands':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='    if type == .sort .zero then\n      -- Propositions are checked'
        replacement='    if false && type == .sort .zero then\n      -- Propositions are checked'
        predicted=['ErasedPredicateBoundary']
        description='Traverse erased mathematical operands of propositions as executable data.'
    elif kind=='carrier-name-only-recursion':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='if active.contains type then return none'
        replacement='if active.any (fun previous => previous.getAppFn.constName? == some name) then return none'
        predicted=['NestedScalarCarrier']
        description='Conflate distinct instantiations of a nested carrier by retaining only its class name.'
    elif kind=='remove-subtype-carrier':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='if name == ``Subtype && args.size == 2 then'
        replacement='if false && name == ``Subtype && args.size == 2 then'
        predicted=['SubtypeScalarCarrier']
        description='Remove the native subtype base-carrier boundary while retaining all predicate-type checks.'
    elif kind=='unfold-membership-boundary':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  if type.getAppFn.isConstOf `Multiset.Mem then\n    -- admission-exit: statementOuter.1 rule=statementMembership\n    return some (witness .statementMembership type)'
        replacement='  if false && type.getAppFn.isConstOf `Multiset.Mem then\n    -- admission-exit: statementOuter.1 rule=statementMembership\n    return some (witness .statementMembership type)'
        predicted=['SubsetMetadataBoundary']
        description='Unfold past the supported membership terminal instead of recognizing its structural boundary.'
    elif kind=='remove-catalog-carrier':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  `D5.S3.ConceptDynamics.InformationEscape.Catalog.Index,'
        replacement=''
        predicted=['CatalogProjectedCarrier']
        description='Remove the declared Catalog.Index representation boundary while retaining concrete carrier and nominal-field checks.'
    elif kind=='remove-bundle-carrier':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  `D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.Index,'
        replacement=''
        predicted=['BundleProjectedCarrier']
        description='Remove the declared PrimitiveBundle.Index representation boundary while retaining receiver data and nominal-field checks.'
    elif kind=='remove-arena-projected-carrier':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='    unless audited do return none'
        replacement='    return none'
        predicted=['ArenaProjectedCarrier','CatalogProjectedCarrier','BundleProjectedCarrier']
        description='Remove the audited rigid arena/signature carrier projection boundary; concrete statement payload rejection remains.'
    elif kind=='nonadmission-trace-edit':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='"incomplete cause=collection_failure operation=collect_readout first={address} site={address}: {ex.toMessageData}"'
        replacement='"incomplete cause=collection_failure operation=collect_readout first={address} site={address} detail={ex.toMessageData}"'
        predicted=[]
        description='Neutral control: edit only a trace string; no inventory or behavior assertion should fail.'
    elif kind=='remove-collection-interfaces':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='if Lean.isClass env name && !listedTypeClasses.contains name then'
        replacement='if Lean.isClass env name && (!listedTypeClasses.contains name || #[`Append, `HAppend, `Union, `Nat.AtLeastTwo].contains name) then'
        predicted=['CollectionAppendHeads','CollectionUnionHead','BoundedNatInterfaceHead']
        description='Remove the observed collection and bounded-natural class interfaces uniformly by inferred class head.'
    elif kind=='remove-statement-let':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='  | .letE _ _ value body _ =>\n    let some body ← substitute body #[value] | return .incomplete\n    let some body ← aliasBody body args | return .incomplete\n    return .next body'
        replacement='  | .letE _ _ _ _ _ => return ← statementUnknown current'
        predicted=['RegisteredLetAlias']
        description='Remove structural let forwarding from the registered-statement alias boundary.'
    elif kind=='asymmetric-equality-boundary':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='for operand in args.extract 1 3 ++ statement.getAppArgs.extract 1 3 do'
        replacement='for operand in args.extract 1 3 do'
        predicted=['RegisteredComputedEquality','RegisteredComputedAlias']
        description='Check only candidate equality operands, allowing a computed registered-statement spelling to escape the boundary.'
    elif kind=='remove-function-interface':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries'
        needle='if Lean.isClass env name && !listedTypeClasses.contains name then'
        replacement='if Lean.isClass env name && (!listedTypeClasses.contains name || #[`DFunLike, `EquivLike].contains name) then'
        predicted=['FunctionInterfaceHead','EquivalenceInterfaceHead']
        description='Remove the function-coercion class interface while leaving receiver and nominal payload checks intact.'
    elif kind=='own-clean-prop-argument':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistRules'
        needle='    let some type ← occurrenceType occurrence | return .incomplete\n    let exact ← exactScalarStatement type'
        replacement='    let some type ← occurrenceType occurrence | return .incomplete\n    let some proof ← boundedMeta (Meta.isProp type) `mutant_prop_clean | return .incomplete\n    if proof then return .allowlisted (witness .proofBoundary type)\n    let exact ← exactScalarStatement type'
        predicted=['ImportedLibraryPrivateProof','IndependentProofConstant','ClosedStatementInhabitant','InlineClosedStatementInhabitant','NominalLiteral']
        description='Classify every Prop-typed argument as allowlisted immediately after bounded inference, bypassing its statement type check. visitOccurrence still erases the proof body; direct application identity check is retained.'
    elif kind=='own-remove-classical-choice':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistRules'
        needle='    if pos == .dataPos && n.getRoot == `Classical then\n      noteUnclassified ⟨"classical_choice", n, namespaceLabel env n, origin⟩'
        replacement='    if false && pos == .dataPos && n.getRoot == `Classical then\n      noteUnclassified ⟨"classical_choice", n, namespaceLabel env n, origin⟩'
        predicted=['ClassicalDirect','TypeBeforeClassicalData','UnclassifiedPayloadParses']
        description='Remove executable Classical namespace rejection; retain the independent unlisted_decision_producer fallback. Predict diagnostic-class assertion reds, not false admission.'
    elif kind=='computed-default-stop':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.Round7ComputedStatement'
        needle='  return .unclassified ⟨"unclassified_statement_head", name,\n    namespaceLabel (← getEnv) name, (← get).theoremName⟩'
        replacement='  return .recognized (witness .statementInductive head)'
        predicted=[name+suffix for suffix in ['', 'Diagnostic'] for name in ['ComputedRegisteredProof','ComputedRegisteredNominalPayload','ComputedRegisteredDecision']]
        description='Treat an unresolved registered statement head as a completed recognized stop, recreating the round-7 default admission.'
    elif kind=='list-nominal-carrier-path':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.SurvivingListBoundaries'
        needle='            if carrierValued ||\n                (concrete.isFVar && !parameter && !auditedFamily) then'
        replacement='            if name != ``List && (carrierValued ||\n                (concrete.isFVar && !parameter && !auditedFamily)) then'
        predicted=[n+'CarrierPath' for n in ['PropositionNodupPayload','LetPropositionNodupPayload','IndexedPropositionNodupPayload','PropositionMemPayload']]
        description='Remove only the nominal List abstract carrier fence; the old metadata fence still rejects, while all four exact diagnostic-path pins fail.'
    elif kind=='list-both-carrier-fences':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AllowlistRules'
        source=source.replace('if carrierEvidence.isSome &&', 'if true &&')
        needle='            if carrierValued ||\n                (concrete.isFVar && !parameter && !auditedFamily) then'
        replacement='            if name != ``List && (carrierValued ||\n                (concrete.isFVar && !parameter && !auditedFamily)) then'
        predicted=['PropositionNodupPayload','LetPropositionNodupPayload']
        description='Remove nominal List abstract-carrier and List metadata carrier fences together; indexed and membership payloads retain independent rejection paths.'
    elif kind=='carrier-default-kind':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.Round7PackedConsumer'
        needle='            if carrierValued ||\n                (concrete.isFVar && !parameter && !auditedFamily) then'
        replacement='            if false && (carrierValued ||\n                (concrete.isFVar && !parameter && !auditedFamily)) then'
        predicted=['PackedCarrierHidden','PackedCarrierOpaqueClean','PackedCarrierHiddenDiagnostic','PackedCarrierOpaqueCleanDiagnostic']
        description='Default-admit nominal carrier-valued and abstract fields by their kind, recreating the round-7 unaudited external carrier boundary.'
    elif kind=='alias-carrier-default-shape':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.AliasSortCarrierBoundaries'
        needle='''    | .defnInfo _ =>
      let value ← Core.instantiateValueLevelParams declaration levels (allowOpaque := false)
      let some body ← aliasBody value args | return none
      if body == concrete then return none
      let some _ ← nominalFieldShape env body parameters | return none
      -- admission-exit: nominalFieldShape.7 rule=fieldAlias
      return some (witness .fieldAlias concrete)'''
        replacement='''    | .defnInfo _ =>
      return some (witness .fieldConcrete concrete)'''
        predicted=['AliasTypeHidden','AliasTypeClean','AliasPropHidden','AliasPropClean','AliasFamilyHidden','AliasFamilyClean']
        description='Treat an explicit nominal field type alias as an ordinary concrete shape without following its body. The six opaque carrier-slot fixtures must be admitted incorrectly; ordinary and proof aliases stay admitted.'
    elif kind=='nested-default-apart':
        TARGET='LeanInformationAudit.Tests.RegistrationGates.NestedStatementIdentity'
        needle='private def checkedStatementType (env : Environment) (type : Expr) :\n    WalkM (Option ProvenanceAdmissionWitness) := do'
        replacement=needle+'\n  return some (witness .statementRigidApart type)'
        predicted=['QuantifiedComputedIdentity','QuantifiedAliasIdentity','ConjoinedComputedIdentity','DisjoinedComputedIdentity','ExistentialComputedIdentity']
        description='Default-admit every observed proposition at the checkedStatementType witness exit, bypassing positive statement distinction.'
    else:raise ValueError(label)
    overrides={
      'drop-list-carrier-fence':[],
      'computed-default-stop':[n+'HeadNamed' for n in ['ComputedRegisteredProof','ComputedRegisteredNominalPayload','ComputedRegisteredDecision']],
      'resume-proof-implementations':['InternalTargetProofErased','InternalCompanionProofErased','ProofArgumentBoundary','AlternativeProofBoundary','ProofFieldBoundary','ErasedPredicateBoundary','BoundedNatInterfaceHead','ProofImplementationInvariance'],
      'remove-algebra-families':['UniformMonoidHeads','UniformRingHeads','UniformOrderHeads','UniformFieldHeads','UniformCommutativeRingHeads','FunctionInterfaceHead'],
      'remove-named-carrier-alias':['ArenaProjectedCarrier','CatalogProjectedCarrier','BundleProjectedCarrier','NestedScalarCarrier','FiniteFunctionRange'],
      'remove-statement-projection':['SubsetMetadataBoundary','ProjectedStatementClean'],
      'remove-statement-let':['RegisteredLetClean']}
    predicted=overrides.get(kind,predicted)
    return TARGET, source, needle, replacement, predicted, description
