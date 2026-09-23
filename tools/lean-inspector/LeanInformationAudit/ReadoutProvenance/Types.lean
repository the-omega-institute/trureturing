import LeanInformationAudit.ReadoutProvenance.Carriers
namespace LeanInformationAudit.RegistrationGates
open Lean

mutual
-- Compare a complete observed proof type, including the type of a nominal
-- proof field. A quantified proof's open mathematical body is not another
-- observed proof value; closed statement subtypes still pass the same guard.
partial def observedType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM TypeClassification := do
  let some kind ← occurrenceType type | return ← unknownType type
  if kind == .sort .zero then
    if ← typeMentions env type then return .statementMention
    unless (← checkedStatementType env type).isSome do
      return ← unknownType type "unresolved_statement_identity"
  -- admission-exit: observedType.1 rule=retained-witness.rule
  return ← inputType env type active

-- One structural fold over inferred types and their type-valued arguments.
-- Nominal fields are native occurrences specialized by constructor-index patterns.
private partial def inputType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM TypeClassification := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return ← unknownType type
  if type.hasLooseBVars || type.hasMVar || type.hasLevelMVar then return ← unknownType type
  if ReadoutFamily.carrierHeads.contains (type.getAppFn.constName?.getD .anonymous) then
    let (decoded, work) := ReadoutFamily.carrier env type (← get).exprFuel
    unless ← chargeTraversal work do return ← unknownType type
    let some decoded := decoded | return ← unknownType type
    if decoded == type then return ← unknownType type
    -- admission-exit: inputType.1 rule=retained-witness.rule
    return ← inputType env decoded active
  let producerAllowed := carrierProducerAllowed env (← get).currentFirst
  -- admission-exit: inputType.2 rule=retained-witness.rule
  if let some cached ← reuseWitness (← get).cleanTypes type then return .allowlisted cached
  -- Closed proposition subtypes can themselves contain statement identity.
  -- Complete occurrence/field types, including open ones, use observedType.
  if closed type then
    let some kind ← occurrenceType type | return ← unknownType type
    if kind == .sort .zero then
      if ← typeMentions env type then return .statementMention
      unless (← checkedStatementType env type).isSome do
        return ← unknownType type "unresolved_statement_identity"
  unless ← chargeTraversal do return ← unknownType type
  let enclosingAssumptions := (← get).assumedFamilyDepth
  let enclosingProducer := (← get).assumedProducer
  modify fun s => { s with assumedFamilyDepth := none, assumedProducer := none }
  let classify : WalkM TypeClassification := do
    -- Recursive occurrences recheck their actual arguments before using an
    -- enclosing-family assumption.
    -- A telescope is already traversed domain by domain by this classifier.
    -- Rescanning each complete suffix with typeMentions would duplicate its
    -- binder reconstruction and comparisons at every level.
    if let .forallE n domain body bi := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) := (← inputType env domain active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return ← unknownType type
        -- admission-exit: inputType.forward.1 rule=retained-witness.rule
        inputType env body active)
      -- admission-exit: inputType.3 rule=telescope
      return ← checkedType .telescope type (exact || decision || dm || bm) (du || bu)
    if let .letE _ domain value body _ := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) := (← inputType env domain active).flags
      let vm ← typeMentions env value
      let some body ← substitute body #[value] | return ← unknownType type
      let (bm, bu) := (← inputType env body active).flags
      -- admission-exit: inputType.4 rule=letType
      return ← checkedType .letType type (exact || decision || dm || vm || bm) (du || bu)
    let mut mentions ← typeMentions env type
    if ← compareCanonical type (← get).decision then mentions := true
    let some reduced ← representationType type | do
      trace[InformationProvenance.check] "failed_type={type}"
      return ← checkedType .nominalFields type mentions true
    mentions := (← typeMentions env reduced) || mentions
    match reduced with
    | .forallE n domain body bi =>
      let (dm, du) := (← inputType env domain active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLocalDecl n bi domain fun x =>
        do
          let some body ← substitute body #[x] | return ← unknownType type
          -- admission-exit: inputType.forward.2 rule=retained-witness.rule
          inputType env body active)
      -- admission-exit: inputType.5 rule=telescope
      return ← checkedType .telescope reduced (mentions || dm || bm) (du || bu)
    | .lam n domain body bi =>
      -- Type-valued lambda expressions are generated by dependent recursors
      -- (for example `Fin.casesOn` motives).  Inspect their domains and bodies
      -- through this same classifier instead of treating the lambda head as
      -- an unknown escape.
      let (dm, du) := (← inputType env domain active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return ← unknownType type
        -- admission-exit: inputType.forward.3 rule=retained-witness.rule
        inputType env body active)
      -- admission-exit: inputType.6 rule=lambdaType
      return ← checkedType .lambdaType reduced (mentions || dm || bm) (du || bu)
    | .letE n domain value body nd =>
      let (dm, du) := (← inputType env domain active).flags
      let (vm, vu) := (← inputType env value active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLetDecl n domain value (fun x => do
        let some body ← substitute body #[x] | return ← unknownType type
        -- admission-exit: inputType.forward.4 rule=retained-witness.rule
        inputType env body active) (nondep := nd))
      -- admission-exit: inputType.7 rule=letType
      return ← checkedType .letType reduced (mentions || dm || vm || bm) (du || vu || bu)
    | .mdata _ body =>
      let (bm, bu) := (← inputType env body active).flags
      -- admission-exit: inputType.8 rule=metadataType
      return ← checkedType .metadataType reduced (mentions || bm) bu
    | _ =>
      -- admission-exit: inputType.9 rule=sortKind
      if reduced.isSort then return ← checkedType .sortKind reduced mentions false
      let some (head, args) ← applicationParts reduced | return ← checkedType .nominalFields type mentions true
      if let .lam .. := head then
        let some body ← aliasBody head args | return ← checkedType .nominalFields type mentions true
        let (bm, bu) := (← inputType env body active).flags
        -- admission-exit: inputType.10 rule=betaType
        return ← checkedType .betaType reduced (mentions || bm) bu
      let mut unclassified := false
      for arg in args do
        if let .const n _ := arg.getAppFn then directConstant env n
        if let .proj n _ _ := arg.getAppFn then directProjection env n
        let some argType ← occurrenceType arg | return ← checkedType .nominalFields type mentions true
        let (tm, tu) := (← inputType env argType active).flags
        mentions := mentions || tm
        unclassified := unclassified || tu
        if let .family result ← typeFamilyArgument env arg argType active then
          let (am, au) := result.flags
          mentions := mentions || am
          unclassified := unclassified || au
      -- A local type-family head is allowed only after its inferred type has
      -- itself passed the funnel.  This keeps local neutral syntax from being
      -- an unknown-tolerant escape hatch.
      if head.isFVar then
        let some neutralType ← occurrenceType reduced | return ← checkedType .nominalFields type mentions true
        let (fm, fu) := (← inputType env neutralType active).flags
        -- admission-exit: inputType.11 rule=scopedParameter
        return ← checkedType .scopedParameter reduced (mentions || fm) (unclassified || fu)
      if let .proj _ _ receiver := head then
        -- Infer both the receiver and projection in the same context. Lean
        -- supplies the receiver's actual parameters, indices and universe.
        let some receiverType ← occurrenceType receiver | return ← checkedType .nominalFields type mentions true
        let (rm, ru) := (← inputType env receiverType active).flags
        let some projectionType ← occurrenceType head | return ← checkedType .auditedProjection type (mentions || rm) true
        let (pm, pu) := (← inputType env projectionType active).flags
        -- admission-exit: inputType.12 rule=auditedProjection
        return ← checkedType .auditedProjection reduced (mentions || rm || pm) (ru || pu || unclassified)
      let .const name _ := head | return ← unknownType reduced
      directProjection env name
      let some declaration := env.find? name | return ← checkedType .nominalFields type mentions true
      unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
      let knownKind ← if declaration.hasValue (allowOpaque := true) then pure none
        else reuseWitness (← get).cleanKinds head
      if !declaration.hasValue (allowOpaque := true) && knownKind.isNone then
        -- The actual head occurrence supplies its inferred kind. This closed
        -- kind is independent of the caller's recursive-family assumptions.
        let some kind ← occurrenceType head | return ← checkedType .nominalFields type mentions true
        let kindVerdict ← inputType env kind #[]
        let (km, ku) := kindVerdict.flags
        mentions := mentions || km
        unclassified := unclassified || ku
        let state ← get
        if !km && !ku && !state.incomplete && !state.forbidden && state.unclassified.isNone then
          unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
          if let some evidence := kindVerdict.witness? then
            modify fun s => { s with cleanKinds := s.cleanKinds.insert (head, evidence.sourceDependency) evidence }
      let some evidence ← statementBoundary | return ← unknownType reduced
      let statement := evidence.matchedType
      let natOrder := fun e =>
        let h := e.getAppFn
        h.isConstOf ``Nat.le || h.isConstOf ``Nat.lt ||
          ((h.isConstOf ``LE.le || h.isConstOf ``LT.lt) &&
            e.getAppArgs[0]?.any (·.isConstOf ``Nat))
      if natOrder reduced && natOrder statement then return ← checkedType .nominalFields type mentions true
      -- Membership of propositions is not a data-carrier boundary. Inspect
      -- the actual receiver carrier even when the interface projection is stuck.
      if name == ``Membership.mem && args.size >= 2 then
        let element := args[0]!
        if element == .sort .zero then return ← checkedType .nominalFields type mentions true
      -- Equality has no independent payload: reflexivity carries only the
      -- operands already checked above. Eliminating an arbitrary equality
      -- would instead ask Lean to solve a theorem (e.g. f x = x).
      if name == ``Eq || name == ``HEq then
        -- Closed computed operands on either side are outside the equality boundary when the
        -- registered statement is an equality. A raw spelling mismatch cannot
        -- certify that a numeric/record alias differs from that statement.
        let inductiveHead := fun e => e.getAppFn.constName?.filter fun n =>
          (env.find? n).any (fun info => match info with | .inductInfo _ => true | _ => false)
        let distinctCarriers := if args.size == 3 && statement.isAppOfArity ``Eq 3 then
          let a := args[0]!
          let b := statement.getAppArgs[0]!
          match inductiveHead a, inductiveHead b with
          | some a, some b => a != b
          | none, some _ => a.isForall || a.isSort
          | some _, none => b.isForall || b.isSort
          | _, _ => false
        else false
        if name == ``Eq && args.size == 3 && statement.isAppOfArity ``Eq 3 && !distinctCarriers then
          for operand in args.extract 1 3 ++ statement.getAppArgs.extract 1 3 do
            let literal := (naturalLiteral operand).isSome
            let nullary := match operand with
              | .const n _ => (env.find? n).any fun info => match info with
                | .ctorInfo ctor => ctor.numFields == 0 && ctor.numParams == 0
                | _ => false
              | _ => false
            if closed operand && !literal && !nullary then
              trace[InformationProvenance.check] "unsupported_equality_operand={repr operand} type={reduced}"
              unclassified := true
        -- admission-exit: inputType.13 rule=equality
        return ← checkedType .equality reduced mentions unclassified
      -- Nat.le has only natural indices and recursive Nat.le premises. Check
      -- the actual operands above; if S is itself an order statement, reject
      -- conservatively so no recursive order subproof can conceal it. This
      -- avoids enumerating numeric representation bounds (UInt32, Char, ...).
      if name == ``Nat.le then
        let some statement ← representationType statement
          | return ← checkedType .nominalFields type mentions true
        let head := statement.getAppFn
        let order := head.isConstOf ``Nat.le || head.isConstOf ``Nat.lt ||
          ((head.isConstOf ``LE.le || head.isConstOf ``LT.lt) &&
            statement.getAppArgs[0]?.any (·.isConstOf ``Nat))
        -- admission-exit: inputType.14 rule=naturalOrder
        return ← checkedType .naturalOrder reduced mentions (unclassified || order)
      -- Membership and uniqueness proofs over checked data carriers contain
      -- only recursive Mem/Pairwise and equality/function proof forms. The
      -- positive statement heads below cannot specialize to those forms.
      if (name == ``List.Pairwise || name == ``List.Mem) && args.size == 3 then
        let some kind ← occurrenceType args[0]! | return ← checkedType .nominalFields type mentions true
        let some (.sort level) ← representationType kind
          | return ← checkedType .nominalFields type mentions true
        let relation := mkApp (mkConst ``Ne [level]) args[0]!
        let some carrier ← namedCarrier env args[0]! | return ← checkedType .nominalFields type mentions true
        let some rigid ← boundedMeta (do
          let carrier ← pure carrier
          let .fvar id := carrier | return false
          return (← id.getDecl).value? (allowNondep := true) |>.isNone) `carrier_rigidity
          | return ← checkedType .nominalFields type mentions true
        -- A rigid parameter is scoped to this occurrence. Applications and
        -- enclosing case substitutions get freshly inferred field types.
        -- admission-exit: inputType.15 rule=rigidCarrier
        let mut carrierEvidence ← if rigid then pure (some (witness .rigidCarrier carrier))
          -- admission-exit: inputType.16 rule=scalarCarrier
          else if carrier.isConstOf ``Nat then pure (some (witness .scalarCarrier carrier))
          else dataCarrier env args[0]!
        if carrierEvidence.isNone && level.isNeverZero then
          let some carrier ← representationType carrier
            | return ← checkedType .nominalFields type mentions true
          if let some (.inductInfo family) := (carrier.getAppFn.constName?.bind env.find?) then
            let nullary := family.numParams == 0 && family.numIndices == 0 &&
              family.ctors.all (fun ctor => match env.find? ctor with
                | some (.ctorInfo info) => info.numFields == 0
                | _ => false)
            if nullary && closed carrier && !carrier.hasLevelMVar then
              unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
              if let some cached := (← get).certifiedNullaryCarriers[carrier]? then
                carrierEvidence := some cached
              else
                let some branches ← caseFields carrier | return ← checkedType .nominalFields type mentions true
                if branches.all (fun (_, _, fields) => fields.isEmpty) then
                  -- admission-exit: inputType.17 rule=nullaryCarrier
                  let evidence := witness .nullaryCarrier carrier
                  carrierEvidence := some evidence
                  unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
                  modify fun s => { s with certifiedNullaryCarriers :=
                    s.certifiedNullaryCarriers.insert carrier evidence }
        let relationAllowed := args[1]! == relation || match args[1]! with
          | .lam _ _ (.lam _ _ body _) _ =>
            body.isAppOfArity ``Ne 3 && body.getAppArgs[1]! == .bvar 1 &&
              body.getAppArgs[2]! == .bvar 0
          | _ => false
        if carrierEvidence.isSome && (name == ``List.Mem || relationAllowed) then
          let some statement ← representationType statement
            | return ← checkedType .nominalFields type mentions true
          let disjoint ← listStatementBoundary env statement
          -- admission-exit: inputType.18 rule=listMetadata
          if disjoint.isSome then return ← checkedType .listMetadata reduced mentions unclassified
        trace[InformationProvenance.check] "unsupported_list_boundary type={reduced} carrier={carrier} allowed={carrierEvidence.isSome} relation={relationAllowed}"
        return ← checkedType .nominalFields type mentions true
      if Lean.isClass env name && !listedTypeClasses.contains name then
        trace[InformationProvenance.check] "unsupported_class={name} type={type}"
        return ← checkedType .nominalFields type mentions true
      -- Quotient carriers and lifted type families expose their relation or
      -- predicate to the same argument classifier; no predicate is a leaf.
      if let some (.quotInfo info) := env.find? name then
        if match info.kind with | .type | .lift => true | _ => false then
          -- admission-exit: inputType.19 rule=quotientType
          return ← checkedType .quotientType reduced mentions unclassified
      if let some (.recInfo recursor) := env.find? name then
        if #[``Bool.rec, ``Nat.rec, ``List.rec, ``Prod.rec, ``Sum.rec, ``Option.rec,
            ``PUnit.rec, ``Fin.rec].contains name then
          -- admission-exit: inputType.20 rule=recursorType
          return ← checkedType .recursorType reduced mentions unclassified
        -- A kernel recursor over one parameter-free, index-free enumeration
        -- has no abstract carrier or proof payload in its constructors. Its
        -- actual motive, branches and major argument were checked above.
        -- This rule classifies output types; registered statement spellings
        -- still reject every recursor in statementStep.
        if recursor.numParams == 0 && recursor.numIndices == 0 &&
            recursor.numMotives == 1 then
          if let [familyName] := recursor.all then
            if let some (.inductInfo family) := env.find? familyName then
              let mut enumeration := family.numParams == 0 && family.numIndices == 0
              for constructor in family.ctors do
                unless ← chargeTraversal do return ← unknownType reduced
                enumeration := enumeration && (env.find? constructor).any fun declaration =>
                  match declaration with
                  | .ctorInfo constructor => constructor.numParams == 0 && constructor.numFields == 0
                  | _ => false
              if enumeration then
                -- admission-exit: inputType.21 rule=enumRecursorType
                return ← checkedType .enumRecursorType reduced mentions unclassified
        trace[InformationProvenance.check] "unclassified_recursor_head={name} type={reduced}"
        return ← unknownType reduced
      if let some (.defnInfo _) := env.find? name then
        -- An explicit type alias forwards its actual parameters. Its raw body
        -- must pass the same structural families; computed data is not evaluated.
        let value ← Core.instantiateValueLevelParams declaration head.constLevels! (allowOpaque := false)
        let some unfolded ← aliasBody value args | return ← checkedType .nominalFields type mentions true
        if unfolded == reduced then return ← checkedType .nominalFields type mentions true
        let (um, uu) := (← inputType env unfolded active).flags
        -- admission-exit: inputType.22 rule=aliasType
        return ← checkedType .aliasType reduced (mentions || um) (unclassified || uu)
      let some (.inductInfo info) := env.find? name | return ← checkedType .nominalFields type mentions true
      for depth in [:active.size] do
        let previous := active[depth]!
        let some (previousHead, previousArgs) ← applicationParts previous | return ← checkedType .nominalFields type mentions true
        unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
        if hash previousHead != hash head then continue
        unless ← chargeExpression previousHead do return ← checkedType .nominalFields type mentions true
        unless ← chargeExpression head do return ← checkedType .nominalFields type mentions true
        if previousHead == head then
          let mut sameParameters := true
          for index in [:info.numParams] do
            unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
            let some a := previousArgs[index]? | return ← checkedType .nominalFields type mentions true
            let some b := args[index]? | return ← checkedType .nominalFields type mentions true
            sameParameters := (a == b) && sameParameters
          let mut coveredIndices := true
          for index in [info.numParams:args.size] do
            unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
            let current := args[index]!
            -- Recursive occurrences with fresh indices share the enclosing
            -- family obligation. Concrete changed indices require fresh cases.
            if current.hasFVar then
              let some normalized ← representationType current | return ← checkedType .nominalFields type mentions true
              if normalized.hasFVar then continue
            let some previous := previousArgs[index]? | return ← checkedType .nominalFields type mentions true
            coveredIndices := (previous == current) && coveredIndices
          if sameParameters && coveredIndices then
            noteFamilyAssumption depth
            -- admission-exit: inputType.23 rule=recursiveFamily
            return ← checkedType .recursiveFamily reduced mentions unclassified
          -- Different parameters are a fresh obligation, as in nested products.
      let some branches ← caseFields reduced | do
        trace[InformationProvenance.check] "unsupported_nominal_fields type={reduced}"
        return ← checkedType .nominalFields type mentions true
      unless ← chargeTraversal (active.size + 1) do return ← checkedType .nominalFields type mentions true
      let nextActive := active.push reduced
      for (lctx, instances, fields) in branches do
        unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
        for field in fields do
          unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
          let (fm, fu) ← (TypeClassification.flags <$> Meta.withLCtx lctx instances do
            let some fieldType ← occurrenceType field | return ← unknownType type
            let some concrete ← representationType fieldType | return ← unknownType fieldType
            -- Constructor fields that introduce a carrier, or hide their value
            -- behind such a carrier, have no concrete representation witness.
            unless ← chargeTraversal args.size do return ← unknownType concrete
            let parameter := args.contains concrete
            -- Predicate slots of these reviewed interfaces are followed at each
            -- actual use. The two project containers require protected imports,
            -- so no value of their type can acquire the external implementation
            -- leaf rule; concrete statement/decision fields remain inspected.
            -- Course-of-values type recursion uses PProd to hold prior types.
            -- This representation is supported only at a protected implementation
            -- or a kernel constructor/recursor with inspected actual arguments.
            -- An opaque external producer of PProd Type still has no witness.
            let auditedProduct := name == ``PProd && producerAllowed
            if auditedProduct then
              modify fun s => { s with assumedProducer := some s.currentFirst }
            let auditedFamily := auditedProduct ||
              (Lean.isClass env name && listedTypeClasses.contains name) ||
              #[`D5.S3.ConceptDynamics.CIRPT.DecidableKernel,
                `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit].contains name ||
              ReadoutFamily.carrierHeads.any fun selector =>
              (env.getProjectionFnInfo? selector).any fun projection =>
                (env.find? projection.ctorName).any fun declaration =>
                  match declaration with
                  | .ctorInfo ctor => ctor.induct == name
                  | _ => false
            let fieldEvidence ← if auditedFamily then do
              -- admission-exit: inputType.field.1 rule=fieldAudited
              pure (some (witness .fieldAudited concrete))
            else nominalFieldShape env concrete (args.extract 0 info.numParams)
            let carrierValued := fieldEvidence.isNone
            if carrierValued ||
                (concrete.isFVar && !parameter && !auditedFamily) then
              trace[InformationProvenance.check] "unclassified_abstract_carrier family={name} field_type={concrete} first={(← get).currentFirst}"
              return ← unknownType concrete "unclassified_abstract_carrier"
            -- admission-exit: inputType.forward.5 rule=retained-witness.rule
            observedType env concrete nextActive)
          mentions := mentions || fm
          unclassified := unclassified || fu
      -- admission-exit: inputType.24 rule=nominalFields
      return ← checkedType .nominalFields reduced mentions unclassified

  let result ← classify
  let producerDependency := (← get).assumedProducer
  let result := bindWitnessSource result producerDependency
  -- Constructor scans introduced in this call have now completed; discharge
  -- their recursive assumptions. A dependency on an enclosing unfinished family
  -- still forbids caching. Independent nested checks can be reused immediately.
  unless ← chargeTraversal do return ← unknownType type
  let unresolved := (← get).assumedFamilyDepth.filter (· < active.size)
  modify fun s => { s with
    assumedFamilyDepth := mergeAssumptions enclosingAssumptions unresolved
    assumedProducer := enclosingProducer.or producerDependency }
  let state ← get
  if let some evidence := result.witness? then
    if unresolved.isNone && !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar &&
        !state.incomplete && !state.forbidden && state.unclassified.isNone then
      unless ← chargeTraversal do return ← unknownType type
      modify fun s => { s with cleanTypes := s.cleanTypes.insert (type, evidence.sourceDependency) evidence }
  -- admission-exit: inputType.25 rule=retained-witness.rule
  return result

-- Probe the inferred telescope first. Only functions ending in Sort supply
-- type families; ordinary data functions keep their term-provenance treatment.
private partial def typeFamilyArgument (env : Environment) (value type : Expr)
    (active : Array Expr) : WalkM FamilyClassification := do
  unless ← chargeTraversal do return .family (← unknownType type)
  -- admission-exit: typeFamilyArgument.1 rule=retained-witness.rule
  if let some cached ← reuseWitness (← get).dataFunctionTypes type then return .data cached
  let canCache := #[value, type].all fun e =>
    !e.hasLooseBVars && !e.hasMVar && !e.hasLevelMVar
  let source := (← get).currentFirst
  let cache := (← get).cleanFamilies
  if let some cached := cache[(value, type, (none : Option Name))]?.orElse fun _ => cache[(value, type, some source)]? then
    modify fun s => { s with
      counters.familyMemoHits := s.counters.familyMemoHits + 1
      assumedProducer := s.assumedProducer.or cached.sourceDependency }
    -- admission-exit: typeFamilyArgument.2 rule=retained-witness.rule
    return .family (.allowlisted cached)
  let enclosing := (← get).assumedFamilyDepth
  let enclosingProducer := (← get).assumedProducer
  modify fun s => { s with assumedFamilyDepth := none, assumedProducer := none }
  let inspect : WalkM FamilyClassification := do
    let some reduced ← representationType type | return .family (← unknownType type)
    match reduced with
    | .forallE n domain body bi =>
      let result ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return .family (← unknownType type)
        unless ← chargeTraversal do return .family (← unknownType type)
        -- admission-exit: typeFamilyArgument.forward.1 rule=retained-witness.rule
        typeFamilyArgument env (mkApp value x) body active
      -- admission-exit: typeFamilyArgument.3 rule=retained-witness.rule
      let .family verdict := result | return result
      let (bm, bu) := verdict.flags
      let (dm, du) := (← inputType env domain active).flags
      -- admission-exit: typeFamilyArgument.4 rule=typeFamily
      return .family (← checkedType .typeFamily value (dm || bm) (du || bu))
    | .sort _ => return .family (← inputType env value active)
    | _ =>
      -- Non-family delegation also requires the positive carrier classification.
      -- A shape outside the type allowlist cannot become data by falling through.
      let verdict ← inputType env reduced active
      match verdict with
      -- admission-exit: typeFamilyArgument.5 rule=retained-witness.rule
      | .allowlisted evidence => return .data evidence
      | _ => return .family verdict
  let result ← inspect
  let state ← get
  let result := match result with
    | .family verdict => .family (bindWitnessSource verdict state.assumedProducer)
    -- admission-exit: typeFamilyArgument.forward.2 rule=retained-witness.rule
    | .data evidence => .data { evidence with sourceDependency := state.assumedProducer }
  modify fun s => { s with
    assumedFamilyDepth := mergeAssumptions enclosing state.assumedFamilyDepth
    assumedProducer := enclosingProducer.or state.assumedProducer }
  -- This fold opens no family frame: every surviving assumption is external.
  match result with
  | .family (.allowlisted evidence) =>
    if canCache && state.assumedFamilyDepth.isNone &&
        !state.incomplete && !state.forbidden && state.unclassified.isNone then
      unless ← chargeTraversal do return .family (← unknownType type)
      modify fun s => { s with cleanFamilies := s.cleanFamilies.insert (value, type, evidence.sourceDependency) evidence }
  | .data evidence =>
    if closed type && state.assumedFamilyDepth.isNone then
      unless ← chargeTraversal do return .family (← unknownType type)
      modify fun s => { s with dataFunctionTypes := s.dataFunctionTypes.insert (type, evidence.sourceDependency) evidence }
  | _ => pure ()
  -- admission-exit: typeFamilyArgument.6 rule=retained-witness.rule
  return result
end

end LeanInformationAudit.RegistrationGates
