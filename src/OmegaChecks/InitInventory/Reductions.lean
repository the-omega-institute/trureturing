module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.EffectObservations
import all OmegaChecks.InitInventory.EffectObservations
meta import OmegaChecks.InitInventory.EffectObservations
public import OmegaChecks.InitInventory.ArrayCasts
import all OmegaChecks.InitInventory.ArrayCasts
meta import OmegaChecks.InitInventory.ArrayCasts
public import OmegaChecks.InitInventory.PointerObservations
import all OmegaChecks.InitInventory.PointerObservations
meta import OmegaChecks.InitInventory.PointerObservations
public import OmegaChecks.InitInventory.Quotient
import all OmegaChecks.InitInventory.Quotient
meta import OmegaChecks.InitInventory.Quotient
public import OmegaChecks.InitInventory.TransformerLaws
import all OmegaChecks.InitInventory.TransformerLaws
meta import OmegaChecks.InitInventory.TransformerLaws
public import OmegaChecks.InitInventory.EnvelopeOrder
import all OmegaChecks.InitInventory.EnvelopeOrder
meta import OmegaChecks.InitInventory.EnvelopeOrder
public import OmegaChecks.InitInventory.Extensionality
import all OmegaChecks.InitInventory.Extensionality
meta import OmegaChecks.InitInventory.Extensionality
public import OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.Logic
meta import OmegaChecks.InitInventory.Logic
public import OmegaChecks.InitInventory.OrderedAlgebra
import all OmegaChecks.InitInventory.OrderedAlgebra
meta import OmegaChecks.InitInventory.OrderedAlgebra
public import OmegaChecks.InitInventory.Order
import all OmegaChecks.InitInventory.Order
meta import OmegaChecks.InitInventory.Order

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

/-- Physical public definition sites with a checked reduction from the original type.
The target universe parameters are a suffix of the witness parameters. -/
def reductions : List (Name × Name × Name × Name) := [
  (`Init.Classical, `Classical.choose, `Classical.choice, ``choiceFromChoose),
  (`Init.Classical, `Exists.choose, `Classical.choice, ``choiceFromExistsChoose),
  (`Init.Classical, `Classical.epsilon, `Classical.choice, ``choiceFromEpsilon),
  (`Init.Classical, `Classical.indefiniteDescription, `Classical.choice, ``choiceFromDescription),
  (`Init.Classical, `Classical.inhabited_of_nonempty, `Classical.choice, ``choiceFromInhabited),
  (`Init.Classical, `Classical.inhabited_of_exists, `Classical.choice, ``choiceFromInhabitedOfExists),
  (`Init.Classical, `Classical.strongIndefiniteDescription, `Classical.choice, ``choiceFromStrongDescription),
  (`Init.Classical, `Classical.typeDecidable, `Classical.choice, ``choiceFromTypeDecidable),
  (`Init.Prelude, `Classical.ofNonempty, `Classical.choice, ``choiceFromOfNonempty),
  (`Init.Core, `iff_iff_eq, `propext, ``propextFromIffIffEq),
  (`Init.Core, `eq_iff_iff, `propext, ``propextFromEqIffIff),
  (`Init.Core, `Iff.subst, `propext, ``propextFromIffSubst),
  (`Init.Core, `Eq.propIntro, `propext, ``propextFromPropIntro),
  (`Init.Ext, `propext_iff, `propext, ``propextFromPropextIff),
  (`Init.Classical, `Classical.propComplete, `propext, ``propextFromPropComplete),
  (`Init.PropLemmas, `ite_iff_left_iff, `propext, ``propextFromIteIffLeft),
  (`Init.PropLemmas, `ite_iff_right_iff, `propext, ``propextFromIteIffRight),
  (`Init.PropLemmas, `left_iff_ite_iff, `propext, ``propextFromLeftIffIte),
  (`Init.PropLemmas, `right_iff_ite_iff, `propext, ``propextFromRightIffIte),
  (`Init.Grind.Norm, `Lean.Grind.iff_eq, `propext, ``propextFromGrindIffEq),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix, `Classical.choice, ``choiceFromFix),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix, `Classical.choice, ``choiceFromFix),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix₂, `Classical.choice, ``choiceFromFix₂),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix₂, `Classical.choice, ``choiceFromFix₂),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix₃, `Classical.choice, ``choiceFromFix₃),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix₃, `Classical.choice, ``choiceFromFix₃),
  -- Even the logically opaque loop must return an element when its three inputs are units.
  (`Init.WFExtrinsicFix, `WellFounded.opaqueFix₃, `Classical.choice, ``choiceFromFix₃),
  (`Init.Grind.Injective, `Lean.Grind.leftInv, `Classical.choice, ``choiceFromLeftInv),
  (`Init.While, `repeatM, `Classical.choice, ``choiceFromRepeatM),
  (`Init.Prelude, `unsafeCast, `sorryAx, ``sorryAxFromUnsafeCast)] ++
  (OptionSelector.laws.map fun (owner, name, witness) => (owner, name, ``Classical.choice, witness)) ++
  (InternalOrder.implicationOrders.map fun (name, witness) => (`Init.Internal.Order.Basic, name, ``propext, witness))

/-- Recheck the transitive kernel terms of each witness with all forbidden declarations absent.
Include complete inductive families so that replay can regenerate their primitive rules. -/
private def replayWitnesses (env : Environment) : IO Unit := do
  let official ← importModules #[{module := `Lean}] {} (level := .private)
  let mut terms : Std.HashMap Name ConstantInfo := {}
  let mut todo := (reductions.map fun (_, _, _, witness) => witness) ++
    ClassicalConsequences.witnesses.map Prod.snd ++
    BooleanReflection.witnesses.map (fun row => row.2.2) ++
    IntegerCancellation.witnesses.map (fun row => row.2.2) ++
    WeakRingOrder.witnesses.map (fun row => row.2.2) ++
    [``TransformerLaws.FiniteFold.funextOfMoveUnit, ``TransformerLaws.FiniteFold.funextOfRepeatUnit] ++
    [``EnvelopeOrder.propextFromRingLift, ``EnvelopeOrder.propextFromModuleLift,
      ``EnvelopeOrder.ringDiagonal, ``EnvelopeOrder.moduleDiagonal,
      ``EnvelopeOrder.propextFromRingOrder, ``EnvelopeOrder.propextFromModuleOrder] ++
    [``Envelope.funextFromCancellation, ``Envelope.funextFromEnvelopeRing,
      ``Envelope.funextFromEnvelopeCommRing, ``Envelope.funextFromEnvelopeIntModule] ++
    [``EffectObservations.base, ``EffectObservations.eio, ``EffectObservations.io,
      ``ArrayCasts.map, ``ArrayCasts.mapIndexed,
      ``PointerObservations.address, ``PointerObservations.pointerEquality, ``PointerObservations.listPointerEquality,
      ``PointerObservations.objectPointerEquality, ``PointerObservations.objectPointerHash] ++
    [``HeterogeneousQuotient.hrecOn, ``HeterogeneousQuotient.hrecOnSetoid,
     ``HeterogeneousQuotient.soundOfPairCoherence, ``HeterogeneousQuotient.setoidSoundOfPairCoherence] ++
    [``ConstructorNormalization.propextOfDecision, ``ConstructorNormalization.addCancelOfSucc,
     ``ConstructorNormalization.prefixEqualityOfCons] ++
    [``EmbeddingRange.ofExists, ``EmbeddingRange.ofLeftInverse,
      ``LexicographicOrder.ofListNotLE, ``LexicographicOrder.ofArrayNotLE, ``LexicographicOrder.ofVectorNotLE,
      ``FiniteMembership.ofRunDecomposition, ``FiniteMembership.ofRunInduction,
      ``FiniteMembership.ofListMember, ``FiniteMembership.ofArrayMember,
      ``FiniteMembership.ofFirstListMember, ``FiniteMembership.ofFirstArrayMember,
      ``FiniteMembership.ofVectorMember, ``FiniteMembership.ofFirstVectorMember,
      ``choiceFromOptionPresence, ``VectorExistence.emOfVectorSucc, ``dneFromClosedRange, ``dneFromOpenRange, ``excludedMiddleFromDNE, ``excludedMiddleOfNotLT,
      ``excludedMiddleOfNotLTIff, ``GrindOrder.excludedMiddleFromComparison, ``GrindOrder.excludedMiddleFromImplication,
      ``GrindOrder.excludedMiddleFromNotNot, ``GrindOrder.excludedMiddleFromLookahead,
      ``AbstractOrder.excludedMiddleOfTrichotomy, ``AbstractOrder.excludedMiddleOfLTTrichotomy,
      ``AbstractOrder.excludedMiddleOfTrichotomousTotal, ``AbstractOrder.excludedMiddleOfNegationTotal,
      ``InternalOrder.familyChoiceOfStateBottom, ``InternalOrder.limitedOmniscienceOfSearch,
      ``InternalOrder.funextOfCompletePointwiseOrder, ``InternalOrder.funextOfChainCompletePointwiseOrder,
      ``InternalOrder.funextOfPointwiseOrder, ``InternalOrder.propextOfImplicationOrder,
      ``InternalOrder.propextOfReverseImplicationOrder, ``InternalOrder.excludedMiddleOfFlatSuprema,
      ``InternalOrder.excludedMiddleOfOptionCCPO, ``InternalOrder.excludedMiddleOfFlatCCPO,
      ``InternalOrder.excludedMiddleOfFlatCSup,
      ``InternalOrder.uniqueChoiceOfLfp, ``InternalOrder.uniqueChoiceOfMonotoneLfp,
      ``InternalOrder.uniqueChoiceOfFix, ``InternalOrder.uniqueChoiceOfProdSup,
      ``InternalOrder.uniqueChoiceOfProdCSup, ``InternalOrder.uniqueChoiceOfFunSup,
      ``InternalOrder.uniqueChoiceOfBot, ``InternalOrder.uniqueChoiceOfChainSup, ``InternalOrder.uniqueChoiceOfSup,
      ``AbstractOrder.excludedMiddleOfLawfulLT, ``AbstractOrder.weakMiddleOfTotalNot,
      ``AbstractOrder.weakMiddleOfLinearPreorder, ``AbstractOrder.weakMiddleOfLinearOrder,
      ``inhabitedPropExtOfProofHEq, ``inhabitedPropExtOfEqTrue,
      ``inhabitedPropExtOfDecision, ``refutedPropExtOfDecision, ``inhabitedPropExtOfEqTrueRule,
      ``refutedPropExtOfEqFalseRule, ``OptionalIndex.decidablePropExtOfIte,
      ``IntegerCancellation.eqVar, ``IntegerCancellation.eqNorm, ``IntegerCancellation.leNorm,
      ``IntegerCancellation.eqCoeff, ``IntegerCancellation.leCoeff,
      ``NaturalCancellation.exprEq, ``NaturalCancellation.exprLe, ``NaturalCancellation.exprLt,
      ``NaturalCancellation.exprNormEq, ``NaturalCancellation.exprNorm, ``NaturalCancellation.polyEq,
      ``NaturalCancellation.polyLe,
      ``OptionalIndex.decidablePropExtOfIsSome, ``TwoWorlds.countermodel]
  while let n :: more := todo do
    todo := more
    if terms.contains n then continue
    let some ci := (official.find? n).orElse fun _ => env.find? n
      | throw <| IO.userError s!"missing witness dependency {n}"
    if let .quotInfo _ := ci then
      -- Replay regenerates the four native primitives from the kernel quotient declaration.
      -- Quot.sound is a separate axiom and still fails the following check.
      unless [`Quot, `Quot.mk, `Quot.ind, `Quot.lift].contains n &&
          official.getModuleIdxFor? n == official.getModuleIdx? `Init.Prelude do
        throw <| IO.userError s!"unexpected quotient primitive in a boundary witness: {n}"
    if ci.isAxiom || ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"forbidden dependency in a boundary witness: {n}"
    terms := terms.insert n ci
    todo := ci.getUsedConstantsAsSet.toList ++ todo
    if let .inductInfo ind := ci then todo := ind.all ++ todo
    if let .ctorInfo ctor := ci then todo := ctor.induct :: todo
  discard <| (← mkEmptyEnvironment).toKernelEnv.replay terms

/-- Construct the law-to-axiom type with the public selector left arbitrary. -/
private def optionLawReductionType (source target : ConstantInfo) (levels : List Level) :
    MetaM Expr := do
  let selector ← getConstInfo ``Option.choice
  unless levels.length == 1 && source.numLevelParams == 1 && selector.numLevelParams == 1 do
    throwError "unexpected universe arity for {source.name}"
  let siteType := source.type.instantiateLevelParams source.levelParams levels
  let selectorConst := mkConst selector.name levels
  unless siteType.find? (· == selectorConst) |>.isSome do
    throwError "missing selector in {source.name}"
  Meta.withLocalDeclD `select (selector.type.instantiateLevelParams selector.levelParams levels) fun select => do
    let law := siteType.replace fun e => if e == selectorConst then some select else none
    let conclusion := target.type.instantiateLevelParams target.levelParams levels
    Meta.mkForallFVars #[select] (.forallE .anonymous law conclusion .default)

/-- Read the order relation from both instances. The premise requires every
official comparison to hold for the proposed port, including both directions
of comparison whenever the two propositions are equivalent. -/
private def orderReductionType (source target : ConstantInfo) : MetaM Expr := do
  let relation (inst p q : Expr) : MetaM Expr := do
    let order ← if source.type.isAppOf ``Order.CompleteLattice then
      Meta.mkAppOptM ``Order.CompleteLattice.toPartialOrder #[none, some inst]
    else pure inst
    Meta.mkAppOptM ``Order.PartialOrder.rel #[none, some order, some p, some q]
  Meta.withLocalDeclD `port source.type fun port =>
    Meta.withLocalDeclD `p (.sort .zero) fun p =>
      Meta.withLocalDeclD `q (.sort .zero) fun q => do
        let admission ← mkArrow (← relation (mkConst source.name) p q) (← relation port p q)
        let allComparisons ← Meta.mkForallFVars #[p, q] admission
        Meta.mkForallFVars #[port] (← mkArrow allComparisons target.type)

run_cmd
  let env ← getEnv
  let mut seen := Std.HashSet.emptyWithCapacity
  for (owner, name, axiomName, witness) in reductions do
    unless !seen.contains (owner, name) do throwError "duplicate axiom reduction for {owner}/{name}"
    seen := seen.insert (owner, name)
    let some idx := env.getModuleIdx? owner | throwError "missing module {owner}"
    let some source := env.header.moduleData[idx]!.constants.find? (·.name == name)
      | throwError "missing definition site {owner}/{name}"
    -- Several compiler axioms have constructively inhabited types (e.g. lcAny : Type).
    -- A reduction to one of those cannot exclude a source declaration.
    unless [`Classical.choice, `propext, `sorryAx].contains axiomName do
      throwError "unsupported impossibility target {axiomName} for {owner}/{name}"
    let proof ← getConstInfo witness
    let target ← getConstInfo axiomName
    let levels := proof.levelParams.map Level.param
    let targetLevels := levels.drop (levels.length - target.numLevelParams)
    let expected ← if OptionSelector.usesSelector owner name then
      Elab.Command.liftCoreM <| Meta.MetaM.run' <| optionLawReductionType source target levels
    else if owner == `Init.Internal.Order.Basic && InternalOrder.implicationOrders.lookup name == some witness then
      Elab.Command.liftCoreM <| Meta.MetaM.run' <| orderReductionType source target
    else do
      -- The source may be specialized to a particular universe tuple when constructing the axiom.
      let .forallE _ input _ _ := proof.type | throwError "missing argument of {witness}"
      let sourceLevels ← Elab.Command.liftCoreM <| Meta.MetaM.run' do
        let fresh ← Meta.mkFreshLevelMVarsFor source
        unless ← Meta.isDefEq input (source.type.instantiateLevelParams source.levelParams fresh) do
          throwError "incorrect source type in {witness}"
        let found ← fresh.mapM instantiateLevelMVars
        if found.any Level.hasMVar then throwError "unresolved source universe in {witness}"
        return found
      pure <| Expr.forallE .anonymous (source.type.instantiateLevelParams source.levelParams sourceLevels)
        (target.type.instantiateLevelParams target.levelParams targetLevels) .default
    unless target.isAxiom && target.numLevelParams == targetLevels.length &&
        !proof.isUnsafe && !proof.isPartial && (proof.value? (allowOpaque := true)).isSome &&
        Kernel.isDefEqGuarded env {} proof.type expected && (← collectAxioms witness).isEmpty do
      throwError "invalid axiom reduction for {owner}/{name}"
  replayWitnesses env

end OmegaChecks.InitBoundaries
