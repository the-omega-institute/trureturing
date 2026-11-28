module
public import Lean
import OmegaChecks.InitInventory.Replay
meta import OmegaChecks.InitInventory.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.IteratorMapStep
import all OmegaChecks.InitInventory.IteratorMapStep
public import OmegaChecks.InitInventory.IteratorLoopLift
import all OmegaChecks.InitInventory.IteratorLoopLift
public import OmegaChecks.InitInventory.PostconditionIdentity
import all OmegaChecks.InitInventory.PostconditionIdentity
public import OmegaChecks.InitInventory.ChoiceOperands
import all OmegaChecks.InitInventory.ChoiceOperands
public import OmegaChecks.InitInventory.ErasedSelection
import all OmegaChecks.InitInventory.ErasedSelection
public import OmegaChecks.InitInventory.WhileChoice
import all OmegaChecks.InitInventory.WhileChoice
public import OmegaChecks.InitInventory.Traversal
import all OmegaChecks.InitInventory.Traversal
public import OmegaChecks.InitInventory.MacroReferences
import all OmegaChecks.InitInventory.MacroReferences
meta import OmegaChecks.InitInventory.MacroReferences
public import OmegaChecks.InitInventory.Dynamic
import all OmegaChecks.InitInventory.Dynamic
meta import OmegaChecks.InitInventory.Dynamic
public import OmegaChecks.InitInventory.StateFactory
import all OmegaChecks.InitInventory.StateFactory
meta import OmegaChecks.InitInventory.StateFactory
public import OmegaChecks.InitInventory.ReferenceSelection
import all OmegaChecks.InitInventory.ReferenceSelection
meta import OmegaChecks.InitInventory.ReferenceSelection
public import OmegaChecks.InitInventory.ReferenceRoundTrip
import all OmegaChecks.InitInventory.ReferenceRoundTrip
meta import OmegaChecks.InitInventory.ReferenceRoundTrip
public import OmegaChecks.InitInventory.EffectObservations
import all OmegaChecks.InitInventory.EffectObservations
meta import OmegaChecks.InitInventory.EffectObservations
public import OmegaChecks.InitInventory.ArrayCasts
import all OmegaChecks.InitInventory.ArrayCasts
meta import OmegaChecks.InitInventory.ArrayCasts
public import OmegaChecks.InitInventory.ByteArrayReads
import all OmegaChecks.InitInventory.ByteArrayReads
meta import OmegaChecks.InitInventory.ByteArrayReads
public import OmegaChecks.InitInventory.PointerObservations
import all OmegaChecks.InitInventory.PointerObservations
meta import OmegaChecks.InitInventory.PointerObservations
public import OmegaChecks.InitInventory.Quotient
import all OmegaChecks.InitInventory.Quotient
meta import OmegaChecks.InitInventory.Quotient
public import OmegaChecks.InitInventory.TransformerLaws
import all OmegaChecks.InitInventory.TransformerLaws
meta import OmegaChecks.InitInventory.TransformerLaws
import all OmegaChecks.InitInventory.ReturnImage
meta import OmegaChecks.InitInventory.ReturnImage
public import OmegaChecks.InitInventory.StrictRingOrder
import all OmegaChecks.InitInventory.StrictRingOrder
meta import OmegaChecks.InitInventory.StrictRingOrder
public import OmegaChecks.InitInventory.EnvelopeOrder
import all OmegaChecks.InitInventory.EnvelopeOrder
meta import OmegaChecks.InitInventory.EnvelopeOrder
public import OmegaChecks.InitInventory.SumFunctions
import all OmegaChecks.InitInventory.SumFunctions
meta import OmegaChecks.InitInventory.SumFunctions
public import OmegaChecks.InitInventory.Extensionality
import all OmegaChecks.InitInventory.Extensionality
meta import OmegaChecks.InitInventory.Extensionality
public import OmegaChecks.InitInventory.EqualityNormalization
import all OmegaChecks.InitInventory.EqualityNormalization
meta import OmegaChecks.InitInventory.EqualityNormalization
public import OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.Logic
meta import OmegaChecks.InitInventory.Logic
public import OmegaChecks.InitInventory.OrderedAlgebra
import all OmegaChecks.InitInventory.OrderedAlgebra
meta import OmegaChecks.InitInventory.OrderedAlgebra
import all OmegaChecks.InitInventory.KripkeModels
public import OmegaChecks.InitInventory.Order
import all OmegaChecks.InitInventory.Order
meta import OmegaChecks.InitInventory.Order
import all OmegaChecks.InitInventory.RangeSize
meta import OmegaChecks.InitInventory.RangeSize
import all OmegaChecks.InitInventory.AbstractOrder
meta import OmegaChecks.InitInventory.AbstractOrder

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

/-- Physical public definition sites with a checked reduction from the original type.
The target universe parameters are a suffix of the witness parameters. -/
def reductions : List (Name × Name × Name × Name) := [
  (`Init.Core, `Quot.indepCoherent, `Quot.sound, ``HeterogeneousQuotient.soundFromUnitCoherence),
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
  (`Init.Core, `instDecidableEqOfIff, `propext, ``ConstructorNormalization.propextOfDecision),
  (`Init.Data.Option.Lemmas, `Option.choice, `Classical.choice, ``OptionSelector.fromSome),
  (`Init.Ext, `propext_iff, `propext, ``propextFromPropextIff),
  (`Init.Classical, `Classical.propComplete, `propext, ``propextFromPropComplete),
  (`Init.PropLemmas, `ite_iff_left_iff, `propext, ``propextFromIteIffLeft),
  (`Init.PropLemmas, `ite_iff_right_iff, `propext, ``propextFromIteIffRight),
  (`Init.PropLemmas, `left_iff_ite_iff, `propext, ``propextFromLeftIffIte),
  (`Init.PropLemmas, `right_iff_ite_iff, `propext, ``propextFromRightIffIte),
  (`Init.Grind.Ring.CommSolver, `Lean.Grind.CommRing.lt_norm_expr, `propext, ``StrictRingOrder.propextFromLT),
  (`Init.Grind.Ring.CommSolver, `Lean.Grind.CommRing.lt_norm_expr_nc, `propext, ``StrictRingOrder.propextFromLTNC),
  (`Init.Grind.Ring.CommSolver, `Lean.Grind.CommRing.le_norm_expr, `propext, ``EnvelopeOrder.propextFromLeNorm),
  (`Init.Grind.Ring.CommSolver, `Lean.Grind.CommRing.le_norm_expr_nc, `propext, ``EnvelopeOrder.propextFromLeNormNC),
  (`Init.Grind.Norm, `Lean.Grind.iff_eq, `propext, ``propextFromGrindIffEq),
  (`Init.Grind.Norm, `Lean.Grind.not_eq_prop, `propext, ``propextFromNotEqProp),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix, `Classical.choice, ``choiceFromFix),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix, `Classical.choice, ``choiceFromFix),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix₂, `Classical.choice, ``choiceFromFix₂),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix₂, `Classical.choice, ``choiceFromFix₂),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix₃, `Classical.choice, ``choiceFromFix₃),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix₃, `Classical.choice, ``choiceFromFix₃),
  -- Even the logically opaque loop must return an element when its three inputs are units.
  (`Init.WFExtrinsicFix, `WellFounded.opaqueFix₃, `Classical.choice, ``choiceFromFix₃),
  (`Init.Internal.Order.Basic, `Lean.Order.flat_csup, `Classical.choice, ``InternalOrder.choiceFromFlatPresence),
  (`Init.Grind.Injective, `Lean.Grind.leftInv, `Classical.choice, ``choiceFromLeftInv),
  (`Init.While, `repeatM, `Classical.choice, ``choiceFromRepeatM),
  (`Init.While, `Lean.Loop.forIn, `Classical.choice, ``WhileChoice.choiceFromLoop),
  (`Init.While, `Lean.instForInLoopUnitOfMonad, `Classical.choice, ``WhileChoice.choiceFromInstance),
  (`Init.Prelude, `unsafeCast, `sorryAx, ``sorryAxFromUnsafeCast)] ++
  (OptionSelector.laws.map fun (owner, name, witness) => (owner, name, ``Classical.choice, witness)) ++
  (InternalOrder.implicationOrders.map fun (name, witness) => (`Init.Internal.Order.Basic, name, ``propext, witness))

/-- Recheck the transitive kernel terms of each witness with all forbidden declarations absent.
Include complete inductive families so that replay can regenerate their primitive rules. -/
private def replayWitnesses (env : Environment) : IO Unit := do
  let official ← importModules #[{module := `Lean}] {} (level := .private)
  let roots := (reductions.map fun (_, _, _, witness) => witness) ++
    [``MeasuredRecursion.goCongrOfRespectsCalls, ``MeasuredRecursion.fixEqOfRespectsCalls] ++
    ClassicalConsequences.witnesses.map Prod.snd ++ [``ClassicalConsequences.ofTypeDecidableEq] ++
    [``MacroReferences.noQueryRoundTrip, ``MacroReferences.noRoundTrip] ++
    [``DynamicRoundTrip.noRoundTrip, ``FactoryCarriers.noCarrierEmbedding, ``FactoryCarriers.noGetCast] ++
    [``PropositionalChoice.ofChoice, ``PropositionalChoice.ofSkolem, ``PropositionalChoice.ofProducts,
      ``PropositionalChoice.choiceIffSkolem, ``PropositionalChoice.choiceIffProducts,
      ``PropositionalChoice.choiceIntoProp, ``PropositionalChoice.skolemIntoProp, ``PropositionalChoice.productsIntoProp,
     ``OptionSelector.decideFromSingleton, ``OptionSelector.decideFromDefault] ++
    ReferenceSelection.witnesses.map (fun row => row.2.2) ++
    [``ReferenceRoundTrip.alloc, ``ReferenceRoundTrip.primAlloc, ``ReferenceRoundTrip.set, ``ReferenceRoundTrip.primSet,
     ``ReferenceRoundTrip.modify, ``ReferenceRoundTrip.primModify] ++
    NaturalComparison.equivalences.map (fun row => row.2.2) ++
    NaturalCastComparison.equivalences.map (fun row => row.2.2) ++
    BooleanReflection.witnesses.map (fun row => row.2.2) ++
    [``BooleanReflection.successfulBitRead, ``BooleanReflection.extractSingleBit] ++
    [``GrindNormalization.normalizePositive, ``GrindNormalization.normalizeNegative,
      ``GrindNormalization.normalizePositiveLeft, ``GrindNormalization.normalizePositiveRight,
      ``GrindNormalization.completeIff, ``GrindNormalization.propextOfLookaheadAndNegative,
      ``GrindNormalization.crossedCongruences] ++
    [``BooleanReflection.trueComparisons, ``BooleanReflection.falseComparisons,
      ``BooleanReflection.ratLETrueIff, ``BooleanReflection.ratLEFalseIff] ++
    InternalOrder.decisionChains.map Prod.snd ++ InternalOrder.tailDecisionChains.map Prod.snd ++
    OrderTags.equivalences.map (fun row => row.2.2) ++ [``OrderTags.propextFromOrderRules] ++
    [``RangeSize.emOfClosed, ``RangeSize.emOfOpen, ``RangeSize.closedOfEM, ``RangeSize.openOfEM] ++
    linearCertificates.map (fun (_, _, _, proof) => proof) ++
    IntegerCancellation.witnesses.map (fun row => row.2.2) ++
    WeakRingOrder.witnesses.map (fun row => row.2.2) ++
    [``MonadicTraversal.IndexedMap.singleton, ``MonadicTraversal.IndexedMap.fromList, ``MonadicTraversal.IndexedMap.fromArray] ++
    [``MonadicTraversal.SingletonSearch.boolOfSingleton, ``MonadicTraversal.SingletonSearch.optionOfSingleton] ++
    MonadicCollectionEquations.comparisons.map (fun row => row.2.2) ++
    [``PublicAlgorithmEquations.ofLength, ``PublicAlgorithmEquations.ofClassifier,
     ``PublicAlgorithmEquations.ofReplicate, ``PublicAlgorithmEquations.ofMap,
     ``PublicAlgorithmEquations.ofAppend, ``PublicAlgorithmEquations.ofByteCopy] ++
    [``MonadicTraversal.fromListFoldl, ``MonadicTraversal.fromListFoldr, ``ArrayLoopCongruence.listForInCongr] ++
    [``funextFromFunextIff, ``PostconditionIdentity.rightIdentity, ``PostconditionIdentity.leftIdentity, ``PostconditionIdentity.ofMonad] ++
    [``IteratorStepLift.funextOfMap, ``IteratorStepLift.funextOfMapM,
     ``IteratorStepLift.funextOfFilter, ``IteratorStepLift.funextOfFilterM] ++
    [``IteratorLoopLift.funextOfForIn, ``IteratorLoopLift.funextOfForIn', ``IteratorLoopLift.funextOfFold] ++
    [``PostconditionIdentity.pureImage, ``PostconditionIdentity.imageBind, ``PostconditionIdentity.associatedPredicates] ++
    [``ErasedSelection.ofLeft, ``ErasedSelection.ofRight, ``ErasedSelection.outOfSelection,
     ``ErasedSelection.recoverOfSelection, ``ErasedSelection.leftIffRight, ``ErasedSelection.recoverProp,
     ``ErasedSelection.outInjIffConstructors, ``ErasedSelection.outInjIffLaw] ++
    [``ChoiceOperands.fromChoice, ``ExistentialConjunction.ofRule] ++
    [``SubsingletonState.ofState, ``SubsingletonState.iffState] ++
    [``QuotientFibers.unaryOfLift, ``QuotientFibers.unaryOfSetoidLift,
      ``QuotientFibers.binaryOfUnaries, ``QuotientFibers.unaryIffBinary,
      ``QuotientFibers.liftFromProp, ``QuotientFibers.liftToProp,
      ``QuotientFibers.unaryOfSelection, ``QuotientFibers.setoidLiftOfSelection_mk] ++
    SumFunctions.consequences.map (fun row => row.2.2) ++
    [``SumFunctions.etaIffBranches, ``SumFunctions.etaOfComposition, ``SumFunctions.compositionOfEta,
      ``SumFunctions.identityOfEta, ``SumFunctions.constantsOfComposition, ``SumFunctions.swapIffIdentity] ++
    TransformerLaws.OptionIteration.directConsequences.map (fun row => row.2.2) ++
    TransformerLaws.OptionIteration.constructions ++
    [``TransformerLaws.MapAfterBind.funextFromMapBind, ``TransformerLaws.MapAfterBind.funextFromStateRunSeq,
     ``TransformerLaws.MapAfterBind.funextFromExceptLiftBind, ``TransformerLaws.MapAfterBind.funextFromExceptLift,
     ``TransformerLaws.MapAfterBind.funextFromScanlCons] ++
    TransformerLaws.ReturnImage.equivalences.map (fun row => row.2.2) ++
    [``TransformerLaws.FiniteFold.funextOfMoveUnit, ``TransformerLaws.FiniteFold.funextOfRepeatUnit] ++
    [``EnvelopeOrder.propextFromRingLift, ``EnvelopeOrder.propextFromModuleLift,
      ``EnvelopeOrder.ringDiagonal, ``EnvelopeOrder.moduleDiagonal,
      ``EnvelopeOrder.propextFromRingOrder, ``EnvelopeOrder.propextFromModuleOrder] ++
    [``Envelope.funextFromCancellation, ``Envelope.funextFromEnvelopeRing,
      ``Envelope.funextFromEnvelopeCommRing, ``Envelope.funextFromEnvelopeIntModule] ++
    [``PointerObservations.exclusivity, ``EffectObservations.base, ``EffectObservations.eio, ``EffectObservations.io,
      ``ArrayCasts.map, ``ArrayCasts.mapIndexed, ``ByteArrayReads.noForInBound, ``ByteArrayReads.noFoldBranchBound,
      ``PointerObservations.address, ``PointerObservations.pointerEquality, ``PointerObservations.listPointerEquality,
      ``PointerObservations.guardedPointerEquality, ``PointerObservations.objectPointerEquality, ``PointerObservations.objectPointerHash,
      ``PointerObservations.packedPayloadEquality, ``PointerObservations.packedPayloadHash] ++
    [``HeterogeneousQuotient.hrecOn, ``HeterogeneousQuotient.hrecOnSetoid,
     ``HeterogeneousQuotient.soundOfPairCoherence, ``HeterogeneousQuotient.setoidSoundOfPairCoherence,
     ``HeterogeneousQuotient.firstOfCoherence, ``QuotientDecision.ofSound,
     ``QuotientDecision.exactOfDecidable, ``QuotientDecision.decisionsOnRepresentatives,
     ``QuotientDecision.soundFromAgreement, ``QuotientDecision.funextOfPositiveDecision] ++
    [``ClassicalOrderDecisions.fromLawfulBEq, ``ClassicalOrderDecisions.fromLawfulOrd] ++
    ContainerEquality.witnesses.map (fun row => row.2.2) ++
    [``ConstructorNormalization.propextOfDecision, ``ConstructorNormalization.addCancelOfSucc,
     ``ConstructorNormalization.prefixEqualityOfCons] ++
    [``EmbeddingRange.ofExists, ``EmbeddingRange.ofLeftInverse, ``EmbeddingRange.existsIff, ``EmbeddingRange.leftInverseIff,
      ``LexicographicOrder.ofListNotLE, ``LexicographicOrder.ofArrayNotLE, ``LexicographicOrder.ofVectorNotLE,
      ``FiniteMembership.firstListMemberIffEqualityCases, ``FiniteMembership.runDecompositionIffEqualityCases,
      ``FiniteMembership.runInductionIffEqualityCases, ``FiniteMembership.ofRunDecomposition, ``FiniteMembership.ofRunInduction,
      ``FiniteMembership.ofListMember, ``FiniteMembership.ofArrayMember,
      ``FiniteMembership.ofFirstListMember, ``FiniteMembership.ofFirstArrayMember,
      ``FiniteMembership.ofVectorMember, ``FiniteMembership.ofFirstVectorMember,
      ``choiceFromOptionPresence, ``VectorExistence.emOfVectorSucc, ``VectorExistence.nonemptyDeciderIffExcludedMiddle,
      ``dneFromClosedRange, ``dneFromOpenRange, ``excludedMiddleFromDNE, ``excludedMiddleOfNotLT,
      ``excludedMiddleOfNotLTIff, ``GrindOrder.excludedMiddleFromComparison, ``GrindOrder.excludedMiddleFromImplication,
      ``GrindOrder.excludedMiddleFromNotNot, ``GrindOrder.excludedMiddleFromLookahead,
      ``AbstractOrder.excludedMiddleOfTrichotomy, ``AbstractOrder.excludedMiddleOfLTTrichotomy,
      ``AbstractOrder.excludedMiddleOfTrichotomousTotal, ``AbstractOrder.excludedMiddleOfNegationTotal,
      ``InternalOrder.familyChoiceOfSTBottom, ``InternalOrder.familyChoiceOfStateBottom, ``InternalOrder.limitedOmniscienceOfSearch,
      ``InternalOrder.funextOfCompletePointwiseOrder, ``InternalOrder.funextOfChainCompletePointwiseOrder,
      ``InternalOrder.funextOfReaderOrder, ``InternalOrder.funextOfStateOrder,
      ``InternalOrder.funextOfPointwiseOrder, ``InternalOrder.propextOfImplicationOrder,
      ``InternalOrder.propextOfReverseImplicationOrder, ``InternalOrder.excludedMiddleOfFlatSuprema,
      ``InternalOrder.FlatSelection.smallChainSelections, ``InternalOrder.excludedMiddleOfFlatCSup, ``InternalOrder.flatCCPOIffEM, ``InternalOrder.optionCCPOIffEM,
      ``InternalOrder.uniqueSelectionOfCompletePi, ``InternalOrder.uniqueSelectionOfChainCompletePi,
      ``InternalOrder.latticeSupIffUniqueChoice, ``InternalOrder.chainSupIffUniqueChoice,
      ``InternalOrder.latticeSupOfUniqueChoice_spec, ``InternalOrder.chainSupOfUniqueChoice_spec,
      ``InternalOrder.uniqueChoiceOfLfp, ``InternalOrder.uniqueChoiceOfMonotoneLfp,
      ``InternalOrder.uniqueChoiceOfFix, ``InternalOrder.uniqueChoiceOfProdSup,
      ``InternalOrder.uniqueChoiceOfFunCSup, ``InternalOrder.uniqueChoiceOfProdCSup, ``InternalOrder.uniqueChoiceOfFunSup,
      ``InternalOrder.uniqueChoiceOfBot, ``InternalOrder.uniqueChoiceOfChainSup, ``InternalOrder.uniqueChoiceOfSup,
      ``AbstractOrder.equalityCasesOfLeIffLtOrEq,
      ``AbstractOrder.equalityCasesOfGrindTrichotomy, ``AbstractOrder.stableEqualityOfGrindComparison,
      ``AbstractOrder.stableEqualityOfArrayAntisymm, ``AbstractOrder.stableEqualityOfVectorAntisymm,
      ``AbstractOrder.stableEqualityOfArrayOrder, ``AbstractOrder.stableEqualityOfVectorOrder,
      ``AbstractOrder.stableEqualityOfListOrder, ``AbstractOrder.equalityCasesOfListComparison,
      ``AbstractOrder.equalityCasesOfArrayComparison,
      ``AbstractOrder.stableEqualityOfCommutativeMin, ``AbstractOrder.stableEqualityOfMinEqOr,
      ``AbstractOrder.stableEqualityOfMaxEqOr, ``AbstractOrder.stableEqualityOfOrderMin,
      ``AbstractOrder.stableEqualityOfOrderMax, ``AbstractOrder.stableEqualityOfTrichotomousLT,
      ``AbstractOrder.weakMiddleOfTotalNotLT,
      ``AbstractOrder.stableEqualityOfHeadLE, ``AbstractOrder.weakEqualityOfLexTotal,
      ``AbstractOrder.equalityCasesOfVectorComparison, ``AbstractOrder.excludedMiddleOfListOrderLT,
      ``AbstractOrder.excludedMiddleOfVectorOrderLT,
      ``AbstractOrder.excludedMiddleOfListLeIffLTOrEq, ``AbstractOrder.excludedMiddleOfArrayLeIffLTOrEq,
      ``AbstractOrder.excludedMiddleOfVectorLeIffLTOrEq,
      ``AbstractOrder.excludedMiddleOfLawfulLT, ``AbstractOrder.weakMiddleOfTotalNot,
      ``AbstractOrder.PredicateBounds.weakMiddleOfLTMax, ``AbstractOrder.PredicateBounds.weakMiddleOfMinLT,
      ``AbstractOrder.weakMiddleOfLinearPreorder, ``AbstractOrder.weakMiddleOfLinearOrder,
      ``inhabitedPropExtOfProofHEq, ``inhabitedPropExtOfEqTrue,
      ``inhabitedPropExtOfDecision, ``refutedPropExtOfDecision, ``inhabitedPropExtOfEqTrueRule,
      ``refutedPropExtOfEqFalseRule, ``OptionalIndex.decidablePropExtOfIte,
      ``IntegerCancellation.eqVar, ``IntegerCancellation.eqNorm, ``IntegerCancellation.leNorm,
      ``IntegerCancellation.eqCoeff, ``IntegerCancellation.leCoeff,
      ``NaturalCancellation.exprEq, ``NaturalCancellation.exprLe, ``NaturalCancellation.exprLt,
      ``NaturalCancellation.exprNormEq, ``NaturalCancellation.exprNorm, ``NaturalCancellation.polyEq,
      ``NaturalCancellation.polyLe,
      ``OptionalIndex.decidablePropExtOfIsSome, ``TwoWorlds.countermodel, ``ForkFrame.countermodel,
      ``ForkFrame.equalityCountermodel, ``ForkFrame.membershipCountermodel,
      ``ClassicalConsequences.weakMiddleOfDeMorgan, ``ClassicalConsequences.deMorganOfWeakMiddle] ++ ClassicalDecisionEquations.rules.map Prod.snd
  discard <| replayBoundaryDependencies official env roots

/-- Abstract just the proof argument of the pinned right-hand `Option.get`.
A port may provide any such proof with the stated equality. -/
private def abstractGetWitness (type : Expr) : MetaM Expr :=
  Meta.forallTelescope type fun params eq => do
    let some (_, _, rhs) := eq.eq? | throwError "missing option equality"
    unless rhs.isAppOfArity ``Option.get 3 do throwError "missing dependent option projection"
    let argument := rhs.appArg!
    Meta.withLocalDeclD `h (← Meta.inferType argument) fun h => do
      let predicate ← Meta.mkLambdaFVars #[h] (mkApp eq.appFn! (mkApp rhs.appFn! h))
      Meta.mkForallFVars params (← Meta.mkAppM ``Exists #[predicate])

/-- Construct the law-to-axiom type with the public selector left arbitrary. -/
private def optionLawReductionType (source target : ConstantInfo) (levels : List Level) :
    MetaM Expr := do
  let selector ← getConstInfo ``Option.choice
  unless levels.length == 1 && source.numLevelParams == 1 && selector.numLevelParams == 1 do
    throwError "unexpected universe arity for {source.name}"
  let original := source.type.instantiateLevelParams source.levelParams levels
  let siteType ← if [``Option.getD_choice, ``Option.get!_choice].contains source.name then
    abstractGetWitness original
  else pure original
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

private abbrev agreesOnEquivalentProps (port reference : type_of% @instDecidableEqOfIff) :=
  ∀ (p q : Prop) (h : p ↔ q),
    @decide (p = q) (@port p q (.isTrue h)) = @decide (p = q) (@reference p q (.isTrue h))

/-- Keep the type and relation arbitrary while instantiating the next two
arguments of the pinned declaration with the unit family and its element. -/
private def unitCoherenceType (source : ConstantInfo) (u : Level) : MetaM Expr := do
  let type := source.type.instantiateLevelParams source.levelParams [u, .succ .zero]
  Meta.forallBoundedTelescope type (some 2) fun params rest => do
    let #[α, r] := params | throwError "missing quotient parameters"
    let quot := mkApp2 (mkConst `Quot [u]) α r
    let family := Expr.lam `q quot (mkConst `Unit) .default
    let value := Expr.lam `a α (mkConst `Unit.unit) .default
    let .forallE _ _ next _ := rest | throwError "missing quotient motive"
    let .forallE _ _ law _ := next.instantiate1 family | throwError "missing quotient function"
    Meta.mkForallFVars params (law.instantiate1 value)

/-- Read the instantiated type from the physical declaration. The kernel
checks the source application with `Eq.refl true` as its entire certificate. -/
private def translatedComparisonType (source : ConstantInfo) : MetaM Expr := do
  let levels := [Level.zero]
  let type := source.type.instantiateLevelParams source.levelParams levels
  let strict := [``Grind.CommRing.lt_norm_expr, ``Grind.CommRing.lt_norm_expr_nc].contains source.name
  Meta.forallBoundedTelescope type (some (if strict then 8 else 7)) fun params _ => do
    let literal (n : Nat) := mkApp (mkConst ``Grind.CommRing.Expr.num) (toExpr (Int.ofNat n))
    let terms := if strict then
      let x := mkApp (mkConst ``Grind.CommRing.Expr.var) (toExpr (0 : Nat))
      #[literal 0, x, literal 1, mkApp2 (mkConst ``Grind.CommRing.Expr.add) x (literal 1)]
    else
      #[literal 0, literal 1, literal 1, literal 2]
    let test := mkAppN (mkConst source.name levels) (params ++ terms)
    let application := mkApp test (← Meta.mkEqRefl (mkConst ``Bool.true))
    let proof ← Meta.mkLambdaFVars params application
    Lean.ofExceptKernelException (Kernel.check (← getEnv) {} proof)

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
    unless [`Classical.choice, `propext, `Quot.sound, `sorryAx].contains axiomName do
      throwError "unsupported impossibility target {axiomName} for {owner}/{name}"
    let proof ← getConstInfo witness
    let target ← getConstInfo axiomName
    let levels := proof.levelParams.map Level.param
    let targetLevels := levels.drop (levels.length - target.numLevelParams)
    let expected ← if OptionSelector.usesSelector owner name || source.name == ``Option.choice then
      let law ← if source.name == ``Option.choice then do
        let some law := env.header.moduleData[idx]!.constants.find? (·.name == ``Option.isSome_choice)
          | throwError "missing official presence law for {owner}/{name}"
        pure law
      else pure source
      Elab.Command.liftCoreM <| Meta.MetaM.run' <| optionLawReductionType law target levels
    else if [``Grind.CommRing.le_norm_expr, ``Grind.CommRing.le_norm_expr_nc,
        ``Grind.CommRing.lt_norm_expr, ``Grind.CommRing.lt_norm_expr_nc].contains source.name then
      Elab.Command.liftCoreM <| Meta.MetaM.run' do
        mkArrow (← translatedComparisonType source) target.type
    else if [``Order.flat_csup, ``Lean.Loop.forIn, ``Lean.instForInLoopUnitOfMonad].contains source.name then
      Elab.Command.liftCoreM <| Meta.MetaM.run' do
        let [u] := levels | throwError "unexpected choice universe for {source.name}"
        let (sourceLevels, observation, reference) := if source.name == ``Order.flat_csup then
          ([Level.succ u], ``InternalOrder.returnsFlatSome, ``InternalOrder.officialFlatPresence)
        else if source.name == ``Lean.Loop.forIn then
          ([u, u], ``WhileChoice.fixed, ``WhileChoice.officialFixed)
        else
          ([u, u], ``WhileChoice.instanceFixed, ``WhileChoice.officialInstanceFixed)
        let behavior := mkConst observation [u]
        let pinned ← getConstInfo reference
        unless Kernel.isDefEqGuarded env {} (pinned.type.instantiateLevelParams pinned.levelParams [u])
            (mkApp behavior (mkConst source.name sourceLevels)) do
          throwError "invalid pinned observation for {source.name}"
        Meta.withLocalDeclD `port (source.type.instantiateLevelParams source.levelParams sourceLevels) fun port => do
          let conclusion := target.type.instantiateLevelParams target.levelParams [u]
          Meta.mkForallFVars #[port] (← mkArrow (mkApp behavior port) conclusion)
    else if source.name == ``Quot.indepCoherent then
      Elab.Command.liftCoreM <| Meta.MetaM.run' do
        let [u] := levels | throwError "unexpected quotient universe parameters"
        mkArrow (← unitCoherenceType source u) (target.type.instantiateLevelParams target.levelParams [u])
    else if owner == `Init.Internal.Order.Basic && InternalOrder.implicationOrders.lookup name == some witness then
      Elab.Command.liftCoreM <| Meta.MetaM.run' <| orderReductionType source target
    else if source.name == ``instDecidableEqOfIff then
      Elab.Command.liftCoreM <| Meta.MetaM.run' <| Meta.withLocalDeclD `port source.type fun port => do
        let agreement := mkApp2 (mkConst ``agreesOnEquivalentProps) port (mkConst source.name)
        Meta.mkForallFVars #[port] (← mkArrow agreement target.type)
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
