module
public import Lean
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitInventory.EnvelopeCancellation
import OmegaChecks.InitInventory.PublicReduction
meta import OmegaChecks.InitInventory.PublicReduction
import OmegaChecks.InitInventory.UnsafeCast
meta import OmegaChecks.InitInventory.UnsafeCast
import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitInventory.OriginalType
meta import OmegaChecks.InitInventory.OriginalType
import OmegaChecks.InitInventory.ConstructorIff
meta import OmegaChecks.InitInventory.ConstructorIff
meta import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitPort.UnsafeRuntime
meta import OmegaChecks.InitPort.UnsafeRuntime
import OmegaChecks.InitPort.EffectRun
meta import OmegaChecks.InitPort.EffectRun
import OmegaChecks.InitInventory.DeclarationEvidence
import OmegaChecks.InitInventory.Conditional
meta import OmegaChecks.InitInventory.Conditional
import OmegaChecks.InitInventory.FieldNormalization
meta import OmegaChecks.InitInventory.FieldNormalization
meta import OmegaChecks.InitInventory.ChoiceOperands
import OmegaChecks.InitInventory.Quotient
import OmegaChecks.InitInventory.RefinedQuotient
meta import OmegaChecks.InitInventory.RefinedQuotient
meta import OmegaChecks.InitInventory.OrderedAlgebra
meta import OmegaChecks.InitInventory.Order
meta import OmegaChecks.InitInventory.Logic
meta import OmegaChecks.InitInventory.Reductions
import Lean.Replay
import all Lean.Util.CollectAxioms
import all Lean.Environment
meta import OmegaChecks.InitInventory.RangeIndex
public import OmegaChecks.InitInventory.ConstraintReflection
public import OmegaChecks.InitInventory.RangeIndex
public import OmegaChecks.InitInventory.Reductions
public import OmegaChecks.InitInventory.TransformerLaws
meta import OmegaChecks.InitInventory.VectorProjection
public import OmegaChecks.InitInventory.VectorProjection
public import OmegaChecks.InitInventory.Traversal
public import OmegaChecks.InitInventory.MonadicZip
meta import OmegaChecks.InitInventory.MonadicZip
public import OmegaChecks.InitInventory.Collector
public import OmegaChecks.InitInventory.StringPatternMatchers
public import OmegaChecks.InitInventory.StringSearchLoops

public section

/-!
Inventory every public declaration site in the pinned Init and the independently importable
strict modules. Run `lake env lean --run src/OmegaChecks/InitInventory.lean LIB OUTPUT`
after building `+OmegaChecks.InitInventory`. An optional third argument writes the gaps as TSV.
-/

open Lean
open OmegaChecks.InitInventory (declarationKind nativeSignatures NativeSite nativeSummary checkedTypeAxioms)

private def installedModules (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut modules := if ← (modToFilePath dir root "olean").pathExists then #[root] else #[]
  for file in ← (dir / root.toString).walkDir do
    if file.extension == some "olean" then
      modules := modules.push (← moduleNameOfFileName file dir)
  return modules.qsort Name.lt

/-- Additional logical consequences with separate proof terms. These do not discharge a
missing official interface in the completeness check. -/
private def logicalConsequence? (owner name : Name) : Option (Name × Name) := do
  if let some entry := OmegaChecks.InitBoundaries.ContainerEquality.witnesses.lookup name then
    return entry
  if let some entry := OmegaChecks.InitBoundaries.MonadicZip.consequence? owner name then
    return entry
  if owner == `Init.Data.Array.Monadic then
    if let some result := OmegaChecks.InitBoundaries.MonadicCollectionEquations.comparisons.lookup name then
      return result
  if owner == `Init.Data.List.ToArray && name == ``List.findRevM?_toArray then
    return (``OmegaChecks.InitBoundaries.MonadicTraversal.ReverseSearch.PredicateList,
      ``OmegaChecks.InitBoundaries.MonadicTraversal.ReverseSearch.predicateIff)
  if owner == `Init.Data.Array.Lemmas then
    if name == ``Array.findSomeRevM?_eq_findSomeM?_reverse then
      return (``OmegaChecks.InitBoundaries.MonadicTraversal.ReverseSearch.ForwardOptionList,
        ``OmegaChecks.InitBoundaries.MonadicTraversal.ReverseSearch.optionIff)
    if name == ``Array.findRevM?_eq_findM?_reverse then
      return (``OmegaChecks.InitBoundaries.MonadicTraversal.ReverseSearch.BoolForwardOfBackward,
        ``OmegaChecks.InitBoundaries.MonadicTraversal.ReverseSearch.boolOfArray)
  if owner == `Init.Data.Array.MapIdx then
    if name == ``List.mapIdxM_toArray then
      return (``OmegaChecks.InitBoundaries.MonadicTraversal.IndexedMap.PairConversion,
        ``OmegaChecks.InitBoundaries.MonadicTraversal.IndexedMap.fromList)
    if name == ``Array.toList_mapIdxM then
      return (``OmegaChecks.InitBoundaries.MonadicTraversal.IndexedMap.PairConversion,
        ``OmegaChecks.InitBoundaries.MonadicTraversal.IndexedMap.fromArray)
  if owner == `Init.Data.Option.Monadic then
    if let some entry := OmegaChecks.InitBoundaries.TransformerLaws.OptionIteration.directConsequences.lookup name then
      return entry
  if owner == `Init.Data.Function then
    if name == ``Function.Injective.exists_leftInverse then
      return (``OmegaChecks.InitBoundaries.EmbeddingRange.SplittingPrinciple,
        ``OmegaChecks.InitBoundaries.EmbeddingRange.existsIff)
    if name == `Function.Injective.leftInverse then
      return (``OmegaChecks.InitBoundaries.EmbeddingRange.SplittingPrinciple,
        ``OmegaChecks.InitBoundaries.EmbeddingRange.leftInverseIff)
  if owner == `Init.Data.Sum.Lemmas then
    if name == ``Sum.forall_sum then
      return (``OmegaChecks.InitBoundaries.SumFunctionEta, ``OmegaChecks.InitBoundaries.sumEtaOfForall)
    if let some result := OmegaChecks.InitBoundaries.SumFunctions.consequences.lookup name then return result
  if owner == `Init.WF then
    if name == ``WellFounded.Nat.fix.go_congr then
      return (``OmegaChecks.InitBoundaries.MeasuredRecursion.EmptyDomainExtensionality,
        ``OmegaChecks.InitBoundaries.MeasuredRecursion.ofFuelCongruence)
    if name == ``WellFounded.Nat.fix_eq then
      return (``OmegaChecks.InitBoundaries.MeasuredRecursion.EmptyDomainExtensionality,
        ``OmegaChecks.InitBoundaries.MeasuredRecursion.ofFixEquation)
  if owner == `Init.Data.Iterators.PostconditionMonad then
    match name with
    | ``Std.Iterators.PostconditionT.bind_pure =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.RightIdentity,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.rightIdentity)
    | ``Std.Iterators.PostconditionT.pure_bind =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.LeftIdentity,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.leftIdentity)
    | ``Std.Iterators.PostconditionT.map_pure =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.PureImage,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.pureImage)
    | ``Std.Iterators.PostconditionT.map_eq_pure_bind =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.ImageBind,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.imageBind)
    | ``Std.Iterators.PostconditionT.bind_assoc =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.AssociatedPredicates,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.associatedPredicates)
    | ``Std.Iterators.instLawfulMonadPostconditionT =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.LeftIdentity,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.ofMonad)
    | _ => pure ()
  if owner == `Init.Internal.Order.Basic then
    if let some witness := OmegaChecks.InitBoundaries.InternalOrder.decisionChains.lookup name then
      return (``Classical.em, witness)
  if owner == `Init.Internal.Order.MonadTail then
    if let some witness := OmegaChecks.InitBoundaries.InternalOrder.tailDecisionChains.lookup name then
      return (``Classical.em, witness)
  if owner == `Init.Internal.Order.Basic then
    if name == ``Lean.Order.instCCPOPi then
      return (``OmegaChecks.InitBoundaries.InternalOrder.MereUniqueChoice,
        ``OmegaChecks.InitBoundaries.InternalOrder.uniqueSelectionOfChainCompletePi)
    if name == ``Lean.Order.instCompleteLatticePi then
      return (``OmegaChecks.InitBoundaries.InternalOrder.MereUniqueChoice,
        ``OmegaChecks.InitBoundaries.InternalOrder.uniqueSelectionOfCompletePi)
  if owner == `Init.Grind.Ring.CommSemiringAdapter && name == ``Lean.Grind.Ring.OfSemiring.of_diseq then
    return (``OmegaChecks.InitBoundaries.RingEnvelopeExact.ReflectsDisequality,
      ``OmegaChecks.InitBoundaries.RingEnvelopeExact.adapterIff)
  if owner == `Init.Grind.Norm && name == ``Lean.Grind.exists_prop then
    return (``OmegaChecks.InitBoundaries.ExistentialConjunction.ClosedEquality,
      ``OmegaChecks.InitBoundaries.ExistentialConjunction.ofRule)
  if owner == `Init.Classical || owner == `Init.Prelude then
    let result := ``OmegaChecks.InitBoundaries.PropositionalChoice.Selection
    match owner, name with
    | `Init.Classical, ``Classical.axiomOfChoice => return (result, ``OmegaChecks.InitBoundaries.PropositionalChoice.ofChoice)
    | `Init.Classical, ``Classical.skolem => return (result, ``OmegaChecks.InitBoundaries.PropositionalChoice.ofSkolem)
    | `Init.Prelude, ``Pi.instNonempty => return (result, ``OmegaChecks.InitBoundaries.PropositionalChoice.ofProducts)
    | _, _ => pure ()
  if let some result := OmegaChecks.InitBoundaries.WeakRingOrder.stabilityEquivalences.lookup name then
    return result
  if owner == `Init.Control.Lawful.MonadAttach.Lemmas then
    if let some result := OmegaChecks.InitBoundaries.TransformerLaws.ReturnImage.equivalences.lookup name then
      return result
  if owner == `Init.Omega.Constraint && name == ``Lean.Omega.Constraint.combine_sat then
    return (``OmegaChecks.InitBoundaries.ConstraintReflection.AndReflection,
      ``OmegaChecks.InitBoundaries.ConstraintReflection.equivalence)
  if owner == `Init.Data.Vector.Count then
    if let some result := OmegaChecks.InitBoundaries.VectorCount.equivalences.lookup name then return result
  if owner == `Init.Data.Range.Polymorphic.NatLemmas || owner == `Init.Data.Range.Polymorphic.IntLemmas then
    if let some result := OmegaChecks.InitBoundaries.RangeIndex.equivalences.lookup name then return result
  if owner == `Init.System.ST || owner == `Init.Control.StateRef || owner == `Init.System.Promise then
    if let some (_, _, witness) := OmegaChecks.InitBoundaries.ReferenceSelection.witnesses.find?
        (fun entry => entry.1 == owner && entry.2.1 == name) then
      return (``OmegaChecks.InitBoundaries.ReferenceSelection.Selection, witness)
  if owner == `Init.Data.Int.OfNat then
    if let some result := OmegaChecks.InitBoundaries.NaturalCastComparison.equivalences.lookup name then
      return result
  if owner == `Init.Sym.Lemmas then
    if let some result := OmegaChecks.InitBoundaries.NaturalComparison.equivalences.lookup name then
      return result
  if owner == `Init.Data.Nat.Internal.Linear || owner == `Init.Data.Int.Linear then
    if let some (_, target, proof, _) := OmegaChecks.InitBoundaries.linearCertificates.find?
        (fun row => row.1 == name) then
      return (target, proof)
  if owner == `Init.Data.Int.Linear then
    if let some (_, target, witness) := OmegaChecks.InitBoundaries.IntegerCancellation.witnesses.find?
        (fun row => row.1 == name) then
      return (target, witness)
  match owner, name with
  | `Init.Data.Range.Polymorphic.Basic, ``Std.Rxc.size_pos_iff_le =>
    return (``Classical.em, ``OmegaChecks.InitBoundaries.RangeSize.emOfClosed)
  | `Init.Data.Range.Polymorphic.Basic, ``Std.Rxo.size_pos_iff_lt =>
    return (``Classical.em, ``OmegaChecks.InitBoundaries.RangeSize.emOfOpen)
  | `Init.Data.Vector.Lemmas, ``Vector.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofVectorMember)
  | `Init.Data.Vector.Lemmas, ``Vector.eq_push_append_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofFirstVectorMember)
  | `Init.Data.List.Lemmas, ``List.eq_replicate_or_eq_replicate_append_cons =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.runDecompositionIffEqualityCases)
  | `Init.Data.List.Lemmas, ``List.replicateRecOn =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.runInductionIffEqualityCases)
  | `Init.Data.List.Lemmas, ``List.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofListMember)
  | `Init.Data.Array.Lemmas, ``Array.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofArrayMember)
  | `Init.Data.List.Lemmas, ``List.eq_append_cons_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.firstListMemberIffEqualityCases)
  | `Init.Data.Array.Lemmas, ``Array.eq_push_append_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofFirstArrayMember)
  | `Init.Internal.Order.Basic, ``Lean.Order.inf =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.lfp =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfLfp)
  | `Init.Internal.Order.Basic, ``Lean.Order.lfp_monotone =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfMonotoneLfp)
  | `Init.Internal.Order.Basic, ``Lean.Order.fix =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfFix)
  | `Init.Internal.Order.Basic, ``Lean.Order.prod_sup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfProdSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.prod_csup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfProdCSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.fun_sup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfFunSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.fun_csup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfFunCSup)
  | `Init.Internal.Order.MonadTail, ``Lean.Order.ST.bot' =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.FamilyChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.familyChoiceOfSTBottom)
  | `Init.Internal.Order.Basic, ``Lean.Order.EST.bot =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.FamilyChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.familyChoiceOfStateBottom)
  | `Init.Internal.Order.Basic, ``Lean.Order.CompleteLattice.sup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.CCPO.csup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfChainSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.bot =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfBot)
  | `Init.Control.Lawful.Basic, ``bind_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.dependentFunextFromBindCongr)
  | `Init.Control.Lawful.Basic, ``map_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.dependentFunextFromMapCongr)
  | `Init.Control.Basic, ``forIn'_eq_forIn => return (``funext, ``OmegaChecks.InitBoundaries.funextFromForInEq)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instWeaklyLawfulMonadAttachReaderTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTWeakAttach)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instLawfulMonadAttachReaderTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTAttach)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instWeaklyLawfulMonadAttachStateTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateTWeakAttach)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instLawfulMonadAttachStateTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateTAttach)
  | `Init.Control.Lawful.MonadLift.Instances, ``ExceptT.lift_bind =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.MapAfterBind.funextFromExceptLiftBind)
  | `Init.Control.Lawful.MonadLift.Instances, ``ExceptT.instLawfulMonadLift =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.MapAfterBind.funextFromExceptLift)
  | `Init.Control.Lawful.MonadLift.Instances, ``StateCpsT.instLawfulMonadLiftOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateCpsLift)
  | `Init.Control.Lawful.MonadLift.Instances, ``ExceptCpsT.instLawfulMonadLiftOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromExceptCpsLift)
  | `Init.Control.Lawful.Instances, ``StateT.seqLeft_eq =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateSeqLeft)
  | `Init.Control.Lawful.Instances, ``StateT.seqRight_eq =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateSeqRight)
  | `Init.Data.List.Scan.Lemmas, ``List.scanlM_cons =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.MapAfterBind.funextFromScanlCons)
  | `Init.Control.Lawful.Basic, ``map_bind =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.MapAfterBind.funextFromMapBind)
  | `Init.Control.Lawful.Instances, ``StateT.run_seq =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.MapAfterBind.funextFromStateRunSeq)
  | `Init.Control.Lawful.Basic, ``LawfulMonad.mk' =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMonadConstructor)
  | `Init.Data.Vector.Monadic, ``Vector.map_toArray_inj =>
    return (``OmegaChecks.InitBoundaries.VectorProjection.ArrayTests,
      ``OmegaChecks.InitBoundaries.VectorProjection.arrayTestsOfOriginal)
  | `Init.Control.Lawful.Lemmas, ``map_inj_of_left_inverse =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMapInjectiveLeftInverse)
  | `Init.Control.Lawful.Lemmas, ``map_inj_right_of_nonempty =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMapInjectiveNonempty)
  | `Init.Control.Lawful.Lemmas, ``map_inj_right =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMapInjectiveMonad)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulFunctor =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTFunctor)
  | `Init.Control.State, ``instSubsingletonStateM =>
    return (``OmegaChecks.InitBoundaries.SubsingletonState.Extensionality,
      ``OmegaChecks.InitBoundaries.SubsingletonState.ofState)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulApplicative =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTApplicative)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTMonad)
  | `Init.Control.Lawful.Instances, ``StateT.instLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateTMonad)
  | `Init.Control.Lawful.Instances, ``ReaderT.ext => return (``funext, ``OmegaChecks.InitBoundaries.funextFromReaderExt)
  | `Init.Control.Lawful.Instances, ``ReaderT.ext_iff => return (``funext, ``OmegaChecks.InitBoundaries.funextFromReaderExtIff)
  | `Init.Control.Lawful.Instances, ``StateT.ext => return (``funext, ``OmegaChecks.InitBoundaries.funextFromStateExt)
  | `Init.Control.Lawful.Instances, ``StateT.ext_iff => return (``funext, ``OmegaChecks.InitBoundaries.funextFromStateExtIff)
  | `Init.Data.Function, ``Function.LeftInverse.id => return (``funext, ``OmegaChecks.InitBoundaries.funextFromLeftInverseId)
  | `Init.Data.Function, ``Function.RightInverse.id => return (``funext, ``OmegaChecks.InitBoundaries.funextFromRightInverseId)
  | `Init.Data.List.Monadic, ``List.foldlM_subtype =>
    return (``funext, ``OmegaChecks.InitBoundaries.MonadicTraversal.fromListFoldl)
  | `Init.Data.List.Monadic, ``List.foldrM_subtype =>
    return (``funext, ``OmegaChecks.InitBoundaries.MonadicTraversal.fromListFoldr)
  | `Init.Data.List.Monadic, ``List.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.ArrayLoopCongruence.listForInCongr)
  | `Init.Data.Array.Monadic, ``Array.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.ArrayLoopCongruence.forInCongr)
  | `Init.Data.Vector.Monadic, ``Vector.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.ArrayLoopCongruence.vectorForInCongr)
  | `Init.Data.Array.Lemmas, ``Array.foldlM_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.ArrayLoopCongruence.foldlCongr)
  | `Init.Data.Array.Lemmas, ``Array.foldrM_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.ArrayLoopCongruence.foldrCongr)
  | `Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop, ``Std.IterM.forIn_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromMonadicCongr)
  | `Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop, ``Std.IterM.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromMonadicCongr')
  | `Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap, ``Std.IterM.step_filterWithPostcondition =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorStepLift.funextOfFilter)
  | `Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap, ``Std.IterM.step_filterM =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorStepLift.funextOfFilterM)
  | `Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap, ``Std.IterM.step_mapWithPostcondition =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorStepLift.funextOfMap)
  | `Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap, ``Std.IterM.step_mapM =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorStepLift.funextOfMapM)
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.forIn_eq_forIn_toIterM =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopLift.funextOfForIn)
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.forIn'_eq_forIn'_toIterM =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopLift.funextOfForIn')
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.foldM_eq_foldM_toIterM =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopLift.funextOfFold)
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.forIn_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromCongr)
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromCongr')
  | `Init.Data.Range.Polymorphic.Map, ``Std.PRange.UpwardEnumerable.Map.succ?_toFun' =>
    return (``funext, ``OmegaChecks.InitBoundaries.RangeMap.funextFromSuccMap)
  | `Init.Ext, ``funext_iff => return (``funext, ``OmegaChecks.InitBoundaries.funextFromFunextIff)
  | `Init.Core, ``Quotient.sound => return (``funext, ``OmegaChecks.InitBoundaries.funextFromQuotientSound)
  | `Init.Core, ``Pi.instSubsingleton => return (``funext, ``OmegaChecks.InitBoundaries.funextFromPiSubsingleton)
  | `Init.Core, ``instSubsingletonSquash => return (``funext, ``OmegaChecks.InitBoundaries.funextFromSquashSubsingleton)
  | `Init.PropLemmas, ``proof_irrel_heq =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfProofHEq)
  | `Init.PropLemmas, ``eq_true_eq_id =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfEqTrue)
  | `Init.Grind.Norm, ``Lean.Grind.eq_true_eq =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.GrindNormalization.normalizePositive)
  | `Init.Grind.Norm, ``Lean.Grind.eq_false_eq =>
    return (``OmegaChecks.InitBoundaries.RefutedPropExt, ``OmegaChecks.InitBoundaries.GrindNormalization.normalizeNegative)
  | `Init.Grind.Lemmas, ``Lean.Grind.eq_eq_of_eq_true_left =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.GrindNormalization.normalizePositiveLeft)
  | `Init.Grind.Lemmas, ``Lean.Grind.eq_eq_of_eq_true_right =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.GrindNormalization.normalizePositiveRight)
  | `Init.Grind.Norm, ``Lean.Grind.flip_bool_eq =>
    return (``OmegaChecks.InitBoundaries.GrindNormalization.FlippedBooleanEquality,
      ``OmegaChecks.InitBoundaries.GrindNormalization.booleanFlipOfNormalization)
  | `Init.Grind.Lemmas, ``Lean.Grind.eq_congr' =>
    return (``OmegaChecks.InitBoundaries.GrindNormalization.FlippedBooleanEquality,
      ``OmegaChecks.InitBoundaries.GrindNormalization.booleanFlipOfCrossed)
  | `Init.Grind.Lemmas, ``Lean.Grind.heq_congr' =>
    return (``OmegaChecks.InitBoundaries.GrindNormalization.FlippedBooleanEquality,
      ``OmegaChecks.InitBoundaries.GrindNormalization.booleanFlipOfHeterogeneousCrossed)
  | `Init.Grind.Lemmas, ``Lean.Grind.of_decide_eq_true | `Init.SimpLemmas, ``eq_true_of_decide =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfDecision)
  | `Init.Grind.Lemmas, ``Lean.Grind.of_decide_eq_false | `Init.SimpLemmas, ``eq_false_of_decide =>
    return (``OmegaChecks.InitBoundaries.RefutedPropExt, ``OmegaChecks.InitBoundaries.refutedPropExtOfDecision)
  | `Init.SimpLemmas, ``eq_true =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfEqTrueRule)
  | `Init.SimpLemmas, ``eq_false | `Init.SimpLemmas, ``eq_false' =>
    return (``OmegaChecks.InitBoundaries.RefutedPropExt, ``OmegaChecks.InitBoundaries.refutedPropExtOfEqFalseRule)
  | `Init.Grind.Norm, ``Lean.Grind.ite_true_false =>
    return (``OmegaChecks.InitBoundaries.OptionalIndex.DecidablePropExt, ``OmegaChecks.InitBoundaries.OptionalIndex.decidablePropExtOfIte)
  | `Init.Data.List.Basic, ``List.replicate_eq_replicateTR =>
    return (``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ReplicateAccumulator,
      ``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ofReplicate)
  | `Init.Data.List.Basic, ``List.map_eq_mapTR =>
    return (``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.MapAfterPrefix,
      ``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ofMap)
  | `Init.Data.List.Basic, ``List.append_eq_appendTR =>
    return (``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.AppendChunks,
      ``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ofAppend)
  | `Init.Data.ByteArray.Basic, ``ByteArray.append_eq_fastAppend =>
    return (``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ByteCopyChunks,
      ``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ofByteCopy)
  | `Init.Data.List.Basic, ``List.length_eq_lengthTR =>
    return (``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.PrefixLength,
      ``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ofLength)
  | `Init.Data.Option.Lemmas, ``Option.not_comp_isSome =>
    return (``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.BindClassifier,
      ``OmegaChecks.InitBoundaries.PublicAlgorithmEquations.ofClassifier)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Expr.of_cancel_eq =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprEq)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Expr.of_cancel_le =>
    return (``OmegaChecks.InitBoundaries.NaturalCancellation.SuccLeEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprLe)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Expr.of_cancel_lt =>
    return (``OmegaChecks.InitBoundaries.NaturalCancellation.SuccLtEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprLt)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.ExprCnstr.eq_of_toNormPoly_eq =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprNormEq)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.ExprCnstr.denote_toNormPoly =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprNorm)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Poly.denote_eq_cancel_eq =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.polyEq)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Poly.denote_le_cancel_eq =>
    return (``OmegaChecks.InitBoundaries.NaturalCancellation.SuccLeEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.polyLe)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_eq_var =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneEq, ``OmegaChecks.InitBoundaries.IntegerCancellation.eqVar)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_eq =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneEq, ``OmegaChecks.InitBoundaries.IntegerCancellation.eqNorm)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_le =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneLE, ``OmegaChecks.InitBoundaries.IntegerCancellation.leNorm)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_eq_coeff =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneEq, ``OmegaChecks.InitBoundaries.IntegerCancellation.eqCoeff)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_le_coeff =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneLE, ``OmegaChecks.InitBoundaries.IntegerCancellation.leCoeff)
  | `Init.GetElem, ``isSome_getElem? =>
    return (``OmegaChecks.InitBoundaries.OptionalIndex.DecidablePropExt, ``OmegaChecks.InitBoundaries.OptionalIndex.decidablePropExtOfIsSome)
  | `Init.Data.Order.Lemmas, ``Std.le_iff_lt_or_eq
  | `Init.Grind.Ordered.Order, ``Lean.Grind.PartialOrder.le_iff_lt_or_eq =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.AbstractOrder.equalityCasesOfLeIffLtOrEq)
  | `Init.Grind.Ordered.Order, ``Lean.Grind.LinearOrder.trichotomy =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.AbstractOrder.equalityCasesOfGrindTrichotomy)
  | `Init.Grind.Ordered.Order, ``Lean.Grind.LinearOrder.le_of_not_lt =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfGrindComparison)
  | `Init.Data.Array.Lex.Lemmas, ``Array.le_antisymm =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfArrayAntisymm)
  | `Init.Data.Vector.Lex, ``Vector.le_antisymm =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfVectorAntisymm)
  | `Init.Data.Array.Lex.Lemmas, ``Array.instIsLinearOrderOfLawfulOrderLT =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfArrayOrder)
  | `Init.Data.Vector.Lex, ``Vector.instIsLinearOrderOfLawfulOrderLT =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfVectorOrder)
  | `Init.Data.List.Lex, ``List.instIsLinearOrder =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfListOrder)
  | `Init.Data.List.Lex, ``List.lt_of_le_of_lt =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.AbstractOrder.equalityCasesOfListComparison)
  | `Init.Data.Array.Lex.Lemmas, ``Array.lt_of_le_of_lt =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.AbstractOrder.equalityCasesOfArrayComparison)
  | `Init.Data.Order.LemmasExtra, `Std.instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfCommutativeMin)
  | `Init.Data.Order.Lemmas, `Std.instMinEqOrOfLawfulOrderLeftLeaningMin =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfMinEqOr)
  | `Init.Data.Order.Lemmas, `Std.instMaxEqOrOfLawfulOrderLeftLeaningMax =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfMaxEqOr)
  | `Init.Data.Order.Lemmas, `Std.instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfOrderMin)
  | `Init.Data.Order.Lemmas, `Std.instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfOrderMax)
  | `Init.Data.Order.Lemmas, `Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfTrichotomousLT)
  | `Init.Data.Order.Lemmas, `Std.instTotalNotLtOfLawfulOrderLTOfLe =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle,
      ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfTotalNotLT)
  | `Init.Data.List.Lex, ``List.left_le_left_of_cons_le_cons =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.StableEquality,
      ``OmegaChecks.InitBoundaries.AbstractOrder.stableEqualityOfHeadLE)
  | `Init.Data.List.Lex, ``List.not_lex_total =>
    return (``OmegaChecks.InitBoundaries.AbstractOrder.WeakEqualityCases,
      ``OmegaChecks.InitBoundaries.AbstractOrder.weakEqualityOfLexTotal)
  | `Init.Data.Vector.Lex, ``Vector.lt_of_le_of_lt =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.AbstractOrder.equalityCasesOfVectorComparison)
  | `Init.Data.List.Lex, ``List.le_total =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfListTotal)
  | `Init.Data.List.Lex, ``List.instTotalLeOfAsymmLt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfListTotalInstance)
  | `Init.Data.List.Lex, ``List.le_total_of_asymm =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfListTotal)
  | `Init.Data.Array.Lex.Lemmas, ``Array.le_total =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfArrayTotal)
  | `Init.Data.Array.Lex.Lemmas, ``Array.instTotalLeOfAsymmLt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfArrayTotalInstance)
  | `Init.Data.Vector.Lex, ``Vector.le_total =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfVectorTotal)
  | `Init.Data.Vector.Lex, ``Vector.instTotalLeOfAsymmLt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfVectorTotalInstance)
  | `Init.Data.Order.Lemmas, ``Std.lt_max_iff =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.PredicateBounds.weakMiddleOfLTMax)
  | `Init.Data.Order.Lemmas, ``Std.min_lt_iff =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.PredicateBounds.weakMiddleOfMinLT)
  | `Init.Classical, ``Classical.not_and_iff_not_or_not =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle,
      ``OmegaChecks.InitBoundaries.ClassicalConsequences.weakMiddleOfDeMorgan)
  | `Init.Grind.Norm, ``Lean.Grind.not_and =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofNegatedConjunction)
  | `Init.Data.Order.Lemmas, ``Std.Asymm.total_not =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfTotalNot)
  | `Init.Data.Order.Factories, ``Std.IsLinearPreorder.of_lt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfLinearPreorder)
  | `Init.Data.Order.Factories, ``Std.IsLinearOrder.of_lt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfLinearOrder)
  | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchAt?_eq_none_iff =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle,
      `OmegaChecks.InitInventory.StringPatterns.weakExcludedMiddleOfMatchAtNone)
  | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchAt?_eq_none_iff =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle,
      `OmegaChecks.InitInventory.StringPatterns.weakExcludedMiddleOfRevMatchAtNone)
  | _, _ => pure ()
  if owner == `Init.Core then
    if name == ``Nat.succ.injEq then
      return (``OmegaChecks.InitBoundaries.ConstructorNormalization.AddCancel,
        ``OmegaChecks.InitBoundaries.ConstructorNormalization.addCancelOfSucc)
    if name == ``List.cons.injEq then
      return (``OmegaChecks.InitBoundaries.ConstructorNormalization.PrefixEquality,
        ``OmegaChecks.InitBoundaries.ConstructorNormalization.prefixEqualityOfCons)
  if owner == `Init.Grind.Order then
    if let some result := OmegaChecks.InitBoundaries.OrderTags.equivalences.lookup name then
      return result
  if owner == `Init.Grind.Ordered.Field || owner == `Init.Grind.Ordered.Ring then
    if let some reduction := OmegaChecks.InitBoundaries.WeakRingOrder.witnesses.lookup name then
      return reduction
  if owner == `Init.SimpLemmas || owner == `Init.Sym.Lemmas || owner == `Init.Data.Bool then
    if let some reduction := OmegaChecks.InitBoundaries.BooleanReflection.witnesses.lookup name then
      return reduction
  if owner == `Init.Classical then
    if name == ``Classical.typeDecidableEq then
      return (``OmegaChecks.InitBoundaries.ClassicalConsequences.DiscontinuousZeroTest,
        ``OmegaChecks.InitBoundaries.ClassicalConsequences.ofTypeDecidableEq)
    if let some witness := OmegaChecks.InitBoundaries.ClassicalConsequences.witnesses.lookup name then
      return (``Classical.em, witness)
  let witness ← match owner, name with
    | `Init.Data.List.Lex, ``List.not_le | `Init.Data.List.Lex, `List.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofListNotLE
    | `Init.Data.Array.Lex.Lemmas, ``Array.not_le | `Init.Data.Array.Lex.Lemmas, `Array.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofArrayNotLE
    | `Init.Data.Vector.Lex, ``Vector.not_le | `Init.Data.Vector.Lex, `Vector.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofVectorNotLE
    | `Init.Data.Vector.Lemmas, ``Vector.instDecidableExistsVectorSucc => some ``OmegaChecks.InitBoundaries.VectorExistence.emOfVectorSucc
    | `Init.Grind.Util, ``Lean.Grind.em => some ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofNormalizedAlternatives
    | `Init.Grind.Norm, ``Lean.Grind.not_forall => some ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofNegatedForall
    | `Init.Grind.Norm, ``Lean.Grind.not_implies => some ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofNegatedImplication
    | `Init.Grind.Norm, ``Lean.Grind.forall_imp_eq_or => some ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofForallImplication
    | `Init.Grind.Norm, ``Lean.Grind.forall_or_forall => some ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofForallOr
    | `Init.Grind.Norm, ``Lean.Grind.forall_forall_or => some ``OmegaChecks.InitBoundaries.GrindQuantifiers.ofOrForall
    | `Init.Grind.Order, ``Lean.Grind.Order.le_of_not_lt => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromComparison
    | `Init.Grind.Norm, ``Lean.Grind.imp_eq => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromImplication
    | `Init.Grind.Norm, ``Lean.Grind.not_not => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromNotNot
    | `Init.Grind.Lemmas, ``Lean.Grind.of_lookahead => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromLookahead
    | `Init.Data.List.Lex, ``List.instLawfulOrderLTOfAsymmLt =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfListOrderLT
    | `Init.Data.Vector.Lex, ``Vector.instLawfulOrderLTOfAsymmLt =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfVectorOrderLT
    | `Init.Data.List.Lex, ``List.cons_le_cons_iff => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfConsLe
    | `Init.Data.List.Lex, ``List.le_iff_exists => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfListLeExists
    | `Init.Data.List.Lex, ``List.le_iff_lt_or_eq => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfListLeIffLTOrEq
    | `Init.Data.Array.Lex.Lemmas, ``Array.le_iff_lt_or_eq => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfArrayLeIffLTOrEq
    | `Init.Data.Vector.Lex, ``Vector.le_iff_lt_or_eq => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfVectorLeIffLTOrEq
    | `Init.Data.Array.Lex.Lemmas, ``Array.le_iff_exists => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfArrayLeExists
    | `Init.Data.Vector.Lex, ``Vector.le_iff_exists => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfVectorLeExists
    | `Init.Data.Order.Lemmas, ``Std.Trichotomous.rel_or_eq_or_rel_swap =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfTrichotomy
    | `Init.Data.Order.Lemmas, ``Std.lt_trichotomy => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfLTTrichotomy
    | `Init.Data.Order.Lemmas, ``Std.total_of_refl_of_trichotomous =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfTrichotomousTotal
    | `Init.Data.Order.Lemmas, ``Std.total_of_not_rel_swap_imp_rel =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfNegationTotal
    | `Init.Data.Order.Factories, ``Std.LawfulOrderLT.of_lt => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfLawfulLT
    | `Init.Data.Order.Lemmas, ``Std.not_lt => some ``OmegaChecks.InitBoundaries.excludedMiddleOfNotLT
    | `Init.Data.Order.Lemmas, ``Std.not_lt_iff_not_le_or_ge =>
      some ``OmegaChecks.InitBoundaries.excludedMiddleOfNotLTIff
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.IsMatch.exists_isLongestMatch =>
      some ``OmegaChecks.InitInventory.StringPatterns.forwardLongestIff
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.IsRevMatch.exists_isLongestRevMatch =>
      some ``OmegaChecks.InitInventory.StringPatterns.backwardLongestIff
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchesAt_iff_exists_isMatch =>
      some ``OmegaChecks.InitInventory.StringPatterns.matchesAtIffEM
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchesAt_iff_exists_isRevMatch =>
      some ``OmegaChecks.InitInventory.StringPatterns.revMatchesAtIffEM
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchAt?_eq_some_iff =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfMatchAtSome
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchAt?_eq_some_iff =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevMatchAtSome
    | _, _ => none
  return (``Classical.em, witness)

private def inventory (lib strictDir : System.FilePath) (visible strict full witnesses : Environment) (modules : Array Name)
    (gaps : Option IO.FS.Handle) (observedRuntime observedPacked : List String) : CoreM Json := do
  let official ← getEnv
  let reductions := OmegaChecks.InitInventory.reductionPaths visible strict full
  let boundaries : Std.HashMap (Name × Name) (Name × Name) := OmegaChecks.InitBoundaries.reductions.foldl
    (init := {}) fun acc (owner, name, target, witness) => acc.insert (owner, name) (target, witness)
  let mut names : NameSet := {}
  let mut duplicateNames : NameSet := {}
  let publicName := fun (n : Name) => !isPrivateName n && !n.isInternalOrNum && !n.hasMacroScopes
  for data in visible.header.moduleData do
    for n in data.constNames do
      if publicName n then
        if names.contains n then duplicateNames := duplicateNames.insert n
        names := names.insert n
  let mut certifiedEndpoints : Array (Array String) := #[]
  let mut certifiedFormationArguments : Array (Array String) := #[]
  let mut certifiedTransportPaths : Array (Array String) := #[]
  let mut certifiedRepresentativeRefutations : Array (Array String) := #[]
  let mut certifiedSites := 0
  let mut matchedUnique : NameSet := {}
  let mut axiomUnique : NameSet := {}
  let mut withAxiomsUnique : NameSet := {}
  let mut rows := #[]
  let mut matchingNames := 0
  let mut originalTypes := 0
  let mut directAxioms := 0
  let mut withAxioms := 0
  let mut nativeByModule := #[]
  let mut allNative := #[]
  if let some file := gaps then
    file.putStrLn "module\tdeclaration\tkind\tunsafe\tpartial\tupstreamAxioms\timpliesAxiom\treductionWitness\tlogicalConsequence\tlogicalConsequenceWitness\trequiredBehavior\tabstractedDependency\truntimeConflictWitness\tequationOperand\toperandImpliesAxiom\toperandReductionWitness\tunchangedTypeAxioms\tunsafePackedObservation\tspecializedEndpointType\tunconditionalLogicalConsequence\tunconditionalLogicalConsequenceWitness\tstrictConstructorIff\tformationArgument\ttransportPathType\tpinnedLiftCoherenceRefuter\trepresentativeRefuter\trefinedQuotientConsequence\toriginalTypeGap"
  for owner in modules do
    let some idx := visible.getModuleIdx? owner | throwError "missing official module {owner}"
    let publicNames := visible.header.moduleData[idx]!.constNames.filter publicName
    let some privateIdx := official.getModuleIdx? owner | throwError "missing private module {owner}"
    let infos ← if publicNames.any duplicateNames.contains then do
      -- Load this defining file directly. The combined environment may select a different
      -- module's declaration with the same name.
      let path := modToFilePath lib owner "olean"
      let parts ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
      pure (parts.map (·.1))[2]!.constants
    else pure official.header.moduleData[privateIdx]!.constants
    let localDecls : NameMap ConstantInfo := infos.foldl (fun m c => m.insert c.name c) {}
    let localAxioms := exportedAxiomsExt.getModuleEntries official privateIdx
    let expected := owner.replacePrefix `Init `OmegaInit
    let strictIdx := strict.getModuleIdx? expected
    let publicStrict : NameMap ConstantInfo := strictIdx.elim {} fun i =>
      strict.header.moduleData[i]!.constants.foldl (fun acc ci => acc.insert ci.name ci) {}
    let strictLocal : NameMap ConstantInfo ← match full.getModuleIdx? expected with
      | none => pure {}
      | some i => do
        let defs ← if publicNames.any duplicateNames.contains then do
          let path := modToFilePath strictDir expected "olean"
          let parts ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
          pure (parts.map (·.1))[2]!.constants
        else pure full.header.moduleData[i]!.constants
        pure (defs.foldl (fun m c => m.insert c.name c) {})
    let officialSigs := nativeSignatures visible idx
    let strictSigs := (strictIdx.map (nativeSignatures strict)).getD {}
    let mut moduleNative : Array NativeSite := #[]
    for name in publicNames.qsort Name.lt do
      let some info := localDecls.find? name | throwError "missing declaration {owner}/{name}"
      let some (_, axioms) := localAxioms.binSearch (name, #[]) (fun a b => Name.quickLt a.1 b.1)
        | throwError "missing official axiom closure for {owner}/{name}"
      let typeAxioms ← checkedTypeAxioms official info axioms
      let kernelReductionAxiom ← if owner == `Init.Prelude && name == `unsafeCast then
        some <$> OmegaChecks.InitInventory.UnsafeCast.reductionAxiom official
      else if owner == `Init.ShareCommon && name == `ShareCommon.StateFactory.get then
        some <$> OmegaChecks.InitInventory.UnsafeCast.factoryReductionAxiom official witnesses
      else if owner == `Init.Data.ByteArray.Basic && [`ByteArray.forInUnsafe.loop, `ByteArray.foldlMUnsafe.fold].contains name then
        some <$> (OmegaChecks.InitBoundaries.ByteArrayReads.readAxiom witnesses info).run'
      else pure none
      let constructorIff := OmegaChecks.InitInventory.hasStrictConstructorIff official full info
      let operand := OmegaChecks.InitBoundaries.ChoiceOperands.operand? owner info
      let endpointType : Option String ← match operand with
        | some op => do
          if !OmegaChecks.InitBoundaries.ChoiceOperands.hasChoiceEndpoints owner info then pure none
          else
            let certify := OmegaChecks.InitBoundaries.ChoiceOperands.certifyEndpoints official info op
            (Meta.MetaM.run' certify).toIO' {fileName := "<official equality endpoints>", fileMap := default} {env := witnesses}
            pure (some "Classical.choice")
        | none => pure none
      if endpointType.isSome then
        if let some op := operand then
          certifiedEndpoints := certifiedEndpoints.push #[owner.toString, name.toString, op.name.toString, op.witness.toString]
      let fixFormation := operand.filter (OmegaChecks.InitBoundaries.ChoiceOperands.isFixFormation owner info)
      let conditional := fixFormation.map (fun op => ((``Classical.choice).toString, op.witness,
        "The pinned type forms the complete unrestricted fixed-point operator before using the termination premise")) <|>
        OmegaChecks.InitInventory.conditionalConsequence? owner name
      let transportPath ← if owner == `Init.Core && [``Quot.rec, ``Quot.recOn, ``Quotient.rec, ``Quotient.recOn].contains name then do
        let setoid := name.getPrefix == ``Quotient
        let pointFirst := [``Quot.recOn, ``Quotient.recOn].contains name
        let certify := OmegaChecks.InitBoundaries.HeterogeneousQuotient.certifyTransportPath official info setoid pointFirst
        (Meta.MetaM.run' certify).toIO' {fileName := "<official quotient transport>", fileMap := default} {env := witnesses}
        let path := if setoid then ``Quotient.sound else ``Quot.sound
        certifiedTransportPaths := certifiedTransportPaths.push #[owner.toString, name.toString, path.toString]
        pure (some path.toString)
      else pure none
      let liftOperand ← if OmegaChecks.InitBoundaries.EnvelopeCancellation.liftOperation? owner name == some name then do
        let proof := ``OmegaChecks.InitBoundaries.RepresentativeQuotient.refuteEnvelopeCancellation
        OmegaChecks.InitBoundaries.RepresentativeQuotient.certify official witnesses info proof
        pure (some proof.toString)
      else pure none
      let refinedModel := OmegaChecks.InitBoundaries.RefinedQuotient.sites.contains (owner, name)
      if refinedModel then
        OmegaChecks.InitBoundaries.RefinedQuotient.certify official witnesses owner info
      let refutedStatement := if transportPath == some "Quotient.sound" then ``Quotient.sound else name
      let refuter := OmegaChecks.InitBoundaries.RepresentativeQuotient.refuter? owner refutedStatement
      if let some proof := refuter then
        let some statement := localDecls.find? refutedStatement
          | throwError "missing definition site for {refutedStatement}"
        OmegaChecks.InitBoundaries.RepresentativeQuotient.certify official witnesses statement proof
        certifiedRepresentativeRefutations := certifiedRepresentativeRefutations.push
          #[owner.toString, name.toString, refutedStatement.toString, proof.toString]
      let formationArgument ← if owner == `Init.Core && name == ``Quot.liftIndepPr1 then do
        let certify := OmegaChecks.InitBoundaries.HeterogeneousQuotient.certifyLiftArgument official info
        (Meta.MetaM.run' certify).toIO' {fileName := "<official quotient lift argument>", fileMap := default} {env := witnesses}
        certifiedFormationArguments := certifiedFormationArguments.push #[owner.toString, name.toString,
          (``Quot.indepCoherent).toString, (``Quot.sound).toString,
          (``OmegaChecks.InitBoundaries.HeterogeneousQuotient.soundOfLiftArgument).toString]
        pure (some (``Quot.indepCoherent).toString)
      else if owner == `Init.Internal.Order.While && name == `Lean.Loop.forIn.eq_1 then do
        let certify := OmegaChecks.InitBoundaries.ChoiceOperands.checkLoopEndpoint visible info
        (Meta.MetaM.run' certify).toIO' {fileName := "<public loop endpoint>", fileMap := default} {env := visible}
        certifiedFormationArguments := certifiedFormationArguments.push #[owner.toString, name.toString,
          (``Lean.Loop.forIn).toString, (``Classical.choice).toString,
          (``OmegaChecks.InitBoundaries.WhileChoice.choiceFromLoop).toString]
        pure (some (``Lean.Loop.forIn).toString)
      else if let some op := fixFormation then do
        let certify := OmegaChecks.InitBoundaries.ChoiceOperands.checkFixFormation visible info op
        (Meta.MetaM.run' certify).toIO' {fileName := "<fixed-point endpoint>", fileMap := default} {env := witnesses}
        certifiedFormationArguments := certifiedFormationArguments.push #[owner.toString, name.toString,
          op.name.toString, (``Classical.choice).toString, op.witness.toString]
        pure (some op.name.toString)
      else pure none
      let direct := (logicalConsequence? owner name).map (fun (target, witness) => (target.toString, witness))
      let consequence := conditional.map (fun (target, witness, _) => (target, witness)) <|> direct
      let behavior := conditional.map (fun (_, _, premise) => premise)
      let additional := if conditional.isSome then direct else none
      let runtimeConflict : Option String := do
        guard (info.isUnsafe && observedRuntime.contains name.toString)
        let some ("False", witness, _) := conditional | none
        return witness.toString
      let packedObservation := if observedPacked.contains name.toString then
        some "Observed different native results on equal nested lists packed as NonScalar by unsafeCast"
      else none
      let boundary := boundaries[(owner, name)]?
      let selector := if boundary.isSome && OmegaChecks.InitBoundaries.OptionSelector.usesSelector owner name then
        some (``Option.choice).toString else none
      if boundary.isSome then certifiedSites := certifiedSites + 1
      let strictName := if OmegaChecks.InitCompiler.RootNames.isPrimitive expected name then name else `Omega ++ name
      let publicInfo := publicStrict.find? strictName
      let matched := publicInfo.isSome
      let strictInfo ← if matched then do
        let some dst := strictLocal.find? strictName | throwError "missing strict implementation {expected}/{strictName}"
        pure (some dst)
      else pure none
      let observer := (owner == `Init.Util && [`isExclusiveUnsafe, `ptrAddrUnsafe].contains name) ||
        (owner == `Init.ShareCommon && [`ShareCommon.Object.eq, `ShareCommon.Object.hash].contains name)
      let checkedUnsafeRuntime ← if matched && observer then do
        let some dst := full.find? strictName | throwError "missing private observation {strictName}"
        let some symbol := OmegaChecks.InitPort.UnsafeRuntime.observerSymbol? official owner name false
          | throwError "unexpected pinned observation ABI for {name}"
        unless (strict.find? strictName).any (·.isUnsafe) && officialSigs.contains name &&
            strictSigs.contains strictName && OmegaChecks.InitPort.UnsafeRuntime.isOriginal info false &&
            OmegaChecks.InitPort.UnsafeRuntime.isOriginal dst true &&
            OmegaChecks.InitPort.UnsafeRuntime.observerSymbol? full owner name true == some symbol do
          throwError "invalid public, private or native observation {strictName}"
        pure (some symbol)
      else pure none
      let pointerComparison := matched && OmegaChecks.InitPort.PointerComparison.names.contains name &&
        owner == (if name == `ShareCommon.Object.ptrEq then `Init.ShareCommon else `Init.Util)
      if pointerComparison then
        let some dst := full.find? strictName | throwError "missing pointer comparison body {strictName}"
        unless (strict.find? strictName).any (·.isUnsafe) && officialSigs.contains name && strictSigs.contains strictName &&
            OmegaChecks.InitPort.PointerComparison.isOriginal info false && OmegaChecks.InitPort.PointerComparison.isOriginal dst true &&
            OmegaChecks.InitPort.PointerComparison.hasBorrowedABI official name false &&
            OmegaChecks.InitPort.PointerComparison.hasBorrowedABI full name true do
          throwError "invalid public, private or native pointer comparison {strictName}"
      let addressCallback := matched && owner == `Init.Util && name == OmegaChecks.InitPort.Address.name
      if addressCallback then
        let some dst := full.find? strictName | throwError "missing address callback {strictName}"
        unless (strict.find? strictName).any (·.isUnsafe) && officialSigs.contains name && strictSigs.contains strictName &&
            OmegaChecks.InitPort.Address.isOriginal info false && OmegaChecks.InitPort.Address.isOriginal dst true &&
            OmegaChecks.InitPort.Address.hasBorrowedABI official false && OmegaChecks.InitPort.Address.hasBorrowedABI full true do
          throwError "invalid public, private or native address callback {strictName}"
      let pointerHash := matched && owner == `Init.ShareCommon && name == OmegaChecks.InitPort.PointerHash.name
      if pointerHash then
        let some dst := full.find? strictName | throwError "missing pointer hash body {strictName}"
        unless (strict.find? strictName).any (·.isUnsafe) && officialSigs.contains name && strictSigs.contains strictName &&
            OmegaChecks.InitPort.PointerHash.isOriginal info false && OmegaChecks.InitPort.PointerHash.isOriginal dst true &&
            OmegaChecks.InitPort.PointerHash.checkABI official false && OmegaChecks.InitPort.PointerHash.checkABI full true do
          throwError "invalid public, private or native pointer hash {strictName}"
      let effectRunner := matched && owner == `Init.System.IO && OmegaChecks.InitPort.EffectRun.names.contains name
      if effectRunner then
        let some dst := full.find? strictName | throwError "missing effect runner body {strictName}"
        unless (strict.find? strictName).any (·.isUnsafe) && officialSigs.contains name &&
            strictSigs.contains strictName && OmegaChecks.InitPort.EffectRun.isOriginal info false &&
            OmegaChecks.InitPort.EffectRun.isOriginal dst true do
          throwError "invalid public, private or native effect runner {strictName}"
        if name == `unsafeBaseIO then OmegaChecks.InitPort.EffectRun.checkWorld full.toKernelEnv
      let strictOwner := if matched then some expected else none
      let typeGap ← match publicInfo with
        | some dst => OmegaChecks.InitInventory.originalTypeGap? official visible strict owner info dst witnesses
        | none => pure none
      let typeGap := typeGap.map fun gap =>
        match OmegaChecks.InitInventory.searchLoopParameter? official visible strict full info with
        | some detail => gap ++ ". " ++ detail
        | none => gap
      if matched && typeGap.isNone then originalTypes := originalTypes + 1
      if matched then
        matchingNames := matchingNames + 1
        matchedUnique := matchedUnique.insert name
      if (!matched || typeGap.isSome) && !info.isAxiom then
        if let some file := gaps then
          file.putStrLn <| String.intercalate "\t" [owner.toString, name.toString,
            declarationKind info, toString info.isUnsafe, toString info.isPartial,
            String.intercalate "," (axioms.toList.map Name.toString),
            (boundary.map (·.1.toString)).getD "", (boundary.map (·.2.toString)).getD "",
            (consequence.map Prod.fst).getD "", (consequence.map (·.2.toString)).getD "", behavior.getD "",
            selector.getD "", runtimeConflict.getD "", (operand.map (·.name.toString)).getD "",
            (operand.map fun _ => (``Classical.choice).toString).getD "", (operand.map (·.witness.toString)).getD "",
            String.intercalate "," (typeAxioms.toList.map Name.toString), packedObservation.getD "", endpointType.getD "",
            (additional.map Prod.fst).getD "", (additional.map (·.2.toString)).getD "", if constructorIff then "true" else "",
            formationArgument.getD "", transportPath.getD "", liftOperand.getD "", (refuter.map Name.toString).getD "",
            if refinedModel then "The pinned operations in the refined interpretation imply Not (type of Quot.sound.{1})" else "",
            typeGap.getD ""]
      if info.isAxiom then
        directAxioms := directAxioms + 1
        axiomUnique := axiomUnique.insert name
      if !axioms.isEmpty then
        withAxioms := withAxioms + 1
        withAxiomsUnique := withAxiomsUnique.insert name
      let reduction := if matched then reductions.get? strictName else none
      let row := Json.mkObj [
        ("name", toJson name.toString), ("module", toJson owner.toString),
        ("kind", toJson (declarationKind info)), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
        ("matchingNameAndModule", toJson matched),
        ("originalTypeChecked", toJson (matched && typeGap.isNone)), ("originalTypeGap", toJson typeGap),
        ("strictUnsafe", toJson (strictInfo.map (·.isUnsafe))), ("strictPartial", toJson (strictInfo.map (·.isPartial))),
        ("publicReductionBoundary", toJson ((reduction.map Prod.fst).getD []).toArray),
        ("officialReductionMechanism", toJson (reduction.map Prod.snd)),
        ("axioms", toJson (axioms.map Name.toString)),
        ("impliesAxiom", toJson (boundary.map (·.1.toString))),
        ("reductionWitness", toJson (boundary.map (·.2.toString))),
        ("strictModule", toJson (strictOwner.map Name.toString))]
      let row ← if officialSigs.contains name && info.hasValue (allowOpaque := true) then do
        let hasSig := matched && strictSigs.contains strictName
        moduleNative := moduleNative.push ⟨matched, hasSig⟩
        pure (row.setObjVal! "strictNativeSignature" (toJson hasSig))
      else pure row
      let row := if refinedModel then row.setObjVal! "refinedQuotientConsequence"
        (toJson "The pinned operations in the refined interpretation imply Not (type of Quot.sound.{1})") else row
      let row := if let some proof := liftOperand then row.setObjVal! "pinnedLiftCoherenceRefuter" (toJson proof) else row
      let row := if let some proof := refuter then row.setObjVal! "representativeRefuter" (toJson proof.toString) else row
      let row := if let some path := transportPath then row.setObjVal! "transportPathType" (toJson path) else row
      let row := if let some argument := formationArgument then row.setObjVal! "formationArgument" (toJson argument) else row
      let row := if constructorIff then row.setObjVal! "strictConstructorIff" (toJson true) else row
      let row := if typeAxioms.isEmpty then row else
        row.setObjVal! "unchangedTypeAxioms" (toJson (typeAxioms.map Name.toString))
      let row := match selector with
        | some dep => row.setObjVal! "abstractedDependency" (toJson dep)
        | none => row
      let row := match operand with
        | some op => row.mergeObj <| Json.mkObj [("equationOperand", toJson op.name.toString),
            ("operandImpliesAxiom", toJson (``Classical.choice).toString), ("operandReductionWitness", toJson op.witness.toString)]
        | none => row
      let row := if let some target := endpointType then row.setObjVal! "specializedEndpointType" (toJson target) else row
      let row := if addressCallback then row.setObjVal! "checkedAddressCallback" (toJson true) else row
      let row := if let some ax := kernelReductionAxiom then row.setObjVal! "kernelReductionAxiom" (toJson ax.toString) else row
      let row := if pointerHash then row.setObjVal! "checkedPointerHash" (toJson true) else row
      let row := if pointerComparison then row.setObjVal! "checkedPointerComparison" (toJson true) else row
      let row := if effectRunner then row.setObjVal! "checkedEffectRunner" (toJson true) else row
      let row := match checkedUnsafeRuntime with
        | some entry => row.setObjVal! "checkedUnsafeRuntime" (toJson entry)
        | none => row
      let row := match packedObservation with
        | some observation => row.setObjVal! "unsafePackedObservation" (toJson observation)
        | none => row
      let row := match runtimeConflict with
        | some witness => row.setObjVal! "runtimeConflictWitness" (toJson witness)
        | none => row
      let row := match additional with
        | some (target, witness) => row.mergeObj <| Json.mkObj [
            ("unconditionalLogicalConsequence", toJson target), ("unconditionalLogicalConsequenceWitness", toJson witness.toString)]
        | none => row
      rows := rows.push <| match consequence with
        | some (target, witness) => row.mergeObj <| Json.mkObj [
            ("logicalConsequence", toJson target), ("logicalConsequenceWitness", toJson witness.toString),
            ("requiredBehavior", toJson behavior)]
        | none => row
    allNative := allNative ++ moduleNative
    nativeByModule := nativeByModule.push (owner.toString, nativeSummary moduleNative)
  unless certifiedSites == boundaries.size do throwError "missing registered public definition site"
  let summary := Json.mkObj [("declarations", toJson rows.size), ("directAxioms", toJson directAxioms),
    ("withAxioms", toJson withAxioms), ("matchingNameAndModule", toJson matchingNames),
    ("originalTypesChecked", toJson originalTypes),
    ("native", nativeSummary allNative)]
  let unique := Json.mkObj [("declarations",toJson names.size), ("directAxioms",toJson axiomUnique.size),
    ("withAxioms",toJson withAxiomsUnique.size), ("matchingNameAndModule",toJson matchedUnique.size)]
  return Json.mkObj [("schemaVersion", toJson 6), ("uniqueNames", unique), ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("nativeByModule", Json.mkObj nativeByModule.toList), ("certifiedChoiceEndpoints", toJson certifiedEndpoints),
    ("certifiedRepresentativeRefutations", toJson certifiedRepresentativeRefutations),
    ("certifiedFormationArguments", toJson certifiedFormationArguments), ("certifiedTransportPaths", toJson certifiedTransportPaths),
    ("modules", toJson (modules.map Name.toString)), ("summary", summary), ("declarations", .arr rows)]

def main (args : List String) : IO Unit := do
  let strictDir :: outputPath :: rest := args | throw <| IO.userError "expected strict olean directory and output file"
  let gaps ← match rest with
    | [] => pure none
    | [path] =>
      if path == outputPath then throw <| IO.userError "inventory and gaps require distinct files"
      pure (some (← IO.FS.Handle.mk path .write))
    | _ => throw <| IO.userError "expected at most one gaps TSV file"
  let sysroot ← findSysroot
  initSearchPath sysroot
  let witnesses ← importModules #[
    {module := `OmegaChecks.InitInventory.ChoiceOperands}, {module := `OmegaChecks.InitInventory.Quotient},
    {module := `OmegaChecks.InitInventory.RefinedQuotient}, {module := `OmegaChecks.InitInventory.StateFactory},
    {module := `OmegaChecks.InitInventory.ByteArrayReads}, {module := `OmegaChecks.InitInventory.EnvelopeOrder},
    {module := `OmegaChecks.InitInventory.FieldNormalization}] {} (level := .private)
  let lib ← getLibDir sysroot
  searchPathRef.set [lib]
  let modules ← installedModules lib `Init
  let imports := modules.map fun mod => {module := mod : Import}
  let visible ← importModules imports {} (level := .exported)
  -- The public environment can replace a hidden body with an axiom-shaped entry.
  -- Use the private artifact for the original declaration kind and axiom dependencies.
  -- Load Lean's exported-axiom extension from the pinned toolchain so every query
  -- can use the dependency closure recorded by Lean when the module was compiled.
  unsafe enableInitializersExecution
  let official ← importModules imports {} (loadExts := true)
  searchPathRef.set [strictDir]
  let basis ← installedModules strictDir `OmegaInit
  let strictImports := basis.map fun mod => {module := mod : Import}
  let strict ← importModules strictImports {} (level := .exported)
  let full ← importModules strictImports {} (level := .private)
  if basis.contains `OmegaInit then
    OmegaChecks.InitBoundaries.FieldNormalization.FiniteStages.replay witnesses full
  for owner in strict.allImportedModuleNames do
    unless owner.getRoot == `OmegaInit do
      throw <| IO.userError s!"expected a strict OmegaInit build, found import {owner}"
  let pointers ← unsafe OmegaChecks.InitBoundaries.PointerObservations.observe modules.size
  let packed ← unsafe OmegaChecks.InitBoundaries.PointerObservations.observePacked modules.size
  let effects ← unsafe OmegaChecks.InitBoundaries.EffectObservations.observe modules.size
  -- Reference counts depend on argument ownership in native code. Run the borrowed call
  -- in a compiled executable so interpreter boxing cannot perturb the observed object.
  let native ← IO.Process.output {cmd := "lake", args := #["-q", "exe", "omegaPointerObservations", "--exclusivity"]}
  unless native.exitCode == 0 do throw <| IO.userError s!"native exclusivity observation failed: {native.stderr}"
  let observedRuntime ← match native.stdout.trimAscii.toString with
    | "true" => pure ("isExclusiveUnsafe" :: pointers ++ effects)
    | "false" => pure (pointers ++ effects)
    | other => throw <| IO.userError s!"unexpected native exclusivity observation: {other}"
  let result ← (inventory lib strictDir visible strict full witnesses modules gaps observedRuntime packed).toIO' {fileName := "<Init inventory>", fileMap := default} {env := official}
  IO.FS.writeFile outputPath (result.compress ++ "\n")
  IO.println (← IO.ofExcept (result.getObjVal? "summary")).compress
