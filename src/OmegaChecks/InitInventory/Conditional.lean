module

public import OmegaChecks.InitInventory.Reductions
public import OmegaChecks.InitInventory.Collector
public import OmegaChecks.InitInventory.OpenRangeLoop
public import OmegaChecks.InitInventory.RangeLoopLift
public import OmegaChecks.InitInventory.FieldNormalization
public import OmegaChecks.InitInventory.StringPatterns
public import OmegaChecks.InitInventory.StringSearchLoops
public import OmegaChecks.InitInventory.StringSplitLoops

open Lean
namespace OmegaChecks.InitInventory

/-- The conclusion uses the indicated semantic agreement in addition to the public type. -/
public def conditionalConsequence? (owner name : Name) : Option (String × Name × String) := do
  if owner == `Init.Data.Iterators.Combinators.Monadic.Take && name == `Std.Iterators.Types.Take.Rel.eq_1 then
    return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)",
      ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromTakeDecision,
      "The right side of the unfolding equation supplies a finiteness decision for every productive iterator")
  if owner == `Init.Data.Range.Polymorphic.RangeIterator && [``Std.Rxc.Iterator.instLawfulIteratorLoop,
      ``Std.Rxo.Iterator.instLawfulIteratorLoop, ``Std.Rxi.Iterator.instLawfulIteratorLoop].contains name then
    return ((``funext).toString, ``OmegaChecks.InitBoundaries.RangeLoopLift.funextFromTwoSteps,
      "On two successive outputs the optimized loop ignores its lift and the default loop performs both lawful identity-monad lifts with their pinned behavior")
  if owner == `Init.Data.Range.Polymorphic.RangeIterator && name == ``Std.Rxo.Iterator.instIteratorLoop.loop then
    return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)",
      ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromOpenRangeLoop,
      "For the natural successor and the comparison g k = false, the identity-monad loop satisfies its official step equation whenever the range is finite")
  if owner == `Init.Data.BitVec.Lemmas then
    if name == ``BitVec.getElem_of_getLsbD_eq_true then
      return ("(true = true) = True", ``OmegaChecks.InitBoundaries.BooleanReflection.successfulBitRead,
        "Index zero of the one-bit word 1 has successful getLsbD and bounded reads")
    if name == ``BitVec.getElem_extractLsb'_eq_decide_getElem then
      return ("(true = true) = (∃ _ : 0 < 1, true = true)", ``OmegaChecks.InitBoundaries.BooleanReflection.extractSingleBit,
        "Extracting one bit at offset zero from the one-bit word 1 preserves its set bit at index zero")
  if owner == `Init.Data.Option.Lemmas then
    let singletonLaw := match name with
      | ``Option.choice_eq_some => some ``OmegaChecks.InitBoundaries.OptionSelector.decideFromSingleton
      | ``Option.choice_eq_default => some ``OmegaChecks.InitBoundaries.OptionSelector.decideFromDefault
      | _ => none
    if let some witness := singletonLaw then
      return ("∀ p : Prop, Decidable p", witness,
        "The same option selector satisfies the stated singleton law on the type PLift p for every proposition p")
  if owner == `Init.Data.Order.Lemmas || owner == `Init.Data.Order.LemmasExtra then
    if name == ``Classical.Order.instLawfulOrderBEq then
      return ("∀ P : Prop, Decidable P", ``OmegaChecks.InitBoundaries.ClassicalOrderDecisions.fromLawfulBEq,
        "The translated equality constructor and its public lawful instance use the same BEq operation")
    if name == ``Classical.Order.instLawfulOrderOrd then
      return ("∀ P : Prop, Decidable P", ``OmegaChecks.InitBoundaries.ClassicalOrderDecisions.fromLawfulOrd,
        "The translated comparison constructor and the isLE_compare field of its public lawful instance use the same Ord operation")
    let observation := match owner, name with
      | `Init.Data.Order.Lemmas, ``Classical.Order.instBEq =>
        some (``OmegaChecks.InitBoundaries.ClassicalOrderDecisions.fromBEq, "beq true false is true")
      | `Init.Data.Order.Lemmas, ``Classical.Order.instMin =>
        some (``OmegaChecks.InitBoundaries.ClassicalOrderDecisions.fromMin, "min true false is true")
      | `Init.Data.Order.Lemmas, ``Classical.Order.instMax =>
        some (``OmegaChecks.InitBoundaries.ClassicalOrderDecisions.fromMax, "max true false is true")
      | `Init.Data.Order.LemmasExtra, ``Classical.Order.instOrd =>
        some (``OmegaChecks.InitBoundaries.ClassicalOrderDecisions.fromOrd, "compare true false is Ordering.eq")
      | _, _ => none
    if let some (proof, result) := observation then
      return ("∀ P : Prop, Decidable P", proof,
        s!"When x ≤ y on Bool is the constant proposition P, {result} exactly when P holds")
  if owner == `Init.Grind.Ring.Field || owner == `Init.Grind.FieldNormNum then
    let quotient := "The field construction uses propext and Quot.sound"
    let entry := match name with
      | ``Lean.Grind.Field.inv_mul => some (``OmegaChecks.InitBoundaries.FieldNormalization.inverseProduct, quotient)
      | ``Lean.Grind.Field.inv_neg => some (``OmegaChecks.InitBoundaries.FieldNormalization.inverseNegative, quotient)
      | ``Lean.Grind.Field.of_mul_eq_zero => some (``OmegaChecks.InitBoundaries.FieldNormalization.productZero, quotient)
      | ``Lean.Grind.Field.of_pow_eq_zero => some (``OmegaChecks.InitBoundaries.FieldNormalization.powerZero, quotient)
      | ``Lean.Grind.Field.div_div_left => some (``OmegaChecks.InitBoundaries.FieldNormalization.divideLeft, quotient)
      | ``Lean.Grind.Field.div_div_right => some (``OmegaChecks.InitBoundaries.FieldNormalization.divideRight, quotient)
      | `Lean.Grind.Field.NormNum.ofRat_inv => some (``OmegaChecks.InitBoundaries.FieldNormalization.inverse, quotient)
      | `Lean.Grind.Field.NormNum.inv_eq => some (``OmegaChecks.InitBoundaries.FieldNormalization.verifyInv, quotient)
      | `Lean.Grind.Field.NormNum.ofRat_div' => some (``OmegaChecks.InitBoundaries.FieldNormalization.divide, quotient ++ " and the rational division computes 1 / (3/2) = 2/3")
      | `Lean.Grind.Field.NormNum.ofRat_zpow' => some (``OmegaChecks.InitBoundaries.FieldNormalization.power, quotient ++ " and the rational integer power computes (2/3)^(-1) = 3/2")
      | _ => none
    if let some (witness, assumptions) := entry then
      return ("∀ P : Prop, ¬¬ P → P", witness, assumptions)
  if owner == `Init.Data.ByteArray.Basic then
    if name == `ByteArray.forInUnsafe.loop then
      return ("False", ``OmegaChecks.InitBoundaries.ByteArrayReads.noForInBound,
        "The uget read has an in-bounds index whenever i < sz for the independently supplied sz")
    if name == `ByteArray.foldlMUnsafe.fold then
      return ("False", ``OmegaChecks.InitBoundaries.ByteArrayReads.noFoldBranchBound,
        "The uget read has an in-bounds index whenever i differs from the independently supplied stop")
  if owner == `Init.Data.Array.Basic && [`Array.mapMUnsafe, `Array.mapFinIdxMUnsafe].contains name then
    let witness := if name == `Array.mapMUnsafe then ``OmegaChecks.InitBoundaries.ArrayCasts.map
      else ``OmegaChecks.InitBoundaries.ArrayCasts.mapIndexed
    return ("False", witness,
      "On Array Unit with word length zero and a callback returning none : Option Empty, the zero-step exit returns some output of the original natural length")
  if owner == `Init.Data.List.ToArray || owner == `Init.Data.Array.Lemmas then
    let entry := match owner, name with
      | `Init.Data.List.ToArray, ``List.findM?_toArray
      | `Init.Data.Array.Lemmas, ``Array.findM?_toList =>
        some (``OmegaChecks.InitBoundaries.MonadicTraversal.SingletonSearch.BoolFusion,
          ``OmegaChecks.InitBoundaries.MonadicTraversal.SingletonSearch.boolOfSingleton)
      | `Init.Data.List.ToArray, ``List.findSomeM?_toArray
      | `Init.Data.Array.Lemmas, ``Array.findSomeM?_toList =>
        some (``OmegaChecks.InitBoundaries.MonadicTraversal.SingletonSearch.OptionFusion,
          ``OmegaChecks.InitBoundaries.MonadicTraversal.SingletonSearch.optionOfSingleton)
      | _, _ => none
    if let some (target, witness) := entry then
      return (target.toString, witness,
        "On the singleton Unit input the array traverses one ForInStep and the list branches directly on the predicate result")
  if owner == `Init.Data.Array.Monadic && [``Array.foldlM_subtype, ``Array.foldrM_subtype].contains name then
    let witness := if name == ``Array.foldlM_subtype then ``OmegaChecks.InitBoundaries.MonadicTraversal.fromListFoldl
      else ``OmegaChecks.InitBoundaries.MonadicTraversal.fromListFoldr
    return ((``funext).toString, witness,
      "A full array fold agrees with the underlying list fold, and unattach preserves the size and projects that list")
  if owner == `Init.Data.List.Monadic && name == ``List.forIn'_loop_congr then
    return ((``funext).toString, ``OmegaChecks.InitBoundaries.ArrayLoopCongruence.listForInCongr,
      "The whole-list traversal starts its auxiliary loop on the full input with the empty prefix")
  if owner == `Init.Data.Fin.Fold then
    let witness ← match name with
      | ``Fin.foldlM_succ_last | ``Fin.foldrM_succ =>
        some ``OmegaChecks.InitBoundaries.TransformerLaws.FiniteFold.funextOfMoveUnit
      | ``Fin.foldlM_add | ``Fin.foldrM_add =>
        some ``OmegaChecks.InitBoundaries.TransformerLaws.FiniteFold.funextOfRepeatUnit
      | _ => none
    return ((``funext).toString, witness,
      "The zero-step fold is pure and the one-step fold binds its callback to pure, as in the pinned zero and successor equations")
  if owner == `Init.Grind.Ring.Envelope || owner == `Init.Grind.Module.Envelope then
    if name == ``Lean.Grind.Ring.OfSemiring.instLEQOfOrderedAdd ||
        name == ``Lean.Grind.IntModule.OfNatModule.instLEQOfOrderedAdd then
      let witness := if owner == `Init.Grind.Ring.Envelope then ``OmegaChecks.InitBoundaries.EnvelopeOrder.propextFromRingOrder
        else ``OmegaChecks.InitBoundaries.EnvelopeOrder.propextFromModuleOrder
      return ((``propext).toString, witness,
        "Over the two-element field, envelope cancellation identifies the diagonal with zero and the proposed order computes both off-diagonal comparisons in the translated preorder")
    let target := (``funext).toString
    if name == ``Lean.Grind.Ring.OfSemiring.neg_add_cancel ||
        name == ``Lean.Grind.IntModule.OfNatModule.neg_add_cancel then
      return (target, ``OmegaChecks.InitBoundaries.Envelope.funextFromCancellation,
        "On the Boolean additive monoid, negation swaps (true,false) and addition of the swapped and original representatives yields (true,true), with zero represented by (false,false)")
    let witness ← match name with
      | ``Lean.Grind.Ring.OfSemiring.ofSemiring => some ``OmegaChecks.InitBoundaries.Envelope.funextFromEnvelopeRing
      | ``Lean.Grind.CommRing.OfCommSemiring.ofCommSemiring => some ``OmegaChecks.InitBoundaries.Envelope.funextFromEnvelopeCommRing
      | ``Lean.Grind.IntModule.OfNatModule.ofNatModule => some ``OmegaChecks.InitBoundaries.Envelope.funextFromEnvelopeIntModule
      | _ => none
    return (target, witness,
      "On the Boolean additive monoid, the proposed structure computes the official negation on (true,false), addition of the swapped and original representatives, and zero")
  if owner == `Init.ShareCommon && name == ``ShareCommon.StateFactory.get then
    return ("False", ``OmegaChecks.InitBoundaries.FactoryCarriers.noGetCast,
      "The pinned reader casts its lifted small factory type to the lifted type of all implementations")
  if owner == `Init.ShareCommon && [``ShareCommon.StateFactory.mk, ``ShareCommon.StateFactory.mkImpl].contains name then
    return ("False", ``OmegaChecks.InitBoundaries.FactoryCarriers.noCarrierEmbedding,
      "Packing and decoding each constant-map builder jointly preserve an injection from its supplied map carrier into its decoded Map type")
  if owner == `Init.System.ST then
    if name == ``ST.mkRef || name == ``ST.Prim.mkRef then
      let witness := if name == ``ST.mkRef then ``OmegaChecks.InitBoundaries.ReferenceRoundTrip.alloc
        else ``OmegaChecks.InitBoundaries.ReferenceRoundTrip.primAlloc
      return ("False", witness,
        "Reading the handle in the world returned by allocation recovers every stored callback on reference addresses and worlds")
    if name == ``ST.Ref.set || name == ``ST.Prim.Ref.set then
      let witness := if name == ``ST.Ref.set then ``OmegaChecks.InitBoundaries.ReferenceRoundTrip.set
        else ``OmegaChecks.InitBoundaries.ReferenceRoundTrip.primSet
      return ("False", witness,
        "Reading the same handle in the world returned by a write recovers every stored callback on reference addresses and worlds")
    if name == ``ST.Ref.modify || name == ``ST.Prim.Ref.modify then
      let witness := if name == ``ST.Ref.modify then ``OmegaChecks.InitBoundaries.ReferenceRoundTrip.modify
        else ``OmegaChecks.InitBoundaries.ReferenceRoundTrip.primModify
      return ("False", witness,
        "Reading the same handle in the world returned by a constant update recovers every stored callback on reference addresses and worlds")
  if owner == `Init.Dynamic && [``Dynamic.mk, ``Dynamic.get?].contains name then
    return ("False", ``OmegaChecks.InitBoundaries.DynamicRoundTrip.noRoundTrip,
      "The total writer and reader jointly recover every stored callback from Dynamic to Bool using the same monomorphic type tag")
  if owner == `Init.Prelude && [``Lean.Macro.mkMethods, ``Lean.Macro.mkMethodsImp,
      ``Lean.Macro.getMethods, ``Lean.Macro.getMethodsImp].contains name then
    return ("False", ``OmegaChecks.InitBoundaries.MacroReferences.noQueryRoundTrip,
      "The total packer and reader jointly preserve hasDecl for every Boolean callback on the packed reference in its own macro context")
  if owner == `Init.Util then
    if name == ``isExclusiveUnsafe then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.exclusivity,
        "Native exclusivity distinguishes a freshly allocated singleton array from a persistent literal with the same element")
    if name == ``ptrAddrUnsafe then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.address,
        "Native addresses distinguish two simultaneously live equal lists")
    if name == ``ptrEq then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.pointerEquality,
        "Native pointer identity distinguishes an alias from an equal, separately allocated list")
    if name == ``withPtrEqUnsafe then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.guardedPointerEquality,
        "Distinct erased type tags permit a constant false callback, but aliasing an equal list field changes the native result from false to true")
    if name == ``withPtrEqDecEq then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.guardedPointerDecision,
        "The native equality decision returns true for distinct erased type tags whose list fields alias")
    if name == ``ptrEqList then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.listPointerEquality,
        "Elementwise pointer identity distinguishes singleton lists containing equal allocations")
  if owner == `Init.System.IO then
    let witness ← match name with
      | `unsafeBaseIO => some ``OmegaChecks.InitBoundaries.EffectObservations.base
      | `unsafeEIO => some ``OmegaChecks.InitBoundaries.EffectObservations.eio
      | `unsafeIO => some ``OmegaChecks.InitBoundaries.EffectObservations.io
      | _ => none
    return ("False", witness, "The same read action returns n and n+1 around an update to its reference cell")
  if owner == `Init.ShareCommon then
    if name == ``ShareCommon.Object.eq then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.packedPayloadEquality,
        "A pure packing of nested lists preserves native payload comparison on an alias and an equal list with a separately allocated child")
    if name == ``ShareCommon.Object.hash then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.packedPayloadHash,
        "A pure packing of nested lists preserves native payload hashes on equal lists with separately allocated children")
    if name == ``ShareCommon.Object.ptrEq then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.objectPointerEquality,
        "Pointer identity distinguishes an alias from a separately allocated NonScalar with the same Nat field")
    if name == ``ShareCommon.Object.ptrHash then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.objectPointerHash,
        "Pointer hashes distinguish two simultaneously live NonScalar objects with the same Nat field")
  if owner == `Init.Classical && (OmegaChecks.InitBoundaries.ClassicalDecisionEquations.rules.lookup name).isSome then
    return ((``Classical.em).toString, ``OmegaChecks.InitBoundaries.ClassicalConsequences.ofDecidableNot,
      "The right-hand side supplies a decision for p from a decision for its negation at every proposition")
  if owner == `Init.Core && name == ``Quot.liftIndepPr1 then
    return ((``Quot.sound).toString, ``OmegaChecks.InitBoundaries.HeterogeneousQuotient.soundOfLiftArgument,
      "The first projection in the original statement requires the lift's coherence argument at the constant unit motive")
  if owner == `Init.Core && name == ``Quotient.decidableEq then
    return ((``funext).toString, ``OmegaChecks.InitBoundaries.QuotientDecision.funextOfPositiveDecision,
      "The official equality decision computes true on the false and true representatives of the indiscrete Boolean quotient")
  if owner == `Init.Core && name == ``Quot.hrecOn then
    return ((``Quot.sound).toString, ``OmegaChecks.InitBoundaries.HeterogeneousQuotient.soundOfPairCoherence,
      "The pinned reduction through Quot.indep identifies pairs of related representatives at the unit motive")
  if owner == `Init.Core && name == ``Quotient.hrecOn then
    return ((``Quotient.sound).toString, ``OmegaChecks.InitBoundaries.HeterogeneousQuotient.setoidSoundOfPairCoherence,
      "The pinned reduction through Quot.indep identifies pairs of setoid-related representatives at the unit motive")
  if owner == `Init.Core && name == ``instDecidableEqOfIff then
    return ((``propext).toString, ``OmegaChecks.InitBoundaries.ConstructorNormalization.propextOfDecision,
      "A positive decision of p ↔ q produces a positive decision of p = q")
  if owner == `Init.Data.Option.Lemmas && [``Option.getD_choice, ``Option.get!_choice].contains name then
    let witness := if name == ``Option.getD_choice then ``OmegaChecks.InitBoundaries.OptionSelector.fromGetD
      else ``OmegaChecks.InitBoundaries.OptionSelector.fromGetBang
    return ((``Classical.choice).toString, witness,
      "The right-hand Option.get retains its proof of presence for the public selector and satisfies the stated equality")
  if owner == `Init.Data.Option.Lemmas && name == ``Option.choice then
    return ((``Classical.choice).toString, ``OmegaChecks.InitBoundaries.OptionSelector.fromSome,
      "For every nonempty type, the selector returns some, as specified by Option.isSome_choice")
  if owner == `Init.Internal.Order.Basic then
    if name == ``Lean.Order.Example.find then
      return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)",
        ``OmegaChecks.InitBoundaries.InternalOrder.limitedOmniscienceOfSearch,
        "The search follows find_eq and every returned index satisfies the predicate as in find_spec")
    if name == ``Lean.Order.instCompleteLatticePi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfCompletePointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed complete lattice")
    if name == ``Lean.Order.instCCPOPi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfChainCompletePointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed chain-complete order")
    if name == ``Lean.Order.instPartialOrderReaderT then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfReaderOrder,
        "For Id with the equality order, pointwise equal reader functions are related as in the pinned instance")
    if name == ``Lean.Order.instPartialOrderStateT then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfStateOrder,
        "For the constant family with the equality order, pointwise equal state functions are related as in the pinned instance")
    if name == ``Lean.Order.instOrderPi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfPointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed order")
    if let some witness := OmegaChecks.InitBoundaries.InternalOrder.implicationOrders.lookup name then
      return ((``propext).toString, witness,
        "Every pair related by the pinned instance's rel field is also related by the replacement")
    if name == ``Lean.Order.flat_csup then
      return ((``Classical.choice).toString, ``OmegaChecks.InitBoundaries.InternalOrder.choiceFromFlatPresence,
        "For nonempty α and the universal predicate on Option α with bottom none, the result has tag some, as in the pinned definition")
  if owner == `Init.Data.String.Slice then
    let witness := match name with
      | ``String.Slice.SplitIterator.instIteratorLoopIdSubsliceOfMonad =>
        some ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromSplitLoop
      | ``String.Slice.SplitInclusiveIterator.instIteratorLoopIdOfMonad =>
        some ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromInclusiveSplitLoop
      | ``String.Slice.RevSplitIterator.instIteratorLoopOfMonad =>
        some ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromReverseSplitLoop
      | _ => none
    if let some witness := witness then
      return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)", witness,
        "The identity-monad split loop is lawful on finite searchers, including repeated zero-width matches")
  if owner == `Init.Data.String.Pattern.Basic then
    if name == ``String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorLoopIdSearchStep then
      return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)",
        ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromForwardSearchLoop,
        "The forward search loop agrees with the default on every well-founded callback, including zero-width matches")
    if name == ``String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorLoopIdSearchStep then
      return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)",
        ``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromBackwardSearchLoop,
        "The backward search loop agrees with the default on every well-founded callback, including zero-width matches")
  if owner == `Init.Data.String.Lemmas.Pattern.Basic then
    if name == ``String.Slice.Pattern.Model.matchAt? then
      return ("∀ P : Prop, Decidable P", `OmegaChecks.InitInventory.StringPatterns.decidableOfForwardResult,
        "The matcher returns some b at a iff IsLongestMatchAt pat a b (matchAt?_eq_some_iff)")
    if name == ``String.Slice.Pattern.Model.revMatchAt? then
      return ("∀ P : Prop, Decidable P", `OmegaChecks.InitInventory.StringPatterns.decidableOfBackwardResult,
        "The matcher returns some a at b iff IsLongestRevMatchAt pat a b (revMatchAt?_eq_some_iff)")
  if owner == `Init.Data.String.Lemmas.Pattern.Split.Basic && name == ``String.Slice.Pattern.Model.split then
    return ("OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle",
      `OmegaChecks.InitInventory.StringPatterns.weakExcludedMiddleOfOfficialSplit,
      "Pointwise agreement with Model.split (split_endPos, split_eq_of_isLongestMatchAt, split_eq_of_not_matchesAt)")
  let (witness, behavior) ← match owner, name with
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toArray.go =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromArrayAccumulator,
        "the finite identity-monad array collector with an empty initial array")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toListRev.go =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromReverseAccumulator,
        "the finite identity-monad reverse collector with an empty initial list")
    | `Init.Data.Iterators.Consumers.Access, `Std.Iter.Partial.atIdxSlow? =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromPartialLookup,
        "the optional index lookup on the partial view of each finite iterator")
    | `Init.Data.Iterators.Consumers.Collect, ``Std.Iter.toList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromCollector,
        "the official result of the ordinary list collector")
    | `Init.Data.Iterators.Consumers.Collect, ``Std.Iter.toArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromArray,
        "the official result of the ordinary array collector")
    | `Init.Data.Iterators.Consumers.Collect, ``Std.Iter.toListRev =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromReverse,
        "the official result of the reverse list collector")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMonadicCollector,
        "the official result of the identity-monad list collector")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMonadicArray,
        "the official result of the identity-monad array collector")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toListRev =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMonadicReverse,
        "the official result of the identity-monad reverse collector")
    | `Init.Data.Slice.Operations, ``Std.Slice.toList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromSlice,
        "the official result of the list of each slice whose underlying iterator is finite")
    | `Init.Data.Slice.Operations, ``Std.Slice.toArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromSliceArray,
        "the official array of each slice whose underlying iterator is finite")
    | `Init.Data.Slice.Operations, ``Std.Slice.toListRev =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromSliceReverse,
        "the official reversed list of each slice whose underlying iterator is finite")
    | `Init.Data.Iterators.Consumers.Access, ``Std.Iter.atIdxSlow? =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromLookup,
        "the official result of the optional lookup at each natural index")
    | `Init.Data.Iterators.Consumers.Monadic.Loop, ``Std.IterM.DefaultConsumers.forIn' =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromDefaultForIn,
        "the official default for-in body on finite identity-monad iterators")
    | `Init.Data.Iterators.Consumers.Monadic.Loop, ``Std.IteratorLoop.defaultImplementation =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromDefaultLoop,
        "the official result of the default identity-monad loop")
    | `Init.Data.Iterators.Combinators.Monadic.FilterMap, ``Std.Iterators.Types.Map.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMapLoop,
        "the official result of the identity-monad loop for mapping the identity")
    | `Init.Data.Iterators.Combinators.Monadic.FilterMap, ``Std.Iterators.Types.FilterMap.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromFilterMapLoop,
        "the official result of the identity-monad loop for filtering with some")
    | `Init.Data.Iterators.Combinators.Monadic.Attach, ``Std.Iterators.Types.Attach.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromAttachLoop,
        "the official result of the identity-monad loop attaching the true predicate")
    | `Init.Data.Iterators.Combinators.Monadic.ULift, ``Std.Iterators.Types.ULiftIterator.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromULiftLoop,
        "the official result of the same-universe identity-monad lifting loop")
    | `Init.Data.Iterators.Combinators.Monadic.Append, ``Std.Iterators.Types.Append.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromAppendLoop,
        "the official result of the identity-monad append loop with a list iterator as the second input")
    | `Init.Data.Iterators.Combinators.Monadic.FlatMap, ``Std.Iterators.Types.Flatten.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromFlattenLoop,
        "the official result of the identity-monad flattening loop for finite outer and inner iterators")
    | `Init.Data.Range.Polymorphic.RangeIterator, ``Std.Rxi.Iterator.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromUnboundedRange,
        "the official identity-monad loop on natural numbers with a finite successor enumeration")
    | `Init.Data.Iterators.Combinators.Monadic.Take, ``Std.Iterators.Types.Take.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromTakeLoop,
        "the official result of the identity-monad take loop")
    | `Init.Data.String.Iter.Basic, ``Std.Iter.toStringList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringList, "it.toStringList")
    | `Init.Data.String.Iter.Basic, ``Std.Iter.toStringArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringArray, "it.toStringArray")
    | `Init.Data.String.Iter.Intercalate, ``Std.Iter.joinString =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringJoin, "String.join (it.toList.map toString)")
    | `Init.Data.String.Iter.Intercalate, ``Std.Iter.intercalateString =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringIntercalate,
        "s.copy.intercalate (it.toList.map toString) for every separator s")
    | _, _ => none
  return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)", witness,
    "On every finite iterator it the result equals " ++ behavior)

end OmegaChecks.InitInventory
