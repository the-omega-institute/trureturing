module
public import Lean
import OmegaChecks.InitCompiler.RootNames
import Lean.Compiler.LCNF.PhaseExt
meta import OmegaChecks.InitInventory.OrderedAlgebra
meta import OmegaChecks.InitInventory.Order
meta import OmegaChecks.InitInventory.Logic
meta import OmegaChecks.InitInventory.Reductions
import Lean.Replay
import all Lean.Util.CollectAxioms
import all Lean.Environment
public import OmegaChecks.InitInventory.Reductions
public import OmegaChecks.InitInventory.TransformerLaws
public import OmegaChecks.InitInventory.Traversal
public import OmegaChecks.InitInventory.Collector
public import OmegaChecks.InitInventory.StringPatterns
public import OmegaChecks.InitInventory.StringSearchLoops

public section

/-!
Inventory every public declaration site in the pinned Init and the independently importable
strict modules. Run `lake env lean --run src/OmegaChecks/InitInventory.lean LIB OUTPUT`
after building `+OmegaChecks.InitInventory`. An optional third argument writes the gaps as TSV.
-/

open Lean

private def installedModules (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut modules := if ← (modToFilePath dir root "olean").pathExists then #[root] else #[]
  for file in ← (dir / root.toString).walkDir do
    if file.extension == some "olean" then
      modules := modules.push (← moduleNameOfFileName file dir)
  return modules.qsort Name.lt

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotientPrimitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The pinned Lean evaluator can calculate these on closed natural numbers
even when the public constant has no definition body (notably Nat.gcd). -/
private def officialReduction (env : Environment) (n : Name) : Option String := do
  let info ← env.find? n
  if #[`Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod, `Nat.pow, `Nat.gcd,
       `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight].contains n then
    return "builtin natural-number reduction"
  match info with
  | .defnInfo _ => return "public definition body"
  | .recInfo _ => return "recursor computation rule"
  | .ctorInfo _ => return "constructor computation rule"
  | .inductInfo _ => return "primitive inductive type"
  | _ => none

/-- One shortest implementation-body path to a sealed strict implementation
whose official counterpart has a public computation rule or inductive interface. -/
private def reductionPaths (official strict full : Environment) : NameMap (List Name × String) := Id.run do
  let mut users : NameMap (Array Name) := {}
  let mut paths : NameMap (List Name × String) := {}
  let mut todo := #[]
  for (n, info) in full.constants.toList do
    let some value := info.value? (allowOpaque := true) | continue
    if !(strict.find? n).any (· matches .defnInfo _) then
      if let some rule := officialReduction official (n.replacePrefix `Omega .anonymous) then
        paths := paths.insert n ([n], rule)
        todo := todo.push n
    if info matches .defnInfo _ | .opaqueInfo _ then
      for dep in value.getUsedConstantsAsSet do
        users := users.insert dep ((users.getD dep #[]).push n)
  todo := todo.qsort Name.lt
  let mut i := 0
  while h : i < todo.size do
    let dependency := todo[i]
    i := i + 1
    let some (path, rule) := paths.get? dependency | continue
    for n in (users.getD dependency #[]).qsort Name.lt do
      unless paths.contains n do
        paths := paths.insert n (n :: path, rule)
        todo := todo.push n
  return paths

/-- Additional logical consequences with separate proof terms. These do not discharge a
missing official interface in the completeness check. -/
private def logicalConsequence? (owner name : Name) : Option (Name × Name) := do
  if owner == `Init.Data.Iterators.PostconditionMonad then
    match name with
    | ``Std.Iterators.PostconditionT.bind_pure =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.RightIdentity,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.rightIdentity)
    | ``Std.Iterators.PostconditionT.pure_bind =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.LeftIdentity,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.leftIdentity)
    | ``Std.Iterators.instLawfulMonadPostconditionT =>
      return (``OmegaChecks.InitBoundaries.PostconditionIdentity.LeftIdentity,
        ``OmegaChecks.InitBoundaries.PostconditionIdentity.ofMonad)
    | _ => pure ()
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
  if owner == `Init.System.ST || owner == `Init.Control.StateRef || owner == `Init.System.Promise then
    if let some (_, _, witness) := OmegaChecks.InitBoundaries.ReferenceSelection.witnesses.find?
        (fun entry => entry.1 == owner && entry.2.1 == name) then
      return (``OmegaChecks.InitBoundaries.ReferenceSelection.Selection, witness)
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
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofRunDecomposition)
  | `Init.Data.List.Lemmas, ``List.replicateRecOn =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofRunInduction)
  | `Init.Data.List.Lemmas, ``List.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofListMember)
  | `Init.Data.Array.Lemmas, ``Array.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofArrayMember)
  | `Init.Data.List.Lemmas, ``List.eq_append_cons_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofFirstListMember)
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
  | `Init.Control.Lawful.Basic, ``LawfulMonad.mk' =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMonadConstructor)
  | `Init.Control.Lawful.Lemmas, ``map_inj_of_left_inverse =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMapInjectiveLeftInverse)
  | `Init.Control.Lawful.Lemmas, ``map_inj_right_of_nonempty =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMapInjectiveNonempty)
  | `Init.Control.Lawful.Lemmas, ``map_inj_right =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMapInjectiveMonad)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulFunctor =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTFunctor)
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
  if owner == `Init.SimpLemmas || owner == `Init.Sym.Lemmas then
    if let some reduction := OmegaChecks.InitBoundaries.BooleanReflection.witnesses.lookup name then
      return reduction
  if owner == `Init.Classical then
    if let some witness := OmegaChecks.InitBoundaries.ClassicalConsequences.witnesses.lookup name then
      return (``Classical.em, witness)
  let witness ← match owner, name with
    | `Init.Data.Function, ``Function.Injective.exists_leftInverse => some ``OmegaChecks.InitBoundaries.EmbeddingRange.ofExists
    | `Init.Data.Function, `Function.Injective.leftInverse => some ``OmegaChecks.InitBoundaries.EmbeddingRange.ofLeftInverse
    | `Init.Data.List.Lex, ``List.not_le | `Init.Data.List.Lex, `List.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofListNotLE
    | `Init.Data.Array.Lex.Lemmas, ``Array.not_le | `Init.Data.Array.Lex.Lemmas, `Array.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofArrayNotLE
    | `Init.Data.Vector.Lex, ``Vector.not_le | `Init.Data.Vector.Lex, `Vector.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofVectorNotLE
    | `Init.Data.Vector.Lemmas, ``Vector.instDecidableExistsVectorSucc => some ``OmegaChecks.InitBoundaries.VectorExistence.emOfVectorSucc
    | `Init.Grind.Order, ``Lean.Grind.Order.le_of_not_lt => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromComparison
    | `Init.Grind.Norm, ``Lean.Grind.imp_eq => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromImplication
    | `Init.Grind.Norm, ``Lean.Grind.not_not => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromNotNot
    | `Init.Grind.Lemmas, ``Lean.Grind.of_lookahead => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromLookahead
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
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfLongest
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.IsRevMatch.exists_isLongestRevMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevLongest
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchesAt_iff_exists_isMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfMatchesAt
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchesAt_iff_exists_isRevMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevMatchesAt
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchAt?_eq_some_iff =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfMatchAtSome
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchAt?_eq_some_iff =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevMatchAtSome
    | _, _ => none
  return (``Classical.em, witness)

/-- The conclusion uses the indicated semantic agreement in addition to the public type. -/
private def conditionalConsequence? (owner name : Name) : Option (String × Name × String) := do
  if owner == `Init.Data.Order.Lemmas || owner == `Init.Data.Order.LemmasExtra then
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
  if owner == `Init.Data.ByteArray.Basic then
    if name == `ByteArray.forInUnsafe.loop then
      return ("False", ``OmegaChecks.InitBoundaries.ByteArrayReads.noForInBound,
        "The uget read has an in-bounds index whenever i < sz for the independently supplied sz")
    if name == `ByteArray.foldlMUnsafe.fold then
      return ("False", ``OmegaChecks.InitBoundaries.ByteArrayReads.noFoldBound,
        "The uget read has an in-bounds index whenever i differs from the independently supplied stop")
  if owner == `Init.Data.Array.Basic && [`Array.mapMUnsafe, `Array.mapFinIdxMUnsafe].contains name then
    let witness := if name == `Array.mapMUnsafe then ``OmegaChecks.InitBoundaries.ArrayCasts.map
      else ``OmegaChecks.InitBoundaries.ArrayCasts.mapIndexed
    return ("False", witness,
      "On Array Unit with word length zero and a callback returning none : Option Empty, the zero-step exit returns some output of the original natural length")
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
  if owner == `Init.ShareCommon && [``ShareCommon.StateFactory.mk, ``ShareCommon.StateFactory.mkImpl,
      ``ShareCommon.StateFactory.get].contains name then
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
    if name == ``ShareCommon.Object.ptrEq then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.objectPointerEquality,
        "Pointer identity distinguishes an alias from a separately allocated NonScalar with the same Nat field")
    if name == ``ShareCommon.Object.ptrHash then
      return ("False", ``OmegaChecks.InitBoundaries.PointerObservations.objectPointerHash,
        "Pointer hashes distinguish two simultaneously live NonScalar objects with the same Nat field")
  if owner == `Init.Core && name == ``Quot.liftIndepPr1 then
    return ((``Quot.sound).toString, ``OmegaChecks.InitBoundaries.HeterogeneousQuotient.soundOfPairCoherence,
      "The lift in the original result requires pair coherence for every motive, including the unit motive")
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
    if name == ``Lean.Order.instOrderPi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfPointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed order")
    if let some witness := OmegaChecks.InitBoundaries.InternalOrder.implicationOrders.lookup name then
      return ((``propext).toString, witness,
        "Every pair related by the pinned instance's rel field is also related by the replacement")
    if name == ``Lean.Order.instCCPOOption then
      return ((``Classical.em).toString, ``OmegaChecks.InitBoundaries.InternalOrder.excludedMiddleOfOptionCCPO,
        "The order underlying the proposed CCPO on options agrees with the official flat order")
    if name == ``Lean.Order.FlatOrder.instCCPO then
      return ((``Classical.em).toString, ``OmegaChecks.InitBoundaries.InternalOrder.excludedMiddleOfFlatCCPO,
        "At options with bottom none the order underlying the proposed CCPO agrees with the flat order")
    if name == ``Lean.Order.flat_csup then
      return ((``Classical.choice).toString, ``OmegaChecks.InitBoundaries.InternalOrder.choiceFromFlatPresence,
        "For nonempty α and the universal predicate on Option α with bottom none, the result has tag some, as in the pinned definition")
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

private def nativeSignatures (env : Environment) (idx : ModuleIdx) : NameSet :=
  (Compiler.LCNF.impureSigExt.getModuleEntries env idx).foldl (fun acc sig => acc.insert sig.name) {}

/-- One entry per public safe definition with a body and an official native signature. -/
private structure NativeSite where
  strictDeclaration : Bool
  strictSignature : Bool

private def nativeSummary (sites : Array NativeSite) : Json :=
  Json.mkObj [("officialSignatures", toJson sites.size),
    ("strictDeclarations", toJson (sites.filter (·.strictDeclaration)).size),
    ("strictSignatures", toJson (sites.filter (·.strictSignature)).size)]

/-- A name in the unchanged official type that the kernel reports missing after
erasing exactly that axiom. An equivalent reformulation can use different proof terms. -/
private def checkedTypeAxioms (official : Environment) (info : ConstantInfo)
    (closure : Array Name) : CoreM (Array Name) := do
  if closure.isEmpty then return #[]
  let used := info.type.getUsedConstants
  let direct := closure.filter fun name => used.contains name && (official.find? name).any (·.isAxiom)
  if direct.isEmpty then return #[]
  let _ ← ofExceptKernelException (Kernel.check official {} info.type)
  let core := official.toKernelEnv
  let constants := core.constants
  for name in direct do
    let without := Environment.ofKernelEnv {core with constants := {constants with
        map₁ := constants.map₁.erase name, map₂ := constants.map₂.erase name}}
    match Kernel.check without {} info.type with
    | .error (.unknownConstant _ missing) =>
      unless missing == name do throwError "checking {info.name} without {name} missed {missing}"
    | .error err => throwError "checking {info.name} without {name}: {err.toMessageData {}}"
    | .ok _ => throwError "the unchanged type of {info.name} checked without {name}"
  return direct

private def inventory (lib : System.FilePath) (visible strict full : Environment) (modules : Array Name)
    (gaps : Option IO.FS.Handle) (observedRuntime : List String) : CoreM Json := do
  let official ← getEnv
  let reductions := reductionPaths visible strict full
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
  let mut certifiedSites := 0
  let mut matchedUnique : NameSet := {}
  let mut axiomUnique : NameSet := {}
  let mut withAxiomsUnique : NameSet := {}
  let mut rows := #[]
  let mut matchingNames := 0
  let mut directAxioms := 0
  let mut withAxioms := 0
  let mut nativeByModule := #[]
  let mut allNative := #[]
  if let some file := gaps then
    file.putStrLn "module\tdeclaration\tkind\tunsafe\tpartial\tupstreamAxioms\timpliesAxiom\treductionWitness\tlogicalConsequence\tlogicalConsequenceWitness\trequiredBehavior\tabstractedDependency\truntimeConflictWitness\tequationOperand\toperandImpliesAxiom\toperandReductionWitness\tunchangedTypeAxioms"
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
    let strictNames := strictIdx.map fun i =>
      NameSet.ofList strict.header.moduleData[i]!.constNames.toList
    let officialSigs := nativeSignatures visible idx
    let strictSigs := (strictIdx.map (nativeSignatures strict)).getD {}
    let mut moduleNative : Array NativeSite := #[]
    for name in publicNames.qsort Name.lt do
      let some info := localDecls.find? name | throwError "missing declaration {owner}/{name}"
      let some (_, axioms) := localAxioms.binSearch (name, #[]) (fun a b => Name.quickLt a.1 b.1)
        | throwError "missing official axiom closure for {owner}/{name}"
      let typeAxioms ← checkedTypeAxioms official info axioms
      let operand := OmegaChecks.InitBoundaries.ChoiceOperands.operand? owner info
      let conditional := conditionalConsequence? owner name
      let consequence := (logicalConsequence? owner name).map (fun (target, witness) => (target.toString, witness))
        <|> conditional.map (fun (target, witness, _) => (target, witness))
      let behavior := conditional.map (fun (_, _, premise) => premise)
      let runtimeConflict : Option String := do
        guard (info.isUnsafe && observedRuntime.contains name.toString)
        let some ("False", witness, _) := conditional | none
        return witness.toString
      let boundary := boundaries[(owner, name)]?
      let selector := if boundary.isSome && OmegaChecks.InitBoundaries.OptionSelector.usesSelector owner name then
        some (``Option.choice).toString else none
      if boundary.isSome then certifiedSites := certifiedSites + 1
      let strictName := if OmegaChecks.InitCompiler.RootNames.isPrimitive expected name then name else `Omega ++ name
      let matched := strictNames.any (·.contains strictName)
      let strictOwner := if matched then some expected else none
      if matched then
        matchingNames := matchingNames + 1
        matchedUnique := matchedUnique.insert name
      if !matched && !info.isAxiom then
        if let some file := gaps then
          file.putStrLn <| String.intercalate "\t" [owner.toString, name.toString,
            declarationKind info, toString info.isUnsafe, toString info.isPartial,
            String.intercalate "," (axioms.toList.map Name.toString),
            (boundary.map (·.1.toString)).getD "", (boundary.map (·.2.toString)).getD "",
            (consequence.map Prod.fst).getD "", (consequence.map (·.2.toString)).getD "", behavior.getD "",
            selector.getD "", runtimeConflict.getD "", (operand.map (·.name.toString)).getD "",
            (operand.map fun _ => (``Classical.choice).toString).getD "", (operand.map (·.witness.toString)).getD "",
            String.intercalate "," (typeAxioms.toList.map Name.toString)]
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
        ("publicReductionBoundary", toJson ((reduction.map Prod.fst).getD []).toArray),
        ("officialReductionMechanism", toJson (reduction.map Prod.snd)),
        ("axioms", toJson (axioms.map Name.toString)),
        ("impliesAxiom", toJson (boundary.map (·.1.toString))),
        ("reductionWitness", toJson (boundary.map (·.2.toString))),
        ("strictModule", toJson (strictOwner.map Name.toString))]
      let row ← if officialSigs.contains name && info.hasValue (allowOpaque := true) && !info.isUnsafe && !info.isPartial then do
        let hasSig := matched && strictSigs.contains strictName
        moduleNative := moduleNative.push ⟨matched, hasSig⟩
        pure (row.setObjVal! "strictNativeSignature" (toJson hasSig))
      else pure row
      let row := if typeAxioms.isEmpty then row else
        row.setObjVal! "unchangedTypeAxioms" (toJson (typeAxioms.map Name.toString))
      let row := match selector with
        | some dep => row.setObjVal! "abstractedDependency" (toJson dep)
        | none => row
      let row := match operand with
        | some op => row.mergeObj <| Json.mkObj [("equationOperand", toJson op.name.toString),
            ("operandImpliesAxiom", toJson (``Classical.choice).toString), ("operandReductionWitness", toJson op.witness.toString)]
        | none => row
      let row := match runtimeConflict with
        | some witness => row.setObjVal! "runtimeConflictWitness" (toJson witness)
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
    ("native", nativeSummary allNative)]
  let unique := Json.mkObj [("declarations",toJson names.size), ("directAxioms",toJson axiomUnique.size),
    ("withAxioms",toJson withAxiomsUnique.size), ("matchingNameAndModule",toJson matchedUnique.size)]
  return Json.mkObj [("schemaVersion", toJson 4), ("uniqueNames", unique), ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("nativeByModule", Json.mkObj nativeByModule.toList),
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
  for owner in strict.allImportedModuleNames do
    unless owner.getRoot == `OmegaInit do
      throw <| IO.userError s!"expected a strict OmegaInit build, found import {owner}"
  let pointers ← unsafe OmegaChecks.InitBoundaries.PointerObservations.observe modules.size
  let effects ← unsafe OmegaChecks.InitBoundaries.EffectObservations.observe modules.size
  -- Reference counts depend on argument ownership in native code. Run the borrowed call
  -- in a compiled executable so interpreter boxing cannot perturb the observed object.
  let native ← IO.Process.output {cmd := "lake", args := #["-q", "exe", "omegaPointerObservations", "--exclusivity"]}
  unless native.exitCode == 0 do throw <| IO.userError s!"native exclusivity observation failed: {native.stderr}"
  let observedRuntime ← match native.stdout.trimAscii.toString with
    | "true" => pure ("isExclusiveUnsafe" :: pointers ++ effects)
    | "false" => pure (pointers ++ effects)
    | other => throw <| IO.userError s!"unexpected native exclusivity observation: {other}"
  let result ← (inventory lib visible strict full modules gaps observedRuntime).toIO' {fileName := "<Init inventory>", fileMap := default} {env := official}
  IO.FS.writeFile outputPath (result.compress ++ "\n")
  IO.println (← IO.ofExcept (result.getObjVal? "summary")).compress
