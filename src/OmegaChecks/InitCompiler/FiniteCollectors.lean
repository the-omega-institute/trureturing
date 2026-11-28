module
public import Lean
import OmegaChecks.InitPort.LawfulLoop
import OmegaChecks.InitPort.PatternMatch
import Init.Data.Iterators.Consumers.Access
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Total
import Init.Data.Slice.Operations
import Init.Data.Slice.Array.Iterator
import all Init.Data.String.Iter.Intercalate

/-! Use the terminating consumer at collection sites with an available finite instance.
The source kernel checks the complete replacement by definitional equality. -/

namespace OmegaChecks.InitCompiler
open Lean Meta

private def pureCollectors := [``Std.Iter.toArray, ``Std.Iter.toList, ``Std.Iter.toListRev]
private def monadicCollectors := [``Std.IterM.toArray, ``Std.IterM.toList, ``Std.IterM.toListRev]
private def sliceCollectors := [``Std.Slice.toArray, ``Std.Slice.toList, ``Std.Slice.toListRev]

private def stringFolds := [``Std.Iter.joinString, ``Std.Iter.intercalateString]

private def isDefaultLoopAlias (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.defnInfo decl) => decl.value.getLambdaBody.getAppFn.isConstOf ``Std.IteratorLoop.defaultImplementation
  | _ => false

private def consumerArity? (head : Name) : Option Nat :=
  if pureCollectors.contains head then some 4
  else if head == ``Std.Iter.atIdxSlow? then some 5
  else if monadicCollectors.contains head || sliceCollectors.contains head then some 6
  else none

private def specializeCollector (e : Expr) : MetaM (Option Expr) := do
  let some head := e.getAppFn.constName? | return none
  let args := e.getAppArgs
  -- The public kernel reduces the wrapper projection on the constructor.
  if head == ``Std.Iter.atIdxSlow? && args.size == 5 then
    let it ← mkAppOptM ``Std.Iter.Total.mk #[args[0]!, args[1]!, args[4]!]
    return some (← mkAppOptM ``Std.Iter.Total.atIdxSlow? #[args[0]!, args[1]!, args[2]!, none, args[3]!, it])
  if pureCollectors.contains head && args.size == 4 then
    let it ← mkAppOptM ``Std.Iter.Total.mk #[args[0]!, args[1]!, args[3]!]
    let method := head.replacePrefix ``Std.Iter ``Std.Iter.Total
    return some (← mkAppOptM method #[args[0]!, args[1]!, args[2]!, none, it])
  if monadicCollectors.contains head && args.size == 6 then
    -- The list consumers place the monad instance before the element type.
    let (m, β, monad) := if head == ``Std.IterM.toArray then (args[2]!, args[1]!, args[3]!)
      else (args[1]!, args[3]!, args[2]!)
    let it ← mkAppOptM ``Std.IterM.Total.mk #[args[0]!, m, β, args[5]!]
    let method := head.replacePrefix ``Std.IterM ``Std.IterM.Total
    return some (← mkAppOptM method #[args[0]!, m, β, monad, args[4]!, none, it])
  return none

public def finiteCollectors (env : Environment) (input : Expr) (withinImplementation := false)
    (keepLoop : Option Name := none) : IO Expr := do
  let used := input.getUsedConstants
  let aliases := used.foldl (init := ({} : NameSet)) fun ns n =>
    if isDefaultLoopAlias env n then ns.insert n else ns
  let hasLoop := env.contains InitPort.LawfulLoop.helper &&
    (!aliases.isEmpty || used.contains ``Std.IteratorLoop.defaultImplementation ||
      used.contains ``Std.IterM.DefaultConsumers.forIn')
  let hasRange := env.contains InitPort.RangeFix.helper && used.contains ``WellFounded.extrinsicFix₃
  let hasSemiringImage := used.contains ``Grind.CommRing.Expr.denoteSAsRing
  let patterns := InitPort.PatternMatch.rules.filter fun rule => used.contains rule.trigger && env.contains rule.helper
  let hasStringFold := used.any stringFolds.contains
  unless hasLoop || hasRange || hasStringFold || !patterns.isEmpty || used.any (fun n => (consumerArity? n).isSome) do return input
  let rewrite : MetaM Expr := Meta.transform input (pre := fun sub => do
    if hasSemiringImage then
      if let some value ← InitPort.PatternMatch.semiringNumeral? sub then return .done value
    if hasRange then
      if let some call ← InitPort.RangeFix.specialize? sub then return .done call
    if hasLoop then
      if let some call ← InitPort.LawfulLoop.specialize? sub then return .done call
    let some head := sub.getAppFn.constName? | return .continue
    -- Both string consumers fold a mapped iterator. Expose the fold only when the
    -- caller supplies finiteness, so the mapped iterator can select a terminating loop.
    if hasStringFold && head == mkPrivateNameCore `Init.Data.String.Iter.Intercalate `Std.Iter.intercalateString.match_1 then
      if let some cases ← unfoldDefinition? sub then return .visit cases
    if stringFolds.contains head then
      let args := sub.getAppArgs
      let arity := if head == ``Std.Iter.joinString then 5 else 6
      if args.size == arity then
        let finite ← mkAppOptM ``Std.Iterators.Finite #[args[0]!, none, args[1]!, args[2]!]
        if (← synthInstance? finite).isSome then
          if let some fold ← unfoldDefinition? sub then return .visit fold
    -- A generic searcher can revisit a position. At concrete uses of the same
    -- instance, the iterator may supply a proof that its traversal is finite.
    if keepLoop != some head && ((hasLoop && aliases.contains head) || (hasStringFold && isDefaultLoopAlias env head)) then
      if let some core ← unfoldDefinition? sub then
        if let some loop ← InitPort.LawfulLoop.specializeFiniteDefault? core then return .done loop
    for rule in patterns do
      unless rule.original == head do continue
      if let some call ← InitPort.PatternMatch.specialize? rule sub then return .done call
    let isSlice := sliceCollectors.contains head
    let some arity := consumerArity? head | return .continue
    -- Rewrites under congrArg often pass the collection function without its final argument.
    unless sub.getAppNumArgs == arity || sub.getAppNumArgs + 1 == arity do return .continue
    try
      forallBoundedTelescope (← inferType sub) (some (arity - sub.getAppNumArgs)) fun xs _ => do
        let call := mkAppN sub xs
        if !withinImplementation && head == ``Std.Slice.toArray && env.contains ``Subarray.copy then
          -- Subarray.copy publicly unfolds to this exact collection, even with an unknown slice.
          if let some copy ← observing? (mkAppM ``Subarray.copy #[call.appArg!]) then
            if ← isDefEq call copy then return .visit (← mkLambdaFVars xs copy)
        let some core ← (if isSlice then unfoldDefinition? call else pure (some call)) | return .continue
        let some result ← specializeCollector core | return .continue
        let result ← instantiateMVars result
        if withinImplementation then
          -- A constructive implementation can compute differently in the destination. Check
          -- the collector in its source context even when the enclosing proof uses that computation.
          let locals := (← getLCtx).getFVars
          let old ← mkLambdaFVars locals call
          let new ← mkLambdaFVars locals result
          unless (Kernel.check env {} old).isOk && (Kernel.check env {} new).isOk &&
              Kernel.isDefEqGuarded env {} old new do return .continue
        -- A list slice may itself contain another collection, for example when
        -- sorting a subarray via the halves of its list representation.
        return .visit (← mkLambdaFVars xs result)
    catch _ => return .continue)
  let .ok result ← (rewrite.run' |>.toIO' {fileName := "<finite collector>", fileMap := default} {env}).toBaseIO
    | return input
  if result.equal input || result.hasMVar then return input
  unless withinImplementation || ((Kernel.check env {} result).isOk &&
      Kernel.isDefEqGuarded env {} input result) do return input
  return result

end OmegaChecks.InitCompiler
