module
public import Lean
import OmegaChecks.InitInventory.Replay
meta import OmegaChecks.InitInventory.Replay
import all Init.Classical
import all Init.WFExtrinsicFix
import all Init.While
import all Init.Internal.Order.While
import all Init.Data.Option.Lemmas
import all Init.Control.Lawful.MonadAttach.Lemmas
public import OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.Logic

open Lean
namespace OmegaChecks.InitBoundaries.ChoiceOperands

/-- An implementation of the public selector supplies a choice function on every nonempty sort. -/
public def fromChoice (select : type_of% @Classical.choice.{u}) : type_of% @Classical.choice.{u} := @select

-- The congruence equation needs only reflexivity once a selector is supplied.
example (select : type_of% @Classical.choice.{u}) {α : Sort u} (h : Nonempty α) : select h = select h := rfl

/-- The value-producing head of an official equation and its reduction to choice. -/
public structure Operand where
  name : Name
  witness : Name
  levels : List Level

/-- The selector laws can be instantiated with the predicate that a value equals itself. -/
private theorem existsSelf {α : Sort u} (h : Nonempty α) : ∃ x : α, x = x :=
  h.elim fun x => ⟨x, rfl⟩

private def specification? : Name → Option (Name × Name)
  | ``Classical.choose_spec => some (``Classical.choose, ``choiceFromChoose)
  | ``Exists.choose_spec => some (``Exists.choose, ``choiceFromExistsChoose)
  | ``Classical.epsilon_spec | ``Classical.epsilon_spec_aux => some (``Classical.epsilon, ``choiceFromEpsilon)
  | _ => none

private def fixWitness? : Name → Option Name
  | ``WellFounded.extrinsicFix | ``WellFounded.partialExtrinsicFix => some ``choiceFromFix
  | ``WellFounded.extrinsicFix₂ | ``WellFounded.partialExtrinsicFix₂ => some ``choiceFromFix₂
  | ``WellFounded.extrinsicFix₃ | ``WellFounded.partialExtrinsicFix₃ => some ``choiceFromFix₃
  | _ => none

private def congruenceWitness? (operand : Name) : Option Name :=
  match operand with
  | ``Classical.choice => some ``fromChoice
  | ``Classical.ofNonempty => some ``choiceFromOfNonempty
  | ``Classical.choose => some ``choiceFromChoose
  | ``Exists.choose => some ``choiceFromExistsChoose
  | other => fixWitness? other

/-- Read the left value of the concluding equality directly from the defining module's type.
The witness consumes the complete polymorphic operation used to state the equation. -/
public def operand? (owner : Name) (source : ConstantInfo) : Option Operand := do
  guard (owner.getRoot == `Init)
  guard source.isTheorem
  if owner == `Init.Internal.Order.While && source.name == `repeatM.congr_simp then
    let [u, _] := source.levelParams | none
    return ⟨``repeatM, ``choiceFromRepeatM, [.param u, .param u]⟩
  if owner == `Init.Classical then
    if let some (name, witness) := specification? source.name then
      guard (source.type.getUsedConstants.contains name)
      return ⟨name, witness, source.levelParams.map Level.param⟩
  let congruence := source.name matches .str _ "congr_simp"
  guard (owner == `Init.WFExtrinsicFix || congruence)
  let mut conclusion := source.type
  while conclusion.isForall do conclusion := conclusion.bindingBody!
  guard (conclusion.isAppOfArity ``Eq 3)
  let args := conclusion.getAppArgs
  guard args[0]!.getAppFn.isBVar
  let .const name levels := args[1]!.getAppFn | none
  let witness? := if congruence && source.name.getPrefix == name then congruenceWitness? name
    else if owner == `Init.WFExtrinsicFix then fixWitness? name else none
  let witness ← witness?
  return ⟨name, witness, levels⟩

private def check (env : Environment) (owner : Name) (source : ConstantInfo) (operand : Operand) : Except String Unit := do
  let ⟨name, witness, levels⟩ := operand
  let some op := env.find? name | throw s!"missing operand {name} in {owner}/{source.name}"
  let some proof := env.find? witness | throw s!"missing choice witness {witness}"
  let some target := env.find? ``Classical.choice | throw "missing official choice type"
  let some (.param targetLevel) := levels.getLast?
    | throw s!"choice at a fixed universe in {owner}/{source.name}"
  let proofLevels := if name == ``repeatM then [.param targetLevel] else levels
  unless source.levelParams.contains targetLevel && levels.length == op.numLevelParams &&
      proofLevels.length == proof.numLevelParams && target.isAxiom do
    throw s!"incompatible operand universes in {owner}/{source.name}"
  let domain := op.type.instantiateLevelParams op.levelParams levels
  let codomain := target.type.instantiateLevelParams target.levelParams [.param targetLevel]
  let expected := Expr.forallE .anonymous domain codomain .default
  unless proof.type.instantiateLevelParams proof.levelParams proofLevels == expected do
    throw s!"incorrect choice witness type for {owner}/{source.name}"

public def isFixFormation (owner : Name) (source : ConstantInfo) (operand : Operand) : Bool :=
  owner == `Init.WFExtrinsicFix && (fixWitness? operand.name).isSome &&
    (source.name == ``WellFounded.extrinsicFix_invImage ||
      ["_eq_apply", "_eq_fix", "_eq_apply_of_acc", "_eq_partialExtrinsicFix"].any
        (source.name == operand.name.appendAfter ·))

open Meta in
/-- Specialize the inverse-image equation to the identity map and the same
recursion step on both sides. Its compatibility premise then follows by reflexivity. -/
private def inverseImageEndpoint (visible : Environment) (source : ConstantInfo) : MetaM (Expr × List Level) := do
  let [_, value, domain] := source.levelParams | throwError "unexpected inverse-image universes"
  let u := Level.param domain
  let levels := [u, .param value, u]
  forallTelescope (source.type.instantiateLevelParams source.levelParams levels) fun xs _ => do
    let #[α, family, _, inh, rel, _, step, _, _, _, wf] := xs | throwError "unexpected inverse-image telescope"
    withLocalDeclD `point α fun point => do
      let sameMap := mkApp (mkConst ``id [u]) α
      let partialApp := mkAppN (mkConst source.name levels) #[α, family, α, inh, rel, sameMap, step, step]
      let .forallE _ coherence _ _ ← inferType partialApp | throwError "missing compatibility premise"
      let agreement ← forallTelescope coherence fun ys target => do
        let some (_, lhs, rhs) := target.eq? | throwError "expected equality of recursion steps"
        unless ← isDefEq lhs rhs do throwError "recursion steps differ under the identity map"
        mkLambdaFVars ys (← mkEqRefl lhs)
      let applied := mkApp3 partialApp agreement point wf
      let type ← Lean.ofExceptKernelException (Kernel.check visible (← getLCtx) applied)
      let some (_, _, rhs) := type.headBeta.eq? | throwError "expected specialized inverse-image equation"
      return (← mkLambdaFVars #[α, family, inh, rel, step, point] rhs, [u, .param value])

open Meta in
/-- Abstract only the arguments actually occurring at the left endpoint. The
equation has an accessibility or well-foundedness premise, and the endpoint
is the entire unrestricted operator independently of that premise. -/
public def checkFixFormation (visible : Environment) (source : ConstantInfo) (op : Operand) : MetaM Unit := do
  let env ← getEnv
  unless isFixFormation `Init.WFExtrinsicFix source op && source.isTheorem &&
      visible.getModuleIdxFor? source.name == visible.getModuleIdx? `Init.WFExtrinsicFix &&
      (visible.find? source.name).any (fun ci => ci.type.equal source.type) do
    throwError "unexpected public fixed-point equation {source.name}"
  let entry ← getConstInfo op.name
  let choice ← getConstInfo ``Classical.choice
  let (endpoint, levels) ← if source.name == ``WellFounded.extrinsicFix_invImage then
    inverseImageEndpoint visible source
  else forallTelescope source.type fun xs conclusion => do
    let some (_, lhs, _) := conclusion.eq? | throwError "expected an equality at {source.name}"
    let args := lhs.getAppArgs
    let omitted := xs.filter (!args.contains ·)
    let #[premise] := omitted | throwError "expected one omitted premise at {source.name}"
    let required := (← inferType premise).getAppFn
    unless (required.isConstOf ``Acc || required.isConstOf ``WellFounded) &&
        lhs.getAppFn == mkConst op.name op.levels && args == xs.filter (· != premise) do
      throwError "the endpoint at {source.name} depends on the termination premise or specializes its operator"
    return (← mkLambdaFVars args lhs, op.levels)
  let actual ← Lean.ofExceptKernelException (Kernel.check visible {} endpoint)
  let result := mkApp (mkConst op.witness levels) endpoint
  let selected ← Lean.ofExceptKernelException (Kernel.check env {} result)
  unless !endpoint.hasFVar && Kernel.isDefEqGuarded visible {} endpoint (mkConst op.name levels) &&
      Kernel.isDefEqGuarded visible {} actual (entry.type.instantiateLevelParams entry.levelParams levels) &&
      Kernel.isDefEqGuarded env {} selected (choice.type.instantiateLevelParams choice.levelParams [levels.getLast!]) do
    throwError "the complete endpoint at {source.name} does not yield the pinned choice type"

open Meta in
/-- Specialize a congruence using the arguments of the existing reduction. Under an arbitrary
implementation of its operator, each of the two resulting endpoints is a complete choice function. -/
public def checkCongruenceEndpoints (official : Environment) (source : ConstantInfo) (operand : Operand) : MetaM Unit := do
  let u := Level.param `u
  let isRepeat := operand.name == ``repeatM
  let sourceLevels := source.levelParams.map fun param =>
    if isRepeat || operand.levels.getLast? == some (.param param) then u else Level.one
  let opLevels := operand.levels.map fun level => level.instantiateParams source.levelParams sourceLevels
  let op ← getConstInfo operand.name
  let choice ← getConstInfo ``Classical.choice
  let env ← getEnv
  -- The result of a monad lives in Type. Its endpoints supply choice on Type u
  -- directly, and choiceFromRepeatM lifts arbitrary sorts through PLift.
  let choiceType := choice.type.instantiateLevelParams choice.levelParams [if isRepeat then u.succ else u]
  let selector := if isRepeat then mkConst ``choiceFromRepeatAtType [u] else mkConst operand.witness opLevels
  withLocalDeclD `op (op.type.instantiateLevelParams op.levelParams opLevels) fun port => do
    let siteType := (source.type.instantiateLevelParams source.levelParams sourceLevels).replace fun term =>
      if term == mkConst operand.name opLevels then some port else none
    forallTelescope choiceType fun params _ => do
      let selected ← withTransparency .all <| whnf (mkAppN (mkApp selector port) params)
      let (args, _, eqn) ← forallMetaTelescope siteType
      let some (_, lhs, rhs) := eqn.eq? | throwError "expected equality"
      unless lhs.getAppFn == port && selected.getAppFn == port &&
          lhs.getAppNumArgs == selected.getAppNumArgs do
        throwError "unexpected application {lhs} / {selected}"
      -- Match the left endpoint to the self-loop or selector application in the constructive witness.
      for (arg, value) in lhs.getAppArgs.zip selected.getAppArgs do
        let arg ← instantiateMVars arg
        if arg.isMVar then arg.mvarId!.assign value
        else unless ← isDefEq arg value do throwError "cannot specialize {arg} to {value}"
      -- A congruence now needs only equality of identical predicates or recursion steps.
      for arg in args do
        unless ← arg.mvarId!.isAssigned do
          discard <| observing? arg.mvarId!.refl
      let args ← args.mapM instantiateMVars
      if args.any (·.hasMVar) then throwError "unresolved arguments for {source.name}: {args}"
      -- The arguments used to expose choice must be available to a zero-axiom caller,
      -- even if the selector and the proposed congruence have yet to be implemented.
      let recipes ← args.mapM (mkLambdaFVars params ·)
      let mut roots := choiceType.getUsedConstantsAsSet.toList
      for recipe in recipes do
        if recipe.hasFVar then throwError "specialization of {source.name} depends on its selector"
        roots := recipe.getUsedConstantsAsSet.toList ++ roots
      let clean ← replayBoundaryDependencies official env roots
      for recipe in recipes do
        discard <| Lean.ofExceptKernelException (Kernel.check clean {} recipe)
      -- Check the whole specialization, including the argument types and equality hypotheses.
      withLocalDeclD `law siteType fun law => do
        let app ← mkLambdaFVars (#[port] ++ params ++ #[law]) (mkAppN law args)
        discard <| Lean.ofExceptKernelException (Kernel.check env {} app)
      -- Read both values from the specialized *official statement*. Neither value
      -- may use the proof of that statement or any parameter beyond α and its inhabitance.
      let declared := source.type.instantiateLevelParams source.levelParams sourceLevels
      withLocalDeclD `congruence declared fun law => do
        let app := mkAppN law args
        let some (_, left, right) := (← inferType app).eq? | throwError "expected an official equality"
        for endpoint in #[left, right] do
          let selected ← mkLambdaFVars params endpoint
          if selected.hasFVar then throwError "open equality endpoint at {source.name}"
          let actual ← Lean.ofExceptKernelException (Kernel.check env {} selected)
          unless Kernel.isDefEqGuarded env {} actual choiceType do
            throwError "official endpoint at {source.name} has type {actual}"
      let expected ← mkForallFVars #[port] choiceType (usedOnly := false)
      for endpoint in #[lhs, rhs] do
        let abstracted ← mkLambdaFVars (#[port] ++ params) (← instantiateMVars endpoint)
        let actual ← Lean.ofExceptKernelException (Kernel.check env {} abstracted)
        unless Kernel.isDefEqGuarded env {} actual expected do
          throwError "{source.name} has a specialized endpoint of unexpected type {actual}"

open Meta in
/-- Read the equality after applying the official specification to a nonempty sort and
the reflexive predicate. Both endpoints must depend only on these two choice arguments. -/
private def checkSpecification (official : Environment) (source : ConstantInfo) (op : Operand) : MetaM Unit := do
  let u := Level.param `u
  let env ← getEnv
  let choice ← getConstInfo ``Classical.choice
  let choiceType := choice.type.instantiateLevelParams choice.levelParams [u]
  forallTelescope choiceType fun params _ => do
    let #[α, h] := params | throwError "unexpected choice type"
    let predicate ← withLocalDeclD `x α fun x => do mkLambdaFVars #[x] (← mkEq x x)
    let existsProof := mkApp2 (mkConst ``existsSelf [u]) α h
    let args := if source.name == ``Classical.epsilon_spec_aux then #[α, h, predicate, existsProof]
      else #[α, predicate, existsProof]
    let recipes ← args.mapM (mkLambdaFVars params ·)
    let roots := recipes.toList.flatMap fun recipe => recipe.getUsedConstantsAsSet.toList
    let clean ← replayBoundaryDependencies official env (roots ++ choiceType.getUsedConstantsAsSet.toList)
    for recipe in recipes do
      discard <| Lean.ofExceptKernelException (Kernel.check clean {} recipe)
    let declared := source.type.instantiateLevelParams source.levelParams [u]
    withLocalDeclD `law declared fun law => do
      let app := mkAppN law args
      let inferred ← Lean.ofExceptKernelException (Kernel.check env (← getLCtx) app)
      let some (_, left, right) := inferred.headBeta.eq? | throwError "expected a specialized equality for {source.name}"
      for term in #[left, right] do
        unless term.getAppFn.isConstOf op.name do throwError "unexpected selector in {source.name}"
        let endpoint ← mkLambdaFVars params term
        if endpoint.hasFVar then throwError "specialized endpoint depends on the specification proof"
        let ty ← Lean.ofExceptKernelException (Kernel.check env {} endpoint)
        unless Kernel.isDefEqGuarded env {} ty choiceType do throwError "incomplete choice type in {source.name}"

/-- Physical congruence sites in the pin. Several modules export the same name.
At each listed site, substituting the arguments of the selector witness into the
actual statement exhibits a function of the type of Classical.choice at both endpoints. -/
private def congruenceSites : List (Name × Name) := [
  (`Init.Classical, `Classical.choose.congr_simp),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix.congr_simp),
  (`Init.Internal.Order.While, `repeatM.congr_simp),
  (`Init.While, `Classical.choice.congr_simp),
  (`Init.While, `Exists.choose.congr_simp),
  (`Init.Control.Lawful.Lemmas, `Exists.choose.congr_simp),
  (`Init.Data.Option.Lemmas, `Classical.choice.congr_simp),
  (`Init.Control.Lawful.MonadAttach.Lemmas, `Classical.ofNonempty.congr_simp),
  (`Init.Data.Iterators.Consumers.Access, `WellFounded.extrinsicFix₂.congr_simp),
  (`Init.Data.Range.Polymorphic.UpwardEnumerable, `Exists.choose.congr_simp),
  (`Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect, `WellFounded.extrinsicFix₂.congr_simp),
  (`Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop, `WellFounded.extrinsicFix₃.congr_simp)]

public def hasChoiceEndpoints (owner : Name) (source : ConstantInfo) : Bool :=
  congruenceSites.contains (owner, source.name) ||
    (owner == `Init.Classical && (specification? source.name).isSome)

/-- The left side of this equation, abstracted over its actual telescope, is the
entire loop at independent universe levels. The loop's fixed-point observation
and the reduction to choice are checked at its definition site in Reductions. -/
public def checkLoopEndpoint (visible : Environment) (source : ConstantInfo) : MetaM Unit := do
  let owner := `Init.Internal.Order.While
  let loop := ``Lean.Loop.forIn
  unless source.isTheorem && source.name == `Lean.Loop.forIn.eq_1 &&
      visible.getModuleIdxFor? source.name == visible.getModuleIdx? owner &&
      (visible.find? source.name).any (fun entry => entry.type.equal source.type) do
    throwError "missing public loop unfolding equation in its pinned module"
  let entry ← getConstInfo loop
  let levels := source.levelParams.map Level.param
  unless levels.length == 2 && entry.numLevelParams == levels.length do
    throwError "unexpected loop universe parameters"
  Meta.forallTelescope source.type fun xs conclusion => do
    let some (_, lhs, rhs) := conclusion.eq? | throwError "expected the loop equality"
    let operation := mkConst loop levels
    unless lhs.getAppFn == operation && lhs.getAppArgs == xs && rhs.getAppFn.isConstOf ``repeatM do
      throwError "unfolding equation does not expose the full pinned loop"
    let endpoint ← Meta.mkLambdaFVars xs lhs
    let type ← Lean.ofExceptKernelException (Kernel.check visible {} endpoint)
    unless Kernel.isDefEqGuarded visible {} type (entry.type.instantiateLevelParams entry.levelParams levels) &&
        Kernel.isDefEqGuarded visible {} endpoint operation do throwError "incomplete loop endpoint"

public def certifyEndpoints (official : Environment) (source : ConstantInfo) (op : Operand) : MetaM Unit :=
  if (specification? source.name).isSome then checkSpecification official source op
  else checkCongruenceEndpoints official source op

run_cmd
  let env ← getEnv
  let pinned ← importModules #[{module := `Lean}] {} (level := .private)
  let mut verified := #[]
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    unless owner.getRoot == `Init do continue
    for source in data.constants do
      unless isPrivateName source.name || source.name.isInternalOrNum || source.name.hasMacroScopes do
        if let some operand := operand? owner source then
          if let .error msg := check env owner source operand then throwError "{msg}"
          if isFixFormation owner source operand then
            Elab.Command.liftCoreM <| Meta.MetaM.run' (checkFixFormation env source operand)
          if source.name.getPrefix == operand.name then
            unless congruenceSites.contains (owner, source.name) do
              throwError "unrecorded choice-valued congruence in {owner}: {source.name}"
            verified := verified.push (owner, source.name)
          if hasChoiceEndpoints owner source then
            Elab.Command.liftCoreM <| Meta.MetaM.run' (certifyEndpoints pinned source operand)
  unless verified.size == congruenceSites.length && congruenceSites.all verified.contains do
    throwError "recorded choice congruences differ from the compiled pin"

end OmegaChecks.InitBoundaries.ChoiceOperands
