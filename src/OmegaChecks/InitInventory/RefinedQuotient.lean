module
public import OmegaChecks.InitInventory.Replay
import all Init.Grind.Ring.Envelope
import all Init.Grind.Module.Envelope
import Init.GrindInstances.Ring.Nat

namespace OmegaChecks.InitBoundaries.RefinedQuotient
universe u v
public abbrev Pair := Nat × Nat
public abbrev base : Pair := (0,1)
public abbrev mid : Pair := (1,2)

@[expose] public def tag {α : Sort u} (a : α) (p : Pair) : Prop :=
  HEq (ULift.up.{1} (PLift.up a)) (ULift.up.{u} (PLift.up p))

@[expose] public def subrel {α : Sort u} (r : α → α → Prop) (a b : α) : Prop :=
  r a b ∧ (a = b ∨ (tag a base ∧ tag b mid) ∨ (tag a mid ∧ tag b base))

@[expose] public def carrier {α : Sort u} (r : α → α → Prop) := Quot (subrel r)
@[expose] public def point {α : Sort u} (r : α → α → Prop) (a : α) : carrier r := Quot.mk _ a

@[expose] public def lift {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ a b, r a b → f a = f b) : carrier r → β :=
  Quot.lift f (fun a b hab => h a b hab.1)

set_option linter.defProp false in
@[expose] public def ind {α : Sort u} {r : α → α → Prop} {β : carrier r → Prop}
    (h : ∀ a, β (point r a)) (q : carrier r) : β q := Quot.ind h q

private theorem lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ a b, r a b → f a = f b) (a : α) : lift f h (point r a) = f a := rfl

private theorem ind_beta {α : Sort u} {r : α → α → Prop} {β : carrier r → Prop}
    (h : ∀ a, β (point r a)) (a : α) : ind h (point r a) = h a := rfl

public theorem decode {a p : Pair} (h : tag a p) : a = p :=
  congrArg (fun v : ULift.{1} (PLift Pair) => v.down.down) (eq_of_heq h)

@[expose] public def observe (p : Pair) : Bool :=
  Nat.casesOn p.1 false (fun n => Nat.casesOn n false (fun _ => true))

@[expose] public def separate (r : Pair → Pair → Prop) (q : carrier r) : Bool :=
  Quot.lift observe (by
    intro a b h
    rcases h.2 with h | ⟨x,y⟩ | ⟨x,y⟩
    · exact congrArg observe h
    · exact (congrArg observe (decode x)).trans (congrArg observe (decode y)).symm
    · exact (congrArg observe (decode x)).trans (congrArg observe (decode y)).symm) q

private theorem same (sound : type_of% @Quot.sound.{1}) (r : Pair → Pair → Prop) (h : r base mid) :
    point r base = point r mid :=
  @sound Pair (subrel r) base mid ⟨h, Or.inr (Or.inl ⟨HEq.rfl, HEq.rfl⟩)⟩

/-- In the refined native quotient, soundness identifies the two inputs while their specified
outputs have different Boolean observations. Soundness is an explicit premise of this
relative argument. The four interpreted primitives themselves are axiom-free. -/
public theorem incompatible (r : Pair → Pair → Prop) (related : r base mid)
    (f : carrier r → carrier r)
    (first : separate r (f (point r base)) = false)
    (second : separate r (f (point r mid)) = true) :
    ¬ type_of% @Quot.sound.{1} := fun sound =>
  Bool.noConfusion (first.symm.trans ((congrArg (fun q => separate r (f q)) (same sound r related)).trans second))

open Lean Lean.Grind
private abbrev ringNat : Semiring Nat := inferInstance
private abbrev moduleNat : NatModule Nat := inferInstance

public def sites := [
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.add),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.sub),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.mul),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.neg),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.nsmul),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.zsmul),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.npow),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.neg),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.nsmul),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.zsmul),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.add),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.sub)]

private def interpretations :=
  [(``Quot, ``carrier), (``Quot.mk, ``point), (``Quot.ind, ``ind), (``Quot.lift, ``lift)]

private def interpret (e : Expr) := e.replace fun t => do
  let .const n us := t | none
  let replacement ← interpretations.lookup n
  return mkConst replacement us

private def checkRules (official clean : Environment) : IO Unit := do
  for (original, target) in interpretations do
    let some (.quotInfo primitive) := official.find? original | throw <| IO.userError s!"missing primitive {original}"
    let some ci := clean.find? target | throw <| IO.userError s!"missing {target}"
    let ls := ci.levelParams.map Level.param
    let expected := interpret (primitive.type.instantiateLevelParams primitive.levelParams ls)
    unless Kernel.isDefEqGuarded clean {} ci.type expected do throw <| IO.userError s!"incorrect type for {target}"
    if original == ``Quot.lift || original == ``Quot.ind then
      let check := Meta.forallTelescope ci.type fun xs _ => do
        Meta.withLocalDeclD `a xs[0]! fun a => do
          let constructor := mkAppN (mkConst ``point [ls.head!]) #[xs[0]!, xs[1]!, a]
          let app := mkAppN (mkConst target ls) (xs.pop.push constructor)
          let .ok result := Kernel.whnf clean (← getLCtx) app | throwError "failed to reduce {target}"
          unless result.isApp && result.appFn!.equal xs[3]! && result.appArg!.equal a do
            throwError "incorrect symbolic computation at a quotient constructor for {target}"
      (Meta.MetaM.run' check).toIO' {fileName := "<refined quotient rules>", fileMap := default} {env := clean}

private def pair (a b : Nat) :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit a) (mkRawNatLit b)

private def natPair := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

private def arithmeticRelation : Pair → Pair → Prop
  | (a,b), (c,d) => ∃ k : Nat, a + d + k = b + c + k

private theorem arithmeticRelated : arithmeticRelation base mid := ⟨0, rfl⟩

/-- Check the two concrete calls against the pinned type and reductions. The refined quotient
collapses exactly the two designated pairs in this test under the ambient soundness premise. -/
public def certify (official witnesses : Environment) (owner : Name) (source : ConstantInfo) : IO Unit := do
  unless sites.contains (owner, source.name) && official.getModuleIdxFor? source.name == official.getModuleIdx? owner &&
      (source matches .defnInfo _) && source.numLevelParams == 1 do throw <| IO.userError s!"unexpected operation {source.name}"
  let ring := owner == `Init.Grind.Ring.Envelope
  let some inst := (witnesses.find? (if ring then ``ringNat else ``moduleNat)).bind ConstantInfo.value?
    | throw <| IO.userError "missing arithmetic instance"
  let op := mkApp2 (mkConst source.name [0]) (mkConst ``Nat) inst
  let .ok opType := Kernel.check official {} op | throw <| IO.userError "bad arithmetic specialization"
  -- Doubling, squaring and negating all separate the two off-diagonal representatives.
  let two := mkRawNatLit 2
  let pow := source.name == ``Ring.OfSemiring.npow
  let fixedScalar := match source.name with
    | ``Ring.OfSemiring.zsmul | ``IntModule.OfNatModule.zsmul => some (mkApp (mkConst ``Int.ofNat) two)
    | ``Ring.OfSemiring.nsmul | ``IntModule.OfNatModule.nsmul => some two
    | _ => none
  let scalarAction := fixedScalar.map (mkApp op)
  let .ok partialType := scalarAction.elim (.ok opType) (Kernel.check official {})
    | throw <| IO.userError "bad scalar specialization"
  let .ok (.forallE _ operand _ _) := Kernel.whnf official {} partialType
    | throw <| IO.userError "expected an envelope argument"
  let .ok quotient := Kernel.whnf official {} operand | throw <| IO.userError "invalid envelope carrier"
  unless quotient.isAppOfArity ``Quot 2 && Kernel.isDefEqGuarded official {} quotient.appFn!.appArg! natPair do
    throw <| IO.userError "incorrect representative type"
  let relation := quotient.appArg!
  let some canonical := (witnesses.find? ``arithmeticRelation).bind ConstantInfo.value?
    | throw <| IO.userError "missing arithmetic relation"
  unless Kernel.isDefEqGuarded witnesses {} relation canonical do
    throw <| IO.userError "unexpected relation on the pair envelope"
  let mk := mkApp2 (mkConst ``Quot.mk [1]) natPair relation
  let clean ← replayBoundaryDependencies official witnesses
    (``incompatible :: ``arithmeticRelated :: ``lift_beta :: ``ind_beta :: interpretations.map Prod.snd)
  checkRules official clean
  let relationModel := mkConst ``arithmeticRelation
  let modelPoint := mkApp2 (mkConst ``point [1]) natPair relationModel
  let observation := mkApp (mkConst ``separate) relationModel
  for (input, arg, expected) in [(pair 0 1, ``base, ``Bool.false), (pair 1 2, ``mid, ``Bool.true)] do
    unless Kernel.isDefEqGuarded clean {} input (mkConst arg) do throw <| IO.userError "wrong witness input"
    let point := mkApp mk input
    let call := match scalarAction with
      | some act => mkApp act point
      | none =>
        if [``Ring.OfSemiring.neg, ``IntModule.OfNatModule.neg].contains source.name then mkApp op point
        else mkApp2 op point (if pow then two else mkApp mk (pair 1 1))
    let .ok resultType := Kernel.check official {} call | throw <| IO.userError "invalid arithmetic application"
    unless Kernel.isDefEqGuarded official {} resultType operand do
      throw <| IO.userError "arithmetic application has the wrong result type"
    let .ok result := Kernel.whnf official {} call | throw <| IO.userError "invalid envelope application"
    unless result.isAppOfArity ``Quot.mk 3 && Kernel.isDefEqGuarded official {} result.appFn! mk do
      throw <| IO.userError "expected a quotient constructor in the pinned computation"
    -- Reify the constructor payload before crossing into the witness environment.
    let payload := result.appArg!
    let .ok coords := Kernel.whnf official {} payload | throw <| IO.userError "invalid representative"
    unless coords.isAppOfArity ``Prod.mk 4 do throw <| IO.userError "expected a pair in the pinned constructor"
    let natValue (e : Expr) : IO Nat := do
      let .ok v := Kernel.whnf official {} e | throw <| IO.userError "invalid coordinate"
      let some n := v.rawNatLit? | throw <| IO.userError "expected a natural coordinate"
      return n
    let checked := pair (← natValue coords.appFn!.appArg!) (← natValue coords.appArg!)
    unless Kernel.isDefEqGuarded official {} payload checked &&
        Kernel.isDefEqGuarded clean {} (mkApp observation (mkApp modelPoint checked)) (mkConst expected) do
      throw <| IO.userError s!"wrong observation at {arg} for {source.name}"
  let some law := clean.find? ``incompatible | throw <| IO.userError "missing refined counterexample"
  let application := mkApp2 (mkConst law.name) (mkConst ``arithmeticRelation) (mkConst ``arithmeticRelated)
  let .ok specialized := Kernel.check clean {} application | throw <| IO.userError "invalid refined model specialization"
  let some originalSound := official.find? ``Quot.sound | throw <| IO.userError "missing pinned quotient soundness"
  unless originalSound.isAxiom do throw <| IO.userError "unexpected pinned quotient soundness"
  let soundType := originalSound.type.instantiateLevelParams originalSound.levelParams [1]
  let verify := Meta.forallBoundedTelescope specialized (some 3) fun args conclusion => do
    let #[candidate, first, second] := args | throwError "expected a candidate and two observations"
    let rel := mkConst ``arithmeticRelation
    let q := mkApp2 (mkConst ``carrier [1]) natPair rel
    let ctx ← getLCtx
    let compare (term expected : Expr) := do
      unless Kernel.isDefEqGuarded clean ctx term expected do throwError "refined quotient witness type mismatch"
    compare (← Meta.inferType candidate) (.forallE `q q q .default)
    for (h, arg, value) in [(first, ``base, ``Bool.false), (second, ``mid, ``Bool.true)] do
      let input := mkApp3 (mkConst ``point [1]) natPair rel (mkConst arg)
      let observed := mkApp2 (mkConst ``separate) rel (mkApp candidate input)
      compare (← Meta.inferType h) (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) observed (mkConst value))
    compare conclusion (.forallE `sound soundType (mkConst ``False) .default)
  (Meta.MetaM.run' verify).toIO' {fileName := "<refined quotient arithmetic>", fileMap := default} {env := clean}

end OmegaChecks.InitBoundaries.RefinedQuotient
