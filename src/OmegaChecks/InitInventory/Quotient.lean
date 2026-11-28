module
public import OmegaChecks.InitPort.Alternatives.Logic.Quotient
import all OmegaChecks.InitPort.Alternatives.Logic.Quotient
public import OmegaChecks.InitInventory.Replay
import OmegaChecks.InitInventory.EnvelopeCancellation

/-! The two public heterogeneous quotient eliminators have constructively inhabited types.
The pinned abbreviations reduce through a pair whose first component is the quotient
point. Equality of those pairs entails quotient soundness even for the unit motive. -/

namespace OmegaChecks.InitBoundaries.HeterogeneousQuotient

public abbrev hrecOn : type_of% @_root_.Quot.hrecOn :=
  @OmegaChecks.InitPort.Alternatives.Quot.hrecOn

public def hrecOnSetoid : type_of% @_root_.Quotient.hrecOn :=
  fun {α} {s} {motive} q f c => @hrecOn α s.r motive q f c

public theorem agrees.{u,v} {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}
    (q : Quot r) (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → r a b → HEq (f a) (f b)) :
    hrecOn q f c = _root_.Quot.hrecOn q f c := by
  induction q using Quot.ind
  rfl

public theorem setoidAgrees {α : Sort u} {s : Setoid α} {motive : Quotient s → Sort v}
    (q : Quotient s) (f : (a : α) → motive (Quotient.mk s a))
    (c : (a b : α) → s.r a b → HEq (f a) (f b)) :
    hrecOnSetoid q f c = _root_.Quotient.hrecOn q f c := agrees q f c

public theorem soundOfPairCoherence
    (coherent : ∀ {α : Sort u} {r : α → α → Prop} (a b : α), r a b →
      Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) a =
        Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) b) :
    type_of% @_root_.Quot.sound.{u} :=
  fun {α r a b} related => congrArg PSigma.fst (@coherent α r a b related)

/-- Restrict the public theorem to the constant unit family. Its transport
premise then holds by reflexivity for every pair of related representatives. -/
public theorem soundFromUnitCoherence
    (law : ∀ {α : Sort u} {r : α → α → Prop},
      (∀ (a b : α), r a b → () = ()) → ∀ (a b : α), r a b →
        Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) a =
          Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) b) :
    type_of% @_root_.Quot.sound.{u} :=
  soundOfPairCoherence fun a b related => law (fun _ _ _ => rfl) a b related

public theorem setoidSoundOfPairCoherence
    (coherent : ∀ {α : Sort u} {s : Setoid α} (a b : α), s.r a b →
      Quot.indep (motive := fun _ : Quotient s => Unit) (fun _ => ()) a =
        Quot.indep (motive := fun _ : Quotient s => Unit) (fun _ => ()) b) :
    type_of% @_root_.Quotient.sound.{u} :=
  fun {α s a b} related => congrArg PSigma.fst (@coherent α s a b related)

/-- At the unit motive the official coherence premise holds by definitional equality. -/
public theorem officialUnitCoherence {α : Sort u} {r : α → α → Prop} (a b : α) (related : r a b) :
    Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) a =
      Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) b :=
  Quot.indepCoherent _ (fun _ _ _ => rfl) a b related

/-- The first projection follows by quotient induction for any supplied pair coherence. -/
public theorem firstOfCoherence {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}
    (f : (a : α) → motive (Quot.mk r a))
    (coherent : ∀ a b, r a b → Quot.indep f a = Quot.indep f b) (q : Quot r) :
    (Quot.lift (Quot.indep f) coherent q).1 = q :=
  Quot.ind (β := fun x => (Quot.lift (Quot.indep f) coherent x).1 = x) (fun _ => rfl) q

/-- The pinned first-projection statement supplies precisely this coherence proof. -/
public theorem officialFirst {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}
    (f : (a : α) → motive (Quot.mk r a))
    (h : ∀ (a b : α) (p : r a b), Eq.ndrec (f a) (Quot.sound p) = f b) (q : Quot r) :
    firstOfCoherence f (Quot.indepCoherent f h) q = Quot.liftIndepPr1 f h q := rfl

/-- The lift's coherence argument may use the original premise and the quotient point.
Specialize them to reflexivity and the first representative's class. -/
public theorem soundOfLiftArgument
    (supply : ∀ {α : Sort u} {r : α → α → Prop},
      (∀ (a b : α), r a b → () = ()) → (q : Quot r) →
      ∀ (a b : α), r a b →
        Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) a =
          Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) b) :
    type_of% @Quot.sound.{u} :=
  soundOfPairCoherence fun {α} {r} a b rel =>
    @supply α r (fun _ _ _ => rfl) (Quot.mk r a) a b rel

open Lean Meta in
/-- Infer the required argument type from the partially applied lift inside the pinned
first projection. Quantify over all the locals in scope at that occurrence. -/
public def certifyLiftArgument (official : Environment) (source : ConstantInfo) : MetaM Unit := do
  let u := Level.param `u
  let declared := source.type.instantiateLevelParams source.levelParams [u, .one]
  forallBoundedTelescope declared (some 2) fun params body => do
    let #[α, r] := params | throwError "unexpected parameters"
    let qType := mkApp2 (mkConst ``Quot [u]) α r
    let motive := Expr.lam `q qType (mkConst ``Unit) .default
    let f := Expr.lam `a α (mkConst ``Unit.unit) .default
    let .forallE _ _ rest _ := body | throwError "expected motive"
    let .forallE _ _ rest _ := rest.instantiate1 motive | throwError "expected function"
    forallTelescope (rest.instantiate1 f) fun xs eq => do
      let #[h, q] := xs | throwError "expected coherence premise and quotient point"
      let some (_, lhs, rhs) := eq.eq? | throwError "expected equality"
      unless rhs == q && lhs.isAppOfArity ``PSigma.fst 3 do throwError "expected first projection"
      let lifted := lhs.appArg!
      unless lifted.isAppOfArity ``Quot.lift 6 && lifted.appArg! == q do
        throwError "unexpected first projection argument"
      let coherence := lifted.appFn!.appArg!
      unless coherence.isAppOfArity ``Quot.indepCoherent 5 && coherence.appArg! == h do
        throwError "unexpected coherence argument in the projection"
      let env ← getEnv
      let prefixType ← Lean.ofExceptKernelException (Kernel.check env (← getLCtx) lifted.appFn!.appFn!)
      let .forallE _ required _ _ := (← whnf prefixType) | throwError "missing formation premise"
      let actual ← Lean.ofExceptKernelException (Kernel.check env (← getLCtx) coherence)
      unless Kernel.isDefEqGuarded env (← getLCtx) actual required do throwError "ingredient type mismatch"
      let supplier ← mkForallFVars (params ++ xs) required
      let target ← getConstInfo ``Quot.sound
      let expected ← mkArrow supplier (target.type.instantiateLevelParams target.levelParams [u])
      let witness ← getConstInfo ``soundOfLiftArgument
      let ty := witness.type.instantiateLevelParams witness.levelParams [u]
      unless Kernel.isDefEqGuarded env {} expected ty do throwError "wrong reduction of formation premise"
      discard <| replayBoundaryDependencies official env [witness.name, ``firstOfCoherence]

open Lean Meta in
/-- Read the last argument of the transport in a recursor's coherence premise.
For recursors taking the quotient point first, use the first representative's class.
After abstracting the remaining inputs the required path has precisely the pinned
soundness type, with the original relation or setoid. -/
public def certifyTransportPath (official : Environment) (source : ConstantInfo) (setoid pointFirst : Bool) : MetaM Unit := do
  let env ← getEnv
  let u := Level.param `u
  let sound := if setoid then ``Quotient.sound else ``Quot.sound
  let target ← getConstInfo sound
  let soundType := target.type.instantiateLevelParams target.levelParams [u]
  let type := source.type.instantiateLevelParams source.levelParams [u, .one]
  forallTelescope soundType fun soundArgs goal => do
    let #[α, r, a, b, p] := soundArgs | throwError "unexpected soundness arguments"
    let q := mkApp3 (mkConst (if setoid then ``Quotient.mk else ``Quot.mk) [u]) α r a
    let qType ← inferType q
    let motive := Expr.lam `q qType (mkConst ``Unit) .default
    let f := Expr.lam `a α (mkConst ``Unit.unit) .default
    let args := if pointFirst then #[α, r, motive, q, f] else #[α, r, motive, f]
    let specialize := mkAppN (mkConst source.name [u, .one]) args
    let inferred ← ofExceptKernelException (Kernel.check env (← getLCtx) specialize)
    let .forallE _ law _ _ ← instantiateForall type args | throwError "missing coherence premise"
    unless Kernel.isDefEqGuarded env (← getLCtx) inferred (← instantiateForall type args) do
      throwError "recursor specialization disagrees with its physical declaration"
    let some (_, lhs, _) := (← instantiateForall law #[a, b, p]).eq? | throwError "missing coherence equation"
    unless lhs.isAppOfArity ``Eq.ndrec 6 do throwError "missing transport"
    let path := lhs.appArg!
    unless path == mkAppN (mkConst sound [u]) soundArgs do throwError "unexpected path {path}"
    let lift ← ofExceptKernelException (Kernel.check env (← getLCtx) lhs.appFn!)
    let .forallE _ required _ _ := (← whnf lift) | throwError "missing path binder"
    unless Kernel.isDefEqGuarded env (← getLCtx) required goal do throwError "the path has wrong type"
    let pathType ← mkForallFVars soundArgs required
    let clean ← replayBoundaryDependencies official env pathType.getUsedConstantsAsSet.toList
    discard <| ofExceptKernelException (Kernel.check clean {} pathType)
    unless Kernel.isDefEqGuarded clean {} soundType pathType do throwError "incomplete path type"

end OmegaChecks.InitBoundaries.HeterogeneousQuotient

namespace OmegaChecks.InitBoundaries.QuotientFibers
universe u v

/-- A pointed lift can return the element in a dependent fiber at the supplied
quotient point. Transport along the branch equality puts every value in that one
fiber, where subsingleton elimination supplies coherence. -/
public def unaryOfLift (lift : type_of% @Quot.pliftOn.{u,v}) :
    type_of% @Quot.recOnSubsingleton.{u,v} := fun {α r F} h q f =>
  letI := Quot.ind (β := fun x => Subsingleton (F x)) h q
  @lift (F q) α r q (fun a e => e.symm ▸ f a) (fun _ _ _ _ _ => Subsingleton.elim _ _)

public def unaryOfSetoidLift (lift : type_of% @Quotient.pliftOn.{u,v}) :
    type_of% @Quotient.recOnSubsingleton.{u,v} := fun {α s F} h q f =>
  letI := Quotient.ind (motive := fun x => Subsingleton (F x)) h q
  @lift (F q) α s q (fun a e => e.symm ▸ f a) (fun _ _ _ _ _ => Subsingleton.elim _ _)

private def unaryOfBinary (binary : type_of% @Quotient.recOnSubsingleton₂.{u,u,v}) :
    type_of% @Quotient.recOnSubsingleton.{u,v} := fun {α s F} h q f =>
  @binary α α s s (fun x _ => F x) (fun a _ => h a) q q (fun a _ => f a)

/-- This direction needs no relation between the two carrier universes when a unary
eliminator is available for each carrier. -/
public def binaryOfUnaries.{u₁,u₂,w} (first : type_of% @Quotient.recOnSubsingleton.{u₁,w})
    (second : type_of% @Quotient.recOnSubsingleton.{u₂,w}) :
    type_of% @Quotient.recOnSubsingleton₂.{u₁,u₂,w} := fun {α β s t F} h x y f =>
  @first α s (fun a => F a y)
    (fun a => Quotient.ind (motive := fun b => Subsingleton (F (Quotient.mk s a) b)) (h a) y) x
    (fun a => @second β t (fun b => F (Quotient.mk s a) b) (h a) y (f a))

public theorem unaryIffBinary : Nonempty (type_of% @Quotient.recOnSubsingleton.{u,v}) ↔
    Nonempty (type_of% @Quotient.recOnSubsingleton₂.{u,u,v}) :=
  ⟨fun ⟨unary⟩ => ⟨binaryOfUnaries @unary @unary⟩, fun ⟨binary⟩ => ⟨unaryOfBinary @binary⟩⟩

/-- A quotient of a proposition supplies its own representative by small elimination.
Proof irrelevance identifies its class with the requested point in every target universe. -/
public def liftFromProp : type_of% @Quot.pliftOn.{0,v} := fun {_ α r} q f _ =>
  let a : α := Quot.ind (β := fun _ : Quot r => α) (fun a => a) q
  f a rfl

/-- In a propositional target the representative can instead be used inside existential elimination. -/
public theorem liftToProp : type_of% @Quot.pliftOn.{u,0} := fun {_ _ _} q f _ => by
  obtain ⟨a, e⟩ := Quot.exists_rep q
  exact f a e.symm

/-- Supply an element only when the entire fiber is subsingleton and known to be inhabited. -/
public abbrev SubsingletonSelection := ∀ {T : Sort v}, Subsingleton T → Nonempty T → T

public def unaryOfSelection (pick : SubsingletonSelection.{v}) : type_of% @Quot.recOnSubsingleton.{u,v} :=
  fun {_ r F} h q f => pick
    (Quot.ind (β := fun q : Quot r => Subsingleton (F q)) h q)
    (Quot.ind (β := fun q : Quot r => Nonempty (F q)) (fun a => ⟨f a⟩) q)

/-- Exactness makes all outputs obtainable from representatives of this one quotient point equal. -/
public def setoidLiftOfSelection (pick : SubsingletonSelection.{max 1 v}) (exactRep : type_of% @Quotient.exact.{u}) :
    type_of% @Quotient.pliftOn.{u,v} := fun {β α s} q f coherent => by
  let T := {b : β // ∃ (a : α) (e : q = Quotient.mk s a), f a e = b}
  have inhabited : Nonempty T := by
    obtain ⟨a, e⟩ := Quotient.exists_rep q
    exact ⟨⟨f a e.symm, a, e.symm, rfl⟩⟩
  have unique : Subsingleton T := ⟨fun x y => by
    obtain ⟨a, e, hx⟩ := x.property
    obtain ⟨b, d, hy⟩ := y.property
    exact Subtype.ext (hx.symm.trans ((coherent a b e d (exactRep (e.symm.trans d))).trans hy))⟩
  exact (pick unique inhabited).val

public theorem setoidLiftOfSelection_mk
    (pick : SubsingletonSelection.{max 1 v}) (exactRep : type_of% @Quotient.exact.{u})
    {β : Sort v} {α : Sort u} {s : Setoid α} (a : α)
    (f : ∀ b, Quotient.mk s a = Quotient.mk s b → β)
    (coherent : ∀ b c (e : Quotient.mk s a = Quotient.mk s b) (d : Quotient.mk s a = Quotient.mk s c),
      s.r b c → f b e = f c d) :
    setoidLiftOfSelection (@pick) (@exactRep) (Quotient.mk s a) f coherent = f a rfl := by
  have branch (x : {z : β // ∃ (b : α) (e : Quotient.mk s a = Quotient.mk s b), f b e = z}) :
      x.val = f a rfl := by
    obtain ⟨b, e, h⟩ := x.property
    exact h.symm.trans (coherent b a e rfl (exactRep e.symm))
  exact branch _

end OmegaChecks.InitBoundaries.QuotientFibers

namespace OmegaChecks.InitBoundaries.QuotientDecision

universe u v

/-- Soundness restricted to setoids whose relations have decisions. -/
public abbrev DecidableRelationSound : Prop :=
  ∀ {α : Sort u} {s : Setoid α} [∀ a b : α, Decidable (s.r a b)] {a b : α},
    s.r a b → Quotient.mk s a = Quotient.mk s b

private def compare {α : Sort u} {s : Setoid α} [d : ∀ a b, Decidable (s.r a b)]
    (x y : Quotient s) : Bool :=
  Quotient.liftOn₂ x y (fun a b => decide (s.r a b)) fun a b a' b' ha hb => by
    cases d a b with
    | isTrue yes =>
      cases d a' b' with
      | isTrue yes' => rfl
      | isFalse no => exact (no (s.iseqv.trans (s.iseqv.symm ha) (s.iseqv.trans yes hb))).elim
    | isFalse no =>
      cases d a' b' with
      | isTrue yes => exact (no (s.iseqv.trans ha (s.iseqv.trans yes (s.iseqv.symm hb)))).elim
      | isFalse no' => rfl

/-- Testing against the class of the fixed representative reflects equality of quotient points. -/
public theorem exactOfDecidable {α : Sort u} {s : Setoid α} [d : ∀ a b, Decidable (s.r a b)]
    {a b : α} (h : Quotient.mk s a = Quotient.mk s b) : s.r a b := by
  have h' := congrArg (compare (Quotient.mk s a)) h
  change decide (s.r a a) = decide (s.r a b) at h'
  exact of_decide_eq_true (h'.symm.trans (decide_eq_true (s.iseqv.refl a)))

/-- Restricted soundness suffices to realize the full decision interface. -/
public def ofSound (sound : DecidableRelationSound.{u}) : type_of% @Quotient.decidableEq.{u} := by
  intro α s d x y
  refine if h : compare x y = true then isTrue ?_ else isFalse ?_
  · induction x using Quotient.ind with | _ a
    induction y using Quotient.ind with | _ b
    exact sound (of_decide_eq_true h)
  · intro e
    cases e
    induction x using Quotient.ind with | _ a
    exact h (decide_eq_true (s.iseqv.refl a))

public theorem decisionsOnRepresentatives (classify : type_of% @Quotient.decidableEq.{u})
    (sound : DecidableRelationSound.{u}) {α : Sort u}
    {s : Setoid α} [d : ∀ a b, Decidable (s.r a b)] (a b : α) :
    @decide _ (@classify α s d (Quotient.mk s a) (Quotient.mk s b)) = decide (s.r a b) := by
  letI : Decidable (Quotient.mk s a = Quotient.mk s b) := @classify α s d _ _
  cases d a b with
  | isTrue yes => exact decide_eq_true (sound yes)
  | isFalse no => exact decide_eq_false (fun h => no (exactOfDecidable h))

public theorem soundFromAgreement
    (classify : type_of% @Quotient.decidableEq.{u})
    (agree : ∀ {α : Sort u} {s : Setoid α} [d : ∀ a b, Decidable (s.r a b)] (a b : α),
      @decide _ (@classify α s d (Quotient.mk s a) (Quotient.mk s b)) = decide (s.r a b)) :
    DecidableRelationSound.{u} := by
  intro α s d a b h
  exact @of_decide_eq_true _ (@classify α s d (Quotient.mk s a) (Quotient.mk s b))
      ((agree a b).trans (decide_eq_true h))

public theorem officialRepresentatives {α : Sort u} {s : Setoid α} [d : ∀ a b, Decidable (s.r a b)] (a b : α) :
    @decide _ (@Quotient.decidableEq α s d (Quotient.mk s a) (Quotient.mk s b)) = decide (s.r a b) := by
  exact decisionsOnRepresentatives (@Quotient.decidableEq) (fun {_ _} [_] {_ _} => Quotient.sound) a b

public abbrev interval := Quotient (Setoid.trivial Bool)
public abbrev point (x : Bool) : interval := Quotient.mk _ x

private theorem funextOfInterval (path : point false = point true) : type_of% @funext.{u,v} := by
  intro α β f g h
  let vary (t : interval) (x : α) : β x :=
    Quotient.liftOn t (fun b => Bool.casesOn b (f x) (g x)) (fun a b _ => by
      cases a <;> cases b
      · rfl
      · exact h x
      · exact (h x).symm
      · rfl)
  exact congrArg vary path

/-- The two distinct representatives of the indiscrete Boolean quotient give the endpoints of an interval. -/
public theorem funextOfPositiveDecision (classify : type_of% @Quotient.decidableEq.{1})
    (positive : @decide (point false = point true)
      (@classify Bool (Setoid.trivial Bool) (fun _ _ => isTrue trivial) _ _) = true) :
    type_of% @funext.{u,v} :=
  funextOfInterval (@of_decide_eq_true _ (@classify Bool (Setoid.trivial Bool) (fun _ _ => isTrue trivial) _ _) positive)

public theorem officialPositive : @decide (point false = point true)
    (@Quotient.decidableEq Bool (Setoid.trivial Bool) (fun _ _ => isTrue trivial) _ _) = true := rfl

end OmegaChecks.InitBoundaries.QuotientDecision

namespace OmegaChecks.InitBoundaries.RepresentativeQuotient

/-! A model of the four quotient primitives of the axiom-free kernel. Each quotient is
interpreted by its representative type. Induction and lifting compute at a class
by ordinary function application, including for relations that identify distinct
representatives. Specializing the translated soundness or squash statement to
the indiscrete setoid on Bool would therefore identify its two constructors. -/

@[expose] public def carrier {α : Sort u} (_r : α → α → Prop) := α
@[expose] public def point {α : Sort u} (r : α → α → Prop) (a : α) : carrier r := a

set_option linter.defProp false in
@[expose] public def induction {α : Sort u} {r : α → α → Prop} {motive : carrier r → Prop}
    (step : ∀ a, motive (point r a)) (q : carrier r) : motive q := step q

@[expose] public def lift {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (_h : ∀ a b, r a b → f a = f b) (q : carrier r) : β := f q

public theorem induction_mk {α : Sort u} {r : α → α → Prop} {p : carrier r → Prop}
    (f : ∀ a, p (point r a)) (a : α) : induction f (point r a) = f a := rfl

public theorem lift_mk {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ a b, r a b → f a = f b) (a : α) : lift f h (point r a) = f a := rfl

public theorem refuteSound
    (law : ∀ {α : Type} {s : Setoid α} {a b : α}, s.r a b → a = b) : False :=
  Bool.noConfusion (@law Bool (Setoid.trivial Bool) false true trivial)

/-- In the representative interpretation the two classes computed by envelope cancellation
at the class of (1,0) are distinct for every relation on pairs. -/
public theorem refuteEnvelopeCancellation (r : Nat × Nat → Nat × Nat → Prop)
    (h : point r (1, 1) = point r (0, 0)) : False :=
  Nat.noConfusion (congrArg Prod.fst h)

public theorem refuteSquash (law : ∀ {α : Type}, Subsingleton α) : False :=
  Bool.noConfusion ((@law Bool).allEq false true)

/-- In the representative interpretation, every equality decision on the two Booleans
must answer false, even when the setoid relates every pair. -/
public theorem refutePositiveDecision
    (classify : ∀ {α : Type} {s : Setoid α} [∀ a b : α, Decidable (s.r a b)], DecidableEq α)
    (positive : @decide (false = true)
      (@classify Bool (Setoid.trivial Bool) (fun _ _ => isTrue trivial) false true) = true) : False :=
  Bool.noConfusion (@of_decide_eq_true _
    (@classify Bool (Setoid.trivial Bool) (fun _ _ => isTrue trivial) false true) positive)

open Lean

private def primitives : List (Name × Name) :=
  [(``Quot, ``carrier), (``Quot.mk, ``point), (``Quot.ind, ``induction), (``Quot.lift, ``lift)]

private def expand (env : Environment) (type : Expr) (names : List Name) : Expr := Id.run do
  let mut e := type
  for name in names do
    e := e.replace fun t => do
      let .const n levels := t | none
      guard (n == name)
      let ci ← env.find? name
      return ci.instantiateValueLevelParams! levels
  return e

private def interpret (official : Environment) (type : Expr) : Expr :=
  let e := expand official type [``Squash, ``Quotient.mk, ``Quotient]
  e.replace fun t => do
    let .const n levels := t | none
    let (_, target) ← primitives.find? (·.1 == n)
    return mkConst target levels

/-- Normalize the interpreted eliminator at a symbolic representative. Compare its branch
and argument separately, since weak head reduction does not reduce arguments. -/
private def checkComputation (env : Environment) (elim : ConstantInfo) : Meta.MetaM Unit := do
  let levels := elim.levelParams.map Level.param
  Meta.forallTelescope elim.type fun xs _ => do
    let u := levels.head!
    Meta.withLocalDeclD `a xs[0]! fun a => do
      let mk := mkAppN (mkConst ``point [u]) #[xs[0]!, xs[1]!, a]
      let call := mkAppN (mkConst elim.name levels) (xs.pop.push mk)
      let ctx ← getLCtx
      let reduced ← ofExceptKernelException (Kernel.whnf env ctx call)
      unless reduced.isApp && reduced.appFn!.equal xs[3]! do
        throwError "representative computation for {elim.name} did not return its branch"
      let arg ← ofExceptKernelException (Kernel.whnf env ctx reduced.appArg!)
      unless arg.equal a do throwError "wrong representative in the branch of {elim.name}"

public def refuter? (owner name : Name) : Option Name := do
  if let some op := EnvelopeCancellation.liftOperation? owner name then
    guard (op != name)
    return ``refuteEnvelopeCancellation
  if (EnvelopeCancellation.observation? owner name).isSome then
    return ``refuteEnvelopeCancellation
  guard (owner == `Init.Core)
  if name == ``Quotient.sound then some ``refuteSound
  else if name == ``instSubsingletonSquash then some ``refuteSquash
  else if name == ``Quotient.decidableEq then some ``refutePositiveDecision
  else none

/-- Check the interpreted primitive signatures and the Bool counterexample against
the physical statement of the selected declaration. Replay every term of this
argument in an environment that does not contain the quotient primitives. -/
public def certify (official witnesses : Environment) (source : ConstantInfo) (refuter : Name) : IO Unit := do
  let some proof := witnesses.find? refuter | throw <| IO.userError s!"missing {refuter}"
  let decision := source.name == ``Quotient.decidableEq
  let envelope := refuter == ``refuteEnvelopeCancellation
  unless (if envelope then source.isTheorem || (source matches .defnInfo _) else if decision then
      source matches .defnInfo _ else source.isTheorem) && source.numLevelParams == 1 do
    throw <| IO.userError s!"unexpected signature at {source.name}"
  let type := interpret official (source.type.instantiateLevelParams source.levelParams [.one])
  let expected ← if envelope then
    EnvelopeCancellation.counterexample official witnesses source ``point
  else if decision then do
    let some observation := witnesses.find? ``QuotientDecision.officialPositive
      | throw <| IO.userError "missing equality decision observation"
    let equation := expand witnesses observation.type [``QuotientDecision.point, ``QuotientDecision.interval]
    let some (_, lhs, rhs) := equation.eq? | throw <| IO.userError "expected an observation equation"
    unless rhs.isConstOf ``Bool.true && lhs.getUsedConstantsAsSet.contains source.name do
      throw <| IO.userError "expected positive observation of the pinned equality decision"
    let .ok observed := Kernel.whnf official {} lhs | throw <| IO.userError "unreducible equality decision"
    unless observed.equal rhs do throw <| IO.userError "unexpected pinned equality decision"
    let translated := interpret official equation
    let decisionVar := mkFVar ⟨`representativeEqualityDecision⟩
    let abstracted := (translated.replace fun t =>
      if t == mkConst source.name [.one] then some decisionVar else none).abstract #[decisionVar]
    pure <| Expr.forallE `classify type (.forallE `positive abstracted (mkConst ``False) .default) .default
  else pure <| Expr.forallE .anonymous type (mkConst ``False) .default
  let clean ← replayBoundaryDependencies official witnesses (refuter :: ``lift_mk :: ``induction_mk ::
    primitives.map Prod.snd ++ expected.getUsedConstantsAsSet.toList)
  if primitives.any fun p => clean.contains p.1 then
    throw <| IO.userError "representative interpretation still depends on native quotients"
  for (original, replacement) in primitives do
    let some (.quotInfo prim) := official.find? original | throw <| IO.userError s!"missing primitive {original}"
    let some dst := clean.find? replacement | throw <| IO.userError s!"missing {replacement}"
    let signature := interpret official (prim.type.instantiateLevelParams prim.levelParams (dst.levelParams.map Level.param))
    unless Kernel.isDefEqGuarded clean {} dst.type signature do
      throw <| IO.userError s!"invalid interpretation of {original}"
    if original == ``Quot.ind || original == ``Quot.lift then
      (Meta.MetaM.run' (checkComputation clean dst)).toIO'
        {fileName := "<quotient representative computation>", fileMap := default} {env := clean}
  if let .error _ := Kernel.check clean {} expected then
    throw <| IO.userError s!"ill-formed counterexample for {source.name}"
  unless Kernel.isDefEqGuarded clean {} proof.type expected do
    throw <| IO.userError s!"counterexample has the wrong domain for {source.name}"

end OmegaChecks.InitBoundaries.RepresentativeQuotient
