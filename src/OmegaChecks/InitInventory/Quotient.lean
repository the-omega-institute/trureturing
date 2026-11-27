module
public import OmegaChecks.InitPort.Alternatives.Logic.Quotient
import all OmegaChecks.InitPort.Alternatives.Logic.Quotient
public import OmegaChecks.InitInventory.Replay

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
