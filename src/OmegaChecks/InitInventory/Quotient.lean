module
public import OmegaChecks.InitPort.Alternatives.Logic.Quotient
import all OmegaChecks.InitPort.Alternatives.Logic.Quotient

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
