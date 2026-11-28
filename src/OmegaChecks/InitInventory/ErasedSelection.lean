module
public import Init.Data.Erased
public import OmegaChecks.InitInventory.Order

namespace OmegaChecks.InitBoundaries.ErasedSelection
universe u

/-- Select a member when the predicate is given as equal to an actual singleton predicate. -/
public abbrev SingletonSelection := ∀ {α : Sort u} (s : α → Prop), (∃ a, (a = ·) = s) → {x // s x}

public abbrev LeftInverse (out : type_of% @Erased.out.{u}) := ∀ {α : Sort u} (a : α), out (Erased.mk a) = a

public abbrev RightInverse (out : type_of% @Erased.out.{u}) := ∀ {α : Sort u} (e : Erased α), Erased.mk (out e) = e

public theorem rightOfLeft (out : type_of% @Erased.out.{u}) (recover : LeftInverse (@out)) : RightInverse (@out) := by
  intro α e
  obtain ⟨s, a, ha⟩ := e
  cases ha
  exact congrArg Erased.mk (recover a)

public theorem leftOfRight (out : type_of% @Erased.out.{u}) (recover : RightInverse (@out)) : LeftInverse (@out) := by
  intro α a
  let eq := recover (Erased.mk a)
  exact (congrArg (fun e : Erased α => e.val a) eq).mpr rfl

public def ofLeft (out : type_of% @Erased.out.{u}) (recover : LeftInverse (@out)) : SingletonSelection.{u} := by
  intro α s h
  let e : Erased α := ⟨s, h⟩
  exact ⟨out e, (congrArg (fun q : Erased α => q.val (out e)) (rightOfLeft (@out) recover e)).mp rfl⟩

public def ofRight (out : type_of% @Erased.out.{u}) (recover : RightInverse (@out)) : SingletonSelection.{u} :=
  ofLeft (@out) (leftOfRight (@out) recover)

public def outOfSelection (pick : SingletonSelection.{u}) : type_of% @Erased.out.{u} :=
  fun {_} e => (pick e.val e.property).val

public theorem recoverOfSelection (pick : SingletonSelection.{u}) : LeftInverse (@outOfSelection (@pick)) := by
  intro α a
  exact (pick (Erased.mk a).val (Erased.mk a).property).property.symm

public theorem leftIffRight (out : type_of% @Erased.out.{u}) : LeftInverse (@out) ↔ RightInverse (@out) :=
  ⟨rightOfLeft (@out), leftOfRight (@out)⟩

/-- At the proposition universe the witness can be eliminated directly into its own proposition. -/
public def outProp : type_of% @Erased.out.{0} := fun {_} e => e.property.elim fun a _ => a

public theorem recoverProp : RightInverse (@outProp) :=
  rightOfLeft (@outProp) (fun _ => rfl)

/-- Test the extractor for injectivity only on values built with the public constructor. -/
public abbrev InjectiveOnConstructors (out : type_of% @Erased.out.{u}) :=
  ∀ {α : Sort u} {a b : α}, out (Erased.mk a) = out (Erased.mk b) → a = b

private theorem mkInjective {α : Sort u} {a b : α} (h : Erased.mk a = Erased.mk b) : a = b :=
  (congrArg (fun e : Erased α => e.val b) h).mpr rfl

public theorem outInjIffConstructors (out : type_of% @Erased.out.{u}) :
    (∀ {α : Sort u} {e f : Erased α}, out e = out f → e = f) ↔ InjectiveOnConstructors (@out) := by
  constructor
  · intro inj α a b h
    exact mkInjective (inj h)
  · intro inj α e f
    obtain ⟨s, a, ha⟩ := e
    obtain ⟨t, b, hb⟩ := f
    cases ha
    cases hb
    exact fun h => congrArg Erased.mk (@inj α a b h)

public theorem outInjIffLaw (out : type_of% @Erased.out.{u}) :
    (∀ {α : Sort u} {e f : Erased α}, e = f ↔ out e = out f) ↔ InjectiveOnConstructors (@out) := by
  constructor
  · intro law
    exact (outInjIffConstructors (@out)).mp (fun {_ _ _} h => law.mpr h)
  · intro inj α e f
    exact ⟨congrArg out, fun h => (outInjIffConstructors (@out)).mpr (@inj) h⟩

/-- The members of an explicitly singleton predicate form a nonempty subsingleton type. -/
public def selectionOfSubsingletonChoice (pick : InternalOrder.UniqueChoice.{max 1 u}) : SingletonSelection.{u} := by
  intro α s h
  letI : Subsingleton {x // s x} := ⟨fun x y => by
    obtain ⟨a, singleton⟩ := h
    have hx := (congrFun singleton x.val).mpr x.property
    have hy := (congrFun singleton y.val).mpr y.property
    exact Subtype.ext (hx.symm.trans hy)⟩
  exact pick (h.elim fun a singleton => ⟨⟨a, (congrFun singleton a).mp rfl⟩⟩)

/-- With extensional equality of predicates, even a bare polymorphic extractor selects from
every nonempty subsingleton. Its values are forced by the carrier in this use. -/
public def subsingletonChoiceOfOut
    (predExt : ∀ {α : Sort u} (f g : α → Prop), (∀ x, f x ↔ g x) → f = g)
    (out : type_of% @Erased.out.{u}) : InternalOrder.UniqueChoice.{u} :=
  fun {α} _ inhabited => out (α := α) ⟨fun _ => True, inhabited.elim fun a =>
    ⟨a, predExt (a = ·) (fun _ => True) (fun x => ⟨fun _ => trivial, fun _ => Subsingleton.elim a x⟩)⟩⟩

/-- A single extractor satisfies all four pinned laws at every sort universe. -/
public theorem lawsOfSelection (pick : SingletonSelection.{u}) :
    let out := @outOfSelection @pick
    LeftInverse (@out) ∧ RightInverse (@out) ∧
      (∀ {α : Sort u} {e f : Erased α}, out e = out f → e = f) ∧
      (∀ {α : Sort u} {e f : Erased α}, e = f ↔ out e = out f) := by
  let out := @outOfSelection @pick
  have left : LeftInverse (@out) := recoverOfSelection @pick
  have right : RightInverse (@out) := rightOfLeft (@out) left
  have inj : ∀ {α : Sort u} {e f : Erased α}, out e = out f → e = f :=
    fun {_ e f} h => (right e).symm.trans ((congrArg Erased.mk h).trans (right f))
  exact ⟨left, right, @inj, fun {_ _ _} => ⟨congrArg out, inj⟩⟩

/-- At the Boolean carrier a faithful extractor decides whether the erased predicate
contains false. -/
public def decideFalseOfBoolOut (out : Erased Bool → Bool) (recover : ∀ b, out (Erased.mk b) = b)
    (e : Erased Bool) : Decidable (e.val false) := by
  have member : e.val false ↔ out e = false := by
    obtain ⟨s, b, eq⟩ := e
    cases eq
    exact Iff.of_eq (congrArg (· = false) (recover b).symm)
  exact if h : out e = false then .isTrue (member.mpr h) else .isFalse fun p => h (member.mp p)

/-- A decision for that one predicate evaluation reconstructs the erased Boolean. -/
public def boolOutOfDecideFalse (test : (e : Erased Bool) → Decidable (e.val false)) (e : Erased Bool) : Bool :=
  @ite Bool (e.val false) (test e) false true

public theorem recoverBoolOfDecideFalse (test : (e : Erased Bool) → Decidable (e.val false)) (b : Bool) :
    boolOutOfDecideFalse test (Erased.mk b) = b := by
  unfold boolOutOfDecideFalse
  cases b with
  | false => exact ite_eq_left rfl
  | true => exact ite_eq_right Bool.noConfusion

example : LeftInverse (@Erased.out.{u}) := @Erased.out_mk
example : RightInverse (@Erased.out.{u}) := @Erased.mk_out
example : InjectiveOnConstructors (@Erased.out.{u}) :=
  (outInjIffConstructors (@Erased.out.{u})).mp @Erased.out_inj
example : InjectiveOnConstructors (@Erased.out.{u}) :=
  (outInjIffLaw (@Erased.out.{u})).mp @Erased.out_inj_iff

end OmegaChecks.InitBoundaries.ErasedSelection
