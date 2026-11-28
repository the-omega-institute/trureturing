module
public import Init.Data.Erased

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

example : LeftInverse (@Erased.out.{u}) := @Erased.out_mk
example : RightInverse (@Erased.out.{u}) := @Erased.mk_out

end OmegaChecks.InitBoundaries.ErasedSelection
