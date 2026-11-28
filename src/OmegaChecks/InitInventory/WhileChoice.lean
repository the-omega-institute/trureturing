module
public import Init.While
import all Init.While

namespace OmegaChecks.InitBoundaries.WhileChoice

/-- A completed action carries its parity. An exception carries the selected element. -/
private abbrev Action (ε : Type u) (β : Type u) := Except ε (Bool × β)

private def toggle (r : Action ε β) : Action ε β :=
  match r with
  | .error x => .error x
  | .ok (b, a) => .ok (!b, a)

private instance : Monad (Action ε) where
  pure a := .ok (false, a)
  bind r k := match r with
    | .error x => .error x
    | .ok (false, a) => k a
    | .ok (true, a) => toggle (k a)

private def step (ε : Type u) (_ : Unit) (s : PUnit.{u+1}) : Action ε (ForInStep PUnit.{u+1}) :=
  .ok (true, .yield s)

private def program (ε : Type u) (s : PUnit.{u+1}) : Action ε (PUnit.{u+1} ⊕ PUnit.{u+1}) :=
  .ok (true, .inl s)

private abbrev outcome (run : type_of% @Lean.Loop.forIn.{u,u}) (ε : Type u) : Action ε PUnit.{u+1} :=
  @run PUnit.{u+1} (Action ε) inferInstance {} .unit (step ε)

public def fixed (run : type_of% @Lean.Loop.forIn.{u,u}) : Prop :=
  ∀ (ε : Type u), Nonempty ε → outcome (@run) ε = toggle (outcome (@run) ε)

/-- A constant exception is a fixed point for every inhabitant of the exception type.
The pinned loop's fixed-point equation therefore applies when that type is nonempty. -/
public theorem officialFixed : fixed (@Lean.Loop.forIn.{u,u}) := by
  intro ε inhabited
  have existsFix : ∃ g, repeatM.body (program ε) g = g :=
    inhabited.elim fun x => ⟨fun _ => .error x, rfl⟩
  exact @repeatM_eq _ (Action ε) _ _ _ (program ε) PUnit.unit existsFix

/-- A successful result would equal its own Boolean complement. -/
public def choiceFromLoop (run : type_of% @Lean.Loop.forIn.{u,u}) (h : fixed (@run)) :
    type_of% @Classical.choice.{u} := by
  intro α inhabited
  have law := h (PLift α) (inhabited.elim fun x => ⟨⟨x⟩⟩)
  cases result : outcome (@run) (PLift α) with
  | error x => exact x.down
  | ok pair =>
    rw [result] at law
    obtain ⟨b, s⟩ := pair
    cases b <;> cases law

private abbrev instanceLoop (inst : type_of% @Lean.instForInLoopUnitOfMonad.{u,u}) :
    type_of% @Lean.Loop.forIn.{u,u} :=
  fun {β m} [mm : Monad m] => @ForIn.forIn m Lean.Loop Unit (@inst m mm) β

public def instanceFixed (inst : type_of% @Lean.instForInLoopUnitOfMonad.{u,u}) : Prop :=
  fixed (@instanceLoop (@inst))

public theorem officialInstanceFixed : instanceFixed (@Lean.instForInLoopUnitOfMonad.{u,u}) :=
  officialFixed

public def choiceFromInstance (inst : type_of% @Lean.instForInLoopUnitOfMonad.{u,u})
    (h : instanceFixed (@inst)) : type_of% @Classical.choice.{u} :=
  choiceFromLoop (@instanceLoop (@inst)) h

end OmegaChecks.InitBoundaries.WhileChoice
