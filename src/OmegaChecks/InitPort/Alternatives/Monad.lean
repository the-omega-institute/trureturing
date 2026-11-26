module
public import Init.Control.Lawful.Instances

/-! Monad laws for optional values and exceptions, and reduction of state operations. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem instLawfulMonadOption : LawfulMonad Option where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map f g x := by cases x <;> rfl
  pure_seq f x := by cases x <;> rfl
  map_pure f x := rfl
  seq_pure f x := by cases f <;> rfl
  seqLeft_eq x y := by cases x <;> cases y <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  seq_assoc x f g := by cases g <;> cases f <;> cases x <;> rfl
  bind_pure_comp f x := by cases x <;> rfl
  bind_map f x := by cases f <;> cases x <;> rfl
  pure_bind a f := rfl
  bind_assoc x f g := by cases x <;> rfl

public theorem instLawfulMonadExcept : LawfulMonad (Except ε) where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map f g x := by cases x <;> rfl
  pure_seq f x := by cases x <;> rfl
  map_pure f x := rfl
  seq_pure f x := by cases f <;> rfl
  seqLeft_eq x y := by cases x <;> cases y <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  seq_assoc x f g := by cases g <;> cases f <;> cases x <;> rfl
  bind_pure_comp f x := by cases x <;> rfl
  bind_map f x := by cases f <;> cases x <;> rfl
  pure_bind a f := rfl
  bind_assoc x f g := by cases x <;> rfl

public theorem StateT.run_liftWith [Monad m] [LawfulMonad m]
    (f : ({β : Type u} → StateT σ m β → m (stM m (StateT σ m) β)) → m α) (s : σ) :
    StateT.run (liftWith f) s = ((·, s) <$> f fun x => x.run s) := by
  dsimp [liftWith, MonadControl.liftWith, StateT.run, StateT.bind, StateT.get, StateT.lift]
  rw [pure_bind]
  exact bind_pure_comp _ _

public theorem StateT.run_restoreM [Monad m] [LawfulMonad m] (x : stM m (StateT σ m) α) (s : σ) :
    StateT.run (restoreM x) s = pure x := by
  dsimp [restoreM, MonadControl.restoreM, StateT.run, StateT.bind, StateT.lift]
  rw [pure_bind, pure_bind, pure_bind]

end OmegaChecks.InitPort.Alternatives
