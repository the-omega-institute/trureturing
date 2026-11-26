module
public import Init.Control.Lawful.Instances
public import Init.Control.Lawful.MonadAttach.Lemmas
public import Init.Control.StateCps
public import Init.Control.ExceptCps

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

public theorem StateCpsT.instLawfulMonad : type_of% @_root_.StateCpsT.instLawfulMonad := by
  intros
  exact {
    map_const := rfl
    id_map := by intros; rfl
    comp_map := by intros; rfl
    pure_seq := by intros; rfl
    map_pure := by intros; rfl
    seq_pure := by intros; rfl
    seqLeft_eq := by intros; rfl
    seqRight_eq := by intros; rfl
    seq_assoc := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    pure_bind := by intros; rfl
    bind_assoc := by intros; rfl
  }

public theorem ExceptCpsT.instLawfulMonad : type_of% @_root_.ExceptCpsT.instLawfulMonad := by
  intros
  exact {
    map_const := rfl
    id_map := by intros; rfl
    comp_map := by intros; rfl
    pure_seq := by intros; rfl
    map_pure := by intros; rfl
    seq_pure := by intros; rfl
    seqLeft_eq := by intros; rfl
    seqRight_eq := by intros; rfl
    seq_assoc := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    pure_bind := by intros; rfl
    bind_assoc := by intros; rfl
  }

public theorem LawfulMonadAttach.canReturn_map_imp' : type_of% @_root_.LawfulMonadAttach.canReturn_map_imp' := by
  intro m α β b _ _ _ _ x f h
  let P (b : β) := ∃ a, MonadAttach.CanReturn x a ∧ f a = b
  let pack (w : Subtype (MonadAttach.CanReturn x)) : Subtype P := ⟨f w.val, w.val, w.property, rfl⟩
  have same : Subtype.val <$> (pack <$> MonadAttach.attach x) = f <$> x := calc
    _ = (Subtype.val ∘ pack) <$> MonadAttach.attach x := (comp_map ..).symm
    _ = f <$> (Subtype.val <$> MonadAttach.attach x) := comp_map Subtype.val f _
    _ = f <$> x := congrArg (f <$> ·) WeaklyLawfulMonadAttach.map_attach
  exact LawfulMonadAttach.canReturn_map_imp (P := P) (same.symm ▸ h)

end OmegaChecks.InitPort.Alternatives
