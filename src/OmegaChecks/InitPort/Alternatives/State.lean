module
public import Init.Control.Lawful.Instances

/-! Restoring and lifting computations in a state transformer. -/

namespace OmegaChecks.InitPort.Alternatives

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
