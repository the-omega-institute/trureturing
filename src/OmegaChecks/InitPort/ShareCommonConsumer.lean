module
prelude
public import OmegaInit.ShareCommon

@[export omega_share_common_pair]
public def sharePair (factory : Omega.ShareCommon.StateFactory) (x y : Omega.List Omega.Bool) :
    Omega.Prod (Omega.List Omega.Bool) (Omega.List Omega.Bool) :=
  Omega.ShareCommonM.run (σ := factory) fun initial =>
    let first := Omega.ShareCommon.State.shareCommon initial x
    let second := Omega.ShareCommon.State.shareCommon first.snd y
    ⟨⟨first.fst, second.fst⟩, second.snd⟩

private def functionalBuilder : Omega.ShareCommon.StateFactoryBuilder where
  Map := fun α β _ _ => Omega.Prod Omega.Nat (α → Omega.Option β)
  mkMap := fun capacity => ⟨capacity, fun _ => .none⟩
  mapFind? := fun map key => map.snd key
  mapInsert := @fun _ _ eq _ map key value => ⟨map.fst, fun query =>
    Omega.Bool.casesOn (motive := fun _ => Omega.Option _) (eq.beq key query)
      (map.snd query) (.some value)⟩
  Set := fun α _ _ => Omega.Prod Omega.Nat (α → Omega.Option α)
  mkSet := fun capacity => ⟨capacity, fun _ => .none⟩
  setFind? := fun set key => set.snd key
  setInsert := @fun _ eq _ set value => ⟨set.fst, fun query =>
    Omega.Bool.casesOn (motive := fun _ => Omega.Option _) (eq.beq value query)
      (set.snd query) (.some value)⟩

@[export omega_share_common_custom_factory]
public def customFactory (_ : Omega.PUnit.{1}) : Omega.ShareCommon.StateFactory :=
  Omega.ShareCommon.StateFactory.mk functionalBuilder

@[export omega_share_common_new_state]
public def newState (factory : Omega.ShareCommon.StateFactory) : Omega.ShareCommon.State.{0} factory :=
  Omega.ShareCommon.State.mk factory
