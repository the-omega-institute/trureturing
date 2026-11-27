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
