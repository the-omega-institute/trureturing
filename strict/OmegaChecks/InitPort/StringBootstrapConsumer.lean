module
prelude
public import OmegaInit.Data.String.Bootstrap

@[export omega_test_bootstrap_text]
public def bootstrapText (s sep : Omega.String) (mark : Omega.Char) (start : Nat) : Omega.String :=
  let matches := fun (c : Omega.Char) => Nat.beq c.val.toNat mark.val.toNat
  let stop := Omega.String.Internal.nextWhile s matches ⟨start⟩
  let run := Omega.Substring.Raw.Internal.takeWhile ⟨s, ⟨start⟩, stop⟩ matches
  let copy := Omega.String.Internal.foldl Omega.String.push sep (Omega.Substring.Raw.Internal.toString run)
  Omega.String.Internal.intercalate sep (.cons copy (.cons s .nil))
