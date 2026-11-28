import OmegaInit.Prelude

private def representative (n : Nat) : Omega.Quot (@Eq Nat) :=
  Omega.Quot.mk _ n

private def readRepresentative (q : Omega.Quot (@Eq Nat)) : Nat :=
  Omega.Quot.lift (fun n => n) (fun _ _ h => h) q

example (n : Nat) : readRepresentative (representative n) = n := rfl

example (q : Omega.Quot (@Eq Nat)) : representative (readRepresentative q) = q :=
  Omega.Quot.ind (β := fun x => representative (readRepresentative x) = x) (fun _ => rfl) q

#guard readRepresentative (representative 37) == 37
