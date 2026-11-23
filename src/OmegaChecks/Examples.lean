prelude
import OmegaMath

open Omega

namespace Tests

private noncomputable def two := Nat.succ Nat.one

example : Eq (Projective.kappa Nat.zero Nat.one) (Ratio.value Nat.one Nat.one) :=
  Eq.refl
example : Eq (Projective.kappa Nat.one Nat.one) (Ratio.value Nat.one two) :=
  Eq.refl
example : Eq (Projective.kappa Nat.one Nat.zero) (Ratio.value Nat.zero Nat.one) :=
  Eq.refl
example : Eq (Projective.kappa Nat.zero Nat.zero) Ratio.undefined := Eq.refl
example : Ratio.Equivalent (Projective.kappa two two) (Ratio.value Nat.one two) :=
  Eq.refl
example (p q k : Nat) :
    Ratio.Equivalent (Projective.kappa (Nat.mul p (Nat.succ k)) (Nat.mul q (Nat.succ k)))
      (Projective.kappa p q) :=
  Projective.kappa_scale p q k

end Tests
