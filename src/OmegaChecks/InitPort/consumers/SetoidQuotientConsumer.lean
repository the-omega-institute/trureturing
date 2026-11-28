import OmegaInit.Core

@[instance_reducible] private def natEq : Omega.Setoid Nat where
  r := Eq
  iseqv := { refl := Eq.refl, symm := Eq.symm, trans := Eq.trans }

private def joinDigits (x y : Omega.Quotient natEq) : Nat :=
  Omega.Quotient.liftOn₂ x y (fun a b => a * 10 + b) (by
    intro _ _ _ _ ha hb
    cases ha
    cases hb
    rfl)

example (a b : Nat) :
    joinDigits (Omega.Quotient.mk natEq a) (Omega.Quotient.mk natEq b) = a * 10 + b := rfl

example (q : Omega.Quotient natEq) : ∃ a : Nat, Omega.Quotient.mk natEq a = q :=
  Omega.Quotient.inductionOn (motive := fun x => ∃ a : Nat, Omega.Quotient.mk natEq a = x)
    q (fun a => ⟨a, rfl⟩)

#guard joinDigits (Omega.Quotient.mk natEq 13) (Omega.Quotient.mk natEq 7) == 137

private def rank (q : Omega.Quotient natEq) : Nat :=
  Omega.Quotient.liftOn q (fun n => n) (fun _ _ h => h)

private def index (q : Omega.Quotient natEq) : Fin (rank q + 1) :=
  Omega.Quotient.hrecOn (motive := fun x => Fin (rank x + 1))
    q (fun n => ⟨n, Nat.lt_succ_self n⟩) (by intro _ _ h; cases h; rfl)

#guard (index (Omega.Quotient.mk natEq 37)).val == 37

example {α : Sort u} (q : Omega.Squash α) : ∃ a : α, Omega.Squash.mk a = q :=
  Omega.Squash.ind (motive := fun x => ∃ a : α, Omega.Squash.mk a = x) (fun a => ⟨a, rfl⟩) q

private def liftSquash {α β : Sort u} [Omega.Subsingleton β] (q : Omega.Squash α) (f : α → β) : β :=
  Omega.Squash.lift q f

example {α β : Sort u} [Omega.Subsingleton β] (a : α) (f : α → β) :
    liftSquash (Omega.Squash.mk a) f = f a := rfl

private def recover (n : Nat) (s : Omega.Squash Nat) : { k : Nat // k = n } :=
  haveI : Omega.Subsingleton { k : Nat // k = n } :=
    ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩
  liftSquash s (fun _ => ⟨n, rfl⟩)

#guard (recover 37 (Omega.Squash.mk 7)).val == 37
