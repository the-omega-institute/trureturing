module
prelude
public import OmegaInit.Prelude
import all OmegaInit.Prelude

/-! Certificates for comparison of the strict binary expansion of numerals. -/

noncomputable section
set_option allowUnsafeReducibility true
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul

namespace OmegaLiteralProofs
open Omega

public theorem rightMono (k : Nat) (a b : Nat) (h : Nat.le a b) : Nat.le (Nat.add a k) (Nat.add b k) :=
  Nat.rec (motive := fun k => Nat.le (Nat.add a k) (Nat.add b k)) h
    (fun _ ih => Nat.succ_le_succ ih) k

public theorem plusSucc (a b : Nat) : Eq (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b)) :=
  Nat.rec (motive := fun b => Eq (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b))) Omega.rfl
    (fun _ ih => congrArg Nat.succ ih) b

public theorem leftMono (k a b : Nat) (h : Nat.le a b) : Nat.le (Nat.add k a) (Nat.add k b) :=
  Nat.rec (motive := fun a => ∀ b, Nat.le a b → Nat.le (Nat.add k a) (Nat.add k b))
    (fun b _ => Nat.rec (motive := fun b => Nat.le k (Nat.add k b)) (Nat.le_refl k)
      (fun _ ih => Nat.le.step ih) b)
    (fun a step b => Nat.rec
      (motive := fun b => Nat.le (Nat.succ a) b → Nat.le (Nat.add k (Nat.succ a)) (Nat.add k b))
      (fun h => False.elim (Nat.not_succ_le_zero a h))
      (fun b _ h => Nat.succ_le_succ (step b (Nat.le_of_succ_le_succ h))) b) a b h
@[expose] public def double (a : Nat) : Nat := Nat.mul a (Nat.succ (Nat.succ Nat.zero))

public theorem double_eq (a : Nat) : Eq (double a) (Nat.add a a) :=
  congrArg (fun n => Nat.add n a)
    (Nat.rec (motive := fun n => Eq (Nat.add Nat.zero n) n) Omega.rfl (fun _ ih => congrArg Nat.succ ih) a)

public theorem bounds (a b : Nat) (h : Nat.lt a b) : Nat.lt (Nat.succ (double a)) (double b) :=
  let x := Nat.succ a
  let g₁ := leftMono x x b h
  let g₂ := rightMono b x b h
  let g₃ := Nat.le_trans g₁ g₂
  let g₄ := Eq.subst (motive := fun t => Nat.le t (Nat.add b b))
    (congrArg Nat.succ (plusSucc a a)) g₃
  let g₅ := Eq.subst (motive := fun t => Nat.le (Nat.succ (Nat.succ t)) (Nat.add b b)) (Eq.symm (double_eq a)) g₄
  Eq.subst (motive := fun t => Nat.le (Nat.succ (Nat.succ (double a))) t) (Eq.symm (double_eq b)) g₅

public theorem digitBounds (a b : Nat) (h : Nat.lt a b) :
    Nat.lt (double a) (double b) :=
  Nat.le_trans (Nat.le.step (Nat.le_refl (Nat.succ (double a)))) (bounds a b h)

public theorem raiseBound (a b : Nat) (h : Nat.lt a b) : Nat.lt a (Nat.succ b) := Nat.le.step h

end OmegaLiteralProofs
