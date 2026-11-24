module
prelude
public import OmegaMath.Geometry.BargmannGram.Coordinates
import OmegaMath.Geometry.BargmannGram.Polynomial
import OmegaMath.Geometry.BargmannGram.Identities

/-!
Omega original.

Exact right multiplication and scalar division for integer quaternion states.
Two states with the same squared norm can differ in whether a rule is enabled.
-/

noncomputable section

@[expose] public section

namespace Omega.Computability.QuaternionFractran

open Omega.Geometry.BargmannGram (Quad4)

def Step (psi A : Quad4) (p : Nat) (q : Quad4) : Prop :=
  And (Not (Eq p Nat.zero)) (Eq (psi.mul A) (Quad4.scale (Int.ofNat p) q))

def Enabled (psi A : Quad4) (p : Nat) : Prop :=
  Exists (fun q => Step psi A p q)

theorem quaternion_fractran_deterministic {psi A q₁ q₂ : Quad4} {p : Int}
    (hp : Not (Eq p Int.zero))
    (h₁ : Eq (psi.mul A) (Quad4.scale p q₁))
    (h₂ : Eq (psi.mul A) (Quad4.scale p q₂)) : Eq q₁ q₂ :=
  Quad4.scale_injective p hp (h₁.symm.trans h₂)

theorem Step.deterministic {psi A q₁ q₂ : Quad4} {p : Nat}
    (h₁ : Step psi A p q₁) (h₂ : Step psi A p q₂) : Eq q₁ q₂ :=
  quaternion_fractran_deterministic (fun h => h₁.left (Int.ofNat_inj.mp h)) h₁.right h₂.right

theorem Step.norm_identity {psi A q : Quad4} {p : Nat} (h : Step psi A p q) :
    Eq (psi.mul A).normSq ((p.mul p).mul q.normSq) :=
  (congrArg Quad4.normSq h.right).trans
    ((Quad4.normSq_scale (Int.ofNat p) q).trans (Nat.mul_assoc p p q.normSq).symm)

def psiX : Quad4 := ⟨Int.one, Int.two, Int.zero, Int.zero⟩
def psiY : Quad4 := ⟨Int.one, Int.zero, Int.two, Int.zero⟩

/-- The product in X-then-Y order has coordinates (1, 2, 2, 4). -/
def psiXY : Quad4 := psiX.mul psiY

/-- The product in Y-then-X order has coordinates (1, 2, 2, -4). -/
def psiYX : Quad4 := psiY.mul psiX

/-- Right multiplication by the conjugate of Y, with coordinates (1, 0, -2, 0). -/
def gateUnwindY : Quad4 := psiY.conj

def unwindDenominator : Nat := Nat.one.succ.succ.succ.succ

theorem psiXY_step : Step psiXY gateUnwindY unwindDenominator psiX :=
  And.intro (Nat.succ_ne_zero _) Eq.refl

private theorem five_mul_ne_six (n : Nat) :
    Not (Eq (unwindDenominator.mul n) unwindDenominator.succ) :=
  let five := unwindDenominator
  let six := five.succ
  let ten := five.add five
  Nat.rec (motive := fun n => Not (Eq (five.mul n) six))
    (fun h => Eq.subst (Nat.le six) h.symm (Nat.le.refl six))
    (fun n _ =>
      Nat.rec (motive := fun n => Not (Eq (five.mul n.succ) six))
        (fun h => Eq.subst (Nat.le six) h.symm (Nat.le.refl six))
        -- Five times (k + 2) is ten successors of five times k.
        (fun k _ h => Eq.subst (Nat.le ten) h (Nat.zero_le (five.mul k))) n) n

theorem psiYX_blocked : Not (Enabled psiYX gateUnwindY unwindDenominator) :=
  fun enabled => enabled.elim (fun q h =>
    have hx : Eq ((Int.ofNat unwindDenominator).mul q.x) (Int.negSucc unwindDenominator) :=
      (congrArg Quad4.x h.right).symm
    five_mul_ne_six q.x.natAbs
      ((Int.natAbs_mul (Int.ofNat unwindDenominator) q.x).symm.trans (congrArg Int.natAbs hx)))

theorem quaternion_fractran_order_separation :
    And (Eq psiXY.normSq (unwindDenominator.mul unwindDenominator))
      (And (Eq psiYX.normSq (unwindDenominator.mul unwindDenominator))
        (And (Step psiXY gateUnwindY unwindDenominator psiX)
          (Not (Enabled psiYX gateUnwindY unwindDenominator)))) :=
  And.intro Eq.refl (And.intro Eq.refl (And.intro psiXY_step psiYX_blocked))

end Omega.Computability.QuaternionFractran
