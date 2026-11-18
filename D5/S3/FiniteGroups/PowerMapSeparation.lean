/- GID: D5/S3/FiniteGroups/PowerMapSeparation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/PowerMapSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/PowerMapSeparation.claim; result=result; claim=claim
   digest: Fixed finite groups with separate integer-power conjugacies but no joint square-cube conjugacy. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Explicit original-coordinate semidirect products for the power-map counterexample. -/

namespace D5.S3.FiniteGroups.PowerMapSeparation

abbrev F := ZMod 3

/-- Original (uncentered) coordinates of the two semidirect products. -/
@[ext] structure S (i : Bool) where
  a : F
  b : F
  x : F
  y : F
  z : F
  s : F
  t : F
  e : Bool
  deriving DecidableEq

private def productEquiv (i : Bool) :
    S i ≃ (F × F) × (F × F × F) × (F × F) × Bool where
  toFun p := ((p.a,p.b),(p.x,p.y,p.z),(p.s,p.t),p.e)
  invFun p := ⟨p.1.1,p.1.2,p.2.1.1,p.2.1.2.1,p.2.1.2.2,
    p.2.2.1.1,p.2.2.1.2,p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (i : Bool) : Fintype (S i) := Fintype.ofEquiv _ (productEquiv i).symm

private def sign (e : Bool) : F := if e then -1 else 1
private def B₁ (i : Bool) (a b x y : F) : F := if i then a*x-b*y else a*x+b*y
private def B₂ (i : Bool) (a b x y z : F) : F := if i then b*x+a*y else a*y+b*z

private def mulS {i : Bool} (p q : S i) : S i := ⟨p.a+q.a, p.b+q.b, p.x+sign p.e*q.x, p.y+sign p.e*q.y,
    p.z+sign p.e*q.z, p.s+sign p.e*q.s+sign p.e*B₁ i p.a p.b q.x q.y,
    p.t+sign p.e*q.t+sign p.e*B₂ i p.a p.b q.x q.y q.z, p.e ^^ q.e⟩
private def oneS (i : Bool) : S i := ⟨0,0,0,0,0,0,0,false⟩
private def invS {i : Bool} (p : S i) : S i := ⟨-p.a,-p.b,-sign p.e*p.x,-sign p.e*p.y,-sign p.e*p.z,
    -sign p.e*p.s+sign p.e*B₁ i p.a p.b p.x p.y,
    -sign p.e*p.t+sign p.e*B₂ i p.a p.b p.x p.y p.z,p.e⟩

instance (i : Bool) : Group (S i) where
  mul := mulS
  one := oneS i
  inv := invS
  mul_assoc p q r := by
    change mulS (mulS p q) r = mulS p (mulS q r)
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    rcases q with ⟨a',b',x',y',z',s',t',e'⟩
    rcases r with ⟨a'',b'',x'',y'',z'',s'',t'',e''⟩
    cases i <;> cases e <;> cases e' <;>
      apply S.ext <;> simp [mulS, sign, B₁, B₂, Bool.xor_assoc, add_assoc] <;> ring
  one_mul p := by
    change mulS (oneS i) p = p
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases i <;> cases e <;> apply S.ext <;>
      simp [mulS, oneS, sign, B₁, B₂]
  mul_one p := by
    change mulS p (oneS i) = p
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases i <;> cases e <;> apply S.ext <;>
      simp [mulS, oneS, sign, B₁, B₂]
  inv_mul_cancel p := by
    change mulS (invS p) p = oneS i
    rcases p with ⟨a,b,x,y,z,s,t,e⟩
    cases i <;> cases e <;> apply S.ext <;>
      simp only [mulS, oneS, invS, sign, B₁, B₂, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte, Bool.xor_self] <;> ring

private theorem card_S (i : Bool) : Fintype.card (S i) = 4374 := by
  rw [Fintype.card_congr (productEquiv i)]
  norm_num [Fintype.card_prod, F]

/-- The same underlying coordinates with the central term centered. -/
private def center (i : Bool) : S i ≃ S false where
  toFun p := ⟨p.a,p.b,p.x,p.y,p.z,p.s+B₁ i p.a p.b p.x p.y,
    p.t+B₂ i p.a p.b p.x p.y p.z,p.e⟩
  invFun p := ⟨p.a,p.b,p.x,p.y,p.z,p.s-B₁ i p.a p.b p.x p.y,
    p.t-B₂ i p.a p.b p.x p.y p.z,p.e⟩
  left_inv p := by apply S.ext <;> simp
  right_inv p := by apply S.ext <;> simp

private def squareC (i : Bool) (p : S false) : S false :=
  if p.e then ⟨-p.a,-p.b,0,0,0,-B₁ i p.a p.b p.x p.y,
    -B₂ i p.a p.b p.x p.y p.z,false⟩
  else ⟨-p.a,-p.b,-p.x,-p.y,-p.z,-p.s,-p.t,false⟩

private def cubeC (p : S false) : S false :=
  if p.e then ⟨0,0,p.x,p.y,p.z,p.s,p.t,true⟩ else oneS false

private theorem center_square (i : Bool) (p : S i) :
    center i (p^2) = squareC i (center i p) := by
  change center i (mulS p p) = squareC i (center i p)
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> apply S.ext <;>
    simp [center, squareC, mulS, sign, B₁, B₂] <;> ring_nf <;> norm_num

private theorem center_cube (i : Bool) (p : S i) :
    center i (p^3) = cubeC (center i p) := by
  change center i (mulS (mulS p p) p) = cubeC (center i p)
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> apply S.ext <;>
    simp [center, cubeC, mulS, oneS, sign, B₁, B₂] <;> ring_nf <;> norm_num

private theorem center_inv (i : Bool) (p : S i) :
    center i p⁻¹ =
      (if p.e then ⟨-p.a,-p.b,p.x,p.y,p.z,(center i p).s,(center i p).t,true⟩
       else ⟨-p.a,-p.b,-p.x,-p.y,-p.z,-(center i p).s,-(center i p).t,false⟩) := by
  change center i (invS p) = _
  rcases p with ⟨a,b,x,y,z,s,t,e⟩
  cases i <;> cases e <;> apply S.ext <;>
    simp [center, invS, sign, B₁, B₂] <;> ring_nf <;> norm_num

private def transportAxis : (F × F × F) ≃ (F × F × F) where
  toFun w := (w.2.2, -w.2.1, w.1)
  invFun w := (w.2.2, -w.2.1, w.1)
  left_inv w := by rcases w with ⟨x,y,z⟩; simp
  right_inv w := by rcases w with ⟨x,y,z⟩; simp

private def transportPlus : (F × F × F) ≃ (F × F × F) where
  toFun w := (-w.1 + w.2.1 - w.2.2, w.1 - w.2.2, w.2.2)
  invFun w := (w.2.1 + w.2.2, w.1 + w.2.1 - w.2.2, w.2.2)
  left_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring
  right_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring

private def transportMinus : (F × F × F) ≃ (F × F × F) where
  toFun w := (-w.1 - w.2.1 - w.2.2, -w.1 + w.2.2, w.2.2)
  invFun w := (w.2.2 - w.2.1, w.2.1 + w.2.2 - w.1, w.2.2)
  left_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring
  right_inv w := by
    rcases w with ⟨x,y,z⟩
    ext <;> dsimp <;> ring

private def transport (a b : F) : (F × F × F) ≃ (F × F × F) :=
  if a = 0 then
    if b = 0 then Equiv.refl _ else transportAxis
  else if b = 0 then Equiv.refl _
  else if a = b then transportPlus else transportMinus

private theorem transport_B₁ (a b x y z : F) :
    B₁ true a b (transport a b (x,y,z)).1 (transport a b (x,y,z)).2.1 =
      B₁ false a b x y := by
  fin_cases a <;> fin_cases b <;>
    simp [transport, transportAxis, transportPlus, transportMinus, B₁] <;> ring

private theorem transport_B₂ (a b x y z : F) :
    B₂ true a b (transport a b (x,y,z)).1 (transport a b (x,y,z)).2.1
      (transport a b (x,y,z)).2.2 = B₂ false a b x y z := by
  fin_cases a <;> fin_cases b <;>
    simp [transport, transportAxis, transportPlus, transportMinus, B₂] <;> ring

private theorem transport_origin (a b : F) : transport a b (0,0,0) = (0,0,0) := by
  simp only [transport]
  split_ifs <;> simp [transportAxis, transportPlus, transportMinus]

private theorem transport_zero : transport 0 0 = Equiv.refl (F × F × F) := by
  simp [transport]

end D5.S3.FiniteGroups.PowerMapSeparation
