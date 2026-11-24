module
prelude
public import OmegaMath.Geometry.Cayley3D.Adjoint

/-! Omega original.

The kernel of the rational quaternion adjoint action.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz.FreeGroup

open Geometry.Cayley3D Quaternion.Polynomial

/-- A scalar quaternion has zero imaginary coordinates. -/
def IsScalar (q : Quaternion) : Prop :=
  And (Eq q.x Int.zero) (And (Eq q.y Int.zero) (Eq q.z Int.zero))

private def e₁ : Vec3 := ⟨Int.one, Int.zero, Int.zero⟩
private def e₂ : Vec3 := ⟨Int.zero, Int.one, Int.zero⟩

private theorem fixed_basis_num (q : Quaternion) (hq : q.Nonzero) (v : Vec3)
    (h : RatVec3.Equiv (Ad q (RatVec3.ofInt v)) (RatVec3.ofInt v)) :
    Eq (adjointNum q v) (Vec3.scale (Int.ofNat q.normSq) v) :=
  let r := (Ad q (RatVec3.ofInt v)).den
  have r_eq : Eq r q.normSq :=
    (Nat.mul_one (adjointDen q)).trans (adjointDen_eq q hq)
  (Vec3.scale_one (adjointNum q v)).symm.trans
    (h.trans (congrArg (fun n => Vec3.scale (Int.ofNat n) v) r_eq))

private theorem diagonal_one_defect (q : Quaternion) :
    Eq ((q.dot q).sub (adjointNum q e₁).x) (Int.two.mul (q.y.square.add q.z.square)) :=
  let Q := Coordinates.variables Nat.zero
  let E : Coordinates := ⟨.zero, .one, .zero, .zero⟩
  let values := Values.cons q.w (.cons q.x (.cons q.y (.cons q.z .nil)))
  ((Q.dot Q).sub ((Q.mul E).mul Q.conj).x).sound (Expr.one.double.mul (Q.y.sq.add Q.z.sq)) values Eq.refl

private theorem diagonal_two_defect (q : Quaternion) :
    Eq ((q.dot q).sub (adjointNum q e₂).y) (Int.two.mul (q.x.square.add q.z.square)) :=
  let Q := Coordinates.variables Nat.zero
  let E : Coordinates := ⟨.zero, .zero, .one, .zero⟩
  let values := Values.cons q.w (.cons q.x (.cons q.y (.cons q.z .nil)))
  ((Q.dot Q).sub ((Q.mul E).mul Q.conj).y).sound (Expr.one.double.mul (Q.x.sq.add Q.z.sq)) values Eq.refl

private theorem squares_zero (a b : Int) (h : Eq (Int.two.mul (a.square.add b.square)) Int.zero) :
    And (Eq a Int.zero) (Eq b Int.zero) :=
  (Int.sum_of_two_squares_eq_zero a b).mp
    (Int.eq_of_mul_eq_mul_left (Int.ofNat_succ_ne_zero Nat.one)
      (h.trans (Int.mul_zero Int.two).symm))

/-- Fixing the first two coordinate axes pointwise forces the quaternion to be scalar. -/
theorem scalar_of_ad_fixes (q : Quaternion) (hq : q.Nonzero)
    (h : ∀ v : RatVec3, RatVec3.Equiv (Ad q v) v) : IsScalar q :=
  let n := Int.ofNat q.normSq
  have x : Eq (adjointNum q e₁).x (q.dot q) :=
    (congrArg Vec3.x (fixed_basis_num q hq e₁ (h (RatVec3.ofInt e₁)))).trans
      ((Int.mul_one n).trans q.normSq_cast)
  have y : Eq (adjointNum q e₂).y (q.dot q) :=
    (congrArg Vec3.y (fixed_basis_num q hq e₂ (h (RatVec3.ofInt e₂)))).trans
      ((Int.mul_one n).trans q.normSq_cast)
  have vanish := fun (a : Int) (e : Eq a (q.dot q)) =>
    (congrArg ((q.dot q).sub) e).trans (Int.sub_self (q.dot q))
  have yz := squares_zero q.y q.z ((diagonal_one_defect q).symm.trans (vanish _ x))
  have xz := squares_zero q.x q.z ((diagonal_two_defect q).symm.trans (vanish _ y))
  And.intro xz.left yz

private theorem vec_cancel {k : Int} {u v : Vec3} (hk : Not (Eq k Int.zero))
    (h : Eq (u.scale k) (v.scale k)) : Eq u v :=
  Vec3.ext (Int.eq_of_mul_eq_mul_left hk (congrArg Vec3.x h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg Vec3.y h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg Vec3.z h))

private theorem equiv_trans {u v w : RatVec3} (h : u.Equiv v) (g : v.Equiv w) :
    u.Equiv w :=
  let d := Int.ofNat u.den
  let e := Int.ofNat v.den
  let f := Int.ofNat w.den
  have swap := fun (a b : Int) (z : Vec3) =>
    (Vec3.scale_mul z a b).trans
      ((congrArg (fun k => z.scale k) (Int.mul_comm a b)).trans (Vec3.scale_mul z b a).symm)
  vec_cancel (Int.ofNat_succ_ne_zero v.denPred)
    ((swap e f u.num).trans
      ((congrArg (Vec3.scale f) h).trans
        ((swap f d v.num).trans
          ((congrArg (Vec3.scale d) g).trans (swap d e w.num)))))

private theorem adjoint_num_scale_vec (q : Quaternion) (v : Vec3) (k : Int) :
    Eq (adjointNum q (v.scale k)) ((adjointNum q v).scale k) :=
  have pure_scale : Eq (v.scale k).pure (Quaternion.scale k v.pure) :=
    Quaternion.ext (Int.mul_zero k).symm Eq.refl Eq.refl Eq.refl
  congrArg Vec3.imaginary
    ((congrArg (fun a => (q.mul a).mul q.conj) pure_scale).trans
      ((congrArg (fun a : Quaternion => a.mul q.conj)
        (Quaternion.scale_mul_right k q v.pure)).trans
        (Quaternion.scale_mul_left k (q.mul v.pure) q.conj)))

private theorem ad_equiv_input (q : Quaternion) {v w : RatVec3} (h : v.Equiv w) :
    (Ad q v).Equiv (Ad q w) :=
  let n := Int.ofNat (adjointDen q)
  let d := Int.ofNat v.den
  let e := Int.ofNat w.den
  have left := (Vec3.scale_mul (adjointNum q v.num) n e).symm
  have right := Vec3.scale_mul (adjointNum q w.num) n d
  have inner := (adjoint_num_scale_vec q v.num e).symm.trans
    ((congrArg (adjointNum q) h).trans (adjoint_num_scale_vec q w.num d))
  left.trans ((congrArg (Vec3.scale n) inner).trans right)

private theorem ad_one (v : RatVec3) : Eq (Ad Quaternion.one v) v :=
  have one_mul := (Quaternion.scalar_mul Int.one v.num.pure).trans
    (Quaternion.scale_one v.num.pure)
  have mul_one := (Quaternion.mul_scalar Int.one v.num.pure).trans
    (Quaternion.scale_one v.num.pure)
  have hn := congrArg Vec3.imaginary
    ((congrArg (fun a : Quaternion => a.mul Quaternion.one) one_mul).trans mul_one)
  RatVec3.eq_of_num_den hn (Nat.one_mul v.den)

private theorem ad_scalar (k : Int) (hk : Not (Eq k Int.zero)) (v : RatVec3) :
    (Ad (Quaternion.scalar k) v).Equiv v :=
  have one_ne : Quaternion.one.Nonzero := fun h => Int.ofNat_succ_ne_zero Nat.zero h.left
  have scale_eq : Eq (Quaternion.scale k Quaternion.one) (Quaternion.scalar k) :=
    Quaternion.ext (Int.mul_one k) (Int.mul_zero k) (Int.mul_zero k) (Int.mul_zero k)
  Eq.subst (fun a => (Ad a v).Equiv v) scale_eq
    (Eq.subst (fun u => (Ad (Quaternion.scale k Quaternion.one) v).Equiv u) (ad_one v)
      (ad_scale Quaternion.one one_ne k hk v))

/-- Two nonzero quaternions acting identically differ by a projective scalar. -/
theorem scalar_conj_mul_of_ad_agrees (p q : Quaternion) (hp : p.Nonzero) (hq : q.Nonzero)
    (h : ∀ v : RatVec3, (Ad p v).Equiv (Ad q v)) : IsScalar (p.conj.mul q) :=
  have hc : p.conj.Nonzero := Quaternion.nonzero_of_normSq_ne_zero
    (fun e => Quaternion.normSq_ne_zero hp ((Quaternion.normSq_conj p).symm.trans e))
  scalar_of_ad_fixes _ (Quaternion.nonzero_mul hc hq) (fun v =>
    have hpp := ad_hom_eq p.conj p hc hp v
    have hpq := ad_hom_eq p.conj q hc hq v
    have hscale := ad_scalar (Int.ofNat p.normSq)
      (fun e => Quaternion.normSq_ne_zero hp (Int.ofNat_inj.mp e)) v
    have inverse := congrArg (fun a => Ad a v) (Quaternion.conj_mul_eq_normSq p)
    have hfix := Eq.subst (fun (u : RatVec3) => u.Equiv v) (hpp.symm.trans inverse).symm hscale
    have hagree := ad_equiv_input p.conj (h v)
    have hswap : (Ad p.conj (Ad q v)).Equiv (Ad p.conj (Ad p v)) := Eq.symm hagree
    Eq.subst (fun (u : RatVec3) => u.Equiv v) hpq.symm (equiv_trans hswap hfix))

end Omega.Hurwitz.FreeGroup
