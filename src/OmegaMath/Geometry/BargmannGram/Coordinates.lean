module
prelude
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Integer quaternion coordinates and the natural squared Euclidean norm.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

structure Quad4 where
  w : Int
  x : Int
  y : Int
  z : Int

namespace Quad4

def zero : Quad4 := ⟨Int.zero, Int.zero, Int.zero, Int.zero⟩
def one : Quad4 := ⟨Int.one, Int.zero, Int.zero, Int.zero⟩

def add (a b : Quad4) : Quad4 :=
  ⟨a.w.add b.w, a.x.add b.x, a.y.add b.y, a.z.add b.z⟩

def scale (k : Int) (a : Quad4) : Quad4 :=
  ⟨k.mul a.w, k.mul a.x, k.mul a.y, k.mul a.z⟩

def mul (a b : Quad4) : Quad4 :=
  ⟨(((a.w.mul b.w).sub (a.x.mul b.x)).sub (a.y.mul b.y)).sub (a.z.mul b.z),
   (((a.w.mul b.x).add (a.x.mul b.w)).add (a.y.mul b.z)).sub (a.z.mul b.y),
   (((a.w.mul b.y).sub (a.x.mul b.z)).add (a.y.mul b.w)).add (a.z.mul b.x),
   (((a.w.mul b.z).add (a.x.mul b.y)).sub (a.y.mul b.x)).add (a.z.mul b.w)⟩

def conj (a : Quad4) : Quad4 := ⟨a.w, a.x.neg, a.y.neg, a.z.neg⟩

def dot (a b : Quad4) : Int :=
  ((a.w.mul b.w).add (a.x.mul b.x)).add ((a.y.mul b.y).add (a.z.mul b.z))

def normSq (a : Quad4) : Nat :=
  ((a.w.natAbs.mul a.w.natAbs).add (a.x.natAbs.mul a.x.natAbs)).add
    ((a.y.natAbs.mul a.y.natAbs).add (a.z.natAbs.mul a.z.natAbs))

theorem normSq_cast (a : Quad4) : Eq (Int.ofNat a.normSq) (a.dot a) :=
  Eq.map₂ Int.add (Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self)
    (Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self)

theorem ext {a b : Quad4} (hw : Eq a.w b.w) (hx : Eq a.x b.x)
    (hy : Eq a.y b.y) (hz : Eq a.z b.z) : Eq a b :=
  Eq.map₂ (fun w x => Quad4.mk w x a.y a.z) hw hx |>.trans
    (Eq.map₂ (Quad4.mk b.w b.x) hy hz)

theorem normSq_ne_zero (a : Quad4) (h : Not (Eq a zero)) : Not (Eq a.normSq Nat.zero) :=
  fun hn =>
    let halves := (Nat.eq_zero_of_add_eq_zero hn)
    let left := Nat.eq_zero_of_add_eq_zero halves.left
    let right := Nat.eq_zero_of_add_eq_zero halves.right
    let coordinate := fun (v : Int) (hv : Eq (v.natAbs.mul v.natAbs) Nat.zero) =>
      Int.natAbs_eq_zero.mp ((Nat.mul_eq_zero.mp hv).elim (fun e => e) (fun e => e))
    h (ext (coordinate a.w left.left) (coordinate a.x left.right)
      (coordinate a.y right.left) (coordinate a.z right.right))

theorem normSq_conj (a : Quad4) : Eq a.conj.normSq a.normSq :=
  let square := fun x : Int => Eq.map₂ Nat.mul (Int.natAbs_neg x) (Int.natAbs_neg x)
  Eq.map₂ Nat.add (congrArg ((a.w.natAbs.mul a.w.natAbs).add) (square a.x))
    (Eq.map₂ Nat.add (square a.y) (square a.z))

theorem scale_injective (k : Int) (hk : Not (Eq k Int.zero)) {a b : Quad4}
    (h : Eq (scale k a) (scale k b)) : Eq a b :=
  ext (Int.eq_of_mul_eq_mul_left hk (congrArg w h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg x h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg y h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg z h))

end Quad4

def triad (a b c : Quad4) : Quad4 := (a.mul b.conj).mul c

def kappa (a b : Quad4) : IntRatio :=
  IntRatio.value (Int.square (a.dot b)) (a.normSq.mul b.normSq)

def bargmann3 (a b c : Quad4) : IntRatio :=
  IntRatio.value (((a.dot b).mul (b.dot c)).mul (c.dot a))
    ((a.normSq.mul b.normSq).mul c.normSq)

def detGram3 (a b c : Quad4) : IntRatio :=
  ((IntRatio.ofInt Int.one).add ((IntRatio.ofInt (Int.one.add Int.one)).mul (bargmann3 a b c))).sub
    (((kappa a b).add (kappa b c)).add (kappa c a))

end Omega.Geometry.BargmannGram
