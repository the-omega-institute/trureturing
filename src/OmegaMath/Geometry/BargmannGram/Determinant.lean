module
prelude
public import OmegaMath.Geometry.BargmannGram.Identities
import OmegaMath.Geometry.BargmannGram.Fractions

/-!
Omega original.

Common-denominator form of the normalized Gram determinant and its consequences.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

def gramDenominator (a b c : Quad4) : Nat := (a.normSq.mul b.normSq).mul c.normSq

def gramNumeratorOf (a b c : Quad4) : Int :=
  gramNumerator (a.dot a) (b.dot b) (c.dot c) (a.dot b) (b.dot c) (c.dot a)

theorem detGram3_value (a b c : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero)) :
    IntRatio.Equivalent (detGram3 a b c) (IntRatio.value (gramNumeratorOf a b c)
      (gramDenominator a b c)) :=
  let A := a.normSq
  let B := b.normSq
  let C := c.normSq
  let D := gramDenominator a b c
  let p := a.dot b
  let q := b.dot c
  let r := c.dot a
  let u := (p.mul q).mul r
  let v := (Int.square p).mul (c.dot c)
  let w := (Int.square q).mul (a.dot a)
  let x := (Int.square r).mul (b.dot b)
  have hA := a.normSq_ne_zero ha
  have hB := b.normSq_ne_zero hb
  have hC := c.normSq_ne_zero hc
  have hD := nat_mul_ne_zero (nat_mul_ne_zero hA hB) hC
  have castD : Eq (Int.ofNat D) (((a.dot a).mul (b.dot b)).mul (c.dot c)) :=
    Eq.map₂ Int.mul (Eq.map₂ Int.mul a.normSq_cast b.normSq_cast) c.normSq_cast
  have h1 : IntRatio.Equivalent (IntRatio.ofInt Int.one)
      (IntRatio.value (((a.dot a).mul (b.dot b)).mul (c.dot c)) D) :=
    (value_const Int.one D hD).trans (Eq.subst
      (fun n => IntRatio.Equivalent (IntRatio.value (Int.one.mul (Int.ofNat D)) D)
        (IntRatio.value n D)) ((Int.one_mul (Int.ofNat D)).trans castD)
      (IntRatio.equivalent_refl _))
  have h2 : IntRatio.Equivalent ((IntRatio.ofInt Int.two).mul (bargmann3 a b c))
      (IntRatio.value (Int.two.mul u) D) :=
    Eq.subst (fun y => IntRatio.Equivalent y (IntRatio.value (Int.two.mul u) D))
      (value_mul_int Int.two u D).symm (IntRatio.equivalent_refl _)
  have liftRatio := fun (n : Int) (d k : Nat) (hk : Not (Eq k Nat.zero)) (s : Int)
      (hs : Eq (Int.ofNat k) s) (hd : Eq (d.mul k) D) =>
    Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value n d) (IntRatio.value (n.mul t) D)) hs
      (Eq.subst (fun e => IntRatio.Equivalent (IntRatio.value n d)
        (IntRatio.value (n.mul (Int.ofNat k)) e)) hd
        (IntRatio.value_scale_of_ne_zero n d k hk).symm)
  have h3 : IntRatio.Equivalent (kappa a b) (IntRatio.value v D) :=
    liftRatio (Int.square p) (A.mul B) C hC (c.dot c) c.normSq_cast Eq.refl
  have h4 : IntRatio.Equivalent (kappa b c) (IntRatio.value w D) :=
    liftRatio (Int.square q) (B.mul C) A hA (a.dot a) a.normSq_cast
      ((Nat.mul_comm (B.mul C) A).trans (Nat.mul_assoc A B C).symm)
  have h5 : IntRatio.Equivalent (kappa c a) (IntRatio.value x D) :=
    liftRatio (Int.square r) (C.mul A) B hB (b.dot b) b.normSq_cast
      ((congrArg (fun k : Nat => k.mul B) (Nat.mul_comm C A)).trans (Nat.mul_right_comm A C B))
  have positive := (IntRatio.add_congr h1 h2).trans
    (IntRatio.value_add_same (((a.dot a).mul (b.dot b)).mul (c.dot c)) (Int.two.mul u) D)
  have negative := (IntRatio.add_congr ((IntRatio.add_congr h3 h4).trans
    (IntRatio.value_add_same v w D)) h5).trans (IntRatio.value_add_same (v.add w) x D)
  (IntRatio.sub_congr positive negative).trans (value_sub_same _ _ D)

theorem detGram3_nonneg (a b c : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero)) :
    IntRatio.Le (IntRatio.ofInt Int.zero) (detGram3 a b c) :=
  (IntRatio.le_congr (IntRatio.equivalent_refl _) (detGram3_value a b c ha hb hc)).mpr
    (zero_le_value _ _ (nat_mul_ne_zero (nat_mul_ne_zero (a.normSq_ne_zero ha)
      (b.normSq_ne_zero hb)) (c.normSq_ne_zero hc)) (gram_squares_nonneg a b c))

private theorem triad_nonzero (a b : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) : Not (Eq (triad b a b) Quad4.zero) :=
  fun h => nat_mul_ne_zero (nat_mul_ne_zero (a.normSq_ne_zero ha) (b.normSq_ne_zero hb))
    (b.normSq_ne_zero hb) ((normSq_triad a b).symm.trans (congrArg Quad4.normSq h))

theorem geodesic_doubling_detGram3_zero (a b : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) :
    IntRatio.Equivalent (detGram3 a b (triad b a b)) (IntRatio.ofInt Int.zero) :=
  let c := triad b a b
  have hc := triad_nonzero a b ha hb
  have normC : Eq (c.dot c) (((a.dot a).mul (b.dot b)).mul (b.dot b)) :=
    c.normSq_cast.symm.trans ((congrArg Int.ofNat (normSq_triad a b)).trans
      (Eq.map₂ Int.mul (Eq.map₂ Int.mul a.normSq_cast b.normSq_cast) b.normSq_cast))
  have top := Eq.map₂ Int.add
      (congrArg ((a.dot a).mul (b.dot b)).mul normC)
      (congrArg (fun z => Int.two.mul z) (Eq.map₂ Int.mul
        (congrArg (a.dot b).mul (dot_triad_middle a b))
        ((c.dot_comm a).trans (dot_triad_left a b))))
  have vanishes : Eq (gramNumeratorOf a b c) Int.zero :=
    (Eq.map₂ Int.sub top (Eq.map₂ Int.add
        (Eq.map₂ Int.add (congrArg (Int.square (a.dot b)).mul normC)
          (congrArg (fun z => (Int.square z).mul (a.dot a)) (dot_triad_middle a b)))
        (congrArg (fun z => (Int.square z).mul (b.dot b))
          ((c.dot_comm a).trans (dot_triad_left a b))))).trans
      (gram_triad_vanishes (a.dot a) (b.dot b) (a.dot b))
  (detGram3_value a b c ha hb hc).trans (Eq.subst
    (fun n => IntRatio.Equivalent (IntRatio.value n (gramDenominator a b c)) (IntRatio.ofInt Int.zero))
    vanishes.symm (IntRatio.value_zero _ (nat_mul_ne_zero
      (nat_mul_ne_zero (a.normSq_ne_zero ha) (b.normSq_ne_zero hb)) (c.normSq_ne_zero hc))))

def pHalf : Quad4 := ⟨Int.one, Int.one, Int.zero, Int.zero⟩
def qHalf : Quad4 := ⟨Int.one, Int.zero, Int.one, Int.zero⟩

theorem orthogonal_triad_excess :
    IntRatio.Equivalent (detGram3 Quad4.one pHalf qHalf)
      (IntRatio.value Int.one Nat.zero.succ.succ.succ.succ) := Eq.refl

end Omega.Geometry.BargmannGram
