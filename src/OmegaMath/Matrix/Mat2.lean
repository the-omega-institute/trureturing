module
prelude
public import OmegaMath.Data.Int

/-!
Omega original.

Two by two integer matrices, ring laws, and the quadratic characteristic identity.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- A matrix with entries listed in row order. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int

namespace Mat2

def add (A B : Mat2) : Mat2 := ⟨A.a.add B.a, A.b.add B.b, A.c.add B.c, A.d.add B.d⟩
def neg (A : Mat2) : Mat2 := ⟨A.a.neg, A.b.neg, A.c.neg, A.d.neg⟩
def sub (A B : Mat2) : Mat2 := A.add B.neg
def zero : Mat2 := ⟨Int.zero, Int.zero, Int.zero, Int.zero⟩
def one : Mat2 := ⟨Int.one, Int.zero, Int.zero, Int.one⟩

def dot (a b c d : Int) : Int := (a.mul c).add (b.mul d)

def mul (A B : Mat2) : Mat2 :=
  ⟨dot A.a A.b B.a B.c, dot A.a A.b B.b B.d,
    dot A.c A.d B.a B.c, dot A.c A.d B.b B.d⟩

def scale (k : Int) (A : Mat2) : Mat2 := ⟨k.mul A.a, k.mul A.b, k.mul A.c, k.mul A.d⟩
def trace (A : Mat2) : Int := A.a.add A.d
def det (A : Mat2) : Int := (A.a.mul A.d).sub (A.b.mul A.c)
def adj (A : Mat2) : Mat2 := ⟨A.d, A.b.neg, A.c.neg, A.a⟩

theorem ext {A B : Mat2} (a : Eq A.a B.a) (b : Eq A.b B.b)
    (c : Eq A.c B.c) (d : Eq A.d B.d) : Eq A B :=
  have etaA : Eq A (mk A.a A.b A.c A.d) := Eq.refl
  have etaB : Eq (mk B.a B.b B.c B.d) B := Eq.refl
  etaA.trans ((Eq.map₂ (fun x y => mk x y A.c A.d) a b).trans
    ((Eq.map₂ (mk B.a B.b) c d).trans etaB))

theorem add_assoc (A B C : Mat2) : Eq ((A.add B).add C) (A.add (B.add C)) :=
  ext (Int.add_assoc A.a B.a C.a) (Int.add_assoc A.b B.b C.b)
    (Int.add_assoc A.c B.c C.c) (Int.add_assoc A.d B.d C.d)

theorem add_comm (A B : Mat2) : Eq (A.add B) (B.add A) :=
  ext (Int.add_comm A.a B.a) (Int.add_comm A.b B.b)
    (Int.add_comm A.c B.c) (Int.add_comm A.d B.d)

theorem add_zero (A : Mat2) : Eq (A.add zero) A :=
  ext (Int.add_zero A.a) (Int.add_zero A.b) (Int.add_zero A.c) (Int.add_zero A.d)

theorem zero_add (A : Mat2) : Eq (zero.add A) A :=
  (add_comm zero A).trans (add_zero A)

theorem add_right_neg (A : Mat2) : Eq (A.add A.neg) zero :=
  ext (Int.add_right_neg A.a) (Int.add_right_neg A.b)
    (Int.add_right_neg A.c) (Int.add_right_neg A.d)

private theorem dot_assoc (a b c d e f g h : Int) :
    Eq (dot (dot a b c e) (dot a b d f) g h)
      (dot a b (dot c d g h) (dot e f g h)) :=
  have left := Eq.map₂ Int.add
    ((Int.add_mul (a.mul c) (b.mul e) g).trans
      (Eq.map₂ Int.add (Int.mul_assoc a c g) (Int.mul_assoc b e g)))
    ((Int.add_mul (a.mul d) (b.mul f) h).trans
      (Eq.map₂ Int.add (Int.mul_assoc a d h) (Int.mul_assoc b f h)))
  have right := Eq.map₂ Int.add
    (Int.mul_add a (c.mul g) (d.mul h)) (Int.mul_add b (e.mul g) (f.mul h))
  left.trans ((Int.add_add_add_comm _ _ _ _).trans right.symm)

theorem mul_assoc (A B C : Mat2) : Eq ((A.mul B).mul C) (A.mul (B.mul C)) :=
  ext (dot_assoc A.a A.b B.a B.b B.c B.d C.a C.c)
    (dot_assoc A.a A.b B.a B.b B.c B.d C.b C.d)
    (dot_assoc A.c A.d B.a B.b B.c B.d C.a C.c)
    (dot_assoc A.c A.d B.a B.b B.c B.d C.b C.d)

theorem mul_one (A : Mat2) : Eq (A.mul one) A :=
  let left := fun a b => (Eq.map₂ Int.add (Int.mul_one a) (Int.mul_zero b)).trans (Int.add_zero a)
  let right := fun a b => (Eq.map₂ Int.add (Int.mul_zero a) (Int.mul_one b)).trans (Int.zero_add b)
  ext (left A.a A.b) (right A.a A.b) (left A.c A.d) (right A.c A.d)

theorem one_mul (A : Mat2) : Eq (one.mul A) A :=
  let top := fun a b => (Eq.map₂ Int.add (Int.one_mul a) (Int.zero_mul b)).trans (Int.add_zero a)
  let bottom := fun a b => (Eq.map₂ Int.add (Int.zero_mul a) (Int.one_mul b)).trans (Int.zero_add b)
  ext (top A.a A.c) (top A.b A.d) (bottom A.a A.c) (bottom A.b A.d)

theorem mul_add (A B C : Mat2) : Eq (A.mul (B.add C)) ((A.mul B).add (A.mul C)) :=
  let entry := fun a b c d e f =>
    (Eq.map₂ Int.add (Int.mul_add a c e) (Int.mul_add b d f)).trans (Int.add_add_add_comm _ _ _ _)
  ext (entry A.a A.b B.a B.c C.a C.c) (entry A.a A.b B.b B.d C.b C.d)
    (entry A.c A.d B.a B.c C.a C.c) (entry A.c A.d B.b B.d C.b C.d)

theorem add_mul (A B C : Mat2) : Eq ((A.add B).mul C) ((A.mul C).add (B.mul C)) :=
  let entry := fun a b c d e f =>
    (Eq.map₂ Int.add (Int.add_mul a c e) (Int.add_mul b d f)).trans (Int.add_add_add_comm _ _ _ _)
  ext (entry A.a A.b B.a B.b C.a C.c) (entry A.a A.b B.a B.b C.b C.d)
    (entry A.c A.d B.c B.d C.a C.c) (entry A.c A.d B.c B.d C.b C.d)

theorem trace_mul_comm (A B : Mat2) : Eq (trace (A.mul B)) (trace (B.mul A)) :=
  (Int.add_add_add_comm (A.a.mul B.a) (A.b.mul B.c) (A.c.mul B.b) (A.d.mul B.d)).trans
    (Eq.map₂ Int.add
      (Eq.map₂ Int.add (Int.mul_comm A.a B.a) (Int.mul_comm A.c B.b))
      (Eq.map₂ Int.add (Int.mul_comm A.b B.c) (Int.mul_comm A.d B.d)))

private theorem sub_common_left (c a b : Int) :
    Eq ((c.add a).sub (c.add b)) (a.sub b) :=
  (congrArg (fun n => (c.add a).add n) (Int.neg_add (a := c) (b := b))).trans
    ((Int.add_add_add_comm c a c.neg b.neg).trans
      ((congrArg (fun (n : Int) => n.add (a.sub b)) (Int.add_right_neg c)).trans
        (Int.zero_add (a.sub b))))

private theorem expand (a b c d : Int) :
    Eq ((a.add b).mul (c.add d)) (((a.mul c).add (b.mul d)).add ((a.mul d).add (b.mul c))) :=
  (Int.add_mul a b (c.add d)).trans
    ((Eq.map₂ Int.add (Int.mul_add a c d) (Int.mul_add b c d)).trans
      ((Eq.map₂ Int.add Eq.refl (Int.add_comm (b.mul c) (b.mul d))).trans
        (Int.add_add_add_comm _ _ _ _)))

theorem det_mul (A B : Mat2) : Eq (det (A.mul B)) (A.det.mul B.det) :=
  let a := A.a
  let b := A.b
  let c := A.c
  let d := A.d
  let e := B.a
  let f := B.b
  let g := B.c
  let h := B.d
  have positive := (expand (a.mul e) (b.mul g) (c.mul f) (d.mul h)).trans
    (Eq.map₂ Int.add
      (Eq.map₂ Int.add (Int.mul_mul_mul_comm a e c f) (Int.mul_mul_mul_comm b g d h))
      (Eq.map₂ Int.add (Int.mul_mul_mul_comm a e d h)
        ((Int.mul_mul_mul_comm b g c f).trans (congrArg (b.mul c).mul (Int.mul_comm g f)))))
  have negative := (expand (a.mul f) (b.mul h) (c.mul e) (d.mul g)).trans
    (Eq.map₂ Int.add
      (Eq.map₂ Int.add
        ((Int.mul_mul_mul_comm a f c e).trans (congrArg (a.mul c).mul (Int.mul_comm f e)))
        ((Int.mul_mul_mul_comm b h d g).trans (congrArg (b.mul d).mul (Int.mul_comm h g))))
      (Eq.map₂ Int.add (Int.mul_mul_mul_comm a f d g) (Int.mul_mul_mul_comm b h c e)))
  let ad := a.mul d
  let bc := b.mul c
  let eh := e.mul h
  let fg := f.mul g
  have factor := (Int.sub_mul ad bc (eh.sub fg)).trans
    ((Eq.map₂ Int.sub (Int.mul_sub ad eh fg) (Int.mul_sub bc eh fg)).trans
      ((congrArg ((ad.mul eh).sub (ad.mul fg)).add (Int.neg_add (a := (bc.mul eh)) (b := (bc.mul fg).neg))).trans
        ((Eq.map₂ Int.add Eq.refl (Int.add_comm (bc.mul eh).neg (bc.mul fg).neg.neg)).trans
          ((Int.add_add_add_comm _ _ _ _).trans
            (Eq.map₂ Int.add (congrArg (ad.mul eh).add (Int.neg_neg (bc.mul fg)))
              (Int.neg_add (a := (ad.mul fg)) (b := (bc.mul eh))).symm)))))
  (Eq.map₂ Int.sub positive negative).trans
    ((sub_common_left _ _ _).trans
      ((congrArg (fun n => ((ad.mul eh).add (bc.mul fg)).sub ((ad.mul fg).add n))
        (congrArg bc.mul (Int.mul_comm h e))).trans factor.symm))

private theorem cancel_mul (a b : Int) : Eq ((a.mul b.neg).add (b.mul a)) Int.zero :=
  (Eq.map₂ Int.add (Int.mul_neg a b) (Int.mul_comm b a)).trans (Int.add_left_neg (a.mul b))

theorem mul_adj (A : Mat2) : Eq (A.mul A.adj) (scale A.det one) :=
  have diag := Int.mul_one A.det
  have off := Int.mul_zero A.det
  ext (congrArg (A.a.mul A.d).add (Int.mul_neg A.b A.c) |>.trans diag.symm)
    ((cancel_mul A.a A.b).trans off.symm)
    (((Eq.map₂ Int.add (Int.mul_comm A.c A.d) (Int.mul_neg A.d A.c)).trans
      (Int.add_right_neg (A.d.mul A.c))).trans off.symm)
    (((Eq.map₂ Int.add (Int.mul_neg A.c A.b) (Int.mul_comm A.d A.a)).trans
      ((Eq.map₂ Int.add (congrArg Int.neg (Int.mul_comm A.c A.b)) Eq.refl).trans
        (Int.add_comm (A.b.mul A.c).neg (A.a.mul A.d)))).trans diag.symm)

theorem adj_mul (A : Mat2) : Eq (A.adj.mul A) (scale A.det one) :=
  have diag := Int.mul_one A.det
  have off := Int.mul_zero A.det
  ext ((Eq.map₂ Int.add (Int.mul_comm A.d A.a) (Int.neg_mul A.b A.c)).trans diag.symm)
    (((Eq.map₂ Int.add (Int.mul_comm A.d A.b) (Int.neg_mul A.b A.d)).trans
      (Int.add_right_neg (A.b.mul A.d))).trans off.symm)
    (((Eq.map₂ Int.add (Int.neg_mul A.c A.a) (Int.mul_comm A.a A.c)).trans
      (Int.add_left_neg (A.c.mul A.a))).trans off.symm)
    (((Eq.map₂ Int.add ((Int.neg_mul A.c A.b).trans (congrArg Int.neg (Int.mul_comm A.c A.b)))
        Eq.refl).trans (Int.add_comm (A.b.mul A.c).neg (A.a.mul A.d))).trans diag.symm)

private theorem cayley_diag (a d t : Int) :
    Eq ((((a.mul a).add t).sub ((a.add d).mul a)).add ((a.mul d).sub t)) Int.zero :=
  have expandTrace := (Int.add_mul a d a).trans
    (congrArg (a.mul a).add (Int.mul_comm d a))
  have difference := (congrArg (fun n => ((a.mul a).add t).sub n) expandTrace).trans
    (sub_common_left (a.mul a) t (a.mul d))
  have negate := (Int.neg_add (a := (a.mul d)) (b := t.neg)).trans
    ((congrArg (a.mul d).neg.add (Int.neg_neg t)).trans (Int.add_comm (a.mul d).neg t))
  (congrArg (fun (n : Int) => n.add ((a.mul d).sub t)) (difference.trans negate.symm)).trans
    (Int.add_left_neg ((a.mul d).sub t))

private theorem cayley_off (a b d det : Int) :
    Eq ((((a.mul b).add (b.mul d)).sub ((a.add d).mul b)).add (det.mul Int.zero)) Int.zero :=
  have expandTrace := (Int.add_mul a d b).trans
    (congrArg (a.mul b).add (Int.mul_comm d b))
  (Eq.map₂ Int.add
    ((congrArg (fun n => ((a.mul b).add (b.mul d)).sub n) expandTrace).trans (Int.sub_self _))
    (Int.mul_zero det)).trans Eq.refl

/-- Every integer matrix satisfies its monic quadratic characteristic polynomial. -/
theorem cayley_hamilton (A : Mat2) :
    Eq (((A.mul A).sub (scale A.trace A)).add (scale A.det one)) zero :=
  ext ((congrArg (((A.a.mul A.a).add (A.b.mul A.c)).sub (A.trace.mul A.a)).add
      (Int.mul_one A.det)).trans (cayley_diag A.a A.d (A.b.mul A.c)))
    (cayley_off A.a A.b A.d A.det)
    ((Eq.map₂ Int.add
      (Eq.map₂ Int.sub (Eq.map₂ Int.add (Int.mul_comm A.c A.a) (Int.mul_comm A.d A.c))
        Eq.refl) Eq.refl).trans (cayley_off A.a A.c A.d A.det))
    ((Eq.map₂ Int.add
      (Eq.map₂ Int.sub
        ((Int.add_comm (A.c.mul A.b) (A.d.mul A.d)).trans
          (congrArg (A.d.mul A.d).add (Int.mul_comm A.c A.b)))
        (congrArg (fun (n : Int) => n.mul A.d) (Int.add_comm A.a A.d)))
      ((Int.mul_one A.det).trans (congrArg (fun (n : Int) => n.sub (A.b.mul A.c)) (Int.mul_comm A.a A.d)))).trans
      (cayley_diag A.d A.a (A.b.mul A.c)))

end Mat2
end Omega
