module
prelude
public import OmegaMath.Calculus.Jet2.Scalar

/-!
Omega original.

Second-order jets use the coefficients of one, η and η² in degree order.
-/

noncomputable section

@[expose] public section

namespace Omega

structure Jet2 where
  j0 : IntRatio
  j1 : IntRatio
  j2 : IntRatio

namespace Jet2

def Equivalent (a b : Jet2) : Prop :=
  And (IntRatio.Equivalent a.j0 b.j0) (And (IntRatio.Equivalent a.j1 b.j1) (IntRatio.Equivalent a.j2 b.j2))

def Finite (a : Jet2) : Prop :=
  And a.j0.Finite (And a.j1.Finite a.j2.Finite)

theorem equivalent_refl (a : Jet2) : Equivalent a a :=
  And.intro (IntRatio.equivalent_refl a.j0)
    (And.intro (IntRatio.equivalent_refl a.j1) (IntRatio.equivalent_refl a.j2))

theorem Equivalent.symm {a b : Jet2} (h : Equivalent a b) : Equivalent b a :=
  And.intro h.left.symm (And.intro h.right.left.symm h.right.right.symm)

theorem Equivalent.trans {a b c : Jet2} (h : Equivalent a b) (k : Equivalent b c) :
    Equivalent a c :=
  And.intro (h.left.trans k.left)
    (And.intro (h.right.left.trans k.right.left) (h.right.right.trans k.right.right))

def const (c : IntRatio) : Jet2 := ⟨c, IntRatio.zero, IntRatio.zero⟩
def zero : Jet2 := const IntRatio.zero
def one : Jet2 := const IntRatio.one
def var : Jet2 := ⟨IntRatio.zero, IntRatio.one, IntRatio.zero⟩

def add (a b : Jet2) : Jet2 := ⟨(a.j0.add b.j0), (a.j1.add b.j1), (a.j2.add b.j2)⟩
def neg (a : Jet2) : Jet2 := ⟨a.j0.neg, a.j1.neg, a.j2.neg⟩
def sub (a b : Jet2) : Jet2 := a.add b.neg

def mul (a b : Jet2) : Jet2 :=
  ⟨(a.j0.mul b.j0), ((a.j0.mul b.j1).add (a.j1.mul b.j0)),
    (((a.j0.mul b.j2).add (a.j1.mul b.j1)).add (a.j2.mul b.j0))⟩

theorem add_congr {a b c d : Jet2} (h : Equivalent a b) (k : Equivalent c d) :
    Equivalent (a.add c) (b.add d) :=
  And.intro (IntRatio.add_congr h.left k.left)
    (And.intro (IntRatio.add_congr h.right.left k.right.left)
      (IntRatio.add_congr h.right.right k.right.right))

theorem mul_congr {a b c d : Jet2} (h : Equivalent a b) (k : Equivalent c d) :
    Equivalent (a.mul c) (b.mul d) :=
  And.intro (IntRatio.mul_congr h.left k.left)
    (And.intro
      (IntRatio.add_congr (IntRatio.mul_congr h.left k.right.left)
        (IntRatio.mul_congr h.right.left k.left))
      (IntRatio.add_congr
        (IntRatio.add_congr (IntRatio.mul_congr h.left k.right.right)
          (IntRatio.mul_congr h.right.left k.right.left))
        (IntRatio.mul_congr h.right.right k.left)))

theorem add_comm (a b : Jet2) : Equivalent (a.add b) (b.add a) :=
  And.intro (IntRatio.add_comm a.j0 b.j0)
    (And.intro (IntRatio.add_comm a.j1 b.j1) (IntRatio.add_comm a.j2 b.j2))

theorem add_assoc (a b c : Jet2) : Equivalent ((a.add b).add c) (a.add (b.add c)) :=
  And.intro (IntRatio.add_assoc a.j0 b.j0 c.j0)
    (And.intro (IntRatio.add_assoc a.j1 b.j1 c.j1) (IntRatio.add_assoc a.j2 b.j2 c.j2))

theorem add_zero (a : Jet2) : Equivalent (a.add zero) a :=
  And.intro (IntRatio.add_zero a.j0)
    (And.intro (IntRatio.add_zero a.j1) (IntRatio.add_zero a.j2))

theorem add_neg {a : Jet2} (h : a.Finite) : Equivalent (a.add a.neg) zero :=
  And.intro (IntRatio.add_right_neg h.left)
    (And.intro (IntRatio.add_right_neg h.right.left) (IntRatio.add_right_neg h.right.right))

theorem mul_comm (a b : Jet2) : Equivalent (a.mul b) (b.mul a) :=
  let p := (b.j0.mul a.j2)
  let q := (b.j1.mul a.j1)
  let r := (b.j2.mul a.j0)
  And.intro (IntRatio.mul_comm a.j0 b.j0)
    (And.intro
      ((IntRatio.add_congr (IntRatio.mul_comm a.j0 b.j1) (IntRatio.mul_comm a.j1 b.j0)).trans
        (IntRatio.add_comm (b.j1.mul a.j0) (b.j0.mul a.j1)))
      ((IntRatio.add_congr
        (IntRatio.add_congr (IntRatio.mul_comm a.j0 b.j2) (IntRatio.mul_comm a.j1 b.j1))
        (IntRatio.mul_comm a.j2 b.j0)).trans
          ((IntRatio.add_comm (r.add q) p).trans
            ((IntRatio.add_congr (IntRatio.equivalent_refl p) (IntRatio.add_comm r q)).trans
              (IntRatio.add_assoc p q r).symm))))

theorem mul_one {a : Jet2} (h : a.Finite) : Equivalent (a.mul one) a :=
  And.intro (IntRatio.mul_one a.j0)
    (And.intro
      ((IntRatio.add_congr (IntRatio.mul_zero h.left) (IntRatio.mul_one a.j1)).trans
        (IntRatio.zero_add a.j1))
      ((IntRatio.add_congr
        ((IntRatio.add_congr (IntRatio.mul_zero h.left) (IntRatio.mul_zero h.right.left)).trans
          (IntRatio.add_zero IntRatio.zero))
        (IntRatio.mul_one a.j2)).trans (IntRatio.zero_add a.j2)))

/-- Reorder the six terms in the degree-two coefficient of a triple product. -/
private theorem group_degree_two (a b c d e f : IntRatio) :
    IntRatio.Equivalent ((a.add (b.add d)).add ((c.add e).add f))
      ((((a.add b).add c).add (d.add e)).add f) :=
  (IntRatio.add_congr (IntRatio.add_assoc a b d).symm (IntRatio.add_assoc c e f)).trans
    ((IntRatio.add_add_add_comm (a.add b) d c (e.add f)).trans
      ((IntRatio.add_congr (IntRatio.equivalent_refl ((a.add b).add c))
        (IntRatio.add_assoc d e f).symm).trans
          (IntRatio.add_assoc ((a.add b).add c) (d.add e) f).symm))

theorem mul_assoc (a b c : Jet2) : Equivalent ((a.mul b).mul c) (a.mul (b.mul c)) :=
  let A := (a.j0.mul (b.j0.mul c.j2))
  let B := (a.j0.mul (b.j1.mul c.j1))
  let C := (a.j0.mul (b.j2.mul c.j0))
  let D := (a.j1.mul (b.j0.mul c.j1))
  let E := (a.j1.mul (b.j1.mul c.j0))
  let F := (a.j2.mul (b.j0.mul c.j0))
  have expand : ∀ x y z w : IntRatio, (IntRatio.Equivalent (((x.mul y).add z).mul w) ((x.mul (y.mul w)).add (z.mul w))) :=
    fun x y z w => (IntRatio.add_mul (x.mul y) z w).trans
      (IntRatio.add_congr (IntRatio.mul_assoc x y w) (IntRatio.equivalent_refl (z.mul w)))
  have first := (expand a.j0 b.j1 (a.j1.mul b.j0) c.j1).trans
    (IntRatio.add_congr (IntRatio.equivalent_refl B) (IntRatio.mul_assoc a.j1 b.j0 c.j1))
  have second := (IntRatio.add_mul ((a.j0.mul b.j2).add (a.j1.mul b.j1)) (a.j2.mul b.j0) c.j0).trans
    (IntRatio.add_congr
      ((expand a.j0 b.j2 (a.j1.mul b.j1) c.j0).trans
        (IntRatio.add_congr (IntRatio.equivalent_refl C) (IntRatio.mul_assoc a.j1 b.j1 c.j0)))
      (IntRatio.mul_assoc a.j2 b.j0 c.j0))
  have fold := (IntRatio.mul_add a.j0 ((b.j0.mul c.j2).add (b.j1.mul c.j1)) (b.j2.mul c.j0)).trans
    (IntRatio.add_congr (IntRatio.mul_add a.j0 (b.j0.mul c.j2) (b.j1.mul c.j1))
      (IntRatio.equivalent_refl C))
  have degreeOne := (IntRatio.add_congr (IntRatio.mul_assoc a.j0 b.j0 c.j1)
      ((expand a.j0 b.j1 (a.j1.mul b.j0) c.j0).trans
        (IntRatio.add_congr (IntRatio.equivalent_refl (a.j0.mul (b.j1.mul c.j0)))
          (IntRatio.mul_assoc a.j1 b.j0 c.j0)))).trans
    ((IntRatio.add_assoc (a.j0.mul (b.j0.mul c.j1)) (a.j0.mul (b.j1.mul c.j0)) (a.j1.mul (b.j0.mul c.j0))).symm.trans
      (IntRatio.add_congr (IntRatio.mul_add a.j0 (b.j0.mul c.j1) (b.j1.mul c.j0)).symm
        (IntRatio.equivalent_refl (a.j1.mul (b.j0.mul c.j0)))))
  And.intro (IntRatio.mul_assoc a.j0 b.j0 c.j0)
    (And.intro degreeOne
      ((IntRatio.add_congr (IntRatio.add_congr (IntRatio.mul_assoc a.j0 b.j0 c.j2) first) second).trans
        ((group_degree_two A B C D E F).trans
          (IntRatio.add_congr
            (IntRatio.add_congr fold.symm (IntRatio.mul_add a.j1 (b.j0.mul c.j1) (b.j1.mul c.j0)).symm)
            (IntRatio.equivalent_refl F)))))

theorem mul_add (a b c : Jet2) : Equivalent (a.mul (b.add c)) ((a.mul b).add (a.mul c)) :=
  let p := (a.j0.mul b.j2)
  let q := (a.j1.mul b.j1)
  let r := (a.j2.mul b.j0)
  let s := (a.j0.mul c.j2)
  let t := (a.j1.mul c.j1)
  let u := (a.j2.mul c.j0)
  And.intro (IntRatio.mul_add a.j0 b.j0 c.j0)
    (And.intro
      ((IntRatio.add_congr (IntRatio.mul_add a.j0 b.j1 c.j1) (IntRatio.mul_add a.j1 b.j0 c.j0)).trans
        (IntRatio.add_add_add_comm (a.j0.mul b.j1) (a.j0.mul c.j1) (a.j1.mul b.j0) (a.j1.mul c.j0)))
      ((IntRatio.add_congr
        ((IntRatio.add_congr (IntRatio.mul_add a.j0 b.j2 c.j2) (IntRatio.mul_add a.j1 b.j1 c.j1)).trans
          (IntRatio.add_add_add_comm p s q t)) (IntRatio.mul_add a.j2 b.j0 c.j0)).trans
        (IntRatio.add_add_add_comm (p.add q) (s.add t) r u)))

theorem var_cube : Equivalent ((var.mul var).mul var) zero :=
  And.intro Eq.refl (And.intro Eq.refl Eq.refl)

end Jet2
end Omega
