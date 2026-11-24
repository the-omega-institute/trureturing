module
prelude
public import OmegaMath.Matrix.Mat2

/-!
Omega original.

Doubled coordinates for the twelve projective Hurwitz units and the modulo-five
rank-one certificates for the six norm-five generators.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz

open Omega

structure Coordinates where
  w : Int
  x : Int
  y : Int
  z : Int

def Coordinates.normSq (q : Coordinates) : Int :=
  ((q.w.square.add q.x.square).add q.y.square).add q.z.square

/-- The book's twelve projective unit representatives, in atlas order. -/
inductive Core where
  | scalar | ppp | npp | pnp | ppn | nnp | npn | pnn | nnn | i | j | k

def Core.doubled : Core → Coordinates :=
  let o := Int.zero
  let p := Int.one
  let n := p.neg
  let t := Int.two
  Core.rec ⟨t, o, o, o⟩ ⟨p, p, p, p⟩ ⟨p, n, p, p⟩ ⟨p, p, n, p⟩
    ⟨p, p, p, n⟩ ⟨p, n, n, p⟩ ⟨p, n, p, n⟩ ⟨p, p, n, n⟩ ⟨p, n, n, n⟩
    ⟨o, t, o, o⟩ ⟨o, o, t, o⟩ ⟨o, o, o, t⟩

def bySign {α : Type} (nonnegative negative : α) : Int → α :=
  Int.rec (fun _ => nonnegative) (fun _ => negative)

def byNatZero {α : Type} (zero positive : α) : Nat → α :=
  Nat.rec zero (fun _ _ => positive)

def recoverCore (q : Coordinates) : Core :=
  byNatZero
    (byNatZero (byNatZero .k .j q.y.natAbs) .i q.x.natAbs)
    (byNatZero
      (bySign (bySign (bySign .ppp .ppn q.z) (bySign .pnp .pnn q.z) q.y)
        (bySign (bySign .npp .npn q.z) (bySign .nnp .nnn q.z) q.y) q.x)
      .scalar q.w.natAbs.pred)
    q.w.natAbs

theorem core_recover (u : Core) : Eq (recoverCore u.doubled) u :=
  Core.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
    Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl u

theorem core_distinct {u v : Core} (h : Eq u.doubled v.doubled) : Eq u v :=
  (core_recover u).symm.trans ((congrArg recoverCore h).trans (core_recover v))

theorem core_unit (u : Core) : Eq u.doubled.normSq (Int.two.mul Int.two) :=
  Core.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl
    Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl u

/-- The norm-five primary generators and their quaternion conjugates. -/
inductive Generator where
  | iPos | iNeg | jPos | jNeg | kPos | kNeg

def Generator.coordinates : Generator → Coordinates :=
  let w := Int.one
  let o := Int.zero
  let t := Int.two
  let n := t.neg
  Generator.rec ⟨w, t, o, o⟩ ⟨w, n, o, o⟩ ⟨w, o, t, o⟩
    ⟨w, o, n, o⟩ ⟨w, o, o, t⟩ ⟨w, o, o, n⟩

def Generator.opposite : Generator → Generator :=
  Generator.rec .iNeg .iPos .jNeg .jPos .kNeg .kPos

theorem generator_norm (g : Generator) :
    Eq g.coordinates.normSq ((Int.two.mul Int.two).add Int.one) :=
  Generator.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl g

/-- The integer lift of the split matrix, with i sent to diag(2, −2). -/
def split (q : Coordinates) : Mat2 :=
  let x := Int.two.mul q.x
  let z := Int.two.mul q.z
  ⟨q.w.add x, q.y.add z, z.sub q.y, q.w.sub x⟩

inductive Residue where
  | zero | one | two | three | four

namespace Residue

def next : Residue → Residue := Residue.rec .one .two .three .four .zero
def prev : Residue → Residue := Residue.rec .four .zero .one .two .three

def ofInt : Int → Residue :=
  Int.rec (Nat.rec .zero (fun _ => next)) (Nat.rec .four (fun _ => prev))

def toNat : Residue → Nat :=
  let one := Nat.one
  let two := one.succ
  let three := two.succ
  Residue.rec Nat.zero one two three three.succ

def add (a b : Residue) : Residue := Nat.rec a (fun _ => next) b.toNat
def mul (a b : Residue) : Residue := Nat.rec .zero (fun _ r => add r a) b.toNat

def isZero : Residue → Bool :=
  Residue.rec .true .false .false .false .false

end Residue

structure Matrix5 where
  a : Residue
  b : Residue
  c : Residue
  d : Residue

def reduce (A : Mat2) : Matrix5 :=
  ⟨Residue.ofInt A.a, Residue.ofInt A.b, Residue.ofInt A.c, Residue.ofInt A.d⟩

def split5 (q : Coordinates) : Matrix5 := reduce (split q)

def Matrix5.outer (u v s t : Residue) : Matrix5 :=
  ⟨u.mul s, u.mul t, v.mul s, v.mul t⟩

def Matrix5.mul (A B : Matrix5) : Matrix5 :=
  ⟨(A.a.mul B.a).add (A.b.mul B.c), (A.a.mul B.b).add (A.b.mul B.d),
    (A.c.mul B.a).add (A.d.mul B.c), (A.c.mul B.b).add (A.d.mul B.d)⟩

def Matrix5.isZero (A : Matrix5) : Bool :=
  Bool.rec (motive := fun _ => Bool) .false
    (Bool.rec (motive := fun _ => Bool) .false
      (Bool.rec (motive := fun _ => Bool) .false A.d.isZero A.c.isZero) A.b.isZero)
    A.a.isZero

structure Factors where
  u : Residue
  v : Residue
  s : Residue
  t : Residue

def Generator.factors : Generator → Factors :=
  Generator.rec ⟨.zero, .one, .zero, .two⟩ ⟨.one, .zero, .two, .zero⟩
    ⟨.one, .three, .one, .two⟩ ⟨.one, .two, .one, .three⟩
    ⟨.one, .four, .one, .four⟩ ⟨.one, .one, .one, .one⟩

/-- The book's six split images are nonzero outer products modulo five. -/
theorem split_rank_one (g : Generator) :
    let f := g.factors
    And (Eq (split5 g.coordinates) (Matrix5.outer f.u f.v f.s f.t))
      (Eq (split5 g.coordinates).isZero Bool.false) :=
  Generator.rec (motive := fun g =>
      let f := Generator.factors g
      And (Eq (split5 (Generator.coordinates g)) (Matrix5.outer f.u f.v f.s f.t))
        (Eq (split5 (Generator.coordinates g)).isZero Bool.false))
    (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl)
    (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl) g

def Generator.isOpposite (a b : Generator) : Bool :=
  let sameIPos := Generator.rec (motive := fun _ => Bool) .false .true .false .false .false .false
  let sameINeg := Generator.rec (motive := fun _ => Bool) .true .false .false .false .false .false
  let sameJPos := Generator.rec (motive := fun _ => Bool) .false .false .false .true .false .false
  let sameJNeg := Generator.rec (motive := fun _ => Bool) .false .false .true .false .false .false
  let sameKPos := Generator.rec (motive := fun _ => Bool) .false .false .false .false .false .true
  let sameKNeg := Generator.rec (motive := fun _ => Bool) .false .false .false .false .true .false
  Generator.rec (motive := fun _ => Bool) (sameIPos b) (sameINeg b) (sameJPos b)
    (sameJNeg b) (sameKPos b) (sameKNeg b) a

/-- Among the 36 ordered products, exactly the six opposite pairs vanish. -/
theorem split_product_zero (g h : Generator) :
    Eq ((split5 g.coordinates).mul (split5 h.coordinates)).isZero (g.isOpposite h) :=
  let P := fun (a b : Generator) =>
    Eq ((split5 a.coordinates).mul (split5 b.coordinates)).isZero (a.isOpposite b)
  (Generator.rec (motive := fun a => ∀ b, P a b)
    (fun b => Generator.rec (motive := P .iPos) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl b)
    (fun b => Generator.rec (motive := P .iNeg) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl b)
    (fun b => Generator.rec (motive := P .jPos) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl b)
    (fun b => Generator.rec (motive := P .jNeg) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl b)
    (fun b => Generator.rec (motive := P .kPos) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl b)
    (fun b => Generator.rec (motive := P .kNeg) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl b)
    g) h

end Omega.Hurwitz
