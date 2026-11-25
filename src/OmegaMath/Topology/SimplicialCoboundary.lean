/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Core

/-!
Omega original.

Alternating coboundaries on all ordered vertex tuples, including repetitions.
A chosen vertex gives a cone contraction in degrees one and two. Exact edge
differences also telescope along every finite vertex chain.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- The operations of an additive abelian group. Its axioms are expressed by `Laws`. -/
structure AddCommGroup (A : Type v) where
  zeroAt : True → A
  add : A → A → A
  neg : A → A

namespace AddCommGroup

variable {A : Type v} (G : AddCommGroup A)

def ofOperations (zero : A) (add : A → A → A) (neg : A → A) : AddCommGroup A :=
  ⟨fun _ => zero, add, neg⟩

def zero : A :=
  G.zeroAt True.intro

/-- Associativity, commutativity, left identity, and left inverse. -/
def Laws : Prop :=
  And (∀ a b c, Eq (G.add (G.add a b) c) (G.add a (G.add b c)))
    (And (∀ a b, Eq (G.add a b) (G.add b a))
      (And (∀ a, Eq (G.add G.zero a) a) (∀ a, Eq (G.add (G.neg a) a) G.zero)))

namespace Laws

theorem intro
    (assoc : ∀ a b c, Eq (G.add (G.add a b) c) (G.add a (G.add b c)))
    (comm : ∀ a b, Eq (G.add a b) (G.add b a))
    (unit : ∀ a, Eq (G.add G.zero a) a)
    (inverse : ∀ a, Eq (G.add (G.neg a) a) G.zero) : G.Laws :=
  And.intro assoc (And.intro comm (And.intro unit inverse))

variable {G}

theorem add_assoc (laws : G.Laws) (a b c : A) :
    Eq (G.add (G.add a b) c) (G.add a (G.add b c)) :=
  (And.left laws) a b c

theorem add_comm (laws : G.Laws) (a b : A) : Eq (G.add a b) (G.add b a) :=
  (And.left (And.right laws)) a b

theorem zero_add (laws : G.Laws) (a : A) : Eq (G.add G.zero a) a :=
  (And.left (And.right (And.right laws))) a

theorem neg_add_cancel (laws : G.Laws) (a : A) : Eq (G.add (G.neg a) a) G.zero :=
  (And.right (And.right (And.right laws))) a

end Laws

def sub (a b : A) : A :=
  G.add a (G.neg b)

/-- The ternary heap operation associated with an additive abelian group. -/
def heap (a b c : A) : A :=
  G.add (G.sub a b) c

variable (laws : G.Laws)
include laws

theorem add_zero (a : A) : Eq (G.add a G.zero) a :=
  (laws.add_comm a G.zero).trans (laws.zero_add a)

theorem add_neg_cancel (a : A) : Eq (G.add a (G.neg a)) G.zero :=
  (laws.add_comm a (G.neg a)).trans (laws.neg_add_cancel a)

theorem sub_self (a : A) : Eq (G.sub a a) G.zero :=
  G.add_neg_cancel laws a

theorem add_sub_assoc (a b c : A) : Eq (G.add a (G.sub b c)) (G.sub (G.add a b) c) :=
  (laws.add_assoc a b (G.neg c)).symm

theorem sub_add_cancel (a b : A) : Eq (G.add (G.sub a b) b) a :=
  (laws.add_assoc a (G.neg b) b).trans
    ((congrArg (G.add a) (laws.neg_add_cancel b)).trans (G.add_zero laws a))

theorem add_sub_cancel_right (a b : A) : Eq (G.sub (G.add a b) b) a :=
  (laws.add_assoc a b (G.neg b)).trans
    ((congrArg (G.add a) (G.add_neg_cancel laws b)).trans (G.add_zero laws a))

theorem sub_add_sub_cancel (a b c : A) :
    Eq (G.add (G.sub a b) (G.sub b c)) (G.sub a c) :=
  (G.add_sub_assoc laws (G.sub a b) b c).trans
    (congrArg (fun x => G.sub x c) (G.sub_add_cancel laws a b))

private theorem sub_add_add_sub (a b c d : A) :
    Eq (G.add (G.sub a b) (G.sub (G.add b c) d)) (G.sub (G.add a c) d) :=
  (G.add_sub_assoc laws (G.sub a b) (G.add b c) d).trans
    (congrArg (fun x => G.sub x d) ((laws.add_assoc (G.sub a b) b c).symm.trans
      (congrArg (fun x => G.add x c) (G.sub_add_cancel laws a b))))

private theorem sub_add_complement (a b c : A) :
    Eq (G.add (G.sub a b) (G.sub (G.add c b) a)) c :=
  (laws.add_comm (G.sub a b) (G.sub (G.add c b) a)).trans
    ((G.sub_add_sub_cancel laws (G.add c b) a b).trans (G.add_sub_cancel_right laws c b))

theorem heap_self_left (a b : A) : Eq (G.heap a a b) b :=
  (congrArg (fun x => G.add x b) (G.sub_self laws a)).trans (laws.zero_add b)

theorem heap_self_right (a b : A) : Eq (G.heap a b b) a :=
  G.sub_add_cancel laws a b

theorem heap_assoc (a b c d e : A) : Eq (G.heap (G.heap a b c) d e) (G.heap a b (G.heap c d e)) :=
  (congrArg (fun x => G.add x e) (G.add_sub_assoc laws (G.sub a b) c d).symm).trans
    (laws.add_assoc (G.sub a b) (G.sub c d) e)

theorem heap_comm (a b c : A) : Eq (G.heap a b c) (G.heap c b a) :=
  (laws.add_comm (G.sub a b) c).trans
    ((congrArg (G.add c) (laws.add_comm a (G.neg b))).trans (laws.add_assoc c (G.neg b) a).symm)

end AddCommGroup

namespace SimplicialCoboundary

abbrev C0 (V : Sort u) (A : Type v) := V → A
abbrev C1 (V : Sort u) (A : Type v) := V → V → A
abbrev C2 (V : Sort u) (A : Type v) := V → V → V → A
abbrev C3 (V : Sort u) (A : Type v) := V → V → V → V → A

variable {V : Sort u} {A : Type v}

/-- The oriented edge difference is the value at the last vertex minus the first. -/
def d0 (G : AddCommGroup A) (f : C0 V A) : C1 V A :=
  fun x y => G.sub (f y) (f x)

def d1 (G : AddCommGroup A) (e : C1 V A) : C2 V A :=
  fun x y z => G.sub (G.add (e y z) (e x y)) (e x z)

def d2 (G : AddCommGroup A) (F : C2 V A) : C3 V A :=
  fun x y z w => G.sub (G.add (F y z w) (F x y w)) (G.add (F x z w) (F x y z))

theorem d1_d0 (G : AddCommGroup A) (laws : G.Laws) (f : C0 V A) (x y z : V) :
    Eq (d1 G (d0 G f) x y z) G.zero :=
  (congrArg (fun value => G.sub value (d0 G f x z))
    (G.sub_add_sub_cancel laws (f z) (f y) (f x))).trans (G.sub_self laws (d0 G f x z))

theorem d2_d1 (G : AddCommGroup A) (laws : G.Laws) (e : C1 V A) (x y z w : V) :
    Eq (d2 G (d1 G e) x y z w) G.zero :=
  let zw := e z w
  let yz := e y z
  let xy := e x y
  let yw := e y w
  let xz := e x z
  let xw := e x w
  have left : Eq (G.add (d1 G e y z w) (d1 G e x y w)) (G.sub (G.add (G.add zw yz) xy) xw) :=
    G.sub_add_add_sub laws (G.add zw yz) yw xy xw
  have right : Eq (G.add (d1 G e x z w) (d1 G e x y z)) (G.sub (G.add (G.add zw yz) xy) xw) :=
    (laws.add_comm (d1 G e x z w) (d1 G e x y z)).trans
      ((congrArg (G.add (d1 G e x y z))
        (congrArg (fun value => G.sub value xw) (laws.add_comm zw xz))).trans
        ((G.sub_add_add_sub laws (G.add yz xy) xz zw xw).trans
          (congrArg (fun value => G.sub value xw)
            ((laws.add_comm (G.add yz xy) zw).trans (laws.add_assoc zw yz xy).symm))))
  (congrArg (fun value => G.sub value (G.add (d1 G e x z w) (d1 G e x y z)))
    (left.trans right.symm)).trans (G.sub_self laws (G.add (d1 G e x z w) (d1 G e x y z)))

/-- Prepending the cone vertex lowers degree by one. -/
def H1 (base : V) (e : C1 V A) : C0 V A :=
  e base

def H2 (base : V) (F : C2 V A) : C1 V A :=
  F base

def H3 (base : V) (D : C3 V A) : C2 V A :=
  D base

theorem d0_H1_add_H2_d1 (G : AddCommGroup A) (laws : G.Laws) (base : V) (e : C1 V A) (x y : V) :
    Eq (G.add (d0 G (H1 base e) x y) (H2 base (d1 G e) x y)) (e x y) :=
  G.sub_add_complement laws (e base y) (e base x) (e x y)

theorem d1_H2_add_H3_d2
    (G : AddCommGroup A) (laws : G.Laws) (base : V) (F : C2 V A) (x y z : V) :
    Eq (G.add (d1 G (H2 base F) x y z) (H3 base (d2 G F) x y z)) (F x y z) :=
  G.sub_add_complement laws (G.add (F base y z) (F base x y)) (F base x z) (F x y z)

private theorem congr₂ (op : A → A → A) {a b c d : A} (left : Eq a b) (right : Eq c d) :
    Eq (op a c) (op b d) :=
  (congrArg (fun value => op value c) left).trans (congrArg (op b) right)

/-- The cone operator constructs a primitive at any chosen vertex. -/
theorem d1_H2_of_d2_eq_zero (G : AddCommGroup A) (laws : G.Laws) (base : V) (F : C2 V A)
    (closed : ∀ x y z w, Eq (d2 G F x y z w) G.zero) (x y z : V) :
    Eq (d1 G (H2 base F) x y z) (F x y z) :=
  let coboundary := d1 G (H2 base F) x y z
  (G.add_zero laws coboundary).symm.trans
    ((congrArg (G.add coboundary) (closed base x y z)).symm.trans
      (d1_H2_add_H3_d2 G laws base F x y z))

theorem d2_eq_zero_iff (G : AddCommGroup A) (laws : G.Laws) (base : V) (F : C2 V A) :
    Iff (∀ x y z w, Eq (d2 G F x y z w) G.zero)
      (Exists fun e : C1 V A => ∀ x y z, Eq (d1 G e x y z) (F x y z)) :=
  Iff.intro
    (fun closed => Exists.intro (H2 base F) (d1_H2_of_d2_eq_zero G laws base F closed))
    (fun exact => exact.elim fun e agrees x y z w =>
      (congr₂ G.sub (congr₂ G.add (agrees y z w) (agrees x y w))
        (congr₂ G.add (agrees x z w) (agrees x y z))).symm.trans (d2_d1 G laws e x y z w))

/-- A finite sequence of directed edges whose type records the two endpoints.
`nil` and `cons` accept vertices directly. The inductive constructors store them
as functions out of `True` for the strict prelude's compiler. -/
inductive VertexChain (V : Sort u) : V → V → Type u where
  | nilWith (vertex : True → V) : VertexChain V (vertex True.intro) (vertex True.intro)
  | consWith (first middle last : True → V)
      (tail : VertexChain V (middle True.intro) (last True.intro)) :
      VertexChain V (first True.intro) (last True.intro)

namespace VertexChain

def nil (vertex : V) : VertexChain V vertex vertex :=
  nilWith (fun _ => vertex)

def cons (first : V) {middle last : V} (tail : VertexChain V middle last) : VertexChain V first last :=
  consWith (fun _ => first) (fun _ => middle) (fun _ => last) tail

def sum (G : AddCommGroup A) (e : C1 V A) {first last : V} (chain : VertexChain V first last) : A :=
  VertexChain.rec (motive := fun _ _ _ => A) (fun _ => G.zero)
    (fun first middle _ _ total => G.add (e (first True.intro) (middle True.intro)) total) chain

theorem sum_d0 (G : AddCommGroup A) (laws : G.Laws) (f : C0 V A)
    {first last : V} (chain : VertexChain V first last) :
    Eq (chain.sum G (d0 G f)) (d0 G f first last) :=
  VertexChain.rec (motive := fun x y path => Eq (path.sum G (d0 G f)) (d0 G f x y))
    (fun vertex => (G.sub_self laws (f (vertex True.intro))).symm)
    (fun first middle last _ telescoped =>
      let x := first True.intro
      let y := middle True.intro
      let z := last True.intro
      (congrArg (G.add (d0 G f x y)) telescoped).trans
        ((laws.add_comm (d0 G f x y) (d0 G f y z)).trans
          (G.sub_add_sub_cancel laws (f z) (f y) (f x))))
    chain

theorem sum_d0_loop (G : AddCommGroup A) (laws : G.Laws) (f : C0 V A)
    {base : V} (chain : VertexChain V base base) :
    Eq (chain.sum G (d0 G f)) G.zero :=
  (chain.sum_d0 G laws f).trans (G.sub_self laws (f base))

end VertexChain
end SimplicialCoboundary
end Omega
