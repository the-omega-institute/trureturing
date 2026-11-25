/- GID: D5/S3/Fourier/HurwitzFreeGroup
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite words in the six norm-five Hurwitz generators. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude
public import D5.S3.Fourier.HurwitzFreeGroup.Split5

/-!
Omega original.

Finite words in the six norm-five Hurwitz generators. Every nonempty reduced
word has a nonzero split image modulo five and evaluates to a nonscalar
integer Hamilton quaternion.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz.FreeGroup

inductive Word where
  | nil
  | cons (head : Generator) (tail : Word)

def Word.length : Word → Nat := Word.rec Nat.zero (fun _ _ n => n.succ)

/-- A letter can be prepended when it is not opposite to the first letter. -/
def Word.AllowsPrepend (w : Word) (g : Generator) : Prop :=
  Word.rec (motive := fun _ => Prop) True (fun h _ _ => Eq (g.isOpposite h) .false) w

/-- No letter is followed by its quaternion conjugate. -/
def IsReduced : Word → Prop :=
  Word.rec (motive := fun _ => Prop) True (fun g rest reduced => And (rest.AllowsPrepend g) reduced)

def evalQuat : Word → Quaternion :=
  Word.rec Quaternion.one (fun g _ q => (generatorQuat g).mul q)

def evalSplit5 : Word → Matrix5 :=
  Word.rec matrixOne (fun g _ A => (split5 g.coordinates).mul A)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem evalSplit5_eq (w : Word) : Eq (evalSplit5 w) (quaternionSplit5 (evalQuat w)) :=
  Word.rec (motive := fun w => Eq (evalSplit5 w) (quaternionSplit5 (evalQuat w)))
    rfl
    (fun g w ih =>
      (congrArg (split5 g.coordinates).mul ih).trans
        (quaternionSplit5_mul (generatorQuat g) (evalQuat w)).symm) w

private def RowNonzero (s t : Residue) : Prop :=
  Or (Not (Eq s .zero)) (Not (Eq t .zero))

private theorem residue_zero_or_ne (r : Residue) : Or (Eq r .zero) (Not (Eq r .zero)) :=
  let ne := fun (r : Residue) (nonzero : Eq r.isZero .false) (h : Eq r .zero) =>
    Residue.false_ne_true (nonzero.symm.trans (congrArg Residue.isZero h))
  Residue.rec (motive := fun r => Or (Eq r .zero) (Not (Eq r .zero)))
    (Or.inl rfl) (Or.inr (ne .one rfl)) (Or.inr (ne .two rfl)) (Or.inr (ne .three rfl))
    (Or.inr (ne .four rfl)) r

private theorem factor_row_nonzero (g : Generator) : RowNonzero g.factors.s g.factors.t :=
  let f := g.factors
  let M := Matrix5.outer f.u f.v f.s f.t
  have nonzero : Eq M.isZero .false :=
    (congrArg Matrix5.isZero (split_rank_one g).left).symm.trans (split_rank_one g).right
  (residue_zero_or_ne f.s).elim
    (fun hs => (residue_zero_or_ne f.t).elim
      (fun ht => False.elim (Residue.false_ne_true
        (nonzero.symm.trans
          ((congrArg Matrix5.isZero (Eq.map₂ (Matrix5.outer f.u f.v) hs ht)).trans
            (outer_zero_row f.u f.v)))))
      Or.inr)
    Or.inl

private theorem adjacent_contraction_ne_zero (g h : Generator)
    (allowed : Eq (g.isOpposite h) .false) :
    Not (Eq (contraction g.factors.s g.factors.t h.factors.u h.factors.v) .zero) :=
  let f := g.factors
  let e := h.factors
  let c := contraction f.s f.t e.u e.v
  have factorization : Eq ((split5 g.coordinates).mul (split5 h.coordinates))
      (Matrix5.outer f.u f.v (c.mul e.s) (c.mul e.t)) :=
    (Eq.map₂ Matrix5.mul (split_rank_one g).left (split_rank_one h).left).trans
      (outer_mul f.u f.v f.s f.t e.u e.v e.s e.t)
  fun hc =>
    have zeroRow : Eq (Matrix5.outer f.u f.v (c.mul e.s) (c.mul e.t))
        (Matrix5.outer f.u f.v .zero .zero) :=
      Eq.map₂ (Matrix5.outer f.u f.v)
        ((congrArg (fun a : Residue => a.mul e.s) hc).trans (Residue.zero_mul e.s))
        ((congrArg (fun a : Residue => a.mul e.t) hc).trans (Residue.zero_mul e.t))
    Residue.false_ne_true
      (((split_product_zero g h).trans allowed).symm.trans
        ((congrArg Matrix5.isZero (factorization.trans zeroRow)).trans (outer_zero_row f.u f.v)))

private def HasOuterRow (g : Generator) (A : Matrix5) : Prop :=
  Exists fun s : Residue => Exists fun t : Residue =>
    And (Eq A (Matrix5.outer g.factors.u g.factors.v s t)) (RowNonzero s t)

/-- A nonempty reduced product keeps the first generator's column and a nonzero row. -/
private theorem reduced_outer (w : Word) :
    ∀ g : Generator, IsReduced (.cons g w) → HasOuterRow g (evalSplit5 (.cons g w)) :=
  Word.rec (motive := fun w =>
    ∀ g : Generator, IsReduced (.cons g w) → HasOuterRow g (evalSplit5 (.cons g w)))
    (fun g _ =>
      let f := g.factors
      Exists.intro f.s (Exists.intro f.t
        (And.intro ((matrix_mul_one (split5 g.coordinates)).trans (split_rank_one g).left)
          (factor_row_nonzero g))))
    (fun h _ ih g hr =>
      let f := g.factors
      let e := h.factors
      let c := contraction f.s f.t e.u e.v
      have hc := adjacent_contraction_ne_zero g h hr.left
      (ih h hr.right).elim fun s hs => hs.elim fun t ht =>
        Exists.intro (c.mul s) (Exists.intro (c.mul t) (And.intro
          ((Eq.map₂ Matrix5.mul (split_rank_one g).left ht.left).trans
            (outer_mul f.u f.v f.s f.t e.u e.v s t))
          (ht.right.elim
            (fun h => Or.inl (Residue.mul_ne_zero hc h))
            (fun h => Or.inr (Residue.mul_ne_zero hc h)))))) w

private theorem factor_column_one (g : Generator) :
    Or (Eq g.factors.u .one) (Eq g.factors.v .one) :=
  Generator.rec (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) g

private theorem outer_nonzero (g : Generator) {s t : Residue} (hrow : RowNonzero s t) :
    Eq (Matrix5.outer g.factors.u g.factors.v s t).isZero .false :=
  let f := g.factors
  let A := Matrix5.outer f.u f.v s t
  let recover := fun (a b : Residue) (ha : Eq a .one) (h : Eq (a.mul b) .zero) =>
    (Residue.one_mul b).symm.trans ((congrArg (fun x : Residue => x.mul b) ha).symm.trans h)
  bool_false_of_not_true A.isZero fun hz =>
    have e := entries_zero hz
    (factor_column_one g).elim
      (fun hu => hrow.elim (fun hs => hs (recover f.u s hu e.left))
        (fun ht => ht (recover f.u t hu e.right.left)))
      (fun hv => hrow.elim (fun hs => hs (recover f.v s hv e.right.right.left))
        (fun ht => ht (recover f.v t hv e.right.right.right)))

/-- Every reduced word has a nonzero image modulo five. -/
theorem reduced_word_split5_nonzero (w : Word) (hr : IsReduced w) :
    Eq (evalSplit5 w).isZero .false :=
  (Word.rec (motive := fun w => IsReduced w → Eq (evalSplit5 w).isZero .false)
    (fun _ => rfl)
    (fun g tail _ hr => (reduced_outer tail g hr).elim fun _ hs => hs.elim fun _ ht =>
      (congrArg Matrix5.isZero ht.left).trans (outer_nonzero g ht.right)) w) hr

/-- Natural powers of five, iterated over the word length. -/
def powFive : Nat → Nat := Nat.rec Nat.one (fun _ n => five.mul n)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem generator_normSq (g : Generator) : Eq (generatorQuat g).normSq five :=
  let q := generatorQuat g
  Int.ofNat_inj.mp (q.normSq_cast.trans
    ((Int.add_assoc (q.w.square.add q.x.square) q.y.square q.z.square).symm.trans
      (generator_norm g)))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
/-- The squared Hamilton norm is five to the word length, for any word. -/
theorem reduced_word_normSq (w : Word) : Eq (evalQuat w).normSq (powFive w.length) :=
  Word.rec (motive := fun w => Eq (evalQuat w).normSq (powFive w.length))
    rfl
    (fun g tail ih =>
      (Quaternion.normSq_mul (generatorQuat g) (evalQuat tail)).trans
        (Eq.map₂ Nat.mul (generator_normSq g) ih)) w

private theorem quat_split_zero_of_coord_residues {q : Quaternion}
    (hw : Eq (Residue.ofInt q.w) .zero) (hx : Eq (Residue.ofInt q.x) .zero)
    (hy : Eq (Residue.ofInt q.y) .zero) (hz : Eq (Residue.ofInt q.z) .zero) :
    Eq (quaternionSplit5 q).isZero .true :=
  have double (a : Int) (h : Eq (Residue.ofInt a) .zero) :
      Eq (Residue.ofInt (Int.two.mul a)) .zero :=
    (Residue.ofInt_mul Int.two a).trans (congrArg (Residue.mul .two) h)
  have sum (a b : Int) (ha : Eq (Residue.ofInt a) .zero) (hb : Eq (Residue.ofInt b) .zero) :
      Eq (Residue.ofInt (a.add b)) .zero :=
    (Residue.ofInt_add a b).trans (Eq.map₂ Residue.add ha hb)
  have minus (a : Int) (h : Eq (Residue.ofInt a) .zero) : Eq (Residue.ofInt a.neg) .zero :=
    (Residue.ofInt_neg a).trans (congrArg Residue.neg h)
  have a := sum q.w (Int.two.mul q.x) hw (double q.x hx)
  have b := sum q.y (Int.two.mul q.z) hy (double q.z hz)
  have c := sum (Int.two.mul q.z) q.y.neg (double q.z hz) (minus q.y hy)
  have d := sum q.w (Int.two.mul q.x).neg hw (minus _ (double q.x hx))
  (congrArg Matrix5.isZero
    ((Eq.map₂ (fun a b => Matrix5.mk a b (quaternionSplit5 q).c (quaternionSplit5 q).d) a b).trans
      (Eq.map₂ (Matrix5.mk .zero .zero) c d))).trans rfl

/-- All four integer coordinates are divisible by five. -/
def AllDivisibleByFive (q : Quaternion) : Prop :=
  let f := Int.ofNat five
  Exists fun a : Int => Exists fun b : Int => Exists fun c : Int => Exists fun d : Int =>
    And (Eq q.w (f.mul a)) (And (Eq q.x (f.mul b)) (And (Eq q.y (f.mul c)) (Eq q.z (f.mul d))))

/-- The four coordinates of a reduced word are not simultaneously multiples of five. -/
theorem reduced_word_not_div_five (w : Word) (hr : IsReduced w) :
    Not (AllDivisibleByFive (evalQuat w)) :=
  fun all => all.elim fun a ha => ha.elim fun b hb => hb.elim fun c hc => hc.elim fun d hd =>
    let zero := fun (q k : Int) (h : Eq q ((Int.ofNat five).mul k)) =>
      (congrArg Residue.ofInt h).trans (residue_five_mul k)
    have splitZero := quat_split_zero_of_coord_residues
      (zero _ a hd.left) (zero _ b hd.right.left)
      (zero _ c hd.right.right.left) (zero _ d hd.right.right.right)
    Residue.false_ne_true
      ((reduced_word_split5_nonzero w hr).symm.trans
        ((congrArg Matrix5.isZero (evalSplit5_eq w)).trans splitZero))

private theorem norm_residue_zero (w : Word) (hn : Not (Eq w .nil)) :
    Eq (Residue.ofInt (Int.ofNat (evalQuat w).normSq)) .zero :=
  (congrArg (fun n => Residue.ofInt (Int.ofNat n)) (reduced_word_normSq w)).trans
    ((Word.rec (motive := fun w => Not (Eq w .nil) →
        Eq (Residue.ofInt (Int.ofNat (powFive w.length))) .zero)
      (fun hn => False.elim (hn rfl))
      (fun _ tail _ _ => residue_five_mul (Int.ofNat (powFive tail.length))) w) hn)

/-- No nonempty reduced word evaluates to an integer scalar. -/
theorem reduced_word_ne_scalar (w : Word) (hr : IsReduced w) (hn : Not (Eq w .nil))
    (k : Int) : Not (Eq (evalQuat w) (Quaternion.scalar k)) :=
  fun h =>
    have norm := (congrArg (fun q : Quaternion => Residue.ofInt (Int.ofNat q.normSq)) h).symm.trans
      (norm_residue_zero w hn)
    have scalarNorm : Eq (Int.ofNat (Quaternion.scalar k).normSq) (k.mul k) :=
      (congrArg Int.ofNat (Quaternion.scalar_normSq k)).trans Int.natAbs_mul_self
    have square : Eq ((Residue.ofInt k).mul (Residue.ofInt k)) .zero :=
      (Residue.ofInt_mul k k).symm.trans ((congrArg Residue.ofInt scalarNorm).symm.trans norm)
    have scalarZero : Eq (Residue.ofInt k) .zero :=
      (residue_zero_or_ne (Residue.ofInt k)).elim (fun h => h)
        (fun h => False.elim (Residue.mul_ne_zero h h square))
    have splitZero := quat_split_zero_of_coord_residues (q := Quaternion.scalar k)
      scalarZero rfl rfl rfl
    Residue.false_ne_true
      ((reduced_word_split5_nonzero w hr).symm.trans
        ((congrArg Matrix5.isZero ((evalSplit5_eq w).trans (congrArg quaternionSplit5 h))).trans
          splitZero))

/-- A scalar quaternion is an integer embedded in the scalar coordinate. -/
def IsScalar (q : Quaternion) : Prop := Exists fun k : Int => Eq q (Quaternion.scalar k)

/-- The quaternion represented by a nonempty reduced word is nonscalar. -/
theorem reduced_word_non_scalar (w : Word) (hr : IsReduced w) (hn : Not (Eq w .nil)) :
    Not (IsScalar (evalQuat w)) :=
  fun h => h.elim (reduced_word_ne_scalar w hr hn)

end Omega.Hurwitz.FreeGroup
