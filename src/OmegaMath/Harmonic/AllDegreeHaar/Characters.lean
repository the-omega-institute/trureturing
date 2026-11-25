module
prelude
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude
public import OmegaMath.Harmonic.AllDegreeHaar.Coefficients
import OmegaMath.Algebra.Quaternion.Polynomial

/-!
Omega original.

The even-character recurrence and its finite product expansion.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.AllDegreeHaar

open PiFreeHaar

namespace Characters

def four : Int := Int.ofNat Numerals.four

def shiftFour (p : Poly) : Poly := (p.scale four).shift

def recurrence (p : Poly) : Poly := (shiftFour p).add (p.scale Int.two.neg)

def one : Poly := .cons Int.one .nil

def first : Poly := .cons Int.one.neg (.cons four .nil)

structure Consecutive where
  lower : Poly
  upper : Poly

def character (n : Nat) : Poly :=
  (Nat.rec (motive := fun _ => Consecutive) ⟨one, first⟩
    (fun _ p => ⟨p.upper, (recurrence p.upper).sub p.lower⟩) n).lower

/-- The sum starting at degree `first`, through degree `first + span`. -/
def sum (first span : Nat) : Poly :=
  (Nat.rec (motive := fun _ => Nat → Poly) character
    (fun _ tail start => (character start).add (tail start.succ)) span) first

def gap (m n : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat) (fun n => n)
    (fun m prev n => Nat.rec m.succ (fun n _ => prev n) n) m) n

def span (m n : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => Nat.zero)
    (fun _ prev n => Nat.rec Nat.zero (fun n _ => (prev n).succ.succ) n) m) n

theorem gap_add_span (m n : Nat) : Eq ((gap m n).add (span m n)) (m.add n) :=
  (Nat.rec (motive := fun m => ∀ n, Eq ((gap m n).add (span m n)) (m.add n))
    (fun n => (Nat.add_zero n).trans (Nat.zero_add n).symm)
    (fun m ih n => Nat.rec (motive := fun n => Eq ((gap m.succ n).add (span m.succ n)) (m.succ.add n))
      rfl (fun n _ =>
        let g := gap m n
        let s := span m n
        ((Nat.add_succ g s.succ).trans (congrArg Nat.succ (Nat.add_succ g s))).trans
          ((congrArg (fun k : Nat => k.succ.succ) (ih n)).trans
            ((congrArg Nat.succ (Nat.succ_add m n).symm).trans (Nat.add_succ m.succ n).symm))) n) m) n

/-- The lower endpoint is the sum of the two truncated differences. -/
theorem gap_sub (m n : Nat) : Eq (gap m n) ((m.sub n).add (n.sub m)) :=
  have subZero : ∀ n, Eq (Nat.zero.sub n) Nat.zero :=
    fun n => Nat.rec (motive := fun n => Eq (Nat.zero.sub n) Nat.zero) (Nat.sub_zero .zero)
      (fun k ih => (Nat.sub_succ .zero k).trans ((congrArg Nat.pred ih).trans Nat.pred_zero)) n
  (Nat.rec (motive := fun m => ∀ n, Eq (gap m n) ((m.sub n).add (n.sub m)))
    (fun n => ((Eq.map₂ Nat.add (subZero n) (Nat.sub_zero n)).trans (Nat.zero_add n)).symm)
    (fun m ih n => Nat.rec (motive := fun n => Eq (gap m.succ n) ((m.succ.sub n).add (n.sub m.succ)))
      (((Eq.map₂ Nat.add (Nat.sub_zero m.succ) (subZero m.succ)).trans (Nat.add_zero _)).symm)
      (fun n _ => (ih n).trans (Eq.map₂ Nat.add
        (Nat.succ_sub_succ_eq_sub m n).symm (Nat.succ_sub_succ_eq_sub n m).symm)) n) m) n

private theorem shiftFour_add (p q : Poly) :
    Poly.Same (shiftFour (p.add q)) ((shiftFour p).add (shiftFour q)) :=
  (Poly.shift_congr (Poly.scale_add four p q)).trans (Poly.shift_add _ _)

private theorem recurrence_add (p q : Poly) :
    Poly.Same (recurrence (p.add q)) ((recurrence p).add (recurrence q)) :=
  (Poly.add_congr (shiftFour_add p q) (Poly.scale_add Int.two.neg p q)).trans
    (Poly.add_interchange _ _ _ _)

private theorem recurrence_congr {p q : Poly} (h : Poly.Same p q) :
    Poly.Same (recurrence p) (recurrence q) :=
  Poly.add_congr (Poly.shift_congr (Poly.scale_congr four h)) (Poly.scale_congr Int.two.neg h)

private theorem zero_character_mul (p : Poly) :
    Poly.Same ((character Nat.zero).mul p) p :=
  (Poly.add_congr (Poly.scale_one p) Poly.shift_nil).trans (Poly.add_nil p)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Int.subNatNat in
private theorem first_character_mul (p : Poly) :
    Poly.Same ((character Nat.one).mul p) ((recurrence p).add p) :=
  have h : Poly.Same ((character Nat.one).mul p) ((p.scale Int.one.neg).add (shiftFour p)) :=
    Poly.add_congr (Poly.same_refl _) (Poly.shift_congr
      ((Poly.add_congr (Poly.same_refl _) Poly.shift_nil).trans (Poly.add_nil _)))
  have scalar : Poly.Same (p.scale Int.one.neg) ((p.scale Int.two.neg).add p) :=
    (((Poly.add_scale Int.two.neg Int.one p).trans
      (Poly.add_congr (Poly.same_refl _) (Poly.scale_one p))) :
        Poly.Same (p.scale Int.one.neg) ((p.scale Int.two.neg).add p))
  h.trans ((Poly.add_comm _ _).trans
    ((Poly.add_congr (Poly.same_refl _) scalar).trans (Poly.add_assoc _ _ _).symm))

private theorem recurrence_mul (p q : Poly) :
    Poly.Same ((recurrence p).mul q) (recurrence (p.mul q)) :=
  (Poly.mul_comm _ q).trans ((Poly.mul_add q _ _).trans
    (Poly.add_congr
      ((Poly.shift_mul_right q (p.scale four)).trans
        (Poly.shift_congr ((Poly.mul_scale four q p).trans
          (Poly.scale_congr four (Poly.mul_comm q p)))))
      ((Poly.mul_scale Int.two.neg q p).trans (Poly.scale_congr Int.two.neg (Poly.mul_comm q p)))))

private theorem recurrence_character (n : Nat) :
    Poly.Same (recurrence (character n.succ)) ((character n.succ.succ).add (character n)) :=
  let p := recurrence (character n.succ)
  let q := character n
  fun k =>
    let a := p.get k
    let b := q.get k
    have cancel : Eq ((a.sub b).add b) a :=
      (Int.add_assoc a b.neg b).trans
        ((congrArg a.add (Int.add_left_neg b)).trans (Int.add_zero a))
    (cancel.symm.trans (Eq.map₂ Int.add (Poly.get_sub p q k).symm rfl)).trans
      (Poly.get_add (p.sub q) q k).symm

private theorem recurrence_sum (first span : Nat) :
    Poly.Same (recurrence (sum first.succ span)) ((sum first.succ.succ span).add (sum first span)) :=
  (Nat.rec (motive := fun span => ∀ (first : Nat),
    Poly.Same (recurrence (sum first.succ span)) ((sum first.succ.succ span).add (sum first span)))
    recurrence_character
    (fun k ih first => (recurrence_add (character first.succ) (sum first.succ.succ k)).trans
      ((Poly.add_congr (recurrence_character first) (ih first.succ)).trans
        (Poly.add_interchange _ _ _ _))) span) first

private theorem successor_product (m n : Nat) :
    Poly.Same ((character m.succ.succ).mul (character n))
      ((recurrence ((character m.succ).mul (character n))).sub ((character m).mul (character n))) :=
  (Poly.mul_sub_left (recurrence (character m.succ)) (character m) (character n)).trans
    (Poly.sub_congr (recurrence_mul _ _) (Poly.same_refl _))

private theorem first_product (d : Nat) :
    Poly.Same ((character Nat.one).mul (character d.succ)) (sum d Nat.one.succ) :=
  (first_character_mul _).trans
    ((Poly.add_congr (recurrence_character d) (Poly.same_refl _)).trans
      ((Poly.add_congr (Poly.add_comm _ _) (Poly.same_refl _)).trans
        ((Poly.add_assoc _ _ _).trans (Poly.add_congr (Poly.same_refl _) (Poly.add_comm _ _)))))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem sum_difference (d k : Nat) :
    Poly.Same (((sum d.succ.succ k.succ.succ).add (sum d k.succ.succ)).sub (sum d.succ.succ k))
      (sum d k.succ.succ.succ.succ) :=
  let p := sum d.succ.succ k.succ.succ
  let q := character d
  let r := character d.succ
  let s := sum d.succ.succ k
  fun n =>
    let values : Quaternion.Polynomial.Values :=
      .cons (p.get n) (.cons (q.get n) (.cons (r.get n) (.cons (s.get n) .nil)))
    let a : Quaternion.Polynomial.Expr := .var Nat.zero
    let b : Quaternion.Polynomial.Expr := .var Nat.one
    let c : Quaternion.Polynomial.Expr := .var Nat.one.succ
    let e : Quaternion.Polynomial.Expr := .var Nat.one.succ.succ
    have algebra := Quaternion.Polynomial.Expr.sound
      ((a.add (b.add (c.add e))).sub e) (b.add (c.add a)) values rfl
    (Poly.get_sub (p.add (q.add (r.add s))) s n).trans
      ((Eq.map₂ Int.sub
        ((Poly.get_add p (q.add (r.add s)) n).trans (congrArg (p.get n).add
          ((Poly.get_add q (r.add s) n).trans (congrArg (q.get n).add (Poly.get_add r s n)))))
        rfl).trans (algebra.trans
        ((congrArg (q.get n).add (Poly.get_add r p n).symm).trans
          (Poly.get_add q (r.add p) n).symm)))

private def twice (n : Nat) : Nat := Nat.rec Nat.zero (fun _ x => x.succ.succ) n

private def OrderedProduct (m : Nat) : Prop :=
  ∀ d, Poly.Same ((character m).mul (character (d.add m))) (sum d (twice m))

private theorem ordered_step (m : Nat) (h₀ : OrderedProduct m) (h₁ : OrderedProduct m.succ) :
    OrderedProduct m.succ.succ :=
  fun d =>
    let n := (d.add m).succ.succ
    have hlow : Poly.Same ((character m).mul (character n)) (sum d.succ.succ (twice m)) :=
      Eq.subst (motive := fun t => Poly.Same ((character m).mul (character t)) (sum d.succ.succ (twice m)))
        ((Nat.succ_add d.succ m).trans (congrArg Nat.succ (Nat.succ_add d m))) (h₀ d.succ.succ)
    have hhigh : Poly.Same ((character m.succ).mul (character n)) (sum d.succ (twice m).succ.succ) :=
      Eq.subst (motive := fun t => Poly.Same ((character m.succ).mul (character t)) (sum d.succ (twice m).succ.succ))
        ((Nat.succ_add d m.succ).trans (congrArg Nat.succ (Nat.add_succ d m))) (h₁ d.succ)
    Eq.subst (motive := fun t => Poly.Same ((character m.succ.succ).mul (character t))
      (sum d (twice m.succ.succ)))
      ((Nat.add_succ d m.succ).trans (congrArg Nat.succ (Nat.add_succ d m))).symm ((successor_product m n).trans
      ((Poly.sub_congr ((recurrence_congr hhigh).trans (recurrence_sum d (twice m).succ.succ)) hlow).trans
        (sum_difference d (twice m))))

private theorem ordered_product (m : Nat) : OrderedProduct m :=
  (Nat.rec (motive := fun m => And (OrderedProduct m) (OrderedProduct m.succ))
    (And.intro (fun d => Eq.subst (motive := fun n => Poly.Same ((character Nat.zero).mul (character n))
      (sum d (twice Nat.zero))) (Nat.add_zero d).symm (zero_character_mul (character d)))
      (fun d => Eq.subst (motive := fun n => Poly.Same ((character Nat.one).mul (character n))
        (sum d (twice Nat.one))) (Nat.add_one d).symm (first_product d)))
    (fun m h => And.intro h.right (ordered_step m h.left h.right)) m).left

private theorem endpoints_ordered (m d : Nat) :
    And (Eq (gap m (d.add m)) d) (Eq (span m (d.add m)) (twice m)) :=
  Nat.rec (motive := fun m => And (Eq (gap m (d.add m)) d) (Eq (span m (d.add m)) (twice m)))
    (And.intro (Nat.add_zero d) rfl)
    (fun m h => Eq.subst (motive := fun n =>
      And (Eq (gap m.succ n) d) (Eq (span m.succ n) (twice m.succ))) (Nat.add_succ d m).symm
      (And.intro h.left (congrArg (fun n : Nat => n.succ.succ) h.right))) m

private theorem endpoints_symm (m n : Nat) :
    And (Eq (gap m n) (gap n m)) (Eq (span m n) (span n m)) :=
  (Nat.rec (motive := fun m => ∀ n, And (Eq (gap m n) (gap n m)) (Eq (span m n) (span n m)))
    (fun n => Nat.rec (motive := fun n =>
      And (Eq (gap Nat.zero n) (gap n Nat.zero)) (Eq (span Nat.zero n) (span n Nat.zero)))
      (And.intro rfl rfl) (fun _ _ => And.intro rfl rfl) n)
    (fun m ih n => Nat.rec (motive := fun n =>
      And (Eq (gap m.succ n) (gap n m.succ)) (Eq (span m.succ n) (span n m.succ)))
      (And.intro rfl rfl)
      (fun n _ => And.intro (ih n).left (congrArg (fun k : Nat => k.succ.succ) (And.right (ih n)))) n) m) n

private theorem add_difference (m n : Nat) :
    Or (Exists (fun (d : Nat) => Eq n (d.add m))) (Exists (fun (d : Nat) => Eq m (d.add n))) :=
  (Nat.rec (motive := fun m => ∀ n,
    Or (Exists (fun (d : Nat) => Eq n (d.add m))) (Exists (fun (d : Nat) => Eq m (d.add n))))
    (fun n => Or.inl (Exists.intro n (Nat.add_zero n).symm))
    (fun m ih n => Nat.rec (motive := fun n =>
      Or (Exists (fun (d : Nat) => Eq n (d.add m.succ))) (Exists (fun (d : Nat) => Eq m.succ (d.add n))))
      (Or.inr (Exists.intro m.succ (Nat.add_zero m.succ).symm))
      (fun n _ => (ih n).elim
        (fun h => h.elim (fun d h => Or.inl (Exists.intro d ((congrArg Nat.succ h).trans (Nat.add_succ d m).symm))))
        (fun h => h.elim (fun d h => Or.inr (Exists.intro d ((congrArg Nat.succ h).trans (Nat.add_succ d n).symm))))) n) m) n

private theorem product_ordered (m d : Nat) :
    Poly.Same ((character m).mul (character (d.add m))) (sum (gap m (d.add m)) (span m (d.add m))) :=
  have ends := endpoints_ordered m d
  (ordered_product m d).trans (fun k => congrArg (fun p : Poly => p.get k)
    (Eq.map₂ sum ends.left ends.right).symm)

theorem product (m n : Nat) :
    Poly.Same ((character m).mul (character n)) (sum (gap m n) (span m n)) :=
  (add_difference m n).elim
    (fun h => h.elim (fun d h => Eq.subst
      (motive := fun n => Poly.Same ((character m).mul (character n)) (sum (gap m n) (span m n)))
      h.symm (product_ordered m d)))
    (fun h => h.elim (fun d h =>
      have ordered := Eq.subst
        (motive := fun m => Poly.Same ((character n).mul (character m)) (sum (gap n m) (span n m)))
        h.symm (product_ordered n d)
      have ends := endpoints_symm m n
      (Poly.mul_comm _ _).trans (ordered.trans
        (fun k => congrArg (fun p : Poly => p.get k) (Eq.map₂ sum ends.left ends.right).symm))))

end Characters
end Omega.Harmonic.AllDegreeHaar
