module
prelude
public import OmegaMath.Arithmetic.Euclidean.Division
public import OmegaMath.Data.IntRatio

/-! Omega original.

Compute the least quarter-depth whose integer threshold exceeds the numerator.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

open Omega

def four : Nat := Nat.one.succ.succ.succ

def pow4 (n : Nat) : Nat := Nat.rec Nat.one (fun _ p => four.mul p) n

private theorem one_le_four : Nat.le Nat.one four := True.intro

private theorem pow4_pos (n : Nat) : Nat.lt Nat.zero (pow4 n) :=
  Nat.rec (motive := fun n => Nat.lt Nat.zero (pow4 n)) True.intro
    (fun _ ih => mul_pos one_le_four ih) n

private theorem le_mul_of_one_le (a b : Nat) (h : Nat.le Nat.one b) : Nat.le a (a.mul b) :=
  Eq.subst (fun x => Nat.le x (a.mul b)) (Nat.mul_one a) (mul_le_mul_left h a)

private theorem lt_four_mul {a : Nat} (ha : Nat.lt Nat.zero a) : Nat.lt a (four.mul a) :=
  have twice : Nat.lt a (Nat.one.succ.mul a) :=
    lt_of_lt_of_le
      (show Nat.lt a ((Nat.one.mul a).add a) from
        Eq.subst (fun x => Nat.lt x ((Nat.one.mul a).add a)) (Nat.one_mul a)
          (add_lt_add_left ha (Nat.one.mul a)))
      (Eq.subst (fun x => Nat.le x (Nat.one.succ.mul a)) (Nat.succ_mul Nat.one a) (Nat.le.refl _))
  lt_of_lt_of_le twice (mul_le_mul_right
    (Nat.le.step (Nat.le.step (Nat.le.refl Nat.one.succ))) a)

private theorem lt_pow4_self (n : Nat) : Nat.lt n (pow4 n) :=
  Nat.rec (motive := fun n => Nat.lt n (pow4 n)) True.intro
    (fun n ih => lt_of_le_of_lt ih (lt_four_mul (pow4_pos n))) n

private theorem pow4_mono {m n : Nat} (h : Nat.le m n) : Nat.le (pow4 m) (pow4 n) :=
  (Nat.rec (motive := fun m => ∀ n, Nat.le m n → Nat.le (pow4 m) (pow4 n))
    (fun n _ => pow4_pos n)
    (fun m ih n => Nat.rec (motive := fun n => Nat.le m.succ n → Nat.le (pow4 m.succ) (pow4 n))
      (fun no => False.elim no) (fun n _ h => mul_le_mul_left (ih n h) four) n) m) n h

def depthLt (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (fun b => Nat.rec Bool.false (fun _ _ => Bool.true) b)
    (fun _ ih b => Nat.rec Bool.false (fun b _ => ih b) b) a b

private theorem depthLt_cases (a b : Nat) (P : Bool → Prop)
    (yes : Nat.lt a b → P Bool.true) (no : Nat.le b a → P Bool.false) : P (depthLt a b) :=
  (Nat.rec (motive := fun a => ∀ b (P : Bool → Prop),
    (Nat.lt a b → P Bool.true) → (Nat.le b a → P Bool.false) → P (depthLt a b))
    (fun b => Nat.rec (motive := fun b => ∀ (P : Bool → Prop),
      (Nat.lt Nat.zero b → P Bool.true) → (Nat.le b Nat.zero → P Bool.false) →
        P (depthLt Nat.zero b))
      (fun _ _ no => no True.intro) (fun b _ _ yes _ => yes (Nat.zero_le b)) b)
    (fun a ih b => Nat.rec (motive := fun b => ∀ (P : Bool → Prop),
      (Nat.lt a.succ b → P Bool.true) → (Nat.le b a.succ → P Bool.false) → P (depthLt a.succ b))
      (fun _ _ no => no True.intro) (fun b _ P yes no => ih b P yes no) b) a) b P yes no

/-- Increase the threshold by a factor of four until it exceeds the numerator. -/
def depthSearch (fuel bound numerator : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => Nat.zero)
    (fun _ search bound => Bool.rec (search (bound.mul four)).succ Nat.zero
      (depthLt numerator bound)) fuel bound

def quarterDepth (c d p q : Nat) : Nat :=
  depthSearch (c.mul q) ((d.mul p).mul four) (c.mul q)

private theorem depthSearch_spec (fuel bound numerator : Nat)
    (h : Nat.lt numerator (bound.mul (pow4 fuel))) :
    Nat.lt numerator (bound.mul (pow4 (depthSearch fuel bound numerator))) :=
  (Nat.rec (motive := fun f => ∀ (b : Nat), Nat.lt numerator (b.mul (pow4 f)) →
    Nat.lt numerator (b.mul (pow4 (depthSearch f b numerator))))
    (fun b (h : Nat.lt numerator (b.mul (pow4 Nat.zero))) => h)
    (fun f ih b h => depthLt_cases numerator b
      (fun test => Nat.lt numerator (b.mul (pow4 (Bool.rec (motive := fun _ => Nat)
        (depthSearch f (b.mul four) numerator).succ Nat.zero test))))
      (fun less => Eq.subst (Nat.lt numerator) (Nat.mul_one b).symm less)
      (fun _ => Eq.subst (Nat.lt numerator) (Nat.mul_assoc b four (pow4 (depthSearch f (b.mul four) numerator)))
        (ih (b.mul four) (Eq.subst (Nat.lt numerator) (Nat.mul_assoc b four (pow4 f)).symm h))))
    fuel) bound h

private theorem depthSearch_le_of_lt (fuel bound numerator N : Nat)
    (h : Nat.lt numerator (bound.mul (pow4 N))) :
    Nat.le (depthSearch fuel bound numerator) N :=
  (Nat.rec (motive := fun f => ∀ (b N : Nat), Nat.lt numerator (b.mul (pow4 N)) →
    Nat.le (depthSearch f b numerator) N)
    (fun _ N _ => Nat.zero_le N)
    (fun f ih b N h => depthLt_cases numerator b
      (fun test => Nat.le (Bool.rec (motive := fun _ => Nat)
        (depthSearch f (b.mul four) numerator).succ Nat.zero test) N)
      (fun _ => Nat.zero_le N)
      (fun notLess =>
        (Nat.rec (motive := fun N => Nat.lt numerator (b.mul (pow4 N)) →
          Nat.le (depthSearch f (b.mul four) numerator).succ N)
          (fun h => False.elim (lt_irrefl b (lt_of_le_of_lt notLess
            (Eq.subst (Nat.lt numerator) (Nat.mul_one b) h))))
          (fun N _ (h : Nat.lt numerator (b.mul (pow4 N.succ))) =>
            have step : Nat.le (depthSearch f (b.mul four) numerator) N :=
              ih (b.mul four) N (Eq.subst (Nat.lt numerator) (Nat.mul_assoc b four (pow4 N)).symm h)
            Nat.succ_le_succ step) N) h))
    fuel) bound N h

/-- A depth is sufficient exactly when its integer threshold exceeds the numerator. -/
theorem quarterDepth_integer_iff (c d p q N : Nat) (hd : Nat.lt Nat.zero d) (hp : Nat.lt Nat.zero p) :
    Iff (Nat.le (quarterDepth c d p q) N)
      (Nat.lt (c.mul q) ((d.mul p).mul (pow4 N.succ))) :=
  let b := (d.mul p).mul four
  let x := c.mul q
  have hb : Nat.lt Nat.zero b := mul_pos (mul_pos hd hp) one_le_four
  have start : Nat.lt x (b.mul (pow4 x)) :=
    lt_of_lt_of_le (lt_pow4_self x)
      (Eq.subst (fun n => Nat.le n (b.mul (pow4 x))) (Nat.one_mul (pow4 x)) (mul_le_mul_right hb (pow4 x)))
  Iff.intro
    (fun h => Eq.subst (Nat.lt x) (Nat.mul_assoc (d.mul p) four (pow4 N))
      (lt_of_lt_of_le (depthSearch_spec x b x start) (mul_le_mul_left (pow4_mono h) b)))
    (fun h => depthSearch_le_of_lt x b x N
      (Eq.subst (Nat.lt x) (Nat.mul_assoc (d.mul p) four (pow4 N)).symm h))

theorem quarterDepth_integer_sound (c d p q N : Nat)
    (hd : Nat.lt Nat.zero d) (hp : Nat.lt Nat.zero p) (h : Nat.le (quarterDepth c d p q) N) :
    Nat.lt (c.mul q) ((d.mul p).mul (pow4 N.succ)) :=
  (quarterDepth_integer_iff c d p q N hd hp).mp h

private theorem ofNat_sub (a b : Nat) :
    Eq ((Int.ofNat a).sub (Int.ofNat b)) (Int.subNatNat a b) :=
  Nat.rec (motive := fun b => Eq ((Int.ofNat a).sub (Int.ofNat b)) (Int.subNatNat a b))
    (Nat.rec (motive := fun a => Eq ((Int.ofNat a).sub Int.zero) (Int.subNatNat a Nat.zero))
      Eq.refl (fun _ _ => Eq.refl) a) (fun _ _ => Eq.refl) b

private theorem le_cast {a b : Nat} (h : Nat.le a b) : (Int.ofNat a).le (Int.ofNat b) :=
  Eq.subst Int.NonNeg (ofNat_sub b a).symm
    (Int.subNatNat_elim b a (fun b a x => Nat.le a b → Int.NonNeg x)
      (fun _ _ _ => True.intro)
      (fun i b ltWrong => False.elim (lt_irrefl b (Nat.le_trans
        (add_lt_add_left (pos_of_ne_zero (Nat.succ_ne_zero i)) b) ltWrong))) h)

private theorem value_lt_of_cross {a b c d : Nat} (hb : Nat.lt Nat.zero b) (hd : Nat.lt Nat.zero d)
    (h : Nat.lt (a.mul d) (c.mul b)) :
    IntRatio.Lt (IntRatio.value (Int.ofNat a) b) (IntRatio.value (Int.ofNat c) d) :=
  (Nat.rec (motive := fun b => ∀ d, Nat.lt Nat.zero b → Nat.lt Nat.zero d →
    Nat.lt (a.mul d) (c.mul b) →
      IntRatio.Lt (IntRatio.value (Int.ofNat a) b) (IntRatio.value (Int.ofNat c) d))
    (fun _ hb _ _ => False.elim hb)
    (fun b _ d => Nat.rec (motive := fun d => Nat.lt Nat.zero b.succ → Nat.lt Nat.zero d →
      Nat.lt (a.mul d) (c.mul b.succ) →
        IntRatio.Lt (IntRatio.value (Int.ofNat a) b.succ) (IntRatio.value (Int.ofNat c) d))
      (fun _ hd _ => False.elim hd)
      (fun d _ _ _ h => And.intro
        (show (Int.ofNat (a.mul d.succ)).le (Int.ofNat (c.mul b.succ)) from le_cast (le_of_lt h))
        (fun e => ne_of_lt h (Int.ofNat_inj.mp e))) d) b) d hb hd h

/-- Divide the exact input ratio by the next power of four. -/
theorem quarterDepth_ratio_sound (c d p q N : Nat)
    (hd : Nat.lt Nat.zero d) (hp : Nat.lt Nat.zero p) (hq : Nat.lt Nat.zero q)
    (h : Nat.le (quarterDepth c d p q) N) :
    IntRatio.Lt ((IntRatio.value (Int.ofNat c) d).mul (IntRatio.ofInt (Int.ofNat (pow4 N.succ))).inv)
      (IntRatio.value (Int.ofNat p) q) :=
  let t := pow4 N.succ
  have one : Eq (IntRatio.ofInt (Int.ofNat t)).inv (IntRatio.value Int.one t) := Eq.refl
  have scaled : Eq ((IntRatio.value (Int.ofNat c) d).mul (IntRatio.value Int.one t))
      (IntRatio.value (Int.ofNat c) (d.mul t)) :=
    (IntRatio.value_mul (Int.ofNat c) Int.one d t).trans
      (congrArg (fun x => IntRatio.value x (d.mul t)) (Int.mul_one (Int.ofNat c)))
  have cross : Nat.lt (c.mul q) (p.mul (d.mul t)) :=
    Eq.subst (Nat.lt (c.mul q)) ((congrArg (fun n : Nat => n.mul t) (Nat.mul_comm d p)).trans
      (Nat.mul_assoc p d t)) (quarterDepth_integer_sound c d p q N hd hp h)
  Eq.subst (fun x => IntRatio.Lt x (IntRatio.value (Int.ofNat p) q))
    ((congrArg (IntRatio.mul (IntRatio.value (Int.ofNat c) d)) one).trans scaled).symm
    (value_lt_of_cross (mul_pos hd (pow4_pos N.succ)) hq cross)

end Omega.Arithmetic
