/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Arithmetic.Euclidean.Division

/-!
Omega original.

Least prime divisors and Euclid's product-plus-one argument in strict arithmetic.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

/-- A prime is greater than one and has only one and itself as divisors. -/
def IsPrime (p : Nat) : Prop :=
  And (Nat.lt Nat.one p) (∀ d, Dvd d p → Or (Eq d Nat.one) (Eq d p))

private theorem pos_of_one_lt {n : Nat} (h : Nat.lt Nat.one n) : Nat.lt Nat.zero n :=
  lt_of_le_of_lt (Nat.zero_le Nat.one) h

private theorem prime_of_no_proper_factor {p : Nat} (hp : Nat.lt Nat.one p)
    (absent : ∀ d, Nat.lt Nat.one d → Nat.lt d p → Not (Dvd d p)) : IsPrime p :=
  have positiveP := pos_of_one_lt hp
  And.intro hp (fun d hd =>
    (le_or_lt d Nat.one).elim
      (fun hle =>
        have nonzeroD : Not (Eq d Nat.zero) := fun hz => hd.elim (fun k hk =>
          have zeroProduct := (congrArg (fun a : Nat => a.mul k) hz).trans (Nat.zero_mul k)
          ne_of_lt positiveP (hk.trans zeroProduct).symm)
        Or.inl (Nat.le_antisymm hle (pos_of_ne_zero nonzeroD)))
      (fun hlarge =>
        (le_or_lt p d).elim
          (fun hle => Or.inr (Nat.le_antisymm (le_of_dvd_of_pos hd positiveP) hle))
          (fun hlt => False.elim (absent d hlarge hlt hd))))

private def IsLeastProperFactor (n bound d : Nat) : Prop :=
  And (Nat.lt Nat.one d) (And (Nat.lt d bound)
    (And (Dvd d n) (∀ e, Nat.lt Nat.one e → Dvd e n → Nat.le d e)))

private def NoProperFactor (n bound : Nat) : Prop :=
  ∀ d, Nat.lt Nat.one d → Nat.lt d bound → Not (Dvd d n)

private theorem noProperFactorBelowTwo (n : Nat) : NoProperFactor n Nat.one.succ :=
  fun d hlarge hbelow _ => lt_irrefl d (lt_of_lt_of_le hbelow hlarge)

private theorem extendFactorExclusion {n bound : Nat}
    (exclude : NoProperFactor n bound)
    (excludeBound : Nat.lt Nat.one bound → Not (Dvd bound n)) :
    NoProperFactor n bound.succ :=
  fun d hlarge hbelow hdiv =>
    (le_or_lt bound d).elim
      (fun hle =>
        have heq := Nat.le_antisymm (Nat.le_of_succ_le_succ hbelow) hle
        excludeBound (Eq.subst (Nat.lt Nat.one) heq hlarge)
          (Eq.subst (fun a => Dvd a n) heq hdiv))
      (fun hlt => exclude d hlarge hlt hdiv)

/-- Scan the candidates from two up to, but excluding, the given number of steps plus two. -/
private def searchProperFactor (n steps : Nat) : Bool :=
  Nat.rec Bool.false (fun step found =>
    Bool.rec (natEq (divMod n step.succ.succ).remainder Nat.zero) Bool.true found) steps

private theorem searchProperFactor_cases (n steps : Nat) (P : Bool → Prop)
    (yes : Exists (IsLeastProperFactor n steps.succ.succ) → P Bool.true)
    (no : NoProperFactor n steps.succ.succ → P Bool.false) :
    P (searchProperFactor n steps) :=
  Nat.rec (motive := fun steps => ∀ (P : Bool → Prop),
      (Exists (IsLeastProperFactor n steps.succ.succ) → P Bool.true) →
      (NoProperFactor n steps.succ.succ → P Bool.false) → P (searchProperFactor n steps))
    (fun _ _ no => no (noProperFactorBelowTwo n))
    (fun step ih P yes no =>
      let d := step.succ.succ
      let remainder := (divMod n d).remainder
      ih (fun found => P (Bool.rec (motive := fun _ => Bool)
        (natEq remainder Nat.zero) Bool.true found))
        (fun found => found.elim (fun p hp => yes (Exists.intro p
          (And.intro hp.left (And.intro (Nat.le.step hp.right.left) hp.right.right)))))
        (fun exclude =>
          let spec := dvd_iff_remainder_zero n d (Nat.zero_le step.succ)
          natEq_cases remainder Nat.zero P
            (fun eq => yes (Exists.intro d
              (And.intro (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le step)))
                (And.intro (Nat.le.refl d.succ) (And.intro (spec.mpr eq)
                  (fun e he hdiv => (le_or_lt d e).elim (fun h => h)
                    (fun h => False.elim (exclude e he h hdiv))))))))
            (fun ne => no (extendFactorExclusion exclude (fun _ hdiv => ne (spec.mp hdiv))))))
    steps P yes no

private theorem properFactorCases (n : Nat) (hn : Nat.lt Nat.one n) :
    Or (Exists (IsLeastProperFactor n n)) (NoProperFactor n n) :=
  Nat.rec (motive := fun n => Nat.lt Nat.one n →
      Or (Exists (IsLeastProperFactor n n)) (NoProperFactor n n))
    (fun h => False.elim h)
    (fun k _ => Nat.rec (motive := fun k => Nat.lt Nat.one k.succ →
        Or (Exists (IsLeastProperFactor k.succ k.succ)) (NoProperFactor k.succ k.succ))
      (fun h => False.elim h)
      (fun k _ _ => searchProperFactor_cases k.succ.succ k (fun _ => _) Or.inl Or.inr) k) n hn

/-- Every natural number greater than one has a prime divisor that is least among
all its divisors greater than one. -/
theorem exists_min_prime_dvd_of_one_lt (n : Nat) (hn : Nat.lt Nat.one n) :
    Exists (fun p => And (IsPrime p) (And (Dvd p n)
      (∀ d, Nat.lt Nat.one d → Dvd d n → Nat.le p d))) :=
  strongInduction (P := fun n => Nat.lt Nat.one n →
    Exists (fun p => And (IsPrime p) (And (Dvd p n)
      (∀ d, Nat.lt Nat.one d → Dvd d n → Nat.le p d))))
    (fun n ih hn => (properFactorCases n hn).elim
      (fun found => found.elim (fun d hd =>
        (ih d hd.right.left hd.left).elim (fun p hp =>
          Exists.intro p (And.intro hp.left (And.intro (dvd_trans hp.right.left hd.right.right.left)
            (fun e he hediv => Nat.le_trans (le_of_dvd_of_pos hp.right.left (pos_of_one_lt hd.left))
              (hd.right.right.right e he hediv)))))))
      (fun exclude => Exists.intro n
        (And.intro (prime_of_no_proper_factor hn exclude) (And.intro (dvd_refl n)
          (fun d hlarge hd => (le_or_lt n d).elim (fun h => h)
            (fun h => False.elim (exclude d hlarge h hd))))))) n hn

/-- Zero is included, with two as its least divisor greater than one. -/
theorem exists_min_prime_dvd (n : Nat) (hn : Not (Eq n Nat.one)) :
    Exists (fun p => And (IsPrime p) (And (Dvd p n)
      (∀ d, Nat.lt Nat.one d → Dvd d n → Nat.le p d))) :=
  Nat.rec (motive := fun n => Not (Eq n Nat.one) →
    Exists (fun p => And (IsPrime p) (And (Dvd p n)
      (∀ d, Nat.lt Nat.one d → Dvd d n → Nat.le p d))))
    (fun _ =>
      have htwo : Nat.lt Nat.one Nat.one.succ := Nat.le.refl Nat.one.succ
      have primeTwo := prime_of_no_proper_factor htwo (noProperFactorBelowTwo Nat.one.succ)
      Exists.intro Nat.one.succ
        (And.intro primeTwo (And.intro (dvd_zero Nat.one.succ) (fun _ hlarge _ => hlarge))))
    (fun n _ hn => exists_min_prime_dvd_of_one_lt n.succ
      (pos_of_ne_zero (fun hz => hn (congrArg Nat.succ hz)))) n hn

theorem exists_prime_dvd (n : Nat) (hn : Not (Eq n Nat.one)) :
    Exists (fun p => And (IsPrime p) (Dvd p n)) :=
  (exists_min_prime_dvd n hn).elim (fun p hp => Exists.intro p (And.intro hp.left hp.right.left))

namespace NatList

theorem dvd_prod_of_mem {p : Nat} {s : NatList} (hm : Mem p s) : Dvd p s.prod :=
  NatList.rec (motive := fun s => Mem p s → Dvd p s.prod) (fun h => False.elim h)
    (fun head tail ih h => h.elim
      (fun he => Eq.subst (fun d => Dvd d (head.mul tail.prod)) he.symm
        (Exists.intro tail.prod Eq.refl))
      (fun ht => dvd_trans (ih ht) (Exists.intro head (Nat.mul_comm head tail.prod)))) s hm

theorem prod_pos {s : NatList} (h : ∀ p, Mem p s → Nat.lt Nat.zero p) :
    Nat.lt Nat.zero s.prod :=
  NatList.rec (motive := fun s => (∀ p, Mem p s → Nat.lt Nat.zero p) → Nat.lt Nat.zero s.prod)
    (fun _ => Nat.le.refl Nat.one)
    (fun head _ ih h => mul_pos (h head (Or.inl Eq.refl))
      (ih (fun p hm => h p (Or.inr hm)))) s h

/-- Every list member greater than one leaves remainder one, even for a zero product. -/
theorem remainder_succ_prod_eq_one (s : NatList) {p : Nat}
    (hp : Nat.lt Nat.one p) (hm : Mem p s) : Eq (divMod s.prod.succ p).remainder Nat.one :=
  have spec := divMod_spec s.prod.succ p (pos_of_one_lt hp)
  (dvd_prod_of_mem hm).elim (fun k hk =>
    divMod_remainder_unique (q' := k) (spec.left.symm.trans (congrArg Nat.succ hk)) spec.right hp)

/-- In particular, no member greater than one divides the successor of the product. -/
theorem not_dvd_succ_prod (s : NatList) {p : Nat}
    (hp : Nat.lt Nat.one p) (hm : Mem p s) : Not (Dvd p s.prod.succ) :=
  fun h =>
    have hzero := (dvd_iff_remainder_zero s.prod.succ p (pos_of_one_lt hp)).mp h
    have hone := s.remainder_succ_prod_eq_one hp hm
    Nat.succ_ne_zero Nat.zero (hone.symm.trans hzero)

end NatList

/-- The successor of a positive list product has a prime divisor outside the list. -/
theorem prime_escape (s : NatList) (hs : Nat.lt Nat.zero s.prod) :
    Exists (fun p => And (IsPrime p) (And (Dvd p s.prod.succ) (Not (NatList.Mem p s)))) :=
  have hlarge : Nat.lt Nat.one s.prod.succ := hs
  (exists_prime_dvd s.prod.succ (fun h => ne_of_lt hlarge h.symm)).elim (fun p hp =>
    Exists.intro p (And.intro hp.left (And.intro hp.right
      (fun hm => s.not_dvd_succ_prod hp.left.left hm hp.right))))

theorem prime_escape_iff_prod_pos (s : NatList) :
    Iff (Exists (fun p => And (IsPrime p) (And (Dvd p s.prod.succ) (Not (NatList.Mem p s)))))
      (Nat.lt Nat.zero s.prod) :=
  Iff.intro
    (fun escape => natEq_cases s.prod Nat.zero (fun _ => Nat.lt Nat.zero s.prod)
      (fun hz => escape.elim (fun p hp =>
        have hdiv : Dvd p Nat.one := Eq.subst (Dvd p) (congrArg Nat.succ hz) hp.right.left
        False.elim (ne_of_lt hp.left.left (dvd_one hdiv).symm)))
      (fun hz => pos_of_ne_zero hz))
    (prime_escape s)

end Omega.Arithmetic
