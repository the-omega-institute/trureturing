/- GID: D5/S3/FiniteGroups/GordonCarry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GordonCarry
   mirror-E: none
   anchors: []
   utility: none
   digest: Mixed-radix predecessor and reversible odd-radix carry transform. -/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Gordon’s bounded digit box and predecessor carry transform. -/

namespace D5.S3.FiniteGroups.Gordon

/-- A nontrivial odd modulus. Repetition of moduli is allowed. -/
structure OddRadix where
  val : ℕ
  one_lt : 1 < val
  odd : Odd val

instance (d : OddRadix) : NeZero d.val := ⟨by have := d.one_lt; omega⟩

/-- Least significant coordinate first; this is not a cyclic group encoding. -/
@[reducible] def Box : List OddRadix → Type
  | [] => PUnit
  | d :: ds => ZMod d.val × Box ds

instance boxAddCommGroup : (ds : List OddRadix) → AddCommGroup (Box ds)
  | [] => inferInstanceAs (AddCommGroup PUnit)
  | d :: ds => letI := boxAddCommGroup ds
               inferInstanceAs (AddCommGroup (ZMod d.val × Box ds))

instance boxFintype : (ds : List OddRadix) → Fintype (Box ds)
  | [] => inferInstanceAs (Fintype PUnit)
  | d :: ds => letI := boxFintype ds
               inferInstanceAs (Fintype (ZMod d.val × Box ds))

instance boxDecidableEq : (ds : List OddRadix) → DecidableEq (Box ds)
  | [] => inferInstanceAs (DecidableEq PUnit)
  | d :: ds => letI := boxDecidableEq ds
               inferInstanceAs (DecidableEq (ZMod d.val × Box ds))

/-- Number of bounded digit tuples; the empty product is one. -/
def volume : List OddRadix → ℕ
  | [] => 1
  | d :: ds => d.val * volume ds

theorem volume_pos (ds : List OddRadix) : 0 < volume ds := by
  induction ds with
  | nil => exact Nat.zero_lt_one
  | cons d ds ih => exact Nat.mul_pos (NeZero.pos d.val) ih

instance (ds : List OddRadix) : NeZero (volume ds) := ⟨(volume_pos ds).ne'⟩

/-- The tuple of ones, including the empty tuple. -/
def ones : (ds : List OddRadix) → Box ds
  | [] => PUnit.unit
  | _ :: ds => (1, ones ds)

/-- Bounded mixed-radix subtraction by one, with a complete borrow at zero. -/
def pred : (ds : List OddRadix) → Box ds → Box ds
  | [], _ => PUnit.unit
  | _ :: ds, (x, y) => if x = 0 then (-1, pred ds y) else (x - 1, y)

/-- The odd-coordinate directed difference at an even step. -/
def carry (ds : List OddRadix) (x : Box ds) : Box ds := -x - pred ds x - ones ds

/-- Ordinary bounded mixed-radix rank. -/
def rank : (ds : List OddRadix) → Box ds → ℕ
  | [], _ => 0
  | d :: ds, (x, y) => x.val + d.val * rank ds y

/-- Successive Euclidean division, starting at the least significant digit. -/
def digits : (ds : List OddRadix) → ℕ → Box ds
  | [], _ => PUnit.unit
  | d :: ds, n => ((n : ZMod d.val), digits ds (n / d.val))

private theorem rank_lt (ds : List OddRadix) (x : Box ds) : rank ds x < volume ds := by
  induction ds with
  | nil => exact Nat.zero_lt_one
  | cons d ds ih =>
    rcases x with ⟨x, y⟩
    have hx := x.val_lt
    have hy := ih y
    dsimp [rank, volume]
    nlinarith

private theorem rank_digits (ds : List OddRadix) (n : ℕ) (hn : n < volume ds) :
    rank ds (digits ds n) = n := by
  induction ds generalizing n with
  | nil =>
    change n < 1 at hn
    have : n = 0 := by omega
    simpa [rank] using this.symm
  | cons d ds ih =>
    have hq : n / d.val < volume ds := (Nat.div_lt_iff_lt_mul (NeZero.pos d.val)).2
      (by simpa [volume, Nat.mul_comm] using hn)
    simpa [digits, rank, ih _ hq, ZMod.val_natCast] using Nat.mod_add_div n d.val

private theorem digits_rank (ds : List OddRadix) (x : Box ds) :
    digits ds (rank ds x) = x := by
  induction ds with
  | nil => exact Subsingleton.elim _ _
  | cons d ds ih =>
    rcases x with ⟨x, y⟩
    have hx := x.val_lt
    have hdiv : (x.val + d.val * rank ds y) / d.val = rank ds y := by
      rw [Nat.add_mul_div_left _ _ (NeZero.pos d.val), Nat.div_eq_of_lt hx, zero_add]
    simp [digits, rank, hdiv, ZMod.natCast_zmod_val, ih]

/-- Rank is a set equivalence, with the second factor supplying the low digit. -/
def rankEquiv (ds : List OddRadix) : Box ds ≃ Fin (volume ds) where
  toFun x := ⟨rank ds x, rank_lt ds x⟩
  invFun n := digits ds n.val
  left_inv := digits_rank ds
  right_inv n := Fin.ext (rank_digits ds n.val n.isLt)

private theorem rank_zero (ds : List OddRadix) : rank ds 0 = 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [rank, ih]

private theorem radix_two_injective (d : OddRadix) :
    Function.Injective (fun x : ZMod d.val => x + x) := by
  have h : IsUnit (2 : ZMod d.val) := (ZMod.isUnit_iff_coprime 2 d.val).2
    (Nat.coprime_two_left.mpr d.odd)
  intro x y hxy
  exact h.mul_left_injective (by simpa [mul_two] using hxy)

theorem box_two_injective (ds : List OddRadix) :
    Function.Injective (fun x : Box ds => x + x) := by
  induction ds with
  | nil => exact fun _ _ _ => Subsingleton.elim _ _
  | cons d ds ih =>
    intro x y h
    exact Prod.ext (radix_two_injective d (congrArg Prod.fst h))
      (ih (congrArg Prod.snd h))

private theorem carry_cons_zero (d : OddRadix) (ds : List OddRadix) (y : Box ds) :
    carry (d :: ds) (0, y) = (0, carry ds y) := by
  change -(0, y) - (if (0 : ZMod d.val) = 0 then (-1, pred ds y) else (0 - 1, y)) - (1, ones ds) = (0, -y - pred ds y - ones ds)
  simp

private theorem carry_cons_ne (d : OddRadix) (ds : List OddRadix)
    (x : ZMod d.val) (y : Box ds) (hx : x ≠ 0) :
    carry (d :: ds) (x, y) = (-x - x, -y - y - ones ds) := by
  change -(x, y) - (if x = 0 then (-1, pred ds y) else (x - 1, y)) - (1, ones ds) = _
  rw [if_neg hx]
  apply Prod.ext
  · change -x - (x - 1) - 1 = -x - x
    ring
  · rfl

/-- The first nonzero input digit is the first nonzero carry output digit. -/
theorem carry_injective (ds : List OddRadix) : Function.Injective (carry ds) := by
  induction ds with
  | nil => exact fun _ _ _ => Subsingleton.elim _ _
  | cons d ds ih =>
    rintro ⟨x, u⟩ ⟨y, v⟩ h
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · subst x; subst y
      rw [carry_cons_zero, carry_cons_zero] at h
      exact Prod.ext rfl (ih (congrArg Prod.snd h))
    · subst x
      rw [carry_cons_zero, carry_cons_ne d ds y v hy] at h
      have hh : y + y = (0 : ZMod d.val) := by
        have := congrArg Prod.fst h
        dsimp at this
        linear_combination this
      exact (hy (radix_two_injective d (by simpa using hh))).elim
    · subst y
      rw [carry_cons_ne d ds x u hx, carry_cons_zero] at h
      have hh : x + x = (0 : ZMod d.val) := by
        have := congrArg Prod.fst h
        dsimp at this
        linear_combination -this
      exact (hx (radix_two_injective d (by simpa using hh))).elim
    · rw [carry_cons_ne d ds x u hx, carry_cons_ne d ds y v hy] at h
      have hxy : x + x = y + y := by
        have := congrArg Prod.fst h
        dsimp at this
        linear_combination -this
      have huv : u + u = v + v := by
        have := congrArg Prod.snd h
        dsimp at this
        apply neg_injective
        calc
          -(u + u) = (-u - u - ones ds) + ones ds := by abel
          _ = (-v - v - ones ds) + ones ds := congrArg (· + ones ds) this
          _ = -(v + v) := by abel
      exact Prod.ext (radix_two_injective d hxy) (box_two_injective ds huv)

private theorem carry_zero (ds : List OddRadix) : carry ds 0 = 0 := by
  induction ds with
  | nil => exact Subsingleton.elim _ _
  | cons d ds ih =>
    change carry (d :: ds) (0, 0) = (0, 0)
    rw [carry_cons_zero, ih]

/-- Complete borrow through zero is exactly the zero fiber, also for no radices. -/
theorem carry_eq_zero (ds : List OddRadix) (x : Box ds) : carry ds x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact carry_injective ds (h.trans (carry_zero ds).symm)
  · rintro rfl; exact carry_zero ds

private theorem pred_rank_step (ds : List OddRadix) (x : Box ds) :
    rank ds (pred ds x) + 1 = if x = 0 then volume ds else rank ds x := by
  induction ds with
  | nil => simp [rank, volume]
  | cons d ds ih =>
    rcases x with ⟨x, y⟩
    have hd := d.one_lt
    have hval : (1 : ZMod d.val).val = 1 := ZMod.val_one'' (by omega)
    by_cases hx : x = 0
    · subst x
      have hv : (-1 : ZMod d.val).val = d.val - 1 := by
        have hone : (1 : ZMod d.val) ≠ 0 := by
          intro he
          have hv := congrArg ZMod.val he
          simp only [hval, ZMod.val_zero] at hv
          omega
        rw [ZMod.neg_val, ite_eq_right hone, hval]
      by_cases hy : y = 0
      · subst y
        have hy' := ih (0 : Box ds)
        simp only [ite_true] at hy'
        have hh := congrArg (fun z => d.val * z) hy'
        have hd1 := Nat.sub_add_cancel (by omega : 1 ≤ d.val)
        simp [pred, rank, volume, hv]
        nlinarith
      · have hy' := ih y
        simp only [if_neg hy] at hy'
        have hh := congrArg (fun z => d.val * z) hy'
        have hd1 := Nat.sub_add_cancel (by omega : 1 ≤ d.val)
        simp [pred, rank, hv, hy]
        nlinarith
    · have hpos := ZMod.val_pos.mpr hx
      have hv : (x - 1).val + 1 = x.val := by
        rw [ZMod.val_sub (by omega), hval]
        omega
      simp [pred, hx, rank, show (x, y) ≠ (0 : Box (d :: ds)) from
        fun h => hx (congrArg Prod.fst h)]
      omega

private theorem complement_val (d : OddRadix) (x : ZMod d.val) :
    x.val + (-x - 1).val + 1 = d.val := by
  have hd := d.one_lt
  have hx := x.val_lt
  have he : ((d.val - (x.val + 1) : ℕ) : ZMod d.val) = -x - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp only [ZMod.natCast_self, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    ring
  rw [← he, ZMod.val_cast_of_lt (by omega)]
  omega

/-- Coordinatewise complement reverses the entire mixed-radix interval. -/
theorem rank_complement (ds : List OddRadix) (x : Box ds) :
    rank ds x + rank ds (-x - ones ds) + 1 = volume ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rcases x with ⟨x, y⟩
    have hx := complement_val d x
    have hy := ih y
    have hh := congrArg (fun z => d.val * z) hy
    dsimp [rank, ones, volume]
    nlinarith

/-- Reduction to bounded digits, including modulus one for the empty product. -/
def residue (ds : List OddRadix) (n : ℕ) : Box ds :=
  (rankEquiv ds).symm ⟨n % volume ds, Nat.mod_lt _ (volume_pos ds)⟩

theorem rank_residue (ds : List OddRadix) (n : ℕ) :
    rank ds (residue ds n) = n % volume ds :=
  congrArg Fin.val ((rankEquiv ds).apply_symm_apply _)

theorem residue_zero (ds : List OddRadix) : residue ds 0 = 0 := by
  apply (rankEquiv ds).injective
  apply Fin.ext
  change rank ds (residue ds 0) = rank ds 0
  rw [rank_residue, rank_zero, Nat.zero_mod]

/-- A predecessor in the digit box agrees with ordinary subtraction at positive indices. -/
theorem pred_residue (ds : List OddRadix) (n : ℕ) (hn : 0 < n) :
    pred ds (residue ds n) = residue ds (n - 1) := by
  apply (rankEquiv ds).injective
  apply Fin.ext
  change rank ds (pred ds (residue ds n)) = rank ds (residue ds (n - 1))
  rw [rank_residue]
  have hs := pred_rank_step ds (residue ds n)
  have hr := rank_residue ds n
  have hp := rank_lt ds (pred ds (residue ds n))
  have hm : ((rank ds (pred ds (residue ds n)) + 1 : ℕ) : ZMod (volume ds)) =
      (n : ZMod (volume ds)) := by
    by_cases h : residue ds n = 0
    · rw [ite_eq_left h] at hs
      rw [hs, ZMod.natCast_self]
      have hnmod : n % volume ds = 0 := by rw [← hr, h, rank_zero]
      exact ((ZMod.natCast_eq_zero_iff n (volume ds)).2
        (Nat.dvd_of_mod_eq_zero hnmod)).symm
    · rw [ite_eq_right h, hr] at hs
      rw [hs, ZMod.natCast_mod]
  have hn' : ((n - 1 : ℕ) : ZMod (volume ds)) + 1 = (n : ZMod (volume ds)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun z : ℕ => (z : ZMod (volume ds))) (Nat.sub_add_cancel hn)
  have hm' : (rank ds (pred ds (residue ds n)) : ZMod (volume ds)) =
      ((n - 1 : ℕ) : ZMod (volume ds)) := by
    rw [Nat.cast_add, Nat.cast_one] at hm
    exact add_right_cancel (hm.trans hn'.symm)
  have hm'' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hm'
  rwa [Nat.mod_eq_of_lt hp] at hm''

end D5.S3.FiniteGroups.Gordon

