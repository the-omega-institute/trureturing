/- GID: D5/S3/Combinatorics/Circle/MersenneWeight
   purpose: arbitrary-exponent Mersenne divisibility rigidity
   dependency: ZeroSumSubsets.cyclic_binary_normal_form
   status: source preparation only; no kernel admission is claimed here. -/
module
public import D5.S3.Combinatorics.Circle.ZeroSumSubsets
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersenneWeight

open scoped BigOperators
open D5.S3.Combinatorics.Circle.ZeroSumSubsets

private def residueList (r : ℕ) (es : List ℕ) : List ℕ :=
  es.map (fun e => e % r)

/-- The coefficient obtained by pushing an exponent list to `Fin r`. -/
private def residueCoeff (r : ℕ) : List ℕ → Fin r → ℕ
  | [], _ => 0
  | e :: es, i => (if e % r = i.val then 1 else 0) + residueCoeff r es i

private theorem residueCoeff_eq_count (r : ℕ) (es : List ℕ) (i : Fin r) :
    residueCoeff r es i = (residueList r es).count i.val := by
  induction es with
  | nil => simp [residueCoeff, residueList]
  | cons e es ih =>
      simp [residueCoeff, residueList, ih, beq_iff_eq]

private theorem delta_sum {r : ℕ} (hr : 0 < r) (e : ℕ) :
    ∑ i : Fin r, (if e % r = i.val then 1 else 0) = 1 := by
  classical
  let j : Fin r := ⟨e % r, Nat.mod_lt e hr⟩
  have hpoint : ∀ i : Fin r,
      (if e % r = i.val then 1 else 0) = if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp
    · have hne : e % r ≠ i.val := by
        intro hi
        apply hij
        apply Fin.ext
        simpa [j] using hi.symm
      simp [hij, hne]
  calc
    ∑ i : Fin r, (if e % r = i.val then 1 else 0) =
        ∑ i : Fin r, (if i = j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = 1 := by simp

private theorem delta_weighted {r : ℕ} (hr : 0 < r) (e : ℕ) :
    ∑ i : Fin r, (if e % r = i.val then 1 else 0) * 2 ^ i.val =
      2 ^ (e % r) := by
  classical
  let j : Fin r := ⟨e % r, Nat.mod_lt e hr⟩
  have hpoint : ∀ i : Fin r,
      (if e % r = i.val then 1 else 0) * 2 ^ i.val =
        if i = j then 2 ^ i.val else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp
    · have hne : e % r ≠ i.val := by
        intro hi
        apply hij
        apply Fin.ext
        simpa [j] using hi.symm
      simp [hij, hne]
  calc
    ∑ i : Fin r, (if e % r = i.val then 1 else 0) * 2 ^ i.val =
        ∑ i : Fin r, (if i = j then 2 ^ i.val else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = 2 ^ (e % r) := by simp [j]

private theorem residueCoeff_sum {r : ℕ} (hr : 0 < r) (es : List ℕ) :
    (∑ i : Fin r, residueCoeff r es i) = es.length := by
  induction es with
  | nil => simp [residueCoeff]
  | cons e es ih =>
      calc
        ∑ i : Fin r, residueCoeff r (e :: es) i =
            (∑ i : Fin r, (if e % r = i.val then 1 else 0)) +
              ∑ i : Fin r, residueCoeff r es i := by
                simp only [residueCoeff, Finset.sum_add_distrib]
        _ = 1 + es.length := by rw [delta_sum hr e, ih]
        _ = (e :: es).length := by simp

private theorem residueCoeff_weight {r : ℕ} (hr : 0 < r) (es : List ℕ) :
    (∑ i : Fin r, residueCoeff r es i * 2 ^ i.val) =
      (residueList r es).map (fun e => 2 ^ e) |>.sum := by
  induction es with
  | nil => simp [residueCoeff, residueList]
  | cons e es ih =>
      calc
        ∑ i : Fin r, residueCoeff r (e :: es) i * 2 ^ i.val =
            (∑ i : Fin r, (if e % r = i.val then 1 else 0) * 2 ^ i.val) +
              ∑ i : Fin r, residueCoeff r es i * 2 ^ i.val := by
                simp only [residueCoeff, Nat.add_mul, Finset.sum_add_distrib]
        _ = 2 ^ (e % r) +
              ((residueList r es).map (fun e => 2 ^ e)).sum := by
                rw [delta_weighted hr e, ih]
        _ = (residueList r (e :: es)).map (fun e => 2 ^ e) |>.sum := by
                simp [residueList]

private theorem residueCoeff_ne_zero {r : ℕ} (hr : 0 < r) {es : List ℕ}
    (hes : es ≠ []) : residueCoeff r es ≠ 0 := by
  intro hzero
  have hsum := residueCoeff_sum hr es
  have hlen : es.length = 0 := by
    calc
      es.length = ∑ i : Fin r, residueCoeff r es i := hsum.symm
      _ = 0 := by simp [hzero]
  have hpos : 0 < es.length := List.length_pos.mpr hes
  omega

private theorem two_pow_residue_modEq {r : ℕ} (hr : 2 ≤ r) (e : ℕ) :
    2 ^ e ≡ 2 ^ (e % r) [MOD 2 ^ r - 1] := by
  have hM : 1 < 2 ^ r - 1 := by
    have hpow : 4 ≤ 2 ^ r := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr)
    omega
  have hbase : 2 ^ r ≡ 1 [MOD 2 ^ r - 1] := by
    change (2 ^ r) % (2 ^ r - 1) = 1 % (2 ^ r - 1)
    have heq : 2 ^ r = (2 ^ r - 1) + 1 := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hM]
  have hpow := hbase.pow (e / r)
  have hmul := hpow.mul (Nat.ModEq.refl (2 ^ (e % r)))
  have hmul' : 2 ^ (r * (e / r)) * 2 ^ (e % r) ≡
      1 * 2 ^ (e % r) [MOD 2 ^ r - 1] := by
    simpa only [pow_mul, one_pow] using hmul
  have heq : e = r * (e / r) + e % r := by omega
  rw [← pow_add, heq] at hmul'
  simpa using hmul'

private theorem residue_sum_modEq (r : ℕ) (hr : 2 ≤ r) (es : List ℕ) :
    (es.map (fun e => 2 ^ e)).sum ≡
      (residueList r es).map (fun e => 2 ^ e) |>.sum [MOD 2 ^ r - 1] := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simpa [residueList] using (two_pow_residue_modEq hr e).add ih

private theorem residue_coeff_weight_dvd {r : ℕ} (hr : 2 ≤ r) (es : List ℕ)
    (hdiv : 2 ^ r - 1 ∣ (es.map (fun e => 2 ^ e)).sum) :
    2 ^ r - 1 ∣ ∑ i : Fin r, residueCoeff r es i * 2 ^ i.val := by
  have hzero : (es.map (fun e => 2 ^ e)).sum ≡ 0 [MOD 2 ^ r - 1] :=
    Nat.modEq_zero_iff_dvd.mpr hdiv
  have hres : (residueList r es).map (fun e => 2 ^ e) |>.sum ≡
      0 [MOD 2 ^ r - 1] :=
    (residue_sum_modEq r hr es).symm.trans hzero
  have hresdiv : 2 ^ r - 1 ∣
      (residueList r es).map (fun e => 2 ^ e) |>.sum :=
    Nat.modEq_zero_iff_dvd.mp hres
  rw [residueCoeff_weight (by omega : 0 < r) es]
  exact hresdiv

private theorem mask_as_geom (A : Finset (Fin r)) :
    (∑ i ∈ A, 2 ^ i.val) = ∑ j ∈ A.image Fin.val, 2 ^ j := by
  rw [Finset.sum_image]
  · rfl
  · intro p hp q hq he
    exact Fin.ext he

private theorem mask_pos {r : ℕ} {A : Finset (Fin r)} (hA : A.Nonempty) :
    0 < ∑ i ∈ A, 2 ^ i.val := by
  obtain ⟨i, hi⟩ := hA
  exact lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) i.val)
    (Finset.single_le_sum (f := fun p : Fin r => 2 ^ p.val)
      (fun _ _ => Nat.zero_le _) hi)

private theorem mask_bound (A : Finset (Fin r)) :
    ∑ i ∈ A, 2 ^ i.val ≤ 2 ^ r - 1 := by
  have hlt : (∑ i ∈ A, 2 ^ i.val) < 2 ^ r := by
    rw [mask_as_geom A]
    apply Nat.geomSum_lt (by decide)
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact i.isLt
  omega

private theorem full_geom (r : ℕ) :
    (∑ j ∈ Finset.range r, 2 ^ j) = 2 ^ r - 1 := by
  simpa using (Nat.geomSum_eq (by decide : 2 ≤ (2 : ℕ)) r)

private theorem count_range_one {r x : ℕ} (hx : x < r) :
    (List.range r).count x = 1 := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hxr : x = r
      · subst x
        simp
      · have hx' : x < r := by omega
        simp [List.range_succ, hxr, ih hx']

private theorem count_range_zero {r x : ℕ} (hx : r ≤ x) :
    (List.range r).count x = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hle : r ≤ x := by omega
      have hxr : x ≠ r := by omega
      simp [List.range_succ, hxr, ih hle]

private theorem residue_perm_of_counts {r : ℕ} (hr : 0 < r) (es : List ℕ)
    (hcount : ∀ i : Fin r, (residueList r es).count i.val = 1) :
    (residueList r es).Perm (List.range r) := by
  apply List.perm_iff_count.mpr
  intro x
  by_cases hx : x < r
  · let i : Fin r := ⟨x, hx⟩
    simpa [i] using (hcount i).trans (count_range_one hx).symm
  · have hnot : x ∉ residueList r es := by
      intro hmem
      obtain ⟨e, he, hev⟩ := List.mem_map.mp hmem
      have hlt : e % r < r := Nat.mod_lt e hr
      omega
    have hleft : (residueList r es).count x = 0 :=
      List.count_eq_zero_of_not_mem hnot
    exact hleft.trans (count_range_zero (Nat.le_of_not_gt hx)).symm

/--
For every nonempty exponent list, divisibility by `2^r - 1` forces at least `r`
terms.  Equality is exactly the case in which the residues modulo `r` are a
permutation of `0, ..., r - 1`; exponents themselves are unrestricted and may
repeat away from their residue classes.

The only cyclic carry input is the public `cyclic_binary_normal_form`.  The
coefficient pushforward and the congruence from arbitrary exponents are proved
locally above, so this theorem does not assume a carry/transitivity premise.
-/
theorem mersenne_weight_rigidity (r : ℕ) (hr : 2 ≤ r) (es : List ℕ) (hes : es ≠ [])
    (hdiv : 2 ^ r - 1 ∣ (es.map (fun e => 2 ^ e)).sum) :
    r ≤ es.length ∧
      (es.length = r ↔
        (es.map (fun e => e % r)).Perm (List.range r)) := by
  have hrpos : 0 < r := by omega
  let n : Fin r → ℕ := residueCoeff r es
  have hnzero : n ≠ 0 := by
    intro hn
    have hsum := residueCoeff_sum hrpos es
    have hlen : es.length = 0 := by
      calc
        es.length = ∑ i : Fin r, n i := by simpa [n] using hsum.symm
        _ = 0 := by simp [hn]
    have hpos : 0 < es.length := List.length_pos.mpr hes
    omega
  obtain ⟨z, hz, hzuniq⟩ :=
    cyclic_binary_normal_form r hrpos 0 n hnzero
  rcases z with ⟨A, m⟩
  rcases hz with ⟨hA, hcarry, hlen, hweight, hcharge, hquotient, hunit⟩
  have hcoeffdiv : 2 ^ r - 1 ∣ ∑ i : Fin r, n i * 2 ^ i.val := by
    simpa [n] using residue_coeff_weight_dvd hr es hdiv
  have hmaskdiv : 2 ^ r - 1 ∣ ∑ i ∈ A, 2 ^ i.val := by
    have hmul : 2 ^ r - 1 ∣ (2 ^ r - 1) * m ⟨r - 1, by omega⟩ :=
      dvd_mul_right (2 ^ r - 1) _
    apply (Nat.dvd_add_iff_left hmul).mpr
    rw [← hweight]
    exact hcoeffdiv
  have hmask : (∑ i ∈ A, 2 ^ i.val) = 2 ^ r - 1 := by
    apply le_antisymm (mask_bound A)
    exact Nat.le_of_dvd (mask_pos hA) hmaskdiv
  have himage : A.image Fin.val = Finset.range r := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
    calc
      ∑ j ∈ A.image Fin.val, 2 ^ j = ∑ i ∈ A, 2 ^ i.val :=
        (mask_as_geom A).symm
      _ = 2 ^ r - 1 := hmask
      _ = ∑ j ∈ Finset.range r, 2 ^ j := (full_geom r).symm
  have huniv : (Finset.univ : Finset (Fin r)).image Fin.val = Finset.range r := by
    ext x
    simp
  have hfull : A = Finset.univ := by
    exact Finset.image_injective Fin.val_injective (himage.trans huniv.symm)
  have hlen' : es.length = r + ∑ i : Fin r, m i := by
    calc
      es.length = ∑ i : Fin r, n i := by simpa [n] using (residueCoeff_sum hrpos es).symm
      _ = A.card + ∑ i : Fin r, m i := hlen
      _ = r + ∑ i : Fin r, m i := by simp [hfull]
  constructor
  · omega
  · constructor
    · intro hEq
      have hm_sum : ∑ i : Fin r, m i = 0 := by omega
      have hm_zero : ∀ i : Fin r, m i = 0 := by
        intro i
        have hle : m i ≤ ∑ j : Fin r, m j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hn_one : ∀ i : Fin r, n i = 1 := by
        intro i
        have hc : (n i : ℤ) = 1 := by
          simpa [hfull, hm_zero] using hcarry i
        exact_mod_cast hc
      have hcount : ∀ i : Fin r, (residueList r es).count i.val = 1 := by
        intro i
        rw [← residueCoeff_eq_count r es i]
        exact hn_one i
      simpa [residueList] using residue_perm_of_counts hrpos es hcount
    · intro hp
      simpa [residueList] using hp.length_eq

end D5.S3.Combinatorics.Circle.MersenneWeight
