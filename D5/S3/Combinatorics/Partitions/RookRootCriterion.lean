/- GID: D5/S3/Combinatorics/Partitions/RookRootCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookRootCriterion
   mirror-E: none(waiver:geometric-singleton-root-criterion)
   anchors: []
   utility: none
   digest: The conditional floor test for roots is equivalent to geometric singleton levels. -/

import D5.S3.Combinatorics.Partitions.RookClassNative
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.Permutation

/-! The source singleton condition concerns partially occupied columns in a level,
    independently of any ordering of labels assigned to equal roots. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Partitions.RookRootCriterion

/-- At most one column ends strictly inside any level. Full columns do not
    contribute a partial top in that level. Zero columns are permitted. -/
def SingletonColumns (m : ℕ) {N : ℕ} (d : Fin N → ℕ) : Prop :=
  ∀ i j, d i % m ≠ 0 → d j % m ≠ 0 → d i / m = d j / m → i = j

/-- The actual integer roots of a padded singleton board. -/
def root (m : ℕ) {N : ℕ} (d : Fin N → ℕ) (i : Fin N) : ℤ :=
  (m : ℤ) * (i.val : ℤ) - (d i : ℤ)

/-- The source condition, imposed only on adjacent roots that are both
    nonmultiples of m. Division is Euclidean, hence floor division for m > 0. -/
def RootFloorCriterion (m : ℕ) {N : ℕ} (a : Fin N → ℤ) : Prop :=
  ∀ i j, j.val = i.val + 1 → a i % (m : ℤ) ≠ 0 → a j % (m : ℤ) ≠ 0 →
    a j / (m : ℤ) ≤ a i / (m : ℤ)

private theorem root_mod_zero_iff (m : ℕ) {N : ℕ} (d : Fin N → ℕ) (i : Fin N) :
    root m d i % (m : ℤ) = 0 ↔ d i % m = 0 := by
  rw [← Int.dvd_iff_emod_eq_zero, root,
    dvd_sub_right (dvd_mul_right (m : ℤ) (i.val : ℤ)),
    Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]

private theorem root_div_partial (m : ℕ) (hm : 0 < m) {N : ℕ}
    (d : Fin N → ℕ) (i : Fin N) (hi : d i % m ≠ 0) :
    root m d i / (m : ℤ) = (i.val : ℤ) - (d i / m : ℕ) - 1 := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hnd : ¬ (m : ℤ) ∣ (d i : ℤ) := by
    simpa only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero] using hi
  rw [root, Int.mul_sub_ediv_left _ _ hm', Int.neg_ediv, if_neg hnd,
    Int.sign_eq_one_of_pos (by exact_mod_cast hm), ← Int.natCast_div]
  omega

private def AdjacentPartial (m : ℕ) {N : ℕ} (d : Fin N → ℕ) : Prop :=
  ∀ i j, j.val = i.val + 1 → d i % m ≠ 0 → d j % m ≠ 0 → d i / m < d j / m

private theorem partial_between (m u v : ℕ) (hu : u % m ≠ 0)
    (huv : u ≤ v) (hq : u / m = v / m) : v % m ≠ 0 := by
  have eu := Nat.mod_add_div u m
  have ev := Nat.mod_add_div v m
  rw [← hq] at ev
  omega

private theorem singleton_iff_adjacent (m : ℕ) {N : ℕ} (d : Fin N → ℕ)
    (hd : Monotone d) : SingletonColumns m d ↔ AdjacentPartial m d := by
  constructor
  · intro h i j hij hi hj
    have hlt : i < j := by simpa only [Fin.lt_def] using (by omega : i.val < j.val)
    have hle : d i / m ≤ d j / m := Nat.div_le_div_right (hd hlt.le)
    have hne : d i / m ≠ d j / m := fun he => (ne_of_lt hlt) (h i j hi hj he)
    omega
  · intro h i j hi hj he
    by_contra hne
    wlog hij : i < j generalizing i j
    · exact this j i hj hi he.symm (Ne.symm hne)
        (lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hne))
    let k : Fin N := ⟨i.val+1, by have := j.isLt; have := hij; simp only [Fin.lt_def] at this; omega⟩
    have hik : i ≤ k := by simp only [Fin.le_iff_val_le_val, k]; omega
    have hkj : k ≤ j := by simpa only [Fin.le_iff_val_le_val, k] using (by have := hij; simp only [Fin.lt_def] at this; omega : i.val+1 ≤ j.val)
    have hq : d i / m = d k / m := by
      have h₁ : d i / m ≤ d k / m := Nat.div_le_div_right (hd hik)
      have h₂ : d k / m ≤ d j / m := Nat.div_le_div_right (hd hkj)
      omega
    have hk := partial_between m (d i) (d k) hi (hd hik) hq
    have hlt := h i k rfl hi hk
    omega

/-- For arbitrary padded Ferrers columns, the precise root floor condition is
    equivalent to the source's geometric singleton condition. -/
theorem rootFloorCriterion_iff_singleton (m : ℕ) (hm : 0 < m) {N : ℕ}
    (d : Fin N → ℕ) (hd : Monotone d) :
    RootFloorCriterion m (root m d) ↔ SingletonColumns m d := by
  rw [singleton_iff_adjacent m d hd]
  constructor
  · intro h i j hij hi hj
    have hi' : root m d i % (m : ℤ) ≠ 0 := (root_mod_zero_iff m d i).not.mpr hi
    have hj' : root m d j % (m : ℤ) ≠ 0 := (root_mod_zero_iff m d j).not.mpr hj
    have hh := h i j hij hi' hj'
    rw [root_div_partial m hm d i hi, root_div_partial m hm d j hj] at hh
    omega
  · intro h i j hij hi hj
    have hi' : d i % m ≠ 0 := (root_mod_zero_iff m d i).not.mp hi
    have hj' : d j % m ≠ 0 := (root_mod_zero_iff m d j).not.mp hj
    have hh := h i j hij hi' hj'
    rw [root_div_partial m hm d i hi', root_div_partial m hm d j hj']
    omega

end D5.S3.Combinatorics.Partitions.RookRootCriterion
