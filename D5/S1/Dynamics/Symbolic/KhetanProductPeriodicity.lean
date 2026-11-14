/- GID: D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Exact-cover product fibres feed the six-cell residue dichotomy. -/

import Mathlib
import D5.S1.Dynamics.Symbolic.KhetanSixCellResidue

/-! This is the product branch of the six-cell route.  The one-dimensional
three-point classification follows from the prime-three shift identity and
Bézout.  The two-column exact-cover equation then supplies the Boolean
adjacent-column hypotheses of the existing residue dichotomy. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanProductPeriodicity

open scoped BigOperators

noncomputable def anchorBit (T : ℤ → ℤ → Prop) (x y : ℤ) : ℕ := by
  classical
  exact if T x y then 1 else 0

noncomputable def oneDWindowCount (S : ℤ → Prop) (b c y : ℤ) : ℕ := by
  classical
  exact Finset.sum ({0, b, c} : Finset ℤ) (fun z => if S (y - z) then 1 else 0)

noncomputable def productWindowCount (T : ℤ → ℤ → Prop) (b c x y : ℤ) : ℕ := by
  classical
  exact Finset.sum ({0, b, c} : Finset ℤ) (fun z =>
    anchorBit T (x - 1) (y - z) + anchorBit T x (y - z))

/-! Cubing the three commuting shifts modulo three makes the three diagonal
bits equal.  Their periods combine by Bézout to give period three. -/
private lemma three_point_bit_periodic
    (f : ℤ → ℤ) (b c : ℤ)
    (hbit : ∀ y, f y = 0 ∨ f y = 1)
    (hcover : ∀ y, f y + f (y - b) + f (y - c) = 1)
    (hgcd : Int.gcd b c = 1) : Function.Periodic f 3 := by
  have hdiagonal : ∀ y, f y = f (y - 3 * b) ∧ f y = f (y - 3 * c) := by
    intro y
    have h0 := hcover y
    have hb : f (y - b) + f (y - 2 * b) + f (y - (b + c)) = 1 := by
      simpa only [show (y - b) - b = y - 2 * b by ring,
        show (y - b) - c = y - (b + c) by ring] using hcover (y - b)
    have hc : f (y - c) + f (y - (b + c)) + f (y - 2 * c) = 1 := by
      simpa only [show (y - c) - b = y - (b + c) by ring,
        show (y - c) - c = y - 2 * c by ring] using hcover (y - c)
    have hbb : f (y - 2 * b) + f (y - 3 * b) + f (y - (2 * b + c)) = 1 := by
      simpa only [show (y - 2 * b) - b = y - 3 * b by ring,
        show (y - 2 * b) - c = y - (2 * b + c) by ring] using hcover (y - 2 * b)
    have hbc : f (y - (b + c)) + f (y - (2 * b + c)) +
        f (y - (b + 2 * c)) = 1 := by
      simpa only [show (y - (b + c)) - b = y - (2 * b + c) by ring,
        show (y - (b + c)) - c = y - (b + 2 * c) by ring] using hcover (y - (b + c))
    have hcc : f (y - 2 * c) + f (y - (b + 2 * c)) + f (y - 3 * c) = 1 := by
      simpa only [show (y - 2 * c) - b = y - (b + 2 * c) by ring,
        show (y - 2 * c) - c = y - 3 * c by ring] using hcover (y - 2 * c)
    have hcube : f y + f (y - 3 * b) + f (y - 3 * c) +
        3 * (f (y - b) + f (y - c) + f (y - 2 * b) + f (y - 2 * c) +
          f (y - (2 * b + c)) + f (y - (b + 2 * c)) + 2 * f (y - (b + c))) = 9 := by
      linear_combination h0 + 2 * hb + 2 * hc + hbb + 2 * hbc + hcc
    have hf0 := hbit y
    have hfb := hbit (y - 3 * b)
    have hfc := hbit (y - 3 * c)
    omega
  have hb : Function.Periodic f (3 * b) := by
    intro y
    simpa using (hdiagonal (y + 3 * b)).1
  have hc : Function.Periodic f (3 * c) := by
    intro y
    simpa using (hdiagonal (y + 3 * c)).2
  have hbez : b * Int.gcdA b c + c * Int.gcdB b c = 1 := by
    simpa [hgcd] using (Int.gcd_eq_gcd_ab b c).symm
  have hp := (hb.int_mul (Int.gcdA b c)).add_period
    (hc.int_mul (Int.gcdB b c))
  have heq : Int.gcdA b c * (3 * b) + Int.gcdB b c * (3 * c) = 3 := by
    calc
      _ = 3 * (b * Int.gcdA b c + c * Int.gcdB b c) := by ring
      _ = 3 := by rw [hbez]; norm_num
  simpa only [Int.cast_id, heq] using hp

/-! A period-three zero-one exact cover occupies exactly one residue class.
Summing over the three residues proves this even before the residues of the
tile offsets have been classified. -/
private lemma three_point_bit_residue
    (f : ℤ → ℤ) (b c : ℤ)
    (hbit : ∀ y, f y = 0 ∨ f y = 1)
    (hcover : ∀ y, f y + f (y - b) + f (y - c) = 1)
    (hp : Function.Periodic f 3) :
    ∃ r : ℤ, ∀ y, f y = 1 ↔ y % 3 = r % 3 := by
  have hmod (y : ℤ) : f y = f (y % 3) := by
    simpa only [Int.cast_id, Int.emod_add_ediv_mul] using
      hp.int_mul (y / 3) (y % 3)
  have hsum : f 0 + f 1 + f 2 = 1 := by
    have hreduce (k d : ℤ) : (k - d) % 3 = (k - d % 3) % 3 := by omega
    have h0 := hcover 0
    have h1 := hcover 1
    have h2 := hcover 2
    rw [hmod (0 - b), hmod (0 - c)] at h0
    rw [hmod (1 - b), hmod (1 - c)] at h1
    rw [hmod (2 - b), hmod (2 - c)] at h2
    rw [hreduce 0 b, hreduce 0 c] at h0
    rw [hreduce 1 b, hreduce 1 c] at h1
    rw [hreduce 2 b, hreduce 2 c] at h2
    have hb0 := Int.emod_nonneg b (by norm_num : (3 : ℤ) ≠ 0)
    have hb3 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 3)
    have hc0 := Int.emod_nonneg c (by norm_num : (3 : ℤ) ≠ 0)
    have hc3 := Int.emod_lt_of_pos c (by norm_num : (0 : ℤ) < 3)
    interval_cases hb : b % 3 <;> interval_cases hc : c % 3 <;>
      norm_num [hb, hc] at h0 h1 h2 <;> omega
  have hbit0 := hbit 0
  have hbit1 := hbit 1
  have hbit2 := hbit 2
  by_cases hf0 : f 0 = 1
  · have hf1 : f 1 = 0 := by omega
    have hf2 : f 2 = 0 := by omega
    refine ⟨0, ?_⟩
    intro y
    rw [hmod y]
    have hy0 := Int.emod_nonneg y (by norm_num : (3 : ℤ) ≠ 0)
    have hy3 := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 3)
    interval_cases hy : y % 3 <;> simp [hf0, hf1, hf2]
  · have hf0' : f 0 = 0 := by omega
    by_cases hf1 : f 1 = 1
    · have hf2 : f 2 = 0 := by omega
      refine ⟨1, ?_⟩
      intro y
      rw [hmod y]
      have hy0 := Int.emod_nonneg y (by norm_num : (3 : ℤ) ≠ 0)
      have hy3 := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 3)
      interval_cases hy : y % 3 <;> simp [hf0', hf1, hf2]
    · have hf1' : f 1 = 0 := by omega
      have hf2 : f 2 = 1 := by omega
      refine ⟨2, ?_⟩
      intro y
      rw [hmod y]
      have hy0 := Int.emod_nonneg y (by norm_num : (3 : ℤ) ≠ 0)
      have hy3 := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 3)
      interval_cases hy : y % 3 <;> simp [hf0', hf1', hf2]

private lemma three_point_tiling_residue
    (S : ℤ → Prop) (b c : ℤ)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : b ≠ c)
    (hgcd : Int.gcd b c = 1)
    (hcover : ∀ y, oneDWindowCount S b c y = 1) :
    ∃ r : ℤ, ∀ y, S y ↔ y % 3 = r % 3 := by
  classical
  let f : ℤ → ℤ := fun y => if S y then 1 else 0
  have hbit : ∀ y, f y = 0 ∨ f y = 1 := by
    intro y
    by_cases hy : S y <;> simp [f, hy]
  have hfcover : ∀ y, f y + f (y - b) + f (y - c) = 1 := by
    intro y
    have h := hcover y
    have h0 : (0 : ℤ) ∉ ({b, c} : Finset ℤ) := by simp [Ne.symm hb0, Ne.symm hc0]
    have hb : b ∉ ({c} : Finset ℤ) := by simp [hbc]
    unfold oneDWindowCount at h
    rw [Finset.sum_insert h0, Finset.sum_insert hb, Finset.sum_singleton] at h
    simp only [sub_zero] at h
    by_cases hy : S y <;> by_cases hyb : S (y - b) <;> by_cases hyc : S (y - c) <;>
      norm_num [f, hy, hyb, hyc] at h <;> norm_num [f, hy, hyb, hyc]
  have hp := three_point_bit_periodic f b c hbit hfcover hgcd
  obtain ⟨r, hr⟩ := three_point_bit_residue f b c hbit hfcover hp
  refine ⟨r, ?_⟩
  intro y
  simpa [f] using hr y

/-! Exact-cover product fibres force one of the two global periods.  The
one-dimensional prime-three classification is proved above and is consumed
here for every adjacent pair of columns. -/
theorem product_three_exact_cover_periodic
    (T : ℤ → ℤ → Prop) (b c : ℤ)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : b ≠ c)
    (hgcd : Int.gcd b c = 1)
    (hcover : ∀ x y, productWindowCount T b c x y = 1) :
    (∀ x y, T (x + 2) y ↔ T x y) ∨
      (∀ x y, T x (y + 3) ↔ T x y) := by
  let C : ℤ → ℤ → Prop := fun x y => T (x - 1) y ∨ T x y
  have hdisj : ∀ x y, ¬ (T (x - 1) y ∧ T x y) := by
    intro x y hboth
    have hbound :
        anchorBit T (x - 1) y + anchorBit T x y ≤
          productWindowCount T b c x y := by
      simpa [productWindowCount] using (Finset.single_le_sum
        (s := ({0, b, c} : Finset ℤ))
        (a := (0 : ℤ))
        (f := fun z =>
          anchorBit T (x - 1) (y - z) + anchorBit T x (y - z))
        (fun _ _ => Nat.zero_le _) (by simp))
    have htwo : 2 ≤ productWindowCount T b c x y := by
      have hbits : anchorBit T (x - 1) y = 1 ∧ anchorBit T x y = 1 := by
        simp [anchorBit, hboth.1, hboth.2]
      calc
        2 = anchorBit T (x - 1) y + anchorBit T x y := by
          simp [hbits.1, hbits.2]
        _ ≤ productWindowCount T b c x y := hbound
    rw [hcover x y] at htwo
    omega
  have hsum_eq : ∀ x y,
      oneDWindowCount (C x) b c y = productWindowCount T b c x y := by
    intro x y
    unfold oneDWindowCount productWindowCount
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hl : T (x - 1) (y - z)
    · have hr : ¬ T x (y - z) := by
        intro hr
        exact hdisj x (y - z) ⟨hl, hr⟩
      simp [C, anchorBit, hl, hr]
    · by_cases hr : T x (y - z)
      · simp [C, anchorBit, hl, hr]
      · simp [C, anchorBit, hl, hr]
  have hCcover : ∀ x y, oneDWindowCount (C x) b c y = 1 := by
    intro x y
    rw [hsum_eq x y]
    exact hcover x y
  choose r hres using fun x =>
    three_point_tiling_residue (C x) b c hb0 hc0 hbc hgcd (hCcover x)
  have hpart : ∀ x y,
      Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3 := by
    intro x y
    rw [← hres x y]
    constructor
    · intro hx
      rcases hx with ⟨hl, _⟩ | ⟨hright, _⟩
      · exact Or.inl hl
      · exact Or.inr hright
    · intro hc'
      rcases hc' with hl | hright
      · exact Or.inl ⟨hl, fun h => hdisj x y ⟨hl, h⟩⟩
      · exact Or.inr ⟨hright, fun h => hdisj x y ⟨h, hright⟩⟩
  exact D5.S1.Dynamics.Symbolic.KhetanSixCellResidue.three_residue_column_dichotomy
    T r hpart hdisj

end D5.S1.Dynamics.Symbolic.KhetanProductPeriodicity
