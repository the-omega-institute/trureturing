/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Residual
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/Residual
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Finite residue row sums control cross block short distance residuals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.KernelCriterion

/-! Residue sums for finite cross block residual bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- A finite lattice sum. For `r < p`, all omitted terms have zero residual. -/
def f (p L r : ℕ) : ℚ :=
  ∑ k ∈ Icc (-(L : ℤ)) (L : ℤ), w L (((p : ℤ) * k - (r : ℤ)).natAbs)

theorem w_eq_zero_iff {L g : ℕ} : w L g = 0 ↔ g = 0 ∨ L ≤ g := by
  simp [w, div_eq_zero_iff, Nat.sub_eq_zero_iff_le]
  omega

private theorem lattice_identity {p x y : ℕ} (hy : p ∣ y) :
    (p : ℤ) * (((y / p : ℕ) : ℤ) - ((x / p : ℕ) : ℤ)) - (x % p : ℕ) =
      (y : ℤ) - (x : ℤ) := by
  have hy' : p * (y / p) = y := Nat.mul_div_cancel' hy
  have hx := Nat.mod_add_div x p
  have hyq : (p : ℤ) * (y / p : ℕ) = (y : ℤ) := by exact_mod_cast hy'
  have hxq : ((x % p : ℕ) : ℤ) + (p : ℤ) * (x / p : ℕ) = (x : ℤ) := by
    exact_mod_cast hx
  nlinarith only [hyq, hxq]

private theorem lattice_injective {p x : ℕ} {B : Finset ℕ}
    (hB : ∀ y ∈ B, p ∣ y) :
    Set.InjOn (fun y : ℕ => ((y / p : ℕ) : ℤ) - (x / p : ℕ)) B := by
  intro y hy z hz he
  have hy' := Nat.mul_div_cancel' (hB y hy)
  have hz' := Nat.mul_div_cancel' (hB z hz)
  have heZ : ((y / p : ℕ) : ℤ) = ((z / p : ℕ) : ℤ) := by
    linarith only [he]
  have he' : y / p = z / p := by exact_mod_cast heZ
  rw [he'] at hy'
  omega

private theorem lattice_mem {p L x y : ℕ} (hp : 0 < p) (hy : p ∣ y)
    (hg : Nat.dist x y < L) :
    ((y / p : ℕ) : ℤ) - (x / p : ℕ) ∈ Icc (-(L : ℤ)) (L : ℤ) := by
  let k : ℤ := ((y / p : ℕ) : ℤ) - (x / p : ℕ)
  have he : (p : ℤ) * k - ((x % p : ℕ) : ℤ) = (y : ℤ) - (x : ℤ) :=
    lattice_identity hy
  have hr : ((x % p : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast Nat.mod_lt x hp
  have hr0 : (0 : ℤ) ≤ (x % p : ℕ) := by positivity
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hL : (1 : ℤ) ≤ L := by omega
  have hg' : -((L : ℤ)) < (y : ℤ) - (x : ℤ) ∧
      (y : ℤ) - (x : ℤ) < (L : ℤ) := by
    unfold Nat.dist at hg
    omega
  simp only [mem_Icc]
  change -(L : ℤ) ≤ k ∧ k ≤ (L : ℤ)
  constructor
  · by_contra hk
    have hk' : k ≤ -(L : ℤ) - 1 := by omega
    have hmul := mul_nonneg (by omega : 0 ≤ (p : ℤ) - 1)
      (by omega : 0 ≤ -k)
    nlinarith
  · by_contra hk
    have hk' : (L : ℤ) + 1 ≤ k := by omega
    have hmul := mul_nonneg (by omega : 0 ≤ (p : ℤ) - 1)
      (by omega : 0 ≤ k - 1)
    nlinarith

/-- Each row injects its nonzero terms into one period's finite lattice sum. -/
private theorem residual_row_le {p L x : ℕ} (hp : 0 < p) (B : Finset ℕ)
    (hB : ∀ y ∈ B, p ∣ y) :
    (∑ y ∈ B, w L (Nat.dist x y)) ≤ f p L (x % p) := by
  let S := B.filter fun y => Nat.dist x y < L
  let k : ℕ → ℤ := fun y => ((y / p : ℕ) : ℤ) - (x / p : ℕ)
  have hinj : Set.InjOn k S := (lattice_injective (x := x) hB).mono
    (by intro y hy; exact (mem_filter.mp hy).1)
  have hsub : S.image k ⊆ Icc (-(L : ℤ)) (L : ℤ) := by
    intro z hz
    rcases mem_image.mp hz with ⟨y, hy, rfl⟩
    exact lattice_mem hp (hB y (mem_filter.mp hy).1) (mem_filter.mp hy).2
  have hzero : (∑ y ∈ B, w L (Nat.dist x y)) =
      ∑ y ∈ S, w L (Nat.dist x y) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro y hyB hy
    exact w_eq_zero_iff.mpr (Or.inr (by simpa [S, hyB] using hy))
  rw [hzero]
  calc
    _ = ∑ y ∈ S, w L (((p : ℤ) * k y - ((x % p : ℕ) : ℤ)).natAbs) := by
      apply sum_congr rfl
      intro y hy
      change w L (Nat.dist x y) = w L (((p : ℤ) *
        (((y / p : ℕ) : ℤ) - ((x / p : ℕ) : ℤ)) - ((x % p : ℕ) : ℤ)).natAbs)
      rw [lattice_identity (x := x) (hB y (mem_filter.mp hy).1), int_distance, Nat.dist_comm y x]
    _ = ∑ z ∈ S.image k, w L (((p : ℤ) * z - ((x % p : ℕ) : ℤ)).natAbs) :=
      (sum_image (f := fun z => w L (((p : ℤ) * z -
        ((x % p : ℕ) : ℤ)).natAbs)) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (by intro z _ _; exact w_nonneg L _)

/-- A cross residual is bounded by the residue row sums, without disjointness assumptions. -/
private theorem crossResidual_le_sum_f {p L : ℕ} (hp : 0 < p) (A B : Finset ℕ)
    (hB : ∀ y ∈ B, p ∣ y) :
    crossResidual L A B ≤ ∑ x ∈ A, f p L (x % p) := by
  exact sum_le_sum fun x _ => residual_row_le hp B hB

private theorem w_natAbs_eq_zero {L : ℕ} {z : ℤ}
    (h : (L : ℤ) ≤ z ∨ z ≤ -(L : ℤ)) : w L z.natAbs = 0 := by
  apply w_eq_zero_iff.mpr ∘ Or.inr
  have hz : (L : ℤ) ≤ (z.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    rcases h with h | h
    · exact h.trans (le_abs_self z)
    · have := neg_le_abs z
      omega
  exact_mod_cast hz

/-- Below one period only the nearest multiples on either side can contribute. -/
private theorem f_eq_two_terms_of_window {p L r : ℕ} (hL : L ≤ p + min r (p - r)) (hrp : r ≤ p) :
    f p L r = w L r + w L (p - r) := by
  by_cases hL0 : L = 0
  · subst L
    simp [f, w]
  have hmin : min r (p - r) ≤ r := min_le_left _ _
  have hp : (0 : ℤ) < p := by omega
  have hr' : (0 : ℤ) ≤ r := by positivity
  have hrp' : (r : ℤ) ≤ p := by exact_mod_cast hrp
  have hleft : L ≤ p + r := hL.trans (Nat.add_le_add_left (min_le_left _ _) p)
  have hright : L ≤ 2 * p - r := by
    have := hL.trans (Nat.add_le_add_left (min_le_right r (p - r)) p)
    omega
  have hleft' : (L : ℤ) ≤ (p : ℤ) + r := by exact_mod_cast hleft
  have hright' : (L : ℤ) ≤ 2 * (p : ℤ) - r := by
    have : L + r ≤ 2 * p := by omega
    have : (L : ℤ) + r ≤ 2 * (p : ℤ) := by exact_mod_cast this
    linarith
  have hsub : ({0, 1} : Finset ℤ) ⊆ Icc (-(L : ℤ)) (L : ℤ) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [mem_Icc] <;> omega
  have he : f p L r = ∑ k ∈ ({0, 1} : Finset ℤ),
      w L (((p : ℤ) * k - (r : ℤ)).natAbs) := by
    symm
    apply sum_subset hsub
    intro k _ hk
    apply w_natAbs_eq_zero
    have hk' : k ≠ 0 ∧ k ≠ 1 := by simpa using hk
    by_cases hk0 : k < 0
    · right
      have := mul_nonneg hp.le (by omega : 0 ≤ -k - 1)
      nlinarith
    · left
      have := mul_nonneg hp.le (by omega : 0 ≤ k - 2)
      nlinarith
  rw [he]
  have habs : ((p : ℤ) - (r : ℤ)).natAbs = p - r := by
    rw [Int.natAbs_natCast_sub_natCast_of_ge hrp]
  simp [habs]

/-- The two-site support formula has an exact window criterion. -/
theorem f_eq_two_terms {p L r : ℕ} (hrp : r ≤ p) :
    f p L r = w L r + w L (p - r) ↔ p = 0 ∨ L ≤ p + min r (p - r) := by
  by_cases hp : p = 0
  · subst p
    have hr : r = 0 := by omega
    subst r
    simp [f, w]
  constructor
  · intro he
    by_contra h
    have hL : p + min r (p - r) < L := by omega
    have hL0 : 0 < L := by omega
    have hsub : ({0, 1} : Finset ℤ) ⊆ Icc (-(L : ℤ)) (L : ℤ) := by
      intro k hk
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp only [mem_Icc] <;> omega
    have hwpos (g : ℕ) (hg : 0 < g) (hgL : g < L) : 0 < w L g := by
      unfold w
      have : 0 < L - g := Nat.sub_pos_of_lt hgL
      positivity
    have hstrict (k : ℤ) (hk : k ∈ Icc (-(L : ℤ)) (L : ℤ))
        (hk' : k ∉ ({0, 1} : Finset ℤ))
        (hkw : 0 < w L (((p : ℤ) * k - (r : ℤ)).natAbs)) : False := by
      have hlt := sum_lt_sum_of_subset hsub hk hk' hkw
        (fun j _ _ => w_nonneg L (((p : ℤ) * j - (r : ℤ)).natAbs))
      have habs : ((p : ℤ) - (r : ℤ)).natAbs = p - r :=
        Int.natAbs_natCast_sub_natCast_of_ge hrp
      simp only [sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)),
        sum_singleton, mul_zero, zero_sub, Int.natAbs_neg, Int.natAbs_natCast,
        mul_one, habs] at hlt
      change w L r + w L (p - r) < f p L r at hlt
      linarith
    by_cases hleft : p + r < L
    · apply hstrict (-1) (by simp only [mem_Icc]; omega) (by decide)
      have habs : ((p : ℤ) * -1 - (r : ℤ)).natAbs = p + r := by
        rw [show (p : ℤ) * -1 - (r : ℤ) = -((p + r : ℕ) : ℤ) by push_cast; ring]
        simp only [Int.natAbs_neg, Int.natAbs_natCast]
      rw [habs]
      exact hwpos (p + r) (by omega) hleft
    · apply hstrict 2 (by simp only [mem_Icc]; omega) (by decide)
      have hd : 2 * p - r < L := by omega
      have habs : ((p : ℤ) * 2 - (r : ℤ)).natAbs = 2 * p - r := by
        rw [show (p : ℤ) * 2 = ((2 * p : ℕ) : ℤ) by push_cast; ring]
        exact Int.natAbs_natCast_sub_natCast_of_ge (by omega)
      rw [habs]
      exact hwpos (2 * p - r) (by omega) hd
  · rintro (h | h)
    · exact False.elim (hp h)
    · exact f_eq_two_terms_of_window h hrp

/-- At two periods exactly four lattice sites may contribute. -/
theorem f_eq_four_terms {p r : ℕ} (hrp : r ≤ p) :
    f p (2 * p) r = w (2 * p) r + w (2 * p) (p - r) +
      w (2 * p) (p + r) + w (2 * p) (2 * p - r) := by
  by_cases hp0 : p = 0
  · subst p
    have : r = 0 := by omega
    subst r
    simp [f, w]
  have hp : (0 : ℤ) < p := by omega
  have hr' : (0 : ℤ) ≤ r := by positivity
  have hrp' : (r : ℤ) ≤ p := by exact_mod_cast hrp
  have hsub : ({-1, 0, 1, 2} : Finset ℤ) ⊆
      Icc (-((2 * p : ℕ) : ℤ)) ((2 * p : ℕ) : ℤ) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp only [mem_Icc] <;> push_cast <;> omega
  have he : f p (2 * p) r = ∑ k ∈ ({-1, 0, 1, 2} : Finset ℤ),
      w (2 * p) (((p : ℤ) * k - (r : ℤ)).natAbs) := by
    symm
    apply sum_subset hsub
    intro k _ hk
    apply w_natAbs_eq_zero
    have hk' : k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 := by simpa using hk
    push_cast
    by_cases hk0 : k < 0
    · right
      have := mul_nonneg hp.le (by omega : 0 ≤ -k - 2)
      nlinarith
    · left
      have := mul_nonneg hp.le (by omega : 0 ≤ k - 3)
      nlinarith
  rw [he]
  have habs₁ : ((p : ℤ) - (r : ℤ)).natAbs = p - r :=
    Int.natAbs_natCast_sub_natCast_of_ge hrp
  have habs₂ : ((p : ℤ) * 2 - (r : ℤ)).natAbs = 2 * p - r := by
    rw [show (p : ℤ) * 2 = ((2 * p : ℕ) : ℤ) by push_cast; ring]
    exact Int.natAbs_natCast_sub_natCast_of_ge (by omega)
  have habs₃ : ((p : ℤ) * -1 - (r : ℤ)).natAbs = p + r := by
    calc
      _ = (-((p + r : ℕ) : ℤ)).natAbs := by congr 1; push_cast; ring
      _ = _ := by rw [Int.natAbs_neg, Int.natAbs_natCast]
  rw [sum_insert (by decide : (-1 : ℤ) ∉ ({0, 1, 2} : Finset ℤ)),
    sum_insert (by decide : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
    sum_insert (by decide : (1 : ℤ) ∉ ({2} : Finset ℤ)), sum_singleton]
  rw [habs₃]
  simp only [mul_zero, zero_sub, Int.natAbs_neg, Int.natAbs_natCast,
    mul_one, habs₁, habs₂]
  ring

/-- The prime power criterion with the computable average residue bound as input. -/
theorem kernel_criterion_residue_average {p a m L : ℕ} {bA bB F : ℚ}
    (hp : p.Prime) (hpm : ¬p ∣ m) (hL : 0 < L)
    (hA : hHat m ≤ bA * m.divisors.card)
    (hB : hHat ((p ^ a * m) / p) ≤ bB * a * m.divisors.card)
    (hF : (∑ d ∈ m.divisors, f p L (d % p)) / (m.divisors.card : ℚ) ≤ F)
    (hTest : KernelTest a p L bA bB F) :
    hHat (p ^ a * m) < ((p ^ a * m).divisors.card : ℚ) := by
  apply kernel_criterion_prime_power hp hpm hL hA hB _ hTest
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  have ht : (0 : ℚ) < m.divisors.card := by
    exact_mod_cast card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  calc
    _ ≤ ∑ d ∈ m.divisors, f p L (d % p) := crossResidual_le_sum_f hp.pos _ _
      (by intro y hy; rcases mem_image.mp hy with ⟨z, _, rfl⟩; exact dvd_mul_right p z)
    _ ≤ F * m.divisors.card := (div_le_iff₀ ht).mp hF

#print axioms f_eq_two_terms
#print axioms f_eq_four_terms
#print axioms w_eq_zero_iff
#print axioms residual_row_le
#print axioms crossResidual_le_sum_f
#print axioms kernel_criterion_residue_average

end D5.S3.Arith.ErdosNicolas
