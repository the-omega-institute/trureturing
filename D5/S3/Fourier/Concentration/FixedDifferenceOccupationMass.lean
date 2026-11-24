/- GID: D5/S3/Fourier/Concentration/FixedDifferenceOccupationMass
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FixedDifferenceOccupationMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed signed count difference factors through its common occupation counts. -/

import D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

/-! The contribution of a fixed count difference to a weighted moment. -/
set_option autoImplicit false

namespace D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass

open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight diagonal)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)
open D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
  (subvectorMultiplicity subvectorMultiplicity_mul_monomialWeight one_le_subvectorMultiplicity)

noncomputable section

/-- The weighted mass of all degree-p pairs with difference a minus b. -/
def fixedDifferenceMass {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (a b : J → ℕ) (p : ℕ) : ℝ :=
  ∑ m ∈ ((piAntidiag univ p : Finset (J → ℕ)) ×ˢ piAntidiag univ p).filter
    (fun m => ∀ j, m.1 j + b j = m.2 j + a j),
      monomialWeight w m.1 * monomialWeight w m.2

/-- The Bessel series coefficient after removing the residual power of the weight. -/
def shiftedCoefficient (x : ℝ) (l r : ℕ) : ℝ :=
  x ^ l / ((l.factorial : ℝ) * ((l + r).factorial : ℝ))


private theorem count_fiber {J : Type*} [Fintype J] [DecidableEq J]
    (a b : J → ℕ) (p d : ℕ) (hd : d ≤ p)
    (ha : ∑ j, a j = d) (hb : ∑ j, b j = d) (hab : ∀ j, a j = 0 ∨ b j = 0) :
    (((piAntidiag univ p : Finset (J → ℕ)) ×ˢ piAntidiag univ p).filter
        (fun m => ∀ j, m.1 j + b j = m.2 j + a j)) =
      (piAntidiag univ (p - d)).image (fun l => (l + a, l + b)) := by
  classical
  ext m
  simp only [mem_filter, mem_product, mem_image, mem_piAntidiag,
    mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨⟨hm, hn⟩, hdiff⟩
    let l : J → ℕ := fun j => min (m.1 j) (m.2 j)
    have hpair : (l + a, l + b) = m := by
      apply Prod.ext
      · funext j
        have h := hdiff j
        change min (m.1 j) (m.2 j) + a j = m.1 j
        rcases hab j with h0 | h0 <;> omega
      · funext j
        have h := hdiff j
        change min (m.1 j) (m.2 j) + b j = m.2 j
        rcases hab j with h0 | h0 <;> omega
    have heq : l + a = m.1 := congrArg Prod.fst hpair
    have hs : ∑ j, (l + a) j = p := by rw [heq]; exact hm
    change (∑ j, (l j + a j)) = p at hs
    rw [sum_add_distrib, ha] at hs
    exact ⟨l, (Nat.eq_sub_of_add_eq hs), hpair⟩
  · rintro ⟨l, hl, rfl⟩
    constructor
    · constructor
      · change (∑ j, (l j + a j)) = p
        rw [sum_add_distrib, hl, ha, Nat.sub_add_cancel hd]
      · change (∑ j, (l j + b j)) = p
        rw [sum_add_distrib, hl, hb, Nat.sub_add_cancel hd]
    · intro j
      change l j + a j + b j = l j + b j + a j
      ac_rfl

theorem weight_factorials {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (p : ℕ) (m : J → ℕ) (hm : ∑ j, m j = p) :
    monomialWeight w m = (p.factorial : ℝ) *
      ∏ j, w j ^ m j / ((m j).factorial : ℝ) := by
  have hspec : (∏ j, ((m j).factorial : ℝ)) * (Nat.multinomial univ m : ℝ) =
      (p.factorial : ℝ) := by
    have h := Nat.multinomial_spec univ m
    rw [hm] at h
    exact_mod_cast h
  have hfac : (∏ j, ((m j).factorial : ℝ)) ≠ 0 := by positivity
  have hmult : (Nat.multinomial univ m : ℝ) =
      (p.factorial : ℝ) / ∏ j, ((m j).factorial : ℝ) :=
    (eq_div_iff hfac).mpr (by rw [mul_comm, hspec])
  rw [monomialWeight, hmult, prod_div_distrib]
  ring

private theorem shifted_factorials (w : ℝ) (l a b : ℕ) (hab : a = 0 ∨ b = 0) :
    (w ^ (l + a) / ((l + a).factorial : ℝ)) *
      (w ^ (l + b) / ((l + b).factorial : ℝ)) =
    w ^ (a + b) * ((w ^ 2) ^ l /
      ((l.factorial : ℝ) * ((l + a + b).factorial : ℝ))) := by
  have hp : w ^ (l + a) * w ^ (l + b) = w ^ (a + b) * (w ^ 2) ^ l := by
    simp only [pow_add, show (w ^ 2) ^ l = w ^ l * w ^ l by
      rw [pow_two, mul_pow]]
    ring
  rw [← mul_div_mul_comm, hp, mul_div_assoc]
  congr 2
  rcases hab with rfl | rfl
  · simp
  · simp [mul_comm]

private theorem shifted_weight {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (a b l : J → ℕ) (p d : ℕ) (hd : d ≤ p)
    (ha : ∑ j, a j = d) (hb : ∑ j, b j = d)
    (hl : ∑ j, l j = p - d) (hab : ∀ j, a j = 0 ∨ b j = 0) :
    monomialWeight w (l + a) * monomialWeight w (l + b) =
      (p.factorial : ℝ) ^ 2 * (∏ j, w j ^ (a j + b j)) *
      ∏ j, (w j ^ 2) ^ l j /
        (((l j).factorial : ℝ) * ((l j + a j + b j).factorial : ℝ)) := by
  have hla : ∑ j, (l + a) j = p := by
    change (∑ j, (l j + a j)) = p
    rw [sum_add_distrib, hl, ha, Nat.sub_add_cancel hd]
  have hlb : ∑ j, (l + b) j = p := by
    change (∑ j, (l j + b j)) = p
    rw [sum_add_distrib, hl, hb, Nat.sub_add_cancel hd]
  rw [weight_factorials w p _ hla, weight_factorials w p _ hlb]
  simp only [Pi.add_apply]
  rw [mul_mul_mul_comm, ← pow_two, ← prod_mul_distrib, mul_assoc, ← prod_mul_distrib]
  congr 1
  exact prod_congr rfl fun j _ => shifted_factorials (w j) (l j) (a j) (b j) (hab j)

private theorem fixedDifferenceMass_eq {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (a b : J → ℕ) (p d : ℕ) (hd : d ≤ p)
    (ha : ∑ j, a j = d) (hb : ∑ j, b j = d) (hab : ∀ j, a j = 0 ∨ b j = 0) :
    fixedDifferenceMass w a b p =
      (p.factorial : ℝ) ^ 2 * (∏ j, w j ^ (a j + b j)) *
      ∑ l ∈ piAntidiag univ (p - d), ∏ j, (w j ^ 2) ^ l j /
        (((l j).factorial : ℝ) * ((l j + a j + b j).factorial : ℝ)) := by
  classical
  unfold fixedDifferenceMass
  rw [count_fiber a b p d hd ha hb hab]
  rw [sum_image (fun l _ k _ h =>
      add_right_cancel (show l + a = k + a from congrArg Prod.fst h))]
  rw [mul_sum]
  exact sum_congr rfl fun l hl =>
    shifted_weight w a b l p d hd ha hb (mem_piAntidiag.mp hl).1 hab

private theorem weight_add_bound {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (a l : J → ℕ) (p d : ℕ) (hd : d ≤ p)
    (ha : ∑ j, a j = d) (hl : ∑ j, l j = p - d) :
    monomialWeight w (l + a) ≤
      (Nat.choose p d : ℝ) * monomialWeight w l * monomialWeight w a := by
  have h := subvectorMultiplicity_mul_monomialWeight w a l
  rw [ha, hl, Nat.add_sub_of_le hd, add_comm a l] at h
  have hm : 1 ≤ subvectorMultiplicity (l + a) a :=
    one_le_subvectorMultiplicity fun j => by
      change a j ≤ l j + a j
      exact Nat.le_add_left _ _
  calc
    monomialWeight w (l + a) = 1 * monomialWeight w (l + a) := by simp
    _ ≤ subvectorMultiplicity (l + a) a * monomialWeight w (l + a) :=
      mul_le_mul_of_nonneg_right hm (monomialWeight_nonneg w hw _)
    _ = _ := by rw [h]; ring

private theorem fixedDifferenceMass_bound {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (a b : J → ℕ) (p d : ℕ) (hd : d ≤ p)
    (ha : ∑ j, a j = d) (hb : ∑ j, b j = d) (hab : ∀ j, a j = 0 ∨ b j = 0) :
    fixedDifferenceMass w a b p ≤
      (Nat.choose p d : ℝ) ^ 2 *
        diagonal w (p - d) *
        (monomialWeight w a * monomialWeight w b) := by
  classical
  have hweight := monomialWeight_nonneg w hw
  unfold fixedDifferenceMass
  rw [count_fiber a b p d hd ha hb hab]
  rw [sum_image (fun l _ k _ h =>
      add_right_cancel (show l + a = k + a from congrArg Prod.fst h))]
  unfold diagonal
  rw [mul_sum, sum_mul]
  refine sum_le_sum fun l hl => ?_
  have hld := (mem_piAntidiag.mp hl).1
  calc
    _ ≤ ((Nat.choose p d : ℝ) * monomialWeight w l * monomialWeight w a) *
        ((Nat.choose p d : ℝ) * monomialWeight w l * monomialWeight w b) :=
      mul_le_mul (weight_add_bound w hw a l p d hd ha hld)
        (weight_add_bound w hw b l p d hd hb hld) (hweight _)
        (mul_nonneg (mul_nonneg (by positivity) (hweight l)) (hweight a))
    _ = _ := by ring

/-- Isolate the exact mass of a difference and bound it by a lower-degree diagonal. -/
theorem fixed_difference_mass {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (a b : J → ℕ) (p d : ℕ) (hd : d ≤ p)
    (ha : ∑ j, a j = d) (hb : ∑ j, b j = d) (hab : ∀ j, a j = 0 ∨ b j = 0) :
    let coefficient := shiftedCoefficient
    (fixedDifferenceMass w a b p =
      (p.factorial : ℝ) ^ 2 * (∏ j, w j ^ (a j + b j)) *
        ∑ l ∈ piAntidiag univ (p - d), ∏ j, coefficient (w j ^ 2) (l j) (a j + b j)) ∧
    ((∀ j, 0 ≤ w j) → fixedDifferenceMass w a b p ≤
      (Nat.choose p d : ℝ) ^ 2 * diagonal w (p - d) *
        (monomialWeight w a * monomialWeight w b)) := by
  refine ⟨?_, fun hw => fixedDifferenceMass_bound w hw a b p d hd ha hb hab⟩
  simpa only [shiftedCoefficient, Nat.add_assoc] using fixedDifferenceMass_eq w a b p d hd ha hb hab

end

end D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass
