/- GID: D5/S1/Recurrence/KimberlingArrayRowPairs
   generality: I
   mirror-B: D5/B/S1/Recurrence/KimberlingArrayRowPairs
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Golden integer units and the separation of rows in the golden power array. -/

import D5.S1.Scale.Lucas
import D5.S1.Scale.Embedding
import D5.S1.Scale.Units
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace D5.S1.Recurrence.KimberlingArray

open D5.S0.Carrier D5.S1.Scale
local notation "φ" => Real.goldenRatio

/-- The row indexed by a natural exponent. -/
def row (i : ℕ) : Set ℕ := {N | ∃ k : ℕ, 1 ≤ k ∧ N = ⌊(k : ℝ) * φ ^ i⌋₊}

/-- Lucas numbers obtained from the integral golden trace. -/
def lucas (n : ℕ) : ℕ := (D5.S1.Scale.goldenLucas n).toNat

/-- Integer powers of the fundamental unit evaluate to real golden powers. -/
theorem embedding_phiUnit_zpow (s : ℤ) :
    embedding ((phiUnit ^ s : GoldenIntˣ) : GoldenInt) = φ ^ s := by
  change ((embedding.toMonoidHom).comp (Units.coeHom GoldenInt)) (phiUnit ^ s) = _
  rw [map_zpow]
  simp

/-- The inverse golden power has the signed conjugate coordinates. -/
theorem phiUnit_neg_nat (r : ℕ) :
    ((phiUnit ^ (-(r : ℤ)) : GoldenIntˣ) : GoldenInt) =
      (-1 : GoldenInt) ^ r * conj (phi ^ r) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  change ((-conj phi) ^ r : GoldenInt) = _
  rw [neg_eq_neg_one_mul, mul_pow]
  congr 1
  exact (map_pow conjEquiv phi r).symm

/-- A small unit with negative golden coordinate has a uniquely oriented inverse power. -/
theorem golden_small_unit (z : GoldenInt) (i : ℕ)
    (hn : norm z = 1 ∨ norm z = -1)
    (hb : z.b < 0) (hsmall : |embedding z| < (φ ^ i)⁻¹) :
    ∃ r : ℕ, i + 1 ≤ r ∧ z = conj (phi ^ r) ∧
      embedding z = (-1 : ℝ) ^ r * (φ ^ r)⁻¹ := by
  obtain ⟨negative, s, hzpow⟩ := (golden_units_eq_signed_phi_pow z).mp
    ((isUnit_iff_norm_eq_one_or_neg_one z).mpr hn)
  have hs : z = ((phiUnit ^ s : GoldenIntˣ) : GoldenInt) ∨
      z = -((phiUnit ^ s : GoldenIntˣ) : GoldenInt) := by
    cases negative with
    | false => exact Or.inl (by simpa [signedPhiPower] using hzpow)
    | true => exact Or.inr (by simpa [signedPhiPower] using hzpow)
  have habs : |embedding z| = φ ^ s := by
    rcases hs with hs | hs <;> rw [hs]
    · rw [embedding_phiUnit_zpow, abs_of_pos (zpow_pos Real.goldenRatio_pos _)]
    · rw [map_neg, abs_neg, embedding_phiUnit_zpow,
        abs_of_pos (zpow_pos Real.goldenRatio_pos _)]
  have hsi : s < -(i : ℤ) := by
    rw [habs, ← zpow_natCast, ← zpow_neg] at hsmall
    exact (zpow_lt_zpow_iff_right₀ Real.one_lt_goldenRatio).mp hsmall
  have hsneg : s ≤ 0 := by omega
  let r := (-s).toNat
  have hsr : s = -(r : ℤ) := by
    dsimp [r]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hir : i + 1 ≤ r := by omega
  have hfr : (0 : ℤ) < Nat.fib r := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < r)
  have hpow : (-1 : GoldenInt) ^ r = ((-1 : ℤ) ^ r : ℤ) := by norm_cast
  have hz : z = conj (phi ^ r) := by
    rw [hsr, phiUnit_neg_nat, hpow] at hs
    rcases neg_one_pow_eq_or ℤ r with hp | hp
    · rcases hs with hs | hs
      · simpa [hp] using hs
      · have hz := congrArg GoldenInt.b hs
        simp [hp, golden_phi_pow_b_eq_fib_index] at hz
        omega
    · rcases hs with hs | hs
      · have hz := congrArg GoldenInt.b hs
        simp [hp, golden_phi_pow_b_eq_fib_index] at hz
        omega
      · simpa [hp] using hs
  refine ⟨r, hir, hz, ?_⟩
  rw [hz]
  have he : embedding (conj (phi ^ r)) = Real.goldenConj ^ r := by
    rw [← show conjEquiv (phi ^ r) = conj (phi ^ r) from rfl, map_pow, map_pow]
    congr 1
    change embedding (conj phi) = Real.goldenConj
    rw [conj_phi, map_sub, map_one, embedding_phi]
    linarith [Real.goldenRatio_add_goldenConj]
  rw [he, show Real.goldenConj = -φ⁻¹ by rw [Real.inv_goldenRatio]; ring,
    neg_pow, inv_pow]

end D5.S1.Recurrence.KimberlingArray

