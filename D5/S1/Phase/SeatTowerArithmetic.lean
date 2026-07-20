/- GID: D5/S1/Phase/SeatTowerArithmetic
   generality: G
   mirror-B: D5/B/S1/Phase/SeatTowerArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Arithmetic reductions for the seat-tower selector, W3 walk, pin gate, and floor. -/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S1.Phase.SeatTowerArithmetic

/-- A multiple of twelve has only the two selector residues modulo twenty-four. -/
theorem mod_twenty_four_eq_zero_or_twelve (psi q : ℤ) (hpsi : psi = 12 * q) :
    psi % 24 = 0 ∨ psi % 24 = 12 := by
  omega

/-- The mod-twenty-four selector is exactly the parity of the quotient by twelve. -/
theorem twenty_four_dvd_iff_even_quotient (psi q : ℤ) (hpsi : psi = 12 * q) :
    (24 : ℤ) ∣ psi ↔ Even q := by
  rw [hpsi]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega

/-- Substituting the Barkan-Hickerson-Knuth identity into the Rademacher
relation gives the W3 walk formula with its endpoint correction. -/
theorem bhk_implies_w3_walk
    (s alt left right left' right' c phi : ℚ) (hc : c ≠ 0)
    (hBHK : 12 * s = -3 + (left' + right') / c - alt)
    (hPhi : phi = (left + right) / c - 12 * s) :
    phi = 3 + alt + ((left + right) - (left' + right')) / c := by
  field_simp [hc] at hBHK hPhi ⊢
  linarith

/-- The Pythagorean input gate is the scaled Eisenstein norm equation. -/
theorem pythagorean_gate_iff_eisenstein_norm (beta gamma0 m : ℤ) :
    (gamma0 - 2 * beta) ^ 2 + 3 * gamma0 ^ 2 = 4 * m * (m + 1) ↔
      beta ^ 2 - beta * gamma0 + gamma0 ^ 2 = m * (m + 1) := by
  constructor <;> intro h <;> nlinarith

/-- A nonzero member of the mod-twelve class has absolute value at least twelve. -/
theorem twelve_le_abs_of_dvd_of_ne_zero (psi : ℤ)
    (hdiv : (12 : ℤ) ∣ psi) (hne : psi ≠ 0) :
    (12 : ℤ) ≤ |psi| := by
  rcases hdiv with ⟨q, rfl⟩
  have hq : q ≠ 0 := by
    intro hzero
    apply hne
    simp [hzero]
  calc
    (12 : ℤ) = 12 * 1 := by norm_num
    _ ≤ 12 * |q| := by
      gcongr
      exact Int.one_le_abs hq
    _ = |12 * q| := by norm_num [abs_mul]

end D5.S1.Phase.SeatTowerArithmetic
