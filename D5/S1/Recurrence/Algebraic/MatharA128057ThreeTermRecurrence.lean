/- GID: D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: The three-term recurrence for the normalized square-root quotient A128057. -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic

/-! The normalized square root of 1+4X² is unique over the rationals.
Its unit inverse defines the source generating function (1+X)/sqrt(1+4X²).
All polynomial scalars are rational; lagged coefficient indices are natural.
The recurrence includes every n ≥ 2, the legal-lag offset-zero interpretation. -/

set_option autoImplicit false

noncomputable section
open PowerSeries
namespace D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence

private def cat : PowerSeries ℚ := rescale (-1) (catalanSeries.map (Nat.castRingHom ℚ))
private def baseRoot : PowerSeries ℚ := 1 + 2 * X * cat
private def baseInv : PowerSeries ℚ := derivative (X * cat)
private def sourceRoot : PowerSeries ℚ := expand 2 (by decide) baseRoot
private def sourceSeries : PowerSeries ℚ := (1 + X) * invOfUnit sourceRoot 1
private def a (n : ℕ) : ℚ := coeff n sourceSeries
private def b (n : ℕ) : ℚ := (-1) ^ n * (Nat.centralBinom n : ℚ)

private theorem cat_eq : X * cat ^ 2 + cat = 1 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  have h' := congrArg (rescale (-1 : ℚ)) h
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X,
    rescale_neg_one_X] at h'
  change cat ^ 2 * -X + 1 = cat at h'
  linear_combination -h'

private theorem root_eq : constantCoeff sourceRoot = 1 ∧ sourceRoot ^ 2 = 1 + 4 * X ^ 2 := by
  have h : baseRoot ^ 2 = 1 + 4 * X := by
    dsimp [baseRoot]
    linear_combination 4 * X * cat_eq
  have he := congrArg (expand 2 (by decide) : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ) h
  constructor
  · simp [sourceRoot, baseRoot]
  · simpa [sourceRoot, expand_X, map_ofNat] using he

private theorem root_unique (r : PowerSeries ℚ) (hc : constantCoeff r = 1)
    (hs : r ^ 2 = 1 + 4 * X ^ 2) : r = sourceRoot := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans root_eq.2.symm) with h | h
  · exact h
  · have he := congrArg (constantCoeff (R := ℚ)) h
    simp only [map_neg, hc, root_eq.1] at he
    norm_num at he

private theorem base_inverse : baseRoot * baseInv = 1 := by
  have hd := congrArg (derivative (R := ℚ)) cat_eq
  simp only [map_add, derivative_one, Derivation.leibniz, derivative_pow,
    derivative_X, smul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] at hd
  dsimp [baseRoot, baseInv]
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul, mul_one]
  linear_combination X * hd + cat_eq

private theorem bridge : sourceSeries = (1 + X) * expand 2 (by decide) baseInv := by
  have he := congrArg (expand 2 (by decide) : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ) base_inverse
  have hinv : sourceRoot * invOfUnit sourceRoot 1 = 1 :=
    mul_invOfUnit _ _ (by simpa using root_eq.1)
  have hb : expand 2 (by decide) baseInv = invOfUnit sourceRoot 1 := by
    calc
      _ = expand 2 (by decide) baseInv * (sourceRoot * invOfUnit sourceRoot 1) := by rw [hinv, mul_one]
      _ = (sourceRoot * expand 2 (by decide) baseInv) * invOfUnit sourceRoot 1 := by ring
      _ = invOfUnit sourceRoot 1 := by
        have hh : sourceRoot * expand 2 (by decide) baseInv = 1 := by simpa [sourceRoot] using he
        rw [hh, one_mul]
  rw [sourceSeries, hb]

private theorem base_coeff (m : ℕ) : coeff m baseInv = b m := by
  rw [baseInv, coeff_derivative]
  have hx : coeff (m + 1) (X * cat) = coeff m cat := by
    simpa only [pow_one] using coeff_X_pow_mul cat 1 m
  rw [hx]
  simp only [cat, coeff_rescale, coeff_map, catalanSeries_coeff, b]
  have h : ((m : ℚ) + 1) * (catalan m : ℚ) = (Nat.centralBinom m : ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom m
  push_cast
  linear_combination (-1 : ℚ) ^ m * h

private theorem paired (m : ℕ) : a (2 * m) = b m ∧ a (2 * m + 1) = b m := by
  have read_succ (j : ℕ) : a (j + 1) =
      (if 2 ∣ j + 1 then b ((j + 1) / 2) else 0) +
      (if 2 ∣ j then b (j / 2) else 0) := by
    simp only [a, bridge, add_mul, one_mul, map_add, coeff_succ_X_mul,
      coeff_expand, base_coeff]
  constructor
  · cases m with
    | zero =>
      have hz : a 0 = coeff 0 baseInv := by simp [a, bridge]
      exact hz.trans (base_coeff 0)
    | succ k =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, read_succ]
      have he : 2 ∣ 2 * k + 1 + 1 := by omega
      have ho : ¬ 2 ∣ 2 * k + 1 := by omega
      simp [he, ho, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  · rw [read_succ]
    have he : 2 ∣ 2 * m := by omega
    have ho : ¬ 2 ∣ 2 * m + 1 := by omega
    simp [he, ho]

private theorem adjacent (m : ℕ) :
    ((m : ℚ) + 1) * b (m + 1) + 2 * (2 * m + 1) * b m = 0 := by
  have h : ((m : ℚ) + 1) * (Nat.centralBinom (m + 1) : ℚ) =
      2 * (2 * m + 1) * (Nat.centralBinom m : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  simp only [b, pow_succ]
  linear_combination -(-1 : ℚ) ^ m * h

private theorem recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℚ) * (5 * n - 9) * a n + 4 * a (n - 1) +
      4 * (5 * (n : ℚ) - 4) * (n - 2) * a (n - 2) = 0 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul m] at hn ⊢
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) - 2 = 2 * k by omega,
      (paired (k + 1)).1, (paired k).2, (paired k).1]
    push_cast
    linear_combination 2 * (10 * (k : ℚ) + 1) * adjacent k
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) + 1 - 1 = 2 * (k + 1) by omega,
      show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega,
      (paired (k + 1)).2, (paired (k + 1)).1, (paired k).2]
    push_cast
    linear_combination 2 * (10 * (k : ℚ) + 11) * adjacent k

theorem result :
    (∃! S : PowerSeries ℚ, constantCoeff S = 1 ∧ S ^ 2 = 1 + 4 * X ^ 2) ∧
    ∀ S : PowerSeries ℚ, constantCoeff S = 1 → S ^ 2 = 1 + 4 * X ^ 2 →
      constantCoeff S⁻¹ = 1 ∧ S * S⁻¹ = 1 ∧ S⁻¹ * S = 1 ∧
      let A := (1 + X) * S⁻¹
      let a : ℕ → ℚ := fun n => coeff n A
      ∀ n : ℕ, 2 ≤ n →
        (n : ℚ) * (5 * n - 9) * a n + 4 * a (n - 1) +
          4 * (5 * (n : ℚ) - 4) * (n - 2) * a (n - 2) = 0 := by
  refine ⟨⟨sourceRoot, root_eq, fun r hr => root_unique r hr.1 hr.2⟩, ?_⟩
  intro S hc hs
  refine ⟨?_, PowerSeries.mul_inv_cancel S (by rw [hc]; norm_num),
    PowerSeries.inv_mul_cancel S (by rw [hc]; norm_num), ?_⟩
  · rw [constantCoeff_inv, hc]; norm_num
  · have he : S = sourceRoot := root_unique S hc hs
    subst S
    have hi : invOfUnit sourceRoot 1 = sourceRoot⁻¹ :=
      invOfUnit_eq' _ _ (by simpa using root_eq.1)
    dsimp only
    intro n hn
    simpa only [a, sourceSeries, hi] using recurrence n hn

end D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence
