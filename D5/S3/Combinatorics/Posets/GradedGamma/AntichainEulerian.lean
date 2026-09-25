/- GID: D5/S3/Combinatorics/Posets/GradedGamma/AntichainEulerian
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/AntichainEulerian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Derivative]
   utility: none
   digest: The antichain descent enumerator satisfies the constructive Eulerian recurrence. -/

import D5.S3.Combinatorics.Posets.GradedGamma.EulerianRecurrence
import D5.S3.Combinatorics.Posets.PPartitions.Series
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
open Polynomial
noncomputable section

private def powerSum (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun q => ((q + 1) ^ (n + 1) : ℤ)

private def oneSubX : PowerSeries ℤ := 1 - PowerSeries.X

private theorem powerSum_step (n : ℕ) :
    powerSum (n + 1) = powerSum n +
      PowerSeries.X * (PowerSeries.derivative ℤ) (powerSum n) := by
  ext q
  cases q with
  | zero =>
      simp only [powerSum, PowerSeries.coeff_mk, map_add]
      rw [← pow_one (PowerSeries.X : PowerSeries ℤ),
        PowerSeries.coeff_X_pow_mul']
      norm_num
  | succ q =>
      simp only [powerSum, PowerSeries.coeff_mk, map_add]
      rw [← pow_one (PowerSeries.X : PowerSeries ℤ),
        PowerSeries.coeff_X_pow_mul', if_pos (by omega : 1 ≤ q + 1),
        PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
      push_cast
      ring

private theorem eulerian_power_sum (n : ℕ) :
    powerSum n * oneSubX ^ (n + 2) =
      (eulerianRecurrence n : PowerSeries ℤ) := by
  induction n with
  | zero =>
      have hs : powerSum 0 = (PowerSeries.invOneSubPow ℤ 2).val := by
        rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
        ext q
        simp [powerSum, Nat.choose_one_right, Nat.add_comm]
      simp only [eulerianRecurrence, Nat.zero_add]
      rw [hs, show oneSubX ^ 2 = (PowerSeries.invOneSubPow ℤ 2).inv from
        (PowerSeries.invOneSubPow_inv_eq_one_sub_pow ℤ 2).symm]
      simpa using (PowerSeries.invOneSubPow ℤ 2).val_inv
  | succ n ih =>
      let D := PowerSeries.derivative ℤ
      have hu : D oneSubX = -1 := by
        simp [D, oneSubX, map_sub, PowerSeries.derivative_X]
      have hd : D (powerSum n * oneSubX ^ (n + 2)) =
          powerSum n * (((n + 2 : ℤ) : PowerSeries ℤ) *
            oneSubX ^ (n + 1) * (-1)) +
            oneSubX ^ (n + 2) * D (powerSum n) := by
        rw [Derivation.leibniz, PowerSeries.derivative_pow, hu]
        simp [smul_eq_mul, mul_comm]
      have hpow : oneSubX ^ (n + 2) = oneSubX ^ (n + 1) * oneSubX := by
        rw [← pow_succ]
      have hrec : (eulerianRecurrence (n + 1) : PowerSeries ℤ) =
          (1 + (((n + 1 : ℤ) : PowerSeries ℤ) * PowerSeries.X)) *
              (eulerianRecurrence n : PowerSeries ℤ) +
            PowerSeries.X * oneSubX *
              (Polynomial.derivative (eulerianRecurrence n) : PowerSeries ℤ) := by
        simp [eulerianRecurrence, oneSubX, map_add]
        left
        change Polynomial.coeToPowerSeries.ringHom (n : Polynomial ℤ) =
          (n : PowerSeries ℤ)
        exact map_natCast _ n
      rw [hrec]
      rw [← ih]
      rw [← PowerSeries.derivative_coe (eulerianRecurrence n)]
      rw [← ih]
      change powerSum (n + 1) * oneSubX ^ (n + 1 + 2) = _
      rw [powerSum_step]
      rw [show n + 1 + 2 = n + 2 + 1 by omega, pow_succ, hd]
      rw [hpow]
      dsimp [oneSubX]
      push_cast
      ring

/-- For any finite antichain, the actual descent sum over all extensions is the
Eulerian polynomial obtained from the insertion recurrence. -/
theorem antichain_W_eulerian {α : Type*} [Fintype α] [PartialOrder α]
    (hdisc : ∀ x y : α, x ≤ y → x = y)
    (ω : α → ℕ) (hω : Function.Injective ω)
    (n : ℕ) (hcard : Fintype.card α = n + 1) :
    WPolynomial ω = eulerianRecurrence n := by
  classical
  have hcount (q : ℕ) :
      Fintype.card (PPartition ω (q + 1)) = (q + 1) ^ (n + 1) := by
    let e : PPartition ω (q + 1) ≃ (α → Fin (q + 1)) := {
      toFun := Subtype.val
      invFun := fun f => ⟨f, by
        constructor
        · intro x y hxy
          rw [hdisc x y hxy]
        · intro x y hxy _
          exact False.elim (hxy.ne (hdisc x y hxy.le))⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro f; rfl }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, hcard]
  have hseries : powerSum n =
      (WPolynomial ω : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (n + 2)).val := by
    have hp := pPartition_series ω hω
    rw [hcard, show n + 1 + 1 = n + 2 by omega] at hp
    calc
      powerSum n = PowerSeries.mk (fun q =>
          (Fintype.card (PPartition ω (q + 1)) : ℤ)) := by
            ext q
            simp [powerSum, hcount q]
      _ = _ := hp
  have hW : powerSum n * oneSubX ^ (n + 2) =
      (WPolynomial ω : PowerSeries ℤ) := by
    rw [hseries, oneSubX, mul_assoc,
      ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    rw [Units.val_inv, mul_one]
  apply Polynomial.ext
  intro k
  have heq := hW.symm.trans (eulerian_power_sum n)
  simpa only [Polynomial.coeff_coe] using congrArg (PowerSeries.coeff k) heq

end
end D5.S3.Combinatorics.Posets.GradedGamma
