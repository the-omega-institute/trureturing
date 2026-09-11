/- GID: D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral cubic cancellation and residue support prove Hanna's A363560 conjecture. -/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

open PowerSeries

namespace D5.S1.Recurrence.Invariants.CubicNinthPowerSubstitutionModThree

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private noncomputable def polynomial (f : PowerSeries R) : PowerSeries R :=
  f - f ^ 3 + f ^ 4 - f ^ 6 + f ^ 7

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  1 + X * polynomial f

private theorem step_agree {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (step f) (step g) := by
  intro n hn
  cases n with
  | zero => simp [step]
  | succ n =>
    have hnd : n < d := by omega
    simp [step, polynomial, h n hnd, agree_pow h 3 n hnd,
      agree_pow h 4 n hnd, agree_pow h 6 n hnd, agree_pow h 7 n hnd]

private theorem fixed_unique {f g : PowerSeries R}
    (hf : f = step f) (hg : g = step g) : f = g := by
  have hall : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← hf, ← hg] using step_agree ih
  ext n
  exact hall (n + 1) n (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 1
  | k + 1 => step (approximation k)

private theorem approximation_stable {d k : ℕ} (h : d ≤ k) :
    Agree d (approximation (R := R) d) (approximation k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree (ih (by omega))

noncomputable def a (n : ℕ) : ℤ :=
  coeff n (approximation (R := ℤ) (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) :
    Agree d generatingSeries (approximation d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext n
  have hg := generating_agree (n + 2) n (by omega)
  have hs := step_agree (generating_agree (n + 1)) n (by omega)
  exact hg.trans hs.symm

theorem cubic_iff_fixed (B : PowerSeries ℤ) (h0 : constantCoeff B = 1) :
    B ^ 3 = 1 + X * (B + B ^ 2 + B ^ 9) ↔
      B = 1 + X * (B - B ^ 3 + B ^ 4 - B ^ 6 + B ^ 7) := by
  have factorization : B + B ^ 2 + B ^ 9 = (B ^ 2 + B + 1) * polynomial B := by
    dsimp [polynomial]
    ring
  have hne : B ^ 2 + B + 1 ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [h0] at hc
  constructor
  · intro he
    have hz : (B ^ 2 + B + 1) * (B - 1 - X * polynomial B) = 0 := by
      rw [factorization] at he
      linear_combination he
    have hc := (mul_eq_zero.mp hz).resolve_left hne
    dsimp [polynomial] at hc
    linear_combination hc
  · intro he
    rw [factorization]
    change B = 1 + X * polynomial B at he
    linear_combination (B ^ 2 + B + 1) * he

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries ^ 3 =
      1 + X * (generatingSeries + generatingSeries ^ 2 + generatingSeries ^ 9) := by
  have h0 : constantCoeff generatingSeries = 1 := by
    have h := congrArg constantCoeff generating_fixed
    simpa [step] using h
  exact ⟨h0, (cubic_iff_fixed generatingSeries h0).mpr generating_fixed⟩

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B ^ 3 = 1 + X * (B + B ^ 2 + B ^ 9)) : B = generatingSeries :=
  fixed_unique ((cubic_iff_fixed B h0).mp hB) generating_fixed

private theorem polynomial_mod_three (B : PowerSeries (ZMod 3)) :
    polynomial (1 + B) = 1 + B ^ 7 := by
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from rfl, map_zero]
  dsimp [polynomial]
  linear_combination (B + 3 * B ^ 2 + 6 * B ^ 3 + 7 * B ^ 4 +
    5 * B ^ 5 + 2 * B ^ 6) * h3

-- Below a fixed degree, convolution adds the residue classes of the factors.
private theorem power_support_below (B : PowerSeries R) (d : ℕ)
    (hB : ∀ i < d, i % 7 ≠ 1 → coeff i B = 0) (k : ℕ) :
    ∀ m < d, m % 7 ≠ k % 7 → coeff m (B ^ k) = 0 := by
  induction k with
  | zero =>
    intro m hm hmod
    have hm0 : m ≠ 0 := by intro he; subst m; simp at hmod
    simp [hm0]
  | succ k ih =>
    intro m hm hmod
    rw [pow_succ, coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_antidiagonal.mp hp
    by_cases hleft : p.1 % 7 = k % 7
    · have hright : p.2 % 7 ≠ 1 := by
        intro hr
        apply hmod
        rw [← hp', Nat.add_mod, hleft, hr, Nat.add_mod k 1]
      rw [hB p.2 (by omega) hright, mul_zero]
    · rw [ih p.1 (by omega) hleft, zero_mul]

private theorem reduced_support (B : PowerSeries (ZMod 3))
    (he : B = X * (1 + B ^ 7)) : ∀ n, n % 7 ≠ 1 → coeff n B = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero =>
      have hc := congrArg (coeff 0) he
      simpa using hc
    | succ m =>
      have hm : m % 7 ≠ 0 := by omega
      have hp : coeff m (B ^ 7) = 0 :=
        power_support_below B (m + 1) ih 7 m (by omega) (by simpa using hm)
      have hm0 : m ≠ 0 := by omega
      have hc := congrArg (coeff (m + 1)) he
      simpa [hp, hm0] using hc

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) (h7 : n % 7 ≠ 1) : 3 ∣ a n := by
  let hom := Int.castRingHom (ZMod 3)
  let A := generatingSeries.map hom
  let B := A - 1
  have hf := (cubic_iff_fixed generatingSeries generating_equation.1).mp
    generating_equation.2
  have hm := congrArg (PowerSeries.map hom) hf
  have hA : A = 1 + X * polynomial A := by
    simpa [A, polynomial] using hm
  have hAB : A = 1 + B := by dsimp [B]; ring
  have hB : B = X * (1 + B ^ 7) := by
    rw [hAB, polynomial_mod_three] at hA
    linear_combination hA
  have hc := reduced_support B hB n h7
  have hz : (a n : ZMod 3) = 0 := by
    simpa [B, A, hom, generatingSeries, show n ≠ 0 by omega] using hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 3).mp hz

#print axioms cubic_iff_fixed
#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CubicNinthPowerSubstitutionModThree
