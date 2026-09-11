/- GID: D5/S1/Recurrence/Invariants/CubedBinaryProductModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CubedBinaryProductModThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Frobenius reduction and support-halving induction prove Hanna's A373308 conjecture. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

open PowerSeries

namespace D5.S1.Recurrence.Invariants.CubedBinaryProductModThree

noncomputable def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 2),
      coeff i ((1 - X : PowerSeries ℤ) ^ 3) *
        (if 2 ∣ n + 1 - i then a ((n + 1 - i) / 2) else 0)
termination_by n => n
decreasing_by omega

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem coeff_step {R : Type*} [CommRing R] (B : PowerSeries R) (n : ℕ) :
    coeff n ((1 - X) ^ 3 * B.subst (X ^ 2)) =
      ∑ i ∈ Finset.range (n + 1), coeff i ((1 - X : PowerSeries R) ^ 3) *
        (if 2 ∣ n - i then coeff ((n - i) / 2) B else 0) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = (1 - X) ^ 3 * generatingSeries.subst (X ^ 2) := by
  have hz : constantCoeff generatingSeries = 1 := by
    simp [generatingSeries, constantCoeff_mk, a]
  refine ⟨hz, ?_⟩
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, hz]
  | succ n => simp only [coeff_step, generatingSeries, coeff_mk, a]

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = (1 - X) ^ 3 * B.subst (X ^ 2)) : B = generatingSeries := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff, generating_equation.1] using h0
    | succ n =>
      conv_lhs => rw [hB, coeff_step]
      conv_rhs => rw [generating_equation.2, coeff_step]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      split_ifs with h
      · exact ih _ (by omega)
      · rfl

-- The reduced equation sends unsupported indices to strictly smaller unsupported indices.
private theorem solution_support (B : PowerSeries (ZMod 3))
    (hB : B = (1 - X ^ 3) * B.subst (X ^ 2)) (n : ℕ) (hn : ¬ 3 ∣ n) :
    coeff n B = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst n
      exact hn (dvd_zero 3)
    have halve (m : ℕ) (hm : m ≤ n) (hm3 : ¬ 3 ∣ m) :
        coeff m (B.subst (X ^ 2 : PowerSeries (ZMod 3))) = (0 : ZMod 3) := by
      rw [coeff_subst_X_pow (by omega : 2 ≠ 0)]
      split_ifs with he
      · have hd : 2 * (m / 2) = m := Nat.mul_div_cancel' he
        have hnot : ¬ 3 ∣ m / 2 := by
          intro h3
          apply hm3
          rw [← hd]
          exact dvd_mul_of_dvd_right h3 2
        exact ih _ (by omega) hnot
      · rfl
    have he := congrArg (coeff n) hB
    rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', halve n le_rfl hn] at he
    split_ifs at he with h3
    · have hnot : ¬ 3 ∣ n - 3 := by
        intro hd
        apply hn
        have hsum := dvd_add hd (dvd_refl 3)
        simpa [Nat.sub_add_cancel h3] using hsum
      rw [halve (n - 3) (by omega) hnot, sub_zero] at he
      exact he
    · simpa using he

theorem mod_three_support (n : ℕ) (hn : ¬ 3 ∣ n) : (a n : ZMod 3) = 0 := by
  let hom := Int.castRingHom (ZMod 3)
  let B := generatingSeries.map hom
  let : CharP (PowerSeries (ZMod 3)) 3 :=
    charP_of_injective_ringHom (f := C (R := ZMod 3)) C_injective 3
  have hf : (1 - X : PowerSeries (ZMod 3)) ^ 3 = 1 - X ^ 3 := by
    rw [sub_pow_char, one_pow]
  have he : B = (1 - X ^ 3) * B.subst (X ^ 2) := by
    have h := congrArg (PowerSeries.map hom) generating_equation.2
    have hs : HasSubst (X ^ 2 : PowerSeries ℤ) := .X_pow (by omega)
    have hm : PowerSeries.map hom (generatingSeries.subst (X ^ 2 : PowerSeries ℤ)) =
        (generatingSeries.map hom).subst (PowerSeries.map hom (X ^ 2 : PowerSeries ℤ)) :=
      map_subst hs generatingSeries
    simp only [map_pow, map_X] at hm
    simpa only [map_mul, map_pow, map_sub, map_one, map_X, hm, hf] using h
  simpa [B, hom, generatingSeries, coeff_map] using solution_support B he n hn

theorem hanna_conjecture (n : ℕ) : 3 ∣ a (3 * n + 1) ∧ 3 ∣ a (3 * n + 2) := by
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    apply mod_three_support
    omega
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    apply mod_three_support
    omega

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_three_support
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CubedBinaryProductModThree
