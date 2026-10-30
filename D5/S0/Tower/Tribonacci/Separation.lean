/- GID: D5/S0/Tower/Tribonacci/Separation
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Separation
   mirror-E: none(waiver:infinite-family-arithmetic-estimate)
   anchors: []
   utility: none
   digest: Distinct admissible Tribonacci conjugate coordinates separate at their natural scale. -/

import D5.S0.Tower.Tribonacci.ModelSet
import D5.S0.Tower.Tribonacci.Gaps
import D5.S0.Tower.DBonacci.Irreducibility
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The missing arithmetic fact is a uniform estimate for ALL distinct
length-Q admissible digit evaluations: integer cubic arithmetic prevents their
conjugate differences from collapsing below a fixed positive multiple of
`‖z‖ ^ Q`. The integer decoder does not supply this fact. The live proof must
bridge reversed admissible negative-power values to positive-power evaluation,
then establish a nonzero integral three-embedding norm and bound the Perron
factor. This is an infinite-family estimate, not bounded enumeration.

The method is the classical Pisot algebraic-norm separation argument. No
research novelty is asserted. The exact hypotheses are membership in the
existing Tribonacci characteristic root multiset and inequality to its Perron
root; either non-Perron root is in scope. -/

namespace D5.S0.Tower.Tribonacci.Separation

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.ModelSet
open D5.S0.Tower.Tribonacci.Binet

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "β" => tribonacciConstant

open Polynomial

private def digitPolynomial {Q : ℕ} (u : TribonacciName Q) : ℤ[X] :=
  ∑ i : Fin Q, if u.1 i then X ^ i.1 else 0

private theorem digitPolynomial_eval {R : Type*} [CommRing R]
    {Q : ℕ} (u : TribonacciName Q) (x : R) :
    (digitPolynomial u).eval₂ (Int.castRingHom R) x =
      ∑ i : Fin Q, if u.1 i then x ^ i.1 else 0 := by
  simp [digitPolynomial, eval₂_finsetSum, apply_ite]

private theorem admissible_reverse (Q : ℕ) (w : Fin Q → Bool)
    (hw : TribonacciAdmissible Q w) :
    TribonacciAdmissible Q (fun i => w i.rev) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    match Q with
    | 0 => trivial
    | 1 => trivial
    | 2 => trivial
    | n + 3 =>
      rw [admissible_add_three_iff]
      constructor
      · intro h
        have hn := D5.S0.Tower.Tribonacci.Representation.admissible_no_three_at
          (n + 3) n w hw (by omega)
        apply hn
        rcases h with ⟨h0, h1, h2⟩
        convert And.intro h2 (And.intro h1 h0) using 1 <;>
          congr 1 <;> apply Fin.ext <;> simp [Fin.rev] <;> omega
      · have hi := ih (n + 2) (by omega) (Fin.init w)
          (D5.S0.Tower.Tribonacci.Representation.admissible_init (n + 2) w hw)
        convert hi using 1
        funext i
        apply congrArg w
        apply Fin.ext
        simp [Fin.tail, Fin.init, Fin.rev]
        omega

private def reverseName {Q : ℕ} (u : TribonacciName Q) : TribonacciName Q :=
  ⟨fun i => u.1 i.rev, admissible_reverse Q u.1 u.2⟩

private theorem reverse_value {Q : ℕ} (u : TribonacciName Q) :
    tribonacciNameValue Q (reverseName u) =
      β ^ (-(Q : ℤ)) * (digitPolynomial u).eval₂ (Int.castRingHom ℝ) β := by
  rw [tribonacciNameValue, tribonacciWordValue, digitPolynomial_eval,
    Finset.mul_sum, ← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro i _
  change (if u.1 i.rev.rev then β ^ (-((i.rev.1 + 1 : ℕ) : ℤ)) else 0) = _
  rw [Fin.rev_rev]
  split_ifs
  · rw [← zpow_natCast, ← zpow_add₀ tribonacciConstant_ne_zero]
    congr 1
    simp only [Fin.val_rev]
    have hi := i.2
    omega
  · ring

private theorem digit_difference_perron_ne_zero {Q : ℕ}
    (u v : TribonacciName Q) (huv : u ≠ v) :
    (digitPolynomial u - digitPolynomial v).eval₂ (Int.castRingHom ℝ) β ≠ 0 := by
  intro h
  rw [eval₂_sub] at h
  have hv : tribonacciNameValue Q (reverseName u) =
      tribonacciNameValue Q (reverseName v) := by
    rw [reverse_value, reverse_value, sub_eq_zero.mp h]
  have hn := D5.S0.Tower.Tribonacci.Gaps.tribonacciNameValue_injective Q hv
  apply huv
  apply Subtype.ext
  funext i
  have he := congrFun (congrArg Subtype.val hn) i.rev
  simpa [reverseName] using he

private def cubic : ℤ[X] := X ^ 3 - X ^ 2 - X - 1

private theorem cubic_irreducible :
    Irreducible (cubic.map (Int.castRingHom ℚ)) := by
  convert (D5.S0.Tower.DBonacci.PerronRoot.dbonacci_irreducible 3 (by norm_num)).2
    using 1 <;> simp [cubic, Finset.sum_range_succ] <;> ring

private theorem cubic_at_perron : cubic.eval₂ (Int.castRingHom ℝ) β = 0 := by
  simp only [cubic, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
  nlinarith [tribonacciConstant_cubic]

private theorem cubic_resultant_ne_zero (p : ℤ[X])
    (hp : p.eval₂ (Int.castRingHom ℝ) β ≠ 0) : cubic.resultant p ≠ 0 := by
  have hn : ¬ cubic.map (Int.castRingHom ℚ) ∣ p.map (Int.castRingHom ℚ) := by
    rintro ⟨a, ha⟩
    apply hp
    have he := congrArg (Polynomial.eval₂ (Rat.castHom ℝ) β) ha
    simpa only [eval₂_mul, eval₂_map, RingHom.comp_intCast, cubic_at_perron,
      zero_mul] using he
  have hc := cubic_irreducible.coprime_iff_not_dvd.mpr hn
  have hr := resultant_ne_zero _ _ hc
  simpa only [resultant_map_map, natDegree_map] using hr

end D5.S0.Tower.Tribonacci.Separation
