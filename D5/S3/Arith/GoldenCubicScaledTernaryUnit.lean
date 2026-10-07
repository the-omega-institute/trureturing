/- GID: D5/S3/Arith/GoldenCubicScaledTernaryUnit
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenCubicScaledTernaryUnit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native ternary Lucas layers have exact three-adic depth and alternating scaled units. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import D5.S1.Scale.FibLucasDouble
import D5.S1.Scale.LucasDoubling
import D5.S3.Arith.CloitreFibFourThreeAdicValuationSigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenCubicScaledTernaryUnit

open D5.S1.Scale D5.S0.Carrier

/-- The actual Lucas layer `L_(3^j)^2 + 2` has three-adic valuation `j + 1`.
Its exact integer quotient by `3^(j+1)` has residue `(-1)^j` modulo three.
The scaled unit is constructed by induction along the native cubic Lucas recurrence. -/
theorem golden_cubic_scaled_ternary_unit : ∀ j : ℕ, 1 ≤ j →
    let A : ℤ := goldenLucas (3 ^ j) ^ 2 + 2
    padicValInt 3 A = j + 1 ∧
      (((A / (3 : ℤ) ^ (j + 1) : ℤ) : ZMod 3) = (-1 : ZMod 3) ^ j) := by
  intro j hj
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let A (k : ℕ) : ℤ := goldenLucas (3 ^ k) ^ 2 + 2
  have hrec (k : ℕ) : A (k + 1) = A k * ((A k) ^ 2 - 3) := by
    by_cases hk : k = 0
    · subst k
      norm_num [A, goldenLucas, trace, phi, pow_succ]
    · have hs := (golden_cubic_lucas_block k (by omega)).2.2.2.2.2
      dsimp [A]
      rw [hs]
      ring
  have hunit : ∀ k : ℕ, ∃ u : ℤ,
      A k = (3 : ℤ) ^ (k + 1) * u ∧ (u : ZMod 3) = (-1 : ZMod 3) ^ k := by
    intro k
    induction k with
    | zero =>
        refine ⟨1, ?_, ?_⟩
        · norm_num [A, goldenLucas, trace, phi]
        · norm_num
    | succ k ih =>
        obtain ⟨u, hu, hc⟩ := ih
        let v : ℤ := u * (3 * ((3 : ℤ) ^ k) ^ 2 * u ^ 2 - 1)
        refine ⟨v, ?_, ?_⟩
        · rw [show k.succ + 1 = (k + 1) + 1 by omega, hrec, hu]
          dsimp [v]
          rw [pow_succ, pow_succ]
          ring
        · dsimp [v]
          push_cast
          rw [show (3 : ZMod 3) = 0 by decide]
          simp only [zero_mul, zero_sub, mul_neg, mul_one]
          rw [hc, pow_succ]
          ring
  have hodd : Odd (3 ^ j) := (by decide : Odd (3 : ℕ)).pow
  have hFn : (Nat.fib (3 ^ j) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.mpr (by positivity : 0 < 3 ^ j)).ne'
  have hLmod : (goldenLucas (3 ^ j) : ZMod 3) = 1 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 72) (ZMod 3))
      (golden_cubic_lucas_block j hj).1
    norm_num [map_intCast] at h ⊢
    exact h
  have hLnot : ¬ (3 : ℤ) ∣ goldenLucas (3 ^ j) := by
    intro hd
    have hz : (goldenLucas (3 ^ j) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    rw [hLmod] at hz
    norm_num at hz
  have hLne : goldenLucas (3 ^ j) ≠ 0 := by
    intro hz
    apply hLnot
    rw [hz]
    exact dvd_zero 3
  have hcop : Nat.Coprime (3 ^ j) 4 := (by decide : Nat.Coprime 3 4).pow_left j
  have hcopFib : Nat.Coprime (Nat.fib (3 ^ j)) 3 := by
    change Nat.gcd (Nat.fib (3 ^ j)) 3 = 1
    calc
      Nat.gcd (Nat.fib (3 ^ j)) 3 = Nat.gcd (Nat.fib (3 ^ j)) (Nat.fib 4) := by norm_num
      _ = Nat.fib (Nat.gcd (3 ^ j) 4) := (Nat.fib_gcd _ _).symm
      _ = 1 := by rw [hcop.gcd_eq_one]; norm_num
  have hFnot : ¬ (3 : ℤ) ∣ (Nat.fib (3 ^ j) : ℤ) := by
    exact_mod_cast (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mp hcopFib.symm
  have hAne : A j ≠ 0 := by
    dsimp [A]
    positivity
  have hF4 : (Nat.fib (4 * 3 ^ j) : ℤ) =
      ((Nat.fib (3 ^ j) : ℤ) * goldenLucas (3 ^ j)) * A j := by
    rw [show 4 * 3 ^ j = 2 * (2 * 3 ^ j) by omega,
      golden_fib_two_mul_eq_fib_mul_lucas, golden_fib_two_mul_eq_fib_mul_lucas,
      golden_lucas_two_mul, hodd.neg_one_pow]
    dsimp [A]
    ring
  have hvalF4 : padicValNat 3 (Nat.fib (4 * 3 ^ j)) = j + 1 := by
    have h := (D5.S3.Arith.CloitreFibFourThreeAdicValuationSigma.result
      (3 ^ j) (by positivity)).1
    unfold D5.S3.Arith.CloitreFibFourThreeAdicValuationSigma.a at h
    have he := Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) h
    simpa only [padicValNat.prime_pow] using he
  have hval : padicValInt 3 (A j) = j + 1 := by
    have h : padicValInt 3 (Nat.fib (4 * 3 ^ j) : ℤ) = j + 1 := by
      simpa only [padicValInt.of_nat] using hvalF4
    rw [hF4, padicValInt.mul (mul_ne_zero hFn hLne) hAne,
      padicValInt.mul hFn hLne,
      padicValInt.eq_zero_of_not_dvd hFnot,
      padicValInt.eq_zero_of_not_dvd hLnot] at h
    simpa using h
  obtain ⟨u, hu, hc⟩ := hunit j
  have hquot : A j / (3 : ℤ) ^ (j + 1) = u := by
    rw [hu]
    exact Int.mul_ediv_cancel_left u (by positivity)
  exact ⟨hval, by change ((A j / (3 : ℤ) ^ (j + 1) : ℤ) : ZMod 3) = _; rw [hquot]; exact hc⟩

end D5.S3.Arith.GoldenCubicScaledTernaryUnit
