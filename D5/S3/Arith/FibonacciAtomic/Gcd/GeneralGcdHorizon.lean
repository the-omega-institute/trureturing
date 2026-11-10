/- GID: D5/S3/Arith/FibonacciAtomic/Gcd/GeneralGcdHorizon
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Gcd/GeneralGcdHorizon
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary-modulus consecutive prefixes inherit the local Fibonacci gcd horizons. -/

import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon

/-!
# Consecutive-prefix transport for Fibonacci gcd observations

The prime and prime-power horizon theorems are local statements.  This file
packages them into the global statement needed for an arbitrary modulus: a
prefix which reaches every local prime-power horizon determines the entire gcd
future.  The proof uses the prime-power decomposition of divisors of the
modulus, so no residue-value recovery assumption is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Gcd.GeneralGcdHorizon

open D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
open D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
open D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (observe)

/-- The local number of consecutive positive readings needed at `p^e`. -/
noncomputable def localHorizon (p e : ℕ) : ℕ :=
  if e = 0 then 0
  else if e = 1 then
    if zeroRank p = p + 1 then zeroRank p - 1 else zeroRank p
  else if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then
    zeroRank (p ^ e)
  else (p - 1) * zeroRank (p ^ (e - 1))

/-- The largest local horizon among prime powers dividing `H`.

The supremum is zero for `H = 1`, matching the constant gcd future. -/
noncomputable def globalHorizon (H : ℕ) : ℕ :=
  H.primeFactors.sup (fun p => localHorizon p (H.factorization p))

private theorem signedValue_bridge (k : ℕ) (hk : 0 < k) (x : ℤ × ℤ) :
    PrimePowerGcdHorizon.signedObservation x.1 x.2 k = signedValue k x := by
  simp only [PrimePowerGcdHorizon.signedObservation, signedValue]
  rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega,
    Int.fib_natCast, Int.fib_natCast]

private theorem prime_signedValue_bridge (k : ℕ) (hk : 0 < k) (x : ℤ × ℤ) :
    PrimeGcdHorizon.signedObservation k x.1 x.2 = signedValue k x := by
  simp [PrimeGcdHorizon.signedObservation, hk.ne', signedValue,
    Int.fib_natCast]

private theorem prime_power_prefix_sound (p e T : ℕ) (hp : p.Prime)
    (he : 1 ≤ e) (hT : localHorizon p e ≤ T) :
    ∀ x y : ℤ × ℤ,
      (∀ k ∈ Finset.Icc 1 T,
        gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) →
      ∀ k, 0 < k → gcdValue (p ^ e) k x = gcdValue (p ^ e) k y := by
  intro x y hxy k hk
  by_cases hone : e = 1
  · subst e
    simp only [pow_one] at hxy ⊢
    have hlocal := PrimeGcdHorizon.sharp_prime_gcd_horizon p hp
    have hsigned :
        Nat.gcd (PrimeGcdHorizon.signedObservation k x.1 x.2).natAbs p =
          Nat.gcd (PrimeGcdHorizon.signedObservation k y.1 y.2).natAbs p := by
      refine hlocal.1 x.1 x.2 y.1 y.2 ?_ k (by omega)
      intro j hj hJ
      have hJ' : j ∈ Finset.Icc 1 T := by
        apply Finset.mem_Icc.mpr
        refine ⟨hj, ?_⟩
        have hdef : localHorizon p 1 = PrimeGcdHorizon.horizon p := by
          simp [localHorizon, PrimeGcdHorizon.horizon]
        omega
      have h := hxy j hJ'
      change Nat.gcd (signedValue j x).natAbs p = Nat.gcd (signedValue j y).natAbs p at h
      rw [← prime_signedValue_bridge j hj x, ← prime_signedValue_bridge j hj y] at h
      exact h
    change Nat.gcd (signedValue k x).natAbs p = Nat.gcd (signedValue k y).natAbs p
    rw [← prime_signedValue_bridge k hk x, ← prime_signedValue_bridge k hk y]
    exact hsigned
  · have he2 : 2 ≤ e := by omega
    have hlocal := PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p e hp he2
    have hsigned :
        Nat.gcd (PrimePowerGcdHorizon.signedObservation x.1 x.2 k).natAbs (p ^ e) =
          Nat.gcd (PrimePowerGcdHorizon.signedObservation y.1 y.2 k).natAbs (p ^ e) := by
      refine hlocal.2.2.1 x.1 x.2 y.1 y.2 ?_ k (by omega)
      intro j hj hJ
      have hJ' : j ∈ Finset.Icc 1 T := by
        apply Finset.mem_Icc.mpr
        refine ⟨hj, ?_⟩
        have hdef : localHorizon p e = PrimePowerGcdHorizon.horizon p e := by
          by_cases hs : zeroRank (p ^ e) = zeroRank (p ^ (e - 1))
          · simp only [localHorizon, PrimePowerGcdHorizon.horizon,
              if_neg (by omega : e ≠ 0), if_neg (by omega : e ≠ 1), if_pos hs]
          · simp only [localHorizon, PrimePowerGcdHorizon.horizon,
              if_neg (by omega : e ≠ 0), if_neg (by omega : e ≠ 1), if_neg hs]
            have growth : zeroRank (p ^ e) = p * zeroRank (p ^ (e - 1)) :=
              hlocal.2.1.resolve_left hs
            rw [growth]
            rw [Nat.sub_mul]
            simp
        omega
      have h := hxy j hJ'
      change Nat.gcd (signedValue j x).natAbs (p ^ e) =
        Nat.gcd (signedValue j y).natAbs (p ^ e) at h
      rw [← signedValue_bridge j hj x, ← signedValue_bridge j hj y] at h
      exact h
    change gcdValue (p ^ e) k x = gcdValue (p ^ e) k y
    change Nat.gcd (signedValue k x).natAbs (p ^ e) =
      Nat.gcd (signedValue k y).natAbs (p ^ e)
    rw [← signedValue_bridge k hk x, ← signedValue_bridge k hk y]
    exact hsigned

/-- Divisors of a positive modulus are determined by their prime-power parts. -/
private theorem gcd_ext (H a b : ℕ) (hH : 0 < H) (ha : a ∣ H) (hb : b ∣ H)
    (hreads : ∀ p : ℕ, p.Prime →
      Nat.gcd a (p ^ H.factorization p) = Nat.gcd b (p ^ H.factorization p)) :
    a = b := by
  apply Nat.dvd_antisymm
  all_goals
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p j hp hj
    have hjP := (hp.pow_dvd_iff_dvd_ordProj hH.ne').mp
      (dvd_trans hj (by assumption))
    have hiff := Nat.gcd_left_eq_iff.mp (hreads p hp) (p ^ j) hjP
    first | exact hiff.mp hj | exact hiff.mpr hj

theorem gcd_value_consecutive_prefix (H T : ℕ) (hH : 0 < H)
    (hT : ∀ p : ℕ, p.Prime → 1 ≤ H.factorization p →
      localHorizon p (H.factorization p) ≤ T) :
    Identifies (gcdValue H) (Finset.Icc 1 T) := by
  intro x y hxy k hk
  apply gcd_ext H (gcdValue H k x) (gcdValue H k y) hH
    (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  intro p hp
  by_cases hz : H.factorization p = 0
  · simp [hz]
  let e := H.factorization p
  have he : 1 ≤ e := by dsimp [e]; omega
  have hlocal := prime_power_prefix_sound p e T hp he (hT p hp he)
  have hprefix : ∀ j ∈ Finset.Icc 1 T,
      gcdValue (p ^ e) j x = gcdValue (p ^ e) j y := by
    intro j hj
    have h := hxy j hj
    have hcomponent (z : ℤ × ℤ) :
        Nat.gcd (gcdValue H j z) (p ^ e) = gcdValue (p ^ e) j z := by
      dsimp [e]
      simp only [gcdValue]
      rw [Nat.gcd_assoc, Nat.gcd_eq_right (Nat.ordProj_dvd H p)]
    rw [← hcomponent x, ← hcomponent y, h]
  have hall := hlocal x y hprefix k hk
  have hcomponent (z : ℤ × ℤ) :
      Nat.gcd (gcdValue H k z) (p ^ e) = gcdValue (p ^ e) k z := by
    dsimp [e]
    simp only [gcdValue]
    rw [Nat.gcd_assoc, Nat.gcd_eq_right (Nat.ordProj_dvd H p)]
  have hcomponent' (z : ℤ × ℤ) :
      Nat.gcd (gcdValue H k z) (p ^ H.factorization p) =
        gcdValue (p ^ H.factorization p) k z := by
    simpa [e] using hcomponent z
  rw [hcomponent' x, hcomponent' y, hall]

theorem actual_gcd_consecutive_prefix (H T : ℕ) (hH : 0 < H)
    (hT : ∀ p : ℕ, p.Prime → 1 ≤ H.factorization p →
      localHorizon p (H.factorization p) ≤ T) :
    Identifies (actualGcd H) (Finset.Icc 1 T) := by
  intro v w hvw k hk
  have hactual (j : ℕ) (hj : 0 < j) (u : ℕ × ℕ) :
      actualGcd H j u = gcdValue H j ((observe u).1, (observe u).2) := by
    have h := congrArg (fun z : ℤ => Nat.gcd z.natAbs H)
      (actual_signed_quantity j u hj)
    simpa [actualGcd, gcdValue] using h
  have hsigned :
      (∀ j ∈ Finset.Icc 1 T,
        gcdValue H j ((observe v).1, (observe v).2) =
          gcdValue H j ((observe w).1, (observe w).2)) := by
    intro j hj
    exact (hactual j (Finset.mem_Icc.mp hj).1 v).symm.trans
      ((hvw j hj).trans (hactual j (Finset.mem_Icc.mp hj).1 w))
  have hfuture := gcd_value_consecutive_prefix H T hH hT
    ((observe v).1, (observe v).2) ((observe w).1, (observe w).2) hsigned k hk
  exact (hactual k hk v).trans (hfuture.trans (hactual k hk w).symm)

theorem actual_gcd_global_prefix (H T : ℕ) (hH : 0 < H)
    (hT : globalHorizon H ≤ T) :
    Identifies (actualGcd H) (Finset.Icc 1 T) := by
  apply actual_gcd_consecutive_prefix H T hH
  intro p hp he
  have hpdvd : p ∣ H :=
    Nat.dvd_of_factorization_pos (by omega : H.factorization p ≠ 0)
  have hmem : p ∈ H.primeFactors :=
    (Nat.mem_primeFactors).2 ⟨hp, hpdvd, hH.ne'⟩
  exact (Finset.le_sup hmem).trans hT

end D5.S3.Arith.FibonacciAtomic.Gcd.GeneralGcdHorizon
