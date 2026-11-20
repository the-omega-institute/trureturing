/- GID: D5/S3/Arith/Primes/GoldenCubicClockCofinality
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicClockCofinality
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Native cubic Lucas observation periods retain every positive time modulus. -/

import D5.S3.Arith.Primes.GoldenCubicBlockSignedRankClock
import D5.S3.Arith.Primes.GoldenCubicBlockTailPeriodClosed
import D5.S3.Arith.Primes.GoldenCubicPrimitiveTernaryPrime

set_option autoImplicit false

/-! Own-prime and cross-prime growth give divisibility cofinality. -/

namespace D5.S3.Arith.Primes.GoldenCubicClockCofinality
open GoldenCubicBlockSignedRankClock GoldenCubicBlockThreeAdic
open ModularOrbitTransientComposition GoldenCubicSignedOrder
open GoldenCubicBlockTailPeriodClosed FiniteFibonacciRankClosure

/-- The eventual periods of nested observation moduli are nested in divisibility. -/
theorem period_dvd_of_modulus_dvd (r s : OrbitRule) (f : ℕ → ℤ)
    (hr : r.Exact f) (hs : s.Exact f) (hd : r.modulus ∣ s.modulus) (ht : 0 < s.period) :
    r.period ∣ s.period := by
  let m := s.transient
  have hc := (hs (m+s.period) m (by omega)).mpr ⟨le_rfl, by simp⟩
  have hdiv : (r.modulus:ℤ) ∣ (s.modulus:ℤ) := by exact_mod_cast hd
  have h := (hr (m+s.period) m (by omega)).mp (hc.of_dvd hdiv)
  simpa only [Nat.add_sub_cancel_left] using h.2

theorem native_period_dvd_of_modulus_dvd (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hd : M ∣ N) : (nativeModulusRule M).period ∣ (nativeModulusRule N).period := by
  obtain ⟨hm, _, he⟩ := native_modulus_rule_spec M hM
  obtain ⟨hn, hNpos, ne⟩ := native_modulus_rule_spec N hN
  exact period_dvd_of_modulus_dvd _ _ cubicBlock he ne (by rwa [hm,hn]) hNpos

theorem local_period_dvd_native (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    (nativePrimePowerRule p b).period ∣ (nativeModulusRule (p^b)).period := by
  obtain ⟨hm, _, he⟩ := nativePrimePowerRule_spec p b hp hb
  obtain ⟨hn, ht, he'⟩ := native_modulus_rule_spec (p^b) (pow_pos hp.pos _)
  exact period_dvd_of_modulus_dvd _ _ cubicBlock he he' (by rw [hm,hn]) ht

/-- A full signed return reduces to a squared return on every divisor. -/
theorem square_order_dvd_signed (Q R : ℕ) (hQ : (3:ℕ).Coprime Q) (hR : R ∣ Q) :
    orderOf (9 : ZMod R) ∣ signedOrder 3 Q hQ := by
  let t := signedOrder 3 Q hQ
  have hh := (signedOrder_dvd_iff_modEq 3 Q t hQ).mp (dvd_rfl : t ∣ t)
  have hR' : (R:ℤ) ∣ (Q:ℤ) := by exact_mod_cast hR
  apply orderOf_dvd_of_pow_eq_one
  have hs : (3:ZMod R)^t = 1 ∨ (3:ZMod R)^t = -1 := by
    rcases hh with hh | hh
    · left
      have h := (ZMod.intCast_eq_intCast_iff _ _ R).mpr (hh.of_dvd hR')
      push_cast at h
      exact h
    · right
      have h := (ZMod.intCast_eq_intCast_iff _ _ R).mpr (hh.of_dvd hR')
      push_cast at h
      exact h
  have h9 : (9:ZMod R)^t = ((3:ZMod R)^t)^2 := by
    rw [show (9:ZMod R) = (3:ZMod R)^2 by ring, ← pow_mul, Nat.mul_comm, pow_mul]
  rw [h9]
  rcases hs with hs | hs <;> simp [hs]

/-- The observer can force an arbitrarily high own-prime power into the signed modulus. -/
theorem large_prime_signed_modulus_precision (p c : ℕ) :
    p^c ∣ rankSignedModulus p (2*padicValNat p (Nat.fib (fibonacciRank p))+c) := by
  dsimp only [rankSignedModulus]
  split_ifs
  · have hh : (2*padicValNat p (Nat.fib (fibonacciRank p))+c)
        -2*padicValNat p (Nat.fib (fibonacciRank p))=c := by omega
    rw [hh]
  · apply dvd_mul_of_dvd_right
    exact pow_dvd_pow _ (by omega)

theorem large_prime_order_dvd_observed (p c : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hc : 0 < c) :
    ∃ M : ℕ, 0 < M ∧ orderOf (9 : ZMod (p^c)) ∣ (nativeModulusRule M).period := by
  let b := 2*padicValNat p (Nat.fib (fibonacciRank p))+c
  have hb : 0 < b := by dsimp [b]; omega
  refine ⟨p^b, pow_pos hp.pos _, ?_⟩
  refine dvd_trans ?_ (local_period_dvd_native p b hp hb)
  simp only [nativePrimePowerRule, dite_eq_left hp, ite_eq_right hp2,
    dite_eq_right hp3, ite_eq_right hp5]
  exact square_order_dvd_signed _ _ _ (large_prime_signed_modulus_precision p c)

/-- Every prime other than three supplies arbitrary digits of its own
time label. The ternary label is supplied by a separate cross-prime argument. -/
theorem own_prime_power_observed (p k : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    ∃ M : ℕ, 0 < M ∧ p^k ∣ (nativeModulusRule M).period := by
  by_cases hp2 : p=2
  · subst p
    let b := k+7
    refine ⟨2^b, by positivity, dvd_trans ?_ (local_period_dvd_native 2 b (by decide) (by dsimp [b]; omega))⟩
    simp only [nativePrimePowerRule, dite_eq_left (by decide : Nat.Prime 2), ite_true]
    have hh : b-7=k := by dsimp [b]; omega
    rw [hh]
  by_cases hp5 : p=5
  · subst p
    let b := k+2
    refine ⟨5^b, by positivity, dvd_trans ?_ (local_period_dvd_native 5 b (by decide) (by dsimp [b]; omega))⟩
    simp only [nativePrimePowerRule, dite_eq_left (by decide : Nat.Prime 5),
      ite_eq_right (by decide : (5:ℕ) ≠ 2), dite_eq_right (by decide : (5:ℕ) ≠ 3), ite_true,
      signedOrder_three_mod_five_pow]
    have h0 : b-1 ≠ 0 := by dsimp [b]; omega
    have h1 : b-1-1=k := by dsimp [b]
    rw [ite_eq_right h0, h1]
    exact dvd_mul_left _ _
  let e := padicValNat p (3^(p-1)-1)
  let c := k+e+1
  have hc : 0 < c := by dsimp [c]; omega
  obtain ⟨M,hM,hd⟩ := large_prime_order_dvd_observed p c hp hp2 hp3 hp5 hc
  refine ⟨M,hM, dvd_trans ?_ hd⟩
  rw [orderOf_nine_prime_power p c hp hp2 hp3 hc]
  apply dvd_mul_of_dvd_right
  exact pow_dvd_pow _ (by change k ≤ c-e; dsimp [c]; omega)

/-- Cofinality of observed periods, with the cyclotomic prime input explicit. -/
theorem native_period_cofinal_of_primitive_third
    (hthird : ∀ k : ℕ, 0 < k →
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ orderOf (9 : ZMod q) = 3^k) :
    ∀ N : ℕ, 0 < N → ∃ M : ℕ, 0 < M ∧ N ∣ (nativeModulusRule M).period := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p k hp hk _
    by_cases h3 : p=3
    · subst p
      obtain ⟨q,hq,hq2,hq3,hq5,hord⟩ := hthird k hk
      obtain ⟨M,hM,hd⟩ := large_prime_order_dvd_observed q 1 hq hq2 hq3 hq5 (by decide)
      rw [pow_one,hord] at hd
      exact ⟨M,hM,hd⟩
    · exact own_prime_power_observed p k hp h3
  · intro h
    omega
  · intro _
    exact ⟨1,by decide,one_dvd _⟩
  · intro a b ha hb hcop ia ib _
    obtain ⟨M,hM,ha'⟩ := ia (by omega)
    obtain ⟨N,hN,hb'⟩ := ib (by omega)
    have hp : 0 < M*N := mul_pos hM hN
    refine ⟨M*N,hp,?_⟩
    apply hcop.mul_dvd_of_dvd_of_dvd
    · exact ha'.trans (native_period_dvd_of_modulus_dvd M (M*N) hM hp (dvd_mul_right _ _))
    · exact hb'.trans (native_period_dvd_of_modulus_dvd N (M*N) hN hp (dvd_mul_left _ _))

/-- A precision depending only on the index isolates every actual orbit
point from every other one. The native projection still stabilizes at one. -/
theorem native_block_isolated_at_three (i n : ℕ) :
    cubicBlock n ≡ cubicBlock i [ZMOD (3:ℤ)^(i+2)] ↔ n=i := by
  rcases lt_trichotomy n i with hl | he | hg
  · constructor
    · intro h
      have h' := (cubicBlock_three_collision_iff i n (i+2) hl).mp h.symm
      omega
    · intro h
      exact (lt_irrefl _ (h ▸ hl)).elim
  · subst n
    exact ⟨fun _ => rfl,fun _ => Int.ModEq.refl _⟩
  · rw [cubicBlock_three_collision_iff n i (i+2) hg]
    omega


/-- A single odd observation prime, different from three, can retain any
prescribed number of ternary digits of sufficiently late time labels. -/
theorem ternary_time_observed_at_other_prime (k : ℕ) (hk : 0 < k) :
    ∃ q b : ℕ, q.Prime ∧ q ≠ 3 ∧ 0 < b ∧
      3^k ∣ (nativeModulusRule (q^b)).period := by
  obtain ⟨q,hq,hq2,hq3,hq5,hord⟩ :=
    GoldenCubicPrimitiveTernaryPrime.exists_prime_orderOf_nine k hk
  let b := 2*padicValNat q (Nat.fib (fibonacciRank q))+1
  have hb : 0 < b := by dsimp [b]; omega
  refine ⟨q,b,hq,hq3,hb,dvd_trans ?_ (local_period_dvd_native q b hq hb)⟩
  simp only [nativePrimePowerRule, dite_eq_left hq, ite_eq_right hq2,
    dite_eq_right hq3, ite_eq_right hq5]
  have hc := square_order_dvd_signed (rankSignedModulus q b) (q^1)
    (rankSignedModulus_coprime q b hq hq3) (large_prime_signed_modulus_precision q 1)
  rw [pow_one,hord] at hc
  exact hc

/-- The observation periods are cofinal among all positive time moduli. -/
theorem native_period_cofinal (N : ℕ) (hN : 0 < N) :
    ∃ M : ℕ, 0 < M ∧ N ∣ (nativeModulusRule M).period :=
  native_period_cofinal_of_primitive_third GoldenCubicPrimitiveTernaryPrime.exists_prime_orderOf_nine N hN

/-- Yet the same late trajectory erases every digit in its own ternary
state channel: each fixed three-power precision eventually reads one. -/
theorem ternary_state_eventually_one (a : ℕ) :
    ∀ n : ℕ, a-1 ≤ n → cubicBlock n ≡ 1 [ZMOD (3:ℤ)^a] :=
  (cubicBlock_three_transient a).1


end D5.S3.Arith.Primes.GoldenCubicClockCofinality
