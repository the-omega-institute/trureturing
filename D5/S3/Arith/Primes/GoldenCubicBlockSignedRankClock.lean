/- GID: D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockSignedRankClock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact transients, periods, and residue counts of native cubic Lucas blocks. -/

import D5.S3.Arith.Primes.GoldenCubicBlockRankReadout
import D5.S3.Arith.Primes.GoldenCubicSignedOrder
import D5.S3.Arith.Primes.GoldenCubicBlockThreeAdic
import D5.S3.Arith.Primes.GoldenCubicFiveClock
import D5.S3.Arith.Primes.ModularOrbitPrimePowerFactorization

set_option autoImplicit false

/-! Signed Fibonacci-rank clocks and their composition over every positive modulus. -/

namespace D5.S3.Arith.Primes.GoldenCubicBlockSignedRankClock

open D5.S1.Scale FiniteFibonacciRankClosure GoldenCubicBlockRankReadout

private theorem rank_prime_to_p (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    ¬ p ∣ fibonacciRank p := by
  have h := (rankWitness p hp).property
  have hr := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound hp hp5 h.1 h.2.1 h.2.2
  rw [fibonacciRank, dite_eq_left hp]
  intro hd
  have hh := hd.trans hr
  split_ifs at hh
  · have hpos : 0 < p - 1 := by have := hp.two_le; omega
    have hle := Nat.le_of_dvd hpos hh
    omega
  · have h1 : p ∣ (p + 1) - p := Nat.dvd_sub hh dvd_rfl
    have h11 : (p+1)-p = 1 := by omega
    rw [h11] at h1
    exact hp.ne_one (Nat.dvd_one.mp h1)

private theorem coprime_three {d : ℕ} (hd : ¬ 3 ∣ d) : Nat.Coprime d 3 :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hd)

private theorem remove_three_power (s d m x : ℕ) (hd : ¬ 3 ∣ d) (hx : ¬ 3 ∣ x) :
    3^s*d ∣ 3^m*x ↔ s ≤ m ∧ d ∣ x := by
  constructor
  · intro h
    refine ⟨?_, ((coprime_three hd).pow_right m).dvd_mul_left.mp ((dvd_mul_left _ _).trans h)⟩
    by_contra hh
    have hsm : m+(s-m) = s := by omega
    have hp : (3:ℕ)^s ∣ 3^m*x := (dvd_mul_right _ _).trans h
    rw [← hsm, pow_add] at hp
    have hx' := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < (3:ℕ)^m)).mp hp
    have h3 : (3:ℕ) ∣ 3^(s-m) := dvd_pow_self _ (by omega)
    exact hx (h3.trans hx')
  · rintro ⟨hs, hd'⟩
    exact Nat.mul_dvd_mul (pow_dvd_pow _ hs) hd'

private theorem signed_index_branches (q : ℕ) (hq : q ≠ 0) :
    0 < (3:ℕ)^q-1 ∧ ¬ (3:ℕ) ∣ 3^q-1 ∧ ¬ (3:ℕ) ∣ 3^q+1 := by
  have ht : 1 < (3:ℕ)^q := one_lt_pow₀ (by decide) hq
  have hd : (3:ℕ) ∣ 3^q := dvd_pow_self _ hq
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    have he := Nat.dvd_sub hd h
    have h1 : (3:ℕ)^q-(3^q-1)=1 := by omega
    rw [h1] at he
    exact (by decide : ¬ (3:ℕ) ∣ 1) he
  · intro h
    have he := Nat.dvd_sub h hd
    rw [Nat.add_sub_cancel_left] at he
    exact (by decide : ¬ (3:ℕ) ∣ 1) he

private theorem branch_readout (p s d m x : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (hpr : ¬ p ∣ fibonacciRank p) (hr : fibonacciRank p = 3^s*d)
    (hd : ¬ 3 ∣ d) (hx3 : ¬ 3 ∣ x) (hx : 0 < x) :
    valuationReadout p (3^m*x) =
      if s ≤ m ∧ d ∣ x then padicValNat p (Nat.fib (fibonacciRank p))+padicValNat p x else 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hbranch : fibonacciRank p ∣ 3^m*x ↔ s ≤ m ∧ d ∣ x := by
    rw [hr, remove_three_power s d m x hd hx3]
  unfold valuationReadout
  by_cases hh : fibonacciRank p ∣ 3^m*x
  · simp only [ite_eq_left hh, ite_eq_left (hbranch.mp hh)]
    congr 1
    have hm3 : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    have hmval : padicValNat p (3^m) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hm3 (hp.dvd_of_dvd_pow h))
    have hdiv : fibonacciRank p * (3^m*x/fibonacciRank p) = 3^m*x :=
      Nat.mul_div_cancel' hh
    have hQ : 3^m*x/fibonacciRank p ≠ 0 := by
      intro he
      rw [he, mul_zero] at hdiv
      exact (mul_ne_zero (by positivity) hx.ne') hdiv.symm
    have hR : fibonacciRank p ≠ 0 := fun he => hpr (he ▸ dvd_zero p)
    have hv := congrArg (padicValNat p) hdiv
    rw [padicValNat.mul hR hQ, padicValNat.mul (by positivity) hx.ne',
      padicValNat.eq_zero_of_not_dvd hpr, hmval, zero_add, zero_add] at hv
    exact hv
  · simp only [ite_eq_right hh, ite_eq_right (fun h => hh (hbranch.mpr h))]

private theorem at_most_one_branch (d x : ℕ) (hd : 2 < d) (hx : 1 ≤ x) :
    ¬ (d ∣ x-1 ∧ d ∣ x+1) := by
  rintro ⟨h1, h2⟩
  have hv := Nat.dvd_sub h2 h1
  have he : x+1-(x-1)=2 := by omega
  rw [he] at hv
  exact (not_le.mpr hd) (Nat.le_of_dvd (by decide) hv)

private theorem branch_threshold (p d h b x : ℕ) [Fact p.Prime] (hx : x ≠ 0)
    (hcp : Nat.Coprime d p) (hb : 0 < b) :
    b ≤ (if d ∣ x then h+padicValNat p x else 0) ↔ d*p^(b-h) ∣ x := by
  by_cases hd : d ∣ x
  · rw [ite_eq_left hd]
    constructor
    · intro hh
      exact ((hcp.pow_right _).mul_dvd_of_dvd_of_dvd hd)
        ((padicValNat_dvd_iff_le hx).mpr (by omega))
    · intro hh
      have hv := (padicValNat_dvd_iff_le hx).mp ((dvd_mul_left _ _).trans hh)
      omega
  · rw [ite_eq_right hd]
    exact iff_of_false (by omega) (fun h => hd ((dvd_mul_right _ _).trans h))

private theorem two_branch_threshold (p b h x : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hx : 1 < x) :
    b ≤ h + padicValNat p (x-1)+padicValNat p (x+1) ↔
      p^(b-h) ∣ x-1 ∨ p^(b-h) ∣ x+1 := by
  have ha : x-1 ≠ 0 := by omega
  have hc : x+1 ≠ 0 := by omega
  rw [padicValNat_dvd_iff_le ha, padicValNat_dvd_iff_le hc]
  have hz : padicValNat p (x-1)=0 ∨ padicValNat p (x+1)=0 := by
    by_cases h1 : p ∣ x-1
    · right
      apply padicValNat.eq_zero_of_not_dvd
      intro h2
      have hu := Nat.dvd_sub h2 h1
      have he : x+1-(x-1)=2 := by omega
      rw [he] at hu
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out (by decide)).mp hu)
    · exact Or.inl (padicValNat.eq_zero_of_not_dvd h1)
  rcases hz with h0|h0 <;> omega

/-- Exact collision criterion at an odd, unramified prime away from
three. The two alternatives are a single global sign, not a square
test modulo a composite modulus. -/
theorem native_prime_power_signed_lag
    (p b n m s d : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hb : 0 < b) (hmn : m < n) (hr : fibonacciRank p = 3^s*d) (hd3 : ¬ 3 ∣ d) :
    let h := padicValNat p (Nat.fib (fibonacciRank p));
    let Q := if d ≤ 2 then p^(b-2*h) else d*p^(b-h);
    ((goldenLucas (3^n)^2+3) ≡ (goldenLucas (3^m)^2+3) [ZMOD (p:ℤ)^b]) ↔
      s ≤ m ∧ (Q ∣ 3^(n-m)-1 ∨ Q ∣ 3^(n-m)+1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let h := padicValNat p (Nat.fib (fibonacciRank p))
  let q := n-m
  let x := (3:ℕ)^q
  let Q := if d ≤ 2 then p^(b-2*h) else d*p^(b-h)
  change _ ↔ s ≤ m ∧ (Q ∣ x-1 ∨ Q ∣ x+1)
  have hq : q ≠ 0 := by dsimp [q]; omega
  have hx : 1 < x := one_lt_pow₀ (by decide) hq
  have hbranches := signed_index_branches q hq
  have he0 : n = m+q := by dsimp [q]; omega
  have he1 : (3:ℕ)^n = 3^m*x := by conv_lhs => rw [he0, pow_add]
  have hminus : (3:ℕ)^n-3^m = 3^m*(x-1) := by
    rw [he1, Nat.mul_sub_left_distrib, mul_one]
  have hplus : (3:ℕ)^n+3^m = 3^m*(x+1) := by
    rw [he1, Nat.mul_add, mul_one]
  have hpr := rank_prime_to_p p hp hp5
  have hdm : ¬ p ∣ d := fun hd => hpr (hr ▸ dvd_mul_of_dvd_right hd _)
  have hcp : d.Coprime p :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hdm |>.symm
  have hminus_read := branch_readout p s d m (x-1) hp hp3 hpr hr hd3
    hbranches.2.1 hbranches.1
  have hplus_read := branch_readout p s d m (x+1) hp hp3 hpr hr hd3
    hbranches.2.2 (by omega)
  rw [cubic_block_odd_prime_rank_collision p n m b hp hp2 hmn, ite_eq_right hp5, zero_add,
    hplus, hminus, hplus_read, hminus_read]
  by_cases hs : s ≤ m
  · simp only [hs, true_and]
    by_cases hd : d ≤ 2
    · have hdpos : 0 < d := Nat.pos_of_ne_zero (fun hz => hd3 (hz ▸ dvd_zero _))
      obtain ⟨u,hu⟩ := (show Odd x from (show Odd (3:ℕ) from by decide).pow)
      have hxminus : 2 ∣ x-1 := ⟨u, by omega⟩
      have hxplus : 2 ∣ x+1 := ⟨u+1, by omega⟩
      have he : d=1 ∨ d=2 := by omega
      have hdm' : d ∣ x-1 := by
        rcases he with h1 | h2
        · rw [h1]; exact one_dvd _
        · rw [h2]; exact hxminus
      have hdp' : d ∣ x+1 := by
        rcases he with h1 | h2
        · rw [h1]; exact one_dvd _
        · rw [h2]; exact hxplus
      simp only [hdm', hdp', ite_true, Q, hd]
      have hh := two_branch_threshold p b (2*h) x hp2 hx
      exact Iff.trans (by dsimp only [h]; omega) hh
    · simp only [Q, hd, ite_false]
      have ho := at_most_one_branch d x (by omega) (by omega)
      have hpos1 : x-1 ≠ 0 := by omega
      have hpos2 : x+1 ≠ 0 := by omega
      have h1 := branch_threshold p d h b (x-1) hpos1 hcp hb
      have h2 := branch_threshold p d h b (x+1) hpos2 hcp hb
      rw [← h1, ← h2]
      by_cases hdm' : d ∣ x-1
      · have hdp' : ¬ d ∣ x+1 := fun hh => ho ⟨hdm',hh⟩
        simp [hdm',hdp',show ¬ b≤0 by omega, h]
      · simp [hdm',show ¬ b≤0 by omega, h]
  · simp [hs, show ¬ b≤0 by omega]

/-- The exact three-primary component of the entry rank gives the
native transient length at every positive prime-power precision. -/
def rankTransient (p : ℕ) : ℕ := padicValNat 3 (fibonacciRank p)

/-- The remaining rank is coprime to three. -/
def rankCore (p : ℕ) : ℕ := (fibonacciRank p).divMaxPow 3

/-- The signed modulus must use a common sign on its entire value. -/
def rankSignedModulus (p b : ℕ) : ℕ :=
  let h := padicValNat p (Nat.fib (fibonacciRank p))
  let d := rankCore p
  if d ≤ 2 then p^(b-2*h) else d*p^(b-h)

theorem canonical_prime_power_signed_lag
    (p b n m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hb : 0 < b) (hmn : m < n) :
    ((goldenLucas (3^n)^2+3) ≡ (goldenLucas (3^m)^2+3) [ZMOD (p:ℤ)^b]) ↔
      rankTransient p ≤ m ∧
        (rankSignedModulus p b ∣ 3^(n-m)-1 ∨ rankSignedModulus p b ∣ 3^(n-m)+1) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hr : fibonacciRank p ≠ 0 := by
    have h := (rankWitness p hp).property.1
    simpa only [fibonacciRank, dite_eq_left hp] using h.ne'
  have he : fibonacciRank p = 3^(rankTransient p)*rankCore p :=
    (Nat.pow_padicValNat_mul_divMaxPow 3 (fibonacciRank p)).symm
  have hn : ¬ 3 ∣ rankCore p := Nat.not_dvd_divMaxPow (by decide) hr
  exact native_prime_power_signed_lag p b n m _ _ hp hp2 hp3 hp5 hb hmn he hn


open GoldenCubicBlockThreeAdic

theorem native_dyadic_period (b n m : ℕ) (hb : 0 < b) (hmn : m<n) :
    cubicBlock n ≡ cubicBlock m [ZMOD (2:ℤ)^b] ↔ 1 ≤ m ∧ 2^(b-7) ∣ n-m := by
  by_cases hm : 1 ≤ m
  · have h := GoldenCubicDyadicClock.dyadicBlock_collision_iff b n m hm hmn
    simpa only [hm, true_and, cubicBlock, GoldenCubicDyadicClock.dyadicBlock] using h
  · have hm0 : m = 0 := by omega
    have hn : 1 ≤ n := by omega
    have h0 : cubicBlock 0 = 4 := by
      open D5.S0.Carrier in norm_num [cubicBlock, goldenLucas, trace, phi]
    have he : ¬ (cubicBlock n ≡ cubicBlock m [ZMOD (2:ℤ)^b]) := by
      intro hc
      have h2 : (2:ℤ) ∣ 2^b := dvd_pow_self _ hb.ne'
      have hd : cubicBlock n ≡ 19 [ZMOD 2] :=
        (GoldenCubicDyadicClock.dyadicBlock_mod128 n hn).of_dvd (by decide)
      rw [hm0, h0] at hc
      exact (by decide : ¬ ((19:ℤ) ≡ 4 [ZMOD 2])) (hd.symm.trans (hc.of_dvd h2))
    exact iff_of_false he (fun h => hm h.1)

theorem native_three_period (b n m : ℕ) (hmn : m<n) :
    cubicBlock n ≡ cubicBlock m [ZMOD (3:ℤ)^b] ↔ b-1 ≤ m ∧ (1:ℕ) ∣ n-m := by
  rw [cubicBlock_three_collision_iff n m b hmn]
  simp only [one_dvd, and_true]
  omega

theorem rankSignedModulus_positive (p b : ℕ) (hp : p.Prime) :
    0 < rankSignedModulus p b := by
  dsimp only [rankSignedModulus]
  split_ifs with hd
  · exact pow_pos hp.pos _
  · exact mul_pos (by omega) (pow_pos hp.pos _)

theorem rankSignedModulus_coprime (p b : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (3:ℕ).Coprime (rankSignedModulus p b) := by
  have hnp : ¬ (3:ℕ) ∣ p := fun h => hp3
    ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp h).symm
  have h3 : (3:ℕ).Coprime p := (coprime_three hnp).symm
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hR : fibonacciRank p ≠ 0 := by
    have h := (rankWitness p hp).property.1
    simpa only [fibonacciRank, dite_eq_left hp] using h.ne'
  have hd : ¬ 3 ∣ rankCore p := Nat.not_dvd_divMaxPow (by decide) hR
  dsimp only [rankSignedModulus]
  split_ifs
  · exact h3.pow_right _
  · exact (coprime_three hd).symm.mul_right (h3.pow_right _)

private theorem signed_pow_nat_to_int (Q q : ℕ) :
    ((Q ∣ 3^q-1) ∨ (Q ∣ 3^q+1)) ↔
      ((3:ℤ)^q ≡ 1 [ZMOD (Q:ℤ)] ∨ (3:ℤ)^q ≡ -1 [ZMOD (Q:ℤ)]) := by
  have hx : 1 ≤ (3:ℕ)^q := Nat.one_le_pow _ _ (by decide)
  apply or_congr
  · rw [Int.modEq_iff_dvd,
      show 1-(3:ℤ)^q = -((3:ℤ)^q-1) by ring, Int.dvd_neg]
    exact_mod_cast (Iff.rfl : (Q ∣ 3^q-1) ↔ Q ∣ 3^q-1)
  · rw [Int.modEq_iff_dvd,
      show -1-(3:ℤ)^q = -((3:ℤ)^q+1) by ring, Int.dvd_neg]
    exact_mod_cast (Iff.rfl : (Q ∣ 3^q+1) ↔ Q ∣ 3^q+1)

/-- At every odd unramified prime other than three, the eventual period
is the order in the unit group quotiented by globally consistent signs. -/
theorem canonical_prime_power_period
    (p b n m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hb : 0 < b) (hmn : m < n) :
    ((goldenLucas (3^n)^2+3) ≡ (goldenLucas (3^m)^2+3) [ZMOD (p:ℤ)^b]) ↔
      rankTransient p ≤ m ∧
        GoldenCubicSignedOrder.signedOrder 3 (rankSignedModulus p b)
          (rankSignedModulus_coprime p b hp hp3) ∣ n-m := by
  rw [canonical_prime_power_signed_lag p b n m hp hp2 hp3 hp5 hb hmn,
    GoldenCubicSignedOrder.signedOrder_dvd_iff_modEq]
  simp only [Nat.cast_ofNat]
  exact and_congr Iff.rfl (signed_pow_nat_to_int _ _)

open ModularOrbitTransientComposition ModularOrbitPrimePowerFactorization

/-- The canonical local rule. Nonprime inputs are unused by the
positive-modulus prime-power factorization. -/
noncomputable def nativePrimePowerRule (p b : ℕ) : OrbitRule :=
  if hp : p.Prime then
    if p = 2 then ⟨p^b, 1, 2^(b-7)⟩
    else if h3 : p = 3 then ⟨p^b, b-1, 1⟩
    else if p = 5 then
      ⟨p^b, 0, GoldenCubicSignedOrder.signedOrder 3 (5^(b-1))
        ((by decide : (3:ℕ).Coprime 5).pow_right (b-1))⟩
    else ⟨p^b, rankTransient p, GoldenCubicSignedOrder.signedOrder 3 (rankSignedModulus p b)
      (rankSignedModulus_coprime p b hp h3)⟩
  else ⟨p^b, 0, 1⟩

theorem nativePrimePowerRule_spec (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    (nativePrimePowerRule p b).modulus = p^b ∧
      0 < (nativePrimePowerRule p b).period ∧ (nativePrimePowerRule p b).Exact cubicBlock := by
  unfold nativePrimePowerRule
  rw [dite_eq_left hp]
  split_ifs with h2 h3 h5
  · subst p
    exact ⟨rfl, by positivity, fun n m hmn => native_dyadic_period b n m hb hmn⟩
  · subst p
    exact ⟨rfl, (show 0 < (1:ℕ) by decide), fun n m hmn => native_three_period b n m hmn⟩
  · subst p
    refine ⟨rfl, GoldenCubicSignedOrder.signedOrder_pos 3 _ (by positivity) _, ?_⟩
    intro n m hmn
    simp only [Nat.zero_le, true_and]
    exact GoldenCubicFiveClock.cubicBlock_five_collision b n m hmn
  · exact ⟨rfl, GoldenCubicSignedOrder.signedOrder_pos 3 _ (rankSignedModulus_positive p b hp) _,
      fun n m hmn => canonical_prime_power_period p b n m hp h2 h3 h5 hb hmn⟩

/-- Max of prime-power transients, lcm of their least periods. -/
noncomputable def nativeModulusRule (M : ℕ) : OrbitRule :=
  ruleForModulus nativePrimePowerRule M

theorem native_modulus_rule_spec (M : ℕ) (hM : 0 < M) :
    (nativeModulusRule M).modulus = M ∧ 0 < (nativeModulusRule M).period ∧
      (nativeModulusRule M).Exact cubicBlock :=
  canonical_rule_spec nativePrimePowerRule cubicBlock nativePrimePowerRule_spec M hM

/-- At every positive integer modulus, all later collisions are exactly
the simultaneous transient and period tests. -/
theorem native_modulus_collision (M n m : ℕ) (hM : 0 < M) (hmn : m<n) :
    (cubicBlock n ≡ cubicBlock m [ZMOD (M:ℤ)]) ↔
      (nativeModulusRule M).transient ≤ m ∧ (nativeModulusRule M).period ∣ n-m :=
  canonical_modulus_collision nativePrimePowerRule cubicBlock nativePrimePowerRule_spec M hM n m hmn

theorem native_modulus_residue_count (M : ℕ) (hM : 0 < M) :
    Nat.card {z : ℤ // ∃ n : ℕ, cubicBlock n % (M:ℤ) = z} =
      (nativeModulusRule M).transient + (nativeModulusRule M).period :=
  canonical_modulus_residue_count nativePrimePowerRule cubicBlock nativePrimePowerRule_spec M hM

theorem native_modulus_tail_period (M k l : ℕ) (hM : 0 < M) (hl : 0 < l) :
    (∀ n, k≤n → cubicBlock (n+l) ≡ cubicBlock n [ZMOD (M:ℤ)]) ↔
      (nativeModulusRule M).transient ≤ k ∧ (nativeModulusRule M).period ∣ l := by
  obtain ⟨hm, _, h⟩ := native_modulus_rule_spec M hM
  have hh := exact_tail_period (nativeModulusRule M) cubicBlock h k l hl
  rwa [hm] at hh

private theorem rank_thirteen : fibonacciRank 13 = 7 := by
  let hp : Nat.Prime 13 := by decide
  rw [fibonacciRank, dite_eq_left hp]
  let r := (rankWitness 13 hp).val
  have h := (rankWitness 13 hp).property
  have hpos : 0 < r := h.1
  have hd : 13 ∣ Nat.fib r := h.2.1
  have hle : r ≤ 7 := h.2.2 7 (by decide) (by decide)
  change r=7
  interval_cases r <;> first | rfl | exact False.elim (by contradiction)

private theorem rank_thirteen_numbers :
    rankTransient 13 = 0 ∧ rankCore 13 = 7 ∧
      padicValNat 13 (Nat.fib (fibonacciRank 13))=1 := by
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h : padicValNat 3 7=0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have hg : (7:ℕ).divMaxPow 3 = 7 := by
    simpa only [h, pow_zero, one_mul] using Nat.pow_padicValNat_mul_divMaxPow 3 7
  simp only [rankTransient, rankCore, rank_thirteen, h, hg,
    show Nat.fib 7 = 13 by decide, padicValNat_self, and_self]

/-- In the native trajectory the least period doubles from three to
six between moduli thirteen and its square. -/
theorem native_thirteen_periods :
    (nativePrimePowerRule 13 1).period = 3 ∧ (nativePrimePowerRule 13 2).period = 6 := by
  obtain ⟨_, hc, hd⟩ := rank_thirteen_numbers
  have h7 : rankSignedModulus 13 1 = 7 := by
    simp only [rankSignedModulus, hc, hd]; decide
  have h91 : rankSignedModulus 13 2 = 91 := by
    simp only [rankSignedModulus, hc, hd]; decide
  simp only [nativePrimePowerRule, dite_eq_left (by decide : Nat.Prime 13),
    ite_eq_right (by decide : (13:ℕ) ≠ 2), dite_eq_right (by decide : (13:ℕ) ≠ 3),
    ite_eq_right (by decide : (13:ℕ) ≠ 5)]
  exact ⟨by
    generalize_proofs hc'
    revert hc'
    rw [h7]
    exact GoldenCubicSignedOrder.signedOrder_three_mod7, by
    generalize_proofs hc'
    revert hc'
    rw [h91]
    exact GoldenCubicSignedOrder.signedOrder_three_mod91⟩

end D5.S3.Arith.Primes.GoldenCubicBlockSignedRankClock
