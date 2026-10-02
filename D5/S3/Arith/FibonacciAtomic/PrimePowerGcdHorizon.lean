/- GID: D5/S3/Arith/FibonacciAtomic/PrimePowerGcdHorizon
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimePowerGcdHorizon
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Nilpotent scalar lifts determine the sharp higher-prime-power gcd horizon. -/

import D5.S3.Arith.FibonacciAtomic.TimeSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon

open D5.S3.Arith.FibonacciAtomic.TimeSampling

def signedObservation (n z : ℤ) (k : ℕ) : ℤ :=
  Int.fib ((k : ℤ) - 1) * n + Int.fib (k : ℤ) * z

def sourceObservation (a b k : ℕ) : ℕ :=
  Nat.fib (k + 3) * a + Nat.fib (k + 4) * b

noncomputable def horizon (p e : ℕ) : ℕ :=
  if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then zeroRank (p ^ e)
  else zeroRank (p ^ e) - zeroRank (p ^ (e - 1))

theorem sharp_prime_power_gcd_horizon (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    (∀ j : ℕ, 0 < zeroRank (p ^ j) ∧ p ^ j ∣ Nat.fib (zeroRank (p ^ j)) ∧
      ∀ k : ℕ, 0 < k → p ^ j ∣ Nat.fib k → zeroRank (p ^ j) ≤ k) ∧
    (zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) ∨
      zeroRank (p ^ e) = p * zeroRank (p ^ (e - 1))) ∧
    (∀ n z n2 z2 : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) ∧
    (∀ a b a2 b2 : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) ∧
    (∃ a b a2 b2 : ℕ, a < p ^ e ∧ b < p ^ e ∧ a2 < p ^ e ∧ b2 < p ^ e ∧
      (∀ k : ℕ, 1 ≤ k → k < horizon p e →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) ∧
      Nat.gcd (sourceObservation a b (horizon p e)) (p ^ e) = p ^ e ∧
      Nat.gcd (sourceObservation a2 b2 (horizon p e)) (p ^ e) = p ^ (e - 1)) := by
  classical
  have primeLarge : 2 ≤ p := hp.two_le
  have ranks (m : ℕ) (hm : 0 < m) :
      0 < zeroRank m ∧ m ∣ Nat.fib (zeroRank m) ∧
        ∀ k : ℕ, 0 < k → m ∣ Nat.fib k → zeroRank m ≤ k := by
    let : NeZero m := ⟨hm.ne'⟩
    let step : ZMod m × ZMod m → ZMod m × ZMod m :=
      fun state => (state.2, state.1 + state.2)
    have injective : Function.Injective step := by
      intro state state2 equality
      have first := congrArg Prod.fst equality
      have second := congrArg Prod.snd equality
      dsimp [step] at first second
      exact Prod.ext (add_right_cancel (first ▸ second)) first
    let castState : ℕ × ℕ → ZMod m × ZMod m := fun state => (state.1, state.2)
    have semiconj : Function.Semiconj castState
        (fun state : ℕ × ℕ => (state.2, state.1 + state.2)) step := by
      intro state
      simp [castState, step]
    obtain ⟨period, positive, returning⟩ := injective.mem_periodicPts (0, 1)
    have zero : (Nat.fib period : ZMod m) = 0 := by
      have equality := congrArg Prod.fst (semiconj.iterate_right period (0, 1))
      simpa [Nat.fib, castState, returning.eq] using equality
    have existsZero : Set.Nonempty {k : ℕ | 0 < k ∧ m ∣ Nat.fib k} :=
      ⟨period, positive, (ZMod.natCast_eq_zero_iff _ _).mp zero⟩
    have minimal := Nat.sInf_mem existsZero
    exact ⟨minimal.1, minimal.2, fun k positive zero => Nat.sInf_le ⟨positive, zero⟩⟩
  have powerRanks := fun j : ℕ => ranks (p ^ j) (pow_pos hp.pos j)
  have recurrence (n z : ℤ) (k : ℕ) :
      signedObservation n z (k + 2) =
        signedObservation n z k + signedObservation n z (k + 1) := by
    unfold signedObservation
    push_cast
    have first := Int.fib_add_two ((k : ℤ) - 1)
    have second := Int.fib_add_two (k : ℤ)
    have normalization : (k : ℤ) + 2 - 1 = k + 1 := by ring
    rw [normalization, second]
    have normalization2 : Int.fib ((k : ℤ) + 1) =
        Int.fib ((k : ℤ) - 1) + Int.fib (k : ℤ) := by
      convert first using 1 <;> congr 1 <;> ring
    rw [normalization2]
    simp only [add_sub_cancel_right]
    ring
  have shift (n z : ℤ) (s r : ℕ) :
      signedObservation n z (s + r) =
        Int.fib ((r : ℤ) - 1) * signedObservation n z s +
          Int.fib (r : ℤ) * signedObservation n z (s + 1) := by
    unfold signedObservation
    push_cast
    have first := Int.fib_add (r : ℤ) ((s : ℤ) - 1)
    have second := Int.fib_add (r : ℤ) (s : ℤ)
    have previous := Int.fib_add_two ((s : ℤ) - 1)
    simp only [sub_add_cancel] at first previous
    rw [show (s : ℤ) + r - 1 = r + (s - 1) by ring,
      show (s : ℤ) + r = r + s by ring, first, second]
    have normalization : Int.fib ((s : ℤ) + 1) =
        Int.fib ((s : ℤ) - 1) + Int.fib (s : ℤ) := by
      convert previous using 1 <;> congr 1 <;> ring
    rw [normalization]
    ring
  let modulus := p ^ e
  let lower := p ^ (e - 1)
  let rank := zeroRank lower
  let scalar : ℤ := Int.fib ((rank : ℤ) - 1)
  let offDiagonal : ℤ := Int.fib (rank : ℤ)
  have modulusPositive : 0 < modulus := pow_pos hp.pos e
  have lowerPositive : 0 < lower := pow_pos hp.pos (e - 1)
  let : NeZero modulus := ⟨modulusPositive.ne'⟩
  have rankFacts := ranks lower lowerPositive
  have rankLarge : 3 ≤ rank := by
    have lowerLarge : 2 ≤ lower := by
      dsimp [lower]
      exact (Nat.le_self_pow (by omega : e - 1 ≠ 0) p).trans' hp.two_le
    have zero := rankFacts.2.1
    change lower ∣ Nat.fib rank at zero
    by_contra small
    have casesRank : rank = 1 ∨ rank = 2 := by omega
    rcases casesRank with one | two
    · rw [one, Nat.fib_one] at zero
      have := Nat.dvd_one.mp zero
      omega
    · rw [two, Nat.fib_two] at zero
      have := Nat.dvd_one.mp zero
      omega
  have modulusFactor : modulus = lower * p := by
    dsimp [modulus, lower]
    rw [← pow_succ]
    congr 1
    omega
  have lowerDivides : (lower : ℤ) ∣ offDiagonal := by
    dsimp [offDiagonal]
    exact_mod_cast rankFacts.2.1
  have primeDividesLower : p ∣ lower := by
    dsimp [lower]
    exact dvd_pow_self p (by omega)
  have scalarNat : scalar = (Nat.fib (rank - 1) : ℤ) := by
    dsimp [scalar]
    have index : (rank : ℤ) - 1 = ((rank - 1 : ℕ) : ℤ) := by omega
    rw [index, Int.fib_natCast]
  have scalarPrime : ¬ p ∣ Nat.fib (rank - 1) := by
    have adjacent := Nat.fib_coprime_fib_succ (rank - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ rank)] at adjacent
    exact fun divides => Nat.not_coprime_of_dvd_of_dvd hp.one_lt divides
      (dvd_trans primeDividesLower rankFacts.2.1) adjacent
  have scalarUnit : IsUnit (scalar : ZMod modulus) := by
    rw [scalarNat, Int.cast_natCast]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr scalarPrime
  have annihilate : (p : ZMod modulus) * (offDiagonal : ZMod modulus) = 0 := by
    obtain ⟨coefficient, coefficientEq⟩ := lowerDivides
    rw [← Int.cast_natCast p, ← Int.cast_mul,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [coefficientEq, modulusFactor]
    exact ⟨coefficient, by push_cast; ring⟩
  have squareZero : (offDiagonal : ZMod modulus) ^ 2 = 0 := by
    have lowerSquare : modulus ∣ lower ^ 2 := by
      rw [modulusFactor, pow_two]
      exact Nat.mul_dvd_mul_left lower primeDividesLower
    obtain ⟨coefficient, coefficientEq⟩ := lowerDivides
    rw [coefficientEq]
    push_cast
    rw [mul_pow]
    have lowerZero : (lower : ZMod modulus) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact lowerSquare
    rw [lowerZero, zero_mul]
  have block (n z : ℤ) (s blocks : ℕ) :
      (scalar : ZMod modulus) * (signedObservation n z (s + blocks * rank) : ZMod modulus) =
        (scalar : ZMod modulus) ^ blocks *
          ((scalar : ZMod modulus) * (signedObservation n z s : ZMod modulus) +
            (blocks : ZMod modulus) * (offDiagonal : ZMod modulus) *
              (signedObservation n z (s + 1) : ZMod modulus)) := by
    induction blocks generalizing s with
    | zero => simp
    | succ blocks ih =>
      have shifted := shift n z (s + blocks * rank) rank
      have next := ih (s + 1)
      have previous := ih s
      have recurrenceMod := congrArg (fun value : ℤ => (value : ZMod modulus)) (recurrence n z s)
      push_cast at recurrenceMod
      have index : s + (blocks + 1) * rank = (s + blocks * rank) + rank := by ring
      rw [index, shifted]
      push_cast
      change (scalar : ZMod modulus) *
          ((scalar : ZMod modulus) * (signedObservation n z (s + blocks * rank) : ZMod modulus) +
            (offDiagonal : ZMod modulus) *
              (signedObservation n z (s + blocks * rank + 1) : ZMod modulus)) = _
      rw [show s + blocks * rank + 1 = s + 1 + blocks * rank by omega]
      calc
        _ = (scalar : ZMod modulus) *
              ((scalar : ZMod modulus) *
                (signedObservation n z (s + blocks * rank) : ZMod modulus)) +
            (offDiagonal : ZMod modulus) *
              ((scalar : ZMod modulus) *
                (signedObservation n z (s + 1 + blocks * rank) : ZMod modulus)) := by ring
        _ = _ := by
          rw [previous, next, show s + 1 + 1 = s + 2 by omega, recurrenceMod, pow_succ]
          have nilpotent : (offDiagonal : ZMod modulus) * offDiagonal = 0 := by
            simpa only [pow_two] using squareZero
          linear_combination
            (scalar : ZMod modulus) ^ blocks * (blocks : ZMod modulus) *
              (signedObservation n z s + signedObservation n z (s + 1) : ZMod modulus) * nilpotent
  have scalarReturn (n z : ℤ) (s : ℕ) :
      (signedObservation n z (s + p * rank) : ZMod modulus) =
        (scalar : ZMod modulus) ^ p * (signedObservation n z s : ZMod modulus) := by
    apply scalarUnit.mul_left_cancel
    rw [block]
    have vanish : (p : ZMod modulus) * offDiagonal *
        (signedObservation n z (s + 1) : ZMod modulus) = 0 := by rw [annihilate, zero_mul]
    rw [vanish, add_zero]
    ring
  have upperZero : modulus ∣ Nat.fib (p * rank) := by
    have returning := scalarReturn 0 1 0
    have returningZero : (Nat.fib (p * rank) : ZMod modulus) = 0 := by
      simpa only [signedObservation, zero_add, mul_zero, mul_one, Int.fib_zero,
        Int.cast_zero, Int.fib_natCast, Int.cast_natCast, mul_zero, add_zero,
        Nat.fib_zero, Nat.cast_zero] using returning
    exact (ZMod.natCast_eq_zero_iff _ _).mp returningZero
  have rankDichotomy : zeroRank modulus = rank ∨ zeroRank modulus = p * rank := by
    have topFacts := ranks modulus modulusPositive
    have lowerEntry := D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      (n := zeroRank modulus) rankFacts.1 rankFacts.2.1 rankFacts.2.2
    have topEntry := D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      (n := p * rank) topFacts.1 topFacts.2.1 topFacts.2.2
    have rankDivides : rank ∣ zeroRank modulus := lowerEntry.mp
      (dvd_trans (by rw [modulusFactor]; exact dvd_mul_right lower p) topFacts.2.1)
    have topDivides : zeroRank modulus ∣ p * rank := topEntry.mp upperZero
    obtain ⟨factor, factorEq⟩ := rankDivides
    have factorDivides : factor ∣ p := by
      rw [factorEq, mul_comm p rank] at topDivides
      exact (Nat.mul_dvd_mul_iff_left rankFacts.1).mp topDivides
    rcases (Nat.dvd_prime hp).mp factorDivides with one | prime
    · left
      simpa [one] using factorEq
    · right
      simpa [prime, mul_comm] using factorEq
  have gcdDivisors (m : ℕ) (x y : ℤ)
      (same : ∀ d : ℕ, d ∣ m → ((d : ℤ) ∣ x ↔ (d : ℤ) ∣ y)) :
      Nat.gcd x.natAbs m = Nat.gcd y.natAbs m := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · apply Int.natCast_dvd.mp
        exact (same _ (Nat.gcd_dvd_right x.natAbs m)).mp
          (Int.natCast_dvd.mpr (Nat.gcd_dvd_left x.natAbs m))
      · exact Nat.gcd_dvd_right x.natAbs m
    · apply Nat.dvd_gcd
      · apply Int.natCast_dvd.mp
        exact (same _ (Nat.gcd_dvd_right y.natAbs m)).mpr
          (Int.natCast_dvd.mpr (Nat.gcd_dvd_left y.natAbs m))
      · exact Nat.gcd_dvd_right y.natAbs m
  have gcdCongruence (m : ℕ) (x y : ℤ)
      (same : (x : ZMod m) = (y : ZMod m)) :
      Nat.gcd x.natAbs m = Nat.gcd y.natAbs m := by
    apply gcdDivisors
    intro d divides
    exact ((ZMod.intCast_eq_intCast_iff _ _ _).mp same |>.of_dvd
      (Int.natCast_dvd_natCast.mpr divides)).dvd_iff
  have unitDivisibility (m : ℕ) (x coefficient : ℤ)
      (unit : IsUnit (coefficient : ZMod m)) :
      ((m : ℤ) ∣ coefficient * x ↔ (m : ℤ) ∣ x) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact unit.mul_right_eq_zero
  have gcdScale (m : ℕ) (x coefficient : ℤ)
      (unit : IsUnit (coefficient : ZMod m)) :
      Nat.gcd (coefficient * x).natAbs m = Nat.gcd x.natAbs m := by
    apply gcdDivisors
    intro d divides
    have unitLower : IsUnit (coefficient : ZMod d) := by
      have mapped := unit.map (ZMod.castHom divides (ZMod d))
      simpa using mapped
    exact unitDivisibility d x coefficient unitLower
  have periodicGcd (n z : ℤ) (s : ℕ) :
      Nat.gcd (signedObservation n z (s + p * rank)).natAbs modulus =
        Nat.gcd (signedObservation n z s).natAbs modulus := by
    calc
      _ = Nat.gcd (scalar ^ p * signedObservation n z s).natAbs modulus :=
        gcdCongruence _ _ _ (by push_cast; exact scalarReturn n z s)
      _ = _ := gcdScale _ _ _ (by push_cast; exact scalarUnit.pow p)
  have scalarLowerUnit : IsUnit (scalar : ZMod lower) := by
    rw [scalarNat, Int.cast_natCast]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr scalarPrime
  have lowerShift (n z : ℤ) (s : ℕ) :
      (signedObservation n z (s + rank) : ZMod lower) =
        (scalar : ZMod lower) * (signedObservation n z s : ZMod lower) := by
    rw [shift]
    change ((scalar * signedObservation n z s +
      offDiagonal * signedObservation n z (s + 1) : ℤ) : ZMod lower) = _
    have offZero : (offDiagonal : ZMod lower) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr lowerDivides
    simpa only [Int.cast_add, Int.cast_mul, offZero, zero_mul, add_zero]
  have lowerPeriodic (n z : ℤ) (s : ℕ) :
      Nat.gcd (signedObservation n z (s + rank)).natAbs lower =
        Nat.gcd (signedObservation n z s).natAbs lower := by
    calc
      _ = Nat.gcd (scalar * signedObservation n z s).natAbs lower :=
        gcdCongruence _ _ _ (by push_cast; exact lowerShift n z s)
      _ = _ := gcdScale _ _ _ scalarLowerUnit
  have gcdThreshold (m d : ℕ) (x : ℤ) (divides : d ∣ m) :
      ((d : ℤ) ∣ x ↔ d ∣ Nat.gcd x.natAbs m) := by
    rw [Int.natCast_dvd]
    exact ⟨fun zero => Nat.dvd_gcd zero divides,
      fun zero => dvd_trans zero (Nat.gcd_dvd_left _ _)⟩
  have recoverTop (x y : ℤ)
      (lowerSame : Nat.gcd x.natAbs lower = Nat.gcd y.natAbs lower)
      (topSame : (modulus : ℤ) ∣ x ↔ (modulus : ℤ) ∣ y) :
      Nat.gcd x.natAbs modulus = Nat.gcd y.natAbs modulus := by
    apply gcdDivisors
    intro d divides
    obtain ⟨level, levelBound, rfl⟩ := (Nat.dvd_prime_pow hp).mp divides
    by_cases top : level = e
    · simpa only [top, modulus, Nat.cast_pow] using topSame
    · have lowerDivisor : p ^ level ∣ lower := by
        exact pow_dvd_pow p (by omega)
      rw [gcdThreshold lower _ x lowerDivisor, gcdThreshold lower _ y lowerDivisor, lowerSame]
  have lowerIterate (n z : ℤ) (s blocks : ℕ) :
      Nat.gcd (signedObservation n z (s + blocks * rank)).natAbs lower =
        Nat.gcd (signedObservation n z s).natAbs lower := by
    induction blocks with
    | zero => simp
    | succ blocks ih =>
      rw [show s + (blocks + 1) * rank = (s + blocks * rank) + rank by ring,
        lowerPeriodic, ih]
  have adjacentFlag (n z : ℤ) (s : ℕ) :
      ((p : ℤ) ∣ signedObservation n z s ∧ (p : ℤ) ∣ signedObservation n z (s + 1)) ↔
        ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ z) := by
    induction s with
    | zero => simp [signedObservation]
    | succ s ih =>
      rw [show s + 1 + 1 = s + 2 by omega, recurrence]
      constructor
      · rintro ⟨next, sum⟩
        apply ih.mp
        exact ⟨by simpa using dvd_sub sum next, next⟩
      · intro initial
        obtain ⟨current, next⟩ := ih.mpr initial
        exact ⟨next, dvd_add current next⟩
  have nonprimitivePeriodic (n z : ℤ)
      (nonprimitive : (p : ℤ) ∣ n ∧ (p : ℤ) ∣ z) (s : ℕ) :
      Nat.gcd (signedObservation n z (s + rank)).natAbs modulus =
        Nat.gcd (signedObservation n z s).natAbs modulus := by
    have companionZero := ((adjacentFlag n z s).mpr nonprimitive).2
    have productZero : (modulus : ℤ) ∣ offDiagonal * signedObservation n z (s + 1) := by
      rw [modulusFactor, Nat.cast_mul]
      exact mul_dvd_mul lowerDivides companionZero
    have shifted : (signedObservation n z (s + rank) : ZMod modulus) =
        (scalar * signedObservation n z s : ℤ) := by
      rw [shift]
      change ((scalar * signedObservation n z s +
        offDiagonal * signedObservation n z (s + 1) : ℤ) : ZMod modulus) = _
      rw [Int.cast_add, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr productZero, add_zero]
    exact (gcdCongruence _ _ _ shifted).trans (gcdScale _ _ _ scalarUnit)
  have decoder (growth : zeroRank modulus = p * rank) (n z : ℤ)
      (primitive : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ z)) (s : ℕ)
      (hit : (lower : ℤ) ∣ signedObservation n z s) :
      ((modulus : ℤ) ∣ signedObservation n z (s + (p - 1) * rank) ↔
        ∀ blocks : ℕ, blocks < p - 1 →
          ¬ (modulus : ℤ) ∣ signedObservation n z (s + blocks * rank)) := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨coefficient, coefficientEq⟩ := lowerDivides
    have hitCopy := hit
    obtain ⟨digit, digitEq⟩ := hitCopy
    have coefficientNonzero : (coefficient : ZMod p) ≠ 0 := by
      intro zero
      have coefficientDivides := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero
      have offTop : (modulus : ℤ) ∣ offDiagonal := by
        rw [coefficientEq, modulusFactor, Nat.cast_mul]
        exact mul_dvd_mul_left (lower : ℤ) coefficientDivides
      have topMinimal := (ranks modulus modulusPositive).2.2 rank rankFacts.1
        (by simpa [offDiagonal] using (Int.natCast_dvd.mp offTop))
      rw [growth] at topMinimal
      change p * rank ≤ rank at topMinimal
      have := Nat.mul_le_mul_left rank hp.two_le
      nlinarith [rankLarge]
    have companionNonzero : (signedObservation n z (s + 1) : ZMod p) ≠ 0 := by
      intro zero
      apply primitive
      apply (adjacentFlag n z s).mp
      exact ⟨dvd_trans (Int.natCast_dvd_natCast.mpr primeDividesLower) hit,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero⟩
    have slopeNonzero : (coefficient : ZMod p) * (signedObservation n z (s + 1) : ZMod p) ≠ 0 :=
      mul_ne_zero coefficientNonzero companionNonzero
    have normalized (blocks : ℕ) :
        (modulus : ℤ) ∣ signedObservation n z (s + blocks * rank) ↔
          (scalar : ZMod p) * (digit : ZMod p) +
            (blocks : ZMod p) * (coefficient : ZMod p) *
              (signedObservation n z (s + 1) : ZMod p) = 0 := by
      have blockEq := block n z s blocks
      have units : ((signedObservation n z (s + blocks * rank) : ZMod modulus) = 0) ↔
          ((scalar * signedObservation n z s + (blocks : ℤ) * offDiagonal *
            signedObservation n z (s + 1) : ℤ) : ZMod modulus) = 0 := by
        rw [← scalarUnit.mul_right_eq_zero, blockEq]
        push_cast
        exact (scalarUnit.pow blocks).mul_right_eq_zero
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, units,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [digitEq, coefficientEq]
      have factorEq : scalar * ((lower : ℤ) * digit) + (blocks : ℤ) *
          ((lower : ℤ) * coefficient) * signedObservation n z (s + 1) =
          (lower : ℤ) * (scalar * digit + (blocks : ℤ) * coefficient *
            signedObservation n z (s + 1)) := by ring
      rw [factorEq, modulusFactor, Nat.cast_mul,
        mul_dvd_mul_iff_left (by exact_mod_cast lowerPositive.ne' : (lower : ℤ) ≠ 0),
        ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rfl
    let root : ZMod p := -(scalar : ZMod p) * digit /
      ((coefficient : ZMod p) * (signedObservation n z (s + 1) : ZMod p))
    have rootCriterion (blocks : ℕ) :
        (modulus : ℤ) ∣ signedObservation n z (s + blocks * rank) ↔
          (blocks : ZMod p) = root := by
      rw [normalized]
      dsimp [root]
      rw [eq_div_iff slopeNonzero]
      constructor <;> intro equation <;> linear_combination equation
    have rootBound : root.val < p := ZMod.val_lt root
    have rootHit : (modulus : ℤ) ∣ signedObservation n z (s + root.val * rank) :=
      (rootCriterion root.val).mpr (ZMod.natCast_zmod_val root)
    have unique (left right : ℕ) (leftBound : left < p) (rightBound : right < p)
        (leftHit : (modulus : ℤ) ∣ signedObservation n z (s + left * rank))
        (rightHit : (modulus : ℤ) ∣ signedObservation n z (s + right * rank)) :
        left = right := by
      have equation := ((rootCriterion left).mp leftHit).trans
        ((rootCriterion right).mp rightHit).symm
      have values := congrArg ZMod.val equation
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] using values
    constructor
    · intro last blocks bound earlier
      have same := unique (p - 1) blocks (by omega) (by omega) last earlier
      omega
    · intro absent
      have last : root.val = p - 1 := by
        by_contra different
        exact absent root.val (by omega) rootHit
      simpa [last] using rootHit
  have lowerFromFull (x y : ℤ) (same : Nat.gcd x.natAbs modulus = Nat.gcd y.natAbs modulus) :
      Nat.gcd x.natAbs lower = Nat.gcd y.natAbs lower := by
    apply gcdDivisors
    intro d divides
    have dividesTop : d ∣ modulus := dvd_trans divides
      (by rw [modulusFactor]; exact dvd_mul_right lower p)
    rw [gcdThreshold modulus d x dividesTop, gcdThreshold modulus d y dividesTop, same]
  have periodicAgreement (period : ℕ) (positive : 0 < period) (word word2 : ℕ → ℕ)
      (periodic : ∀ k, word (k + period) = word k)
      (periodic2 : ∀ k, word2 (k + period) = word2 k)
      (agreement : ∀ k, 1 ≤ k → k ≤ period → word k = word2 k) :
      ∀ k, 1 ≤ k → word k = word2 k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro positiveTime
      by_cases early : k ≤ period
      · exact agreement k positiveTime early
      · have smaller : k - period < k := by omega
        have positiveEarlier : 1 ≤ k - period := by omega
        rw [show k = (k - period) + period by omega, periodic, periodic2]
        exact ih (k - period) smaller positiveEarlier
  have upper : ∀ n z n2 z2 : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (signedObservation n z k).natAbs modulus =
          Nat.gcd (signedObservation n2 z2 k).natAbs modulus) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (signedObservation n z k).natAbs modulus =
          Nat.gcd (signedObservation n2 z2 k).natAbs modulus := by
    intro n z n2 z2 agreement
    rcases rankDichotomy with stagnant | growth
    · have horizonEq : horizon p e = rank := by
        dsimp [horizon]
        rw [if_pos stagnant, stagnant]
      have offZero : (offDiagonal : ZMod modulus) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        have topFacts := (ranks modulus modulusPositive).2.1
        rw [stagnant] at topFacts
        simpa [offDiagonal] using (Int.natCast_dvd_natCast.mpr topFacts)
      have period (initial next : ℤ) (k : ℕ) :
          Nat.gcd (signedObservation initial next (k + rank)).natAbs modulus =
            Nat.gcd (signedObservation initial next k).natAbs modulus := by
        apply (gcdCongruence modulus _ (scalar * signedObservation initial next k) ?_).trans
          (gcdScale _ _ _ scalarUnit)
        rw [shift]
        change ((scalar * signedObservation initial next k + offDiagonal *
          signedObservation initial next (k + 1) : ℤ) : ZMod modulus) = _
        push_cast
        rw [offZero, zero_mul, add_zero]
      apply periodicAgreement rank rankFacts.1 _ _ (period n z) (period n2 z2)
      simpa [horizonEq] using agreement
    · have growing : zeroRank modulus ≠ rank := by
        rw [growth]
        have := Nat.mul_le_mul_left rank hp.two_le
        nlinarith [rankLarge]
      have horizonEq : horizon p e = (p - 1) * rank := by
        dsimp [horizon]
        rw [if_neg growing, growth, Nat.sub_mul, one_mul]
      have paidTwo : 2 ≤ horizon p e := by
        rw [horizonEq]
        have := Nat.mul_le_mul_right rank (by omega : 1 ≤ p - 1)
        omega
      have topPrimeDivides : p ∣ modulus := dvd_pow_self p (by omega)
      have samePrime (k : ℕ) (positive : 1 ≤ k) (paid : k ≤ horizon p e) :
          ((p : ℤ) ∣ signedObservation n z k ↔ (p : ℤ) ∣ signedObservation n2 z2 k) := by
        rw [gcdThreshold modulus p _ topPrimeDivides, gcdThreshold modulus p _ topPrimeDivides,
          agreement k positive paid]
      have sameFlag : ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ z) ↔
          ((p : ℤ) ∣ n2 ∧ (p : ℤ) ∣ z2) := by
        rw [← adjacentFlag n z 1, ← adjacentFlag n2 z2 1]
        exact and_congr (samePrime 1 le_rfl (by omega)) (samePrime 2 (by omega) paidTwo)
      have missing (s : ℕ) (positive : 1 ≤ s) (small : s ≤ rank) :
          Nat.gcd (signedObservation n z (s + (p - 1) * rank)).natAbs modulus =
            Nat.gcd (signedObservation n2 z2 (s + (p - 1) * rank)).natAbs modulus := by
        have paidInitial : s ≤ horizon p e := by
          rw [horizonEq]
          have := Nat.mul_le_mul_right rank (by omega : 1 ≤ p - 1)
          omega
        have lowerSame := lowerFromFull _ _ (agreement s positive paidInitial)
        have lowerMissing : Nat.gcd (signedObservation n z (s + (p - 1) * rank)).natAbs lower =
            Nat.gcd (signedObservation n2 z2 (s + (p - 1) * rank)).natAbs lower := by
          rw [lowerIterate, lowerIterate, lowerSame]
        apply recoverTop _ _ lowerMissing
        by_cases nonprimitive : (p : ℤ) ∣ n ∧ (p : ℤ) ∣ z
        · have nonprimitive2 := sameFlag.mp nonprimitive
          have iterateNonprimitive (initial next : ℤ)
              (flag : (p : ℤ) ∣ initial ∧ (p : ℤ) ∣ next) (blocks : ℕ) :
              Nat.gcd (signedObservation initial next (s + blocks * rank)).natAbs modulus =
                Nat.gcd (signedObservation initial next s).natAbs modulus := by
            induction blocks with
            | zero => simp
            | succ blocks ih =>
              rw [show s + (blocks + 1) * rank = (s + blocks * rank) + rank by ring,
                nonprimitivePeriodic initial next flag, ih]
          rw [gcdThreshold modulus modulus _ dvd_rfl,
            gcdThreshold modulus modulus _ dvd_rfl,
            iterateNonprimitive n z nonprimitive, iterateNonprimitive n2 z2 nonprimitive2,
            agreement s positive paidInitial]
        · have primitive2 : ¬ ((p : ℤ) ∣ n2 ∧ (p : ℤ) ∣ z2) :=
            fun flag => nonprimitive (sameFlag.mpr flag)
          have hitEquivalence : ((lower : ℤ) ∣ signedObservation n z s) ↔
              ((lower : ℤ) ∣ signedObservation n2 z2 s) := by
            rw [gcdThreshold lower lower _ dvd_rfl, gcdThreshold lower lower _ dvd_rfl, lowerSame]
          by_cases hit : (lower : ℤ) ∣ signedObservation n z s
          · rw [decoder growth n z nonprimitive s hit,
              decoder growth n2 z2 primitive2 s (hitEquivalence.mp hit)]
            apply forall_congr'
            intro blocks
            apply imp_congr_right
            intro blockBound
            have paidBlock : s + blocks * rank ≤ horizon p e := by
              rw [horizonEq]
              have := Nat.mul_le_mul_right rank (by omega : blocks + 1 ≤ p - 1)
              nlinarith
            rw [gcdThreshold modulus modulus _ dvd_rfl, gcdThreshold modulus modulus _ dvd_rfl,
              agreement _ (by omega) paidBlock]
          · have absent (initial next : ℤ)
              (notHit : ¬ (lower : ℤ) ∣ signedObservation initial next s) :
                ¬ (modulus : ℤ) ∣ signedObservation initial next (s + (p - 1) * rank) := by
              intro topHit
              have lowerHit : (lower : ℤ) ∣
                  signedObservation initial next (s + (p - 1) * rank) :=
                dvd_trans (Int.natCast_dvd_natCast.mpr
                  (show lower ∣ modulus from by
                    rw [modulusFactor]
                    exact dvd_mul_right lower p)) topHit
              rw [gcdThreshold lower lower _ dvd_rfl, lowerIterate,
                ← gcdThreshold lower lower _ dvd_rfl] at lowerHit
              exact notHit lowerHit
            exact iff_of_false (absent n z hit)
              (absent n2 z2 (fun second => hit (hitEquivalence.mpr second)))
      apply periodicAgreement (p * rank) (Nat.mul_pos hp.pos rankFacts.1) _ _
        (periodicGcd n z) (periodicGcd n2 z2)
      intro k positiveTime bound
      by_cases paid : k ≤ horizon p e
      · exact agreement k positiveTime paid
      · rw [horizonEq] at paid
        have position : 1 ≤ k - (p - 1) * rank ∧ k - (p - 1) * rank ≤ rank := by
          have product : p * rank = (p - 1) * rank + rank := by
            rw [← Nat.succ_mul]
            congr 1
            omega
          omega
        have equality := missing (k - (p - 1) * rank) position.1 position.2
        simpa only [Nat.sub_add_cancel (by omega : (p - 1) * rank ≤ k)] using equality
  have kernelIdentity (terminal k : ℕ) :
      signedObservation (Int.fib (terminal : ℤ)) (-Int.fib ((terminal : ℤ) - 1)) k =
        (-1 : ℤ) ^ k * Int.fib ((terminal : ℤ) - k) := by
    induction k using Nat.twoStepInduction with
    | zero => simp [signedObservation]
    | one => simp [signedObservation]
    | more k current next =>
      rw [recurrence, current, next]
      have reverse := Int.fib_add_two ((terminal : ℤ) - (k + 2))
      have reverseNormalized : Int.fib ((terminal : ℤ) - k) =
          Int.fib ((terminal : ℤ) - (k + 2)) + Int.fib ((terminal : ℤ) - (k + 1)) := by
        convert reverse using 1 <;> congr 1 <;> push_cast <;> ring
      push_cast
      rw [reverseNormalized, pow_succ, pow_add]
      ring
  have kernelAbs (terminal k : ℕ) (before : k ≤ terminal) :
      (signedObservation (Int.fib (terminal : ℤ)) (-Int.fib ((terminal : ℤ) - 1)) k).natAbs =
        Nat.fib (terminal - k) := by
    rw [kernelIdentity, Int.natAbs_mul, Int.natAbs_pow]
    have index : (terminal : ℤ) - k = ((terminal - k : ℕ) : ℤ) := by omega
    simp [index]
  have naturalIdentity (a b k : ℕ) :
      signedObservation (2 * (a : ℤ) + 3 * b) (3 * (a : ℤ) + 5 * b) k =
        (sourceObservation a b k : ℤ) := by
    induction k using Nat.twoStepInduction with
    | zero => norm_num [signedObservation, sourceObservation, Nat.fib_add_two]
    | one => norm_num [signedObservation, sourceObservation, Nat.fib_add_two]
    | more k current next =>
      rw [recurrence, current, next]
      simp only [sourceObservation, Nat.cast_add, Nat.cast_mul]
      rw [show k + 2 + 3 = (k + 3) + 2 by omega,
        show k + 2 + 4 = (k + 4) + 2 by omega,
        Nat.fib_add_two (n := k + 3), Nat.fib_add_two (n := k + 4)]
      push_cast
      rw [show k + 3 + 1 = k + 1 + 3 by omega,
        show k + 4 + 1 = k + 1 + 4 by omega]
      rw [Nat.fib_add_two (n := k + 3)]
      push_cast
      ring
  have naturalUpper : ∀ a b a2 b2 : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (sourceObservation a b k) modulus = Nat.gcd (sourceObservation a2 b2 k) modulus) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (sourceObservation a b k) modulus =
          Nat.gcd (sourceObservation a2 b2 k) modulus := by
    intro a b a2 b2 agreement
    have signed := upper (2 * a + 3 * b) (3 * a + 5 * b)
      (2 * a2 + 3 * b2) (3 * a2 + 5 * b2) (by
        intro k positive paid
        simpa only [naturalIdentity, Int.natAbs_natCast] using agreement k positive paid)
    intro k positive
    simpa only [naturalIdentity, Int.natAbs_natCast] using signed k positive
  have realization (n z : ℤ) : ∃ a b : ℕ, a < modulus ∧ b < modulus ∧
      ∀ k : ℕ, Nat.gcd (sourceObservation a b k) modulus =
        Nat.gcd (signedObservation n z k).natAbs modulus := by
    let first : ZMod modulus := 5 * (n : ZMod modulus) - 3 * (z : ZMod modulus)
    let second : ZMod modulus := -3 * (n : ZMod modulus) + 2 * (z : ZMod modulus)
    refine ⟨first.val, second.val, ZMod.val_lt first, ZMod.val_lt second, ?_⟩
    intro k
    have initial : (2 * (first.val : ℤ) + 3 * second.val : ZMod modulus) = n := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      dsimp [first, second]
      ring
    have next : (3 * (first.val : ℤ) + 5 * second.val : ZMod modulus) = z := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      dsimp [first, second]
      ring
    have same : (sourceObservation first.val second.val k : ZMod modulus) =
        (signedObservation n z k : ZMod modulus) := by
      rw [← Int.cast_natCast, ← naturalIdentity]
      unfold signedObservation
      push_cast
      push_cast at initial next
      rw [initial, next]
    simpa only [Int.natAbs_natCast] using gcdCongruence modulus
      (sourceObservation first.val second.val k : ℤ) (signedObservation n z k)
      (by simpa only [Int.cast_natCast] using same)
  have signedSharp : ∃ n z n2 z2 : ℤ,
      (∀ k : ℕ, 1 ≤ k → k < horizon p e →
        Nat.gcd (signedObservation n z k).natAbs modulus =
          Nat.gcd (signedObservation n2 z2 k).natAbs modulus) ∧
      Nat.gcd (signedObservation n z (horizon p e)).natAbs modulus = modulus ∧
      Nat.gcd (signedObservation n2 z2 (horizon p e)).natAbs modulus = lower := by
    have lowerEntry (k : ℕ) : lower ∣ Nat.fib k ↔ rank ∣ k :=
      D5.S3.Arith.FibonacciRank.fibonacci_entry_point rankFacts.1 rankFacts.2.1 rankFacts.2.2
    have topFacts := ranks modulus modulusPositive
    have topEntry (k : ℕ) : modulus ∣ Nat.fib k ↔ zeroRank modulus ∣ k :=
      D5.S3.Arith.FibonacciRank.fibonacci_entry_point topFacts.1 topFacts.2.1 topFacts.2.2
    rcases rankDichotomy with stagnant | growth
    · have horizonEq : horizon p e = rank := by
        dsimp [horizon]
        rw [if_pos stagnant, stagnant]
      let n : ℤ := Int.fib (rank : ℤ)
      let z : ℤ := -Int.fib ((rank : ℤ) - 1)
      have lowerSame (k : ℕ) :
          (signedObservation n z k : ZMod lower) =
            (signedObservation (n + lower) z k : ZMod lower) := by
        unfold signedObservation
        push_cast
        rw [ZMod.natCast_self]
        ring
      have noLower (k : ℕ) (positive : 1 ≤ k) (early : k < rank) :
          ¬ (lower : ℤ) ∣ signedObservation n z k := by
        intro zero
        have fibonacciZero : lower ∣ Nat.fib (rank - k) := by
          rw [← kernelAbs rank k (by omega)]
          exact Int.natCast_dvd.mp zero
        have divides := (lowerEntry _).mp fibonacciZero
        have bound := Nat.le_of_dvd (by omega : 0 < rank - k) divides
        omega
      refine ⟨n, z, n + lower, z, ?_, ?_, ?_⟩
      · intro k positive early
        rw [horizonEq] at early
        apply recoverTop _ _ (gcdCongruence lower _ _ (lowerSame k))
        have absent := noLower k positive early
        have absent2 : ¬ (lower : ℤ) ∣ signedObservation (n + lower) z k := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← lowerSame,
            ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact absent
        have lowerTop : (lower : ℤ) ∣ (modulus : ℤ) := by
          rw [modulusFactor, Nat.cast_mul]
          exact dvd_mul_right _ _
        exact iff_of_false (fun top => absent (dvd_trans lowerTop top))
          (fun top => absent2 (dvd_trans lowerTop top))
      · rw [horizonEq]
        change Nat.gcd (signedObservation (Int.fib (rank : ℤ))
          (-Int.fib ((rank : ℤ) - 1)) rank).natAbs modulus = modulus
        rw [kernelAbs rank rank le_rfl, Nat.sub_self, Nat.fib_zero, Nat.gcd_zero_left]
      · rw [horizonEq]
        have atTerminal : signedObservation (n + lower) z rank = (lower : ℤ) * scalar := by
          have zero := kernelIdentity rank rank
          have actualZero : signedObservation n z rank = 0 := by
            simpa [n, z] using zero
          dsimp [signedObservation, scalar] at actualZero ⊢
          linear_combination actualZero
        rw [atTerminal, mul_comm]
        exact (gcdScale modulus (lower : ℤ) scalar scalarUnit).trans
          (by
            simp only [Int.natAbs_natCast]
            exact Nat.gcd_eq_left (by rw [modulusFactor]; exact dvd_mul_right lower p))
    · have growing : zeroRank modulus ≠ rank := by
        rw [growth]
        nlinarith [hp.two_le, rankLarge]
      have horizonEq : horizon p e = (p - 1) * rank := by
        dsimp [horizon]
        rw [if_neg growing, growth, Nat.sub_mul, one_mul]
      let terminal := (p - 1) * rank
      have terminalPositive : 0 < terminal := Nat.mul_pos (by omega) rankFacts.1
      have terminalBound : terminal < p * rank := by
        dsimp [terminal]
        exact Nat.mul_lt_mul_of_pos_right (by omega) rankFacts.1
      have offNotTop : ¬ modulus ∣ Nat.fib rank := by
        intro zero
        have minimum := topFacts.2.2 rank rankFacts.1 zero
        rw [growth] at minimum
        nlinarith [hp.two_le, rankLarge]
      have offGcd : Nat.gcd (Nat.fib rank) modulus = lower := by
        obtain ⟨level, bound, equation⟩ :=
          (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right (Nat.fib rank) modulus)
        have lowerGcd : lower ∣ Nat.gcd (Nat.fib rank) modulus :=
          Nat.dvd_gcd rankFacts.2.1 (by rw [modulusFactor]; exact dvd_mul_right lower p)
        have belowTop : level < e := by
          by_contra notBelow
          have levelEq : level = e := by omega
          have zero := Nat.gcd_dvd_left (Nat.fib rank) modulus
          rw [equation, levelEq] at zero
          exact offNotTop zero
        have aboveLower : e - 1 ≤ level := by
          rw [equation] at lowerGcd
          exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp lowerGcd
        have levelEq : level = e - 1 := by omega
        simpa [lower, levelEq] using equation
      have noTop (endpoint k : ℕ) (endpointBound : endpoint ≤ p * rank)
          (positive : 1 ≤ k) (early : k < endpoint) :
          ¬ (modulus : ℤ) ∣ signedObservation (Int.fib (endpoint : ℤ))
            (-Int.fib ((endpoint : ℤ) - 1)) k := by
        intro zero
        have fibonacciZero : modulus ∣ Nat.fib (endpoint - k) := by
          rw [← kernelAbs endpoint k (by omega)]
          exact Int.natCast_dvd.mp zero
        have divides := (topEntry _).mp fibonacciZero
        rw [growth] at divides
        have bound := Nat.le_of_dvd (by omega : 0 < endpoint - k) divides
        omega
      refine ⟨Int.fib (terminal : ℤ), -Int.fib ((terminal : ℤ) - 1),
        Int.fib ((p * rank : ℕ) : ℤ), -Int.fib (((p * rank : ℕ) : ℤ) - 1), ?_, ?_, ?_⟩
      · intro k positive early
        rw [horizonEq] at early
        change k < terminal at early
        apply recoverTop
        · rw [kernelAbs terminal k (by omega), kernelAbs (p * rank) k (by omega)]
          have shifted := lowerPeriodic 0 1 (terminal - k)
          have indices : p * rank - k = terminal - k + rank := by
            have product : p * rank = terminal + rank := by
              dsimp [terminal]
              rw [← Nat.succ_mul]
              congr 1
              omega
            omega
          rw [indices]
          simpa only [signedObservation, mul_zero, mul_one, zero_add,
            Int.fib_natCast, Int.natAbs_natCast] using shifted.symm
        · exact iff_of_false (noTop terminal k terminalBound.le positive early)
            (noTop (p * rank) k le_rfl positive (early.trans terminalBound))
      · rw [horizonEq, kernelAbs terminal terminal le_rfl, Nat.sub_self,
          Nat.fib_zero, Nat.gcd_zero_left]
      · rw [horizonEq, kernelAbs (p * rank) terminal terminalBound.le]
        have difference : p * rank - terminal = rank := by
          have product : p * rank = terminal + rank := by
            dsimp [terminal]
            rw [← Nat.succ_mul]
            congr 1
            omega
          rw [product]
          omega
        rw [difference]
        exact offGcd
  obtain ⟨n, z, n2, z2, agreement, terminal, terminal2⟩ := signedSharp
  obtain ⟨a, b, aBound, bBound, source⟩ := realization n z
  obtain ⟨a2, b2, a2Bound, b2Bound, source2⟩ := realization n2 z2
  refine ⟨powerRanks, rankDichotomy, upper, naturalUpper,
    a, b, a2, b2, aBound, bBound, a2Bound, b2Bound, ?_, ?_, ?_⟩
  · intro k positive early
    rw [source, source2]
    exact agreement k positive early
  · rw [source]
    exact terminal
  · rw [source2]
    exact terminal2

#print axioms sharp_prime_power_gcd_horizon

end D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
