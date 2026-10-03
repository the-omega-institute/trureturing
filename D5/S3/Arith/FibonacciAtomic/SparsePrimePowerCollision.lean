/- GID: D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sparse positive-time observations leave fixed primitive prime-power collisions. -/

import D5.S3.Arith.FibonacciAtomic.TimeSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision

open D5.S3.Arith.FibonacciAtomic.TimeSampling

def signedObservation (n z : ℤ) (k : ℕ) : ℤ :=
  Int.fib ((k : ℤ) - 1) * n + Int.fib (k : ℤ) * z

def sourceObservation (a b k : ℕ) : ℕ :=
  Nat.fib (k + 3) * a + Nat.fib (k + 4) * b

noncomputable def threshold (p e : ℕ) : ℕ :=
  if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then zeroRank (p ^ e)
  else zeroRank (p ^ e) - zeroRank (p ^ (e - 1))

set_option maxHeartbeats 800000 in
theorem sparse_prime_power_gcd_collision (p e Q : ℕ) (hp : p.Prime)
    (he : 2 ≤ e) (hQ : 0 < Q) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k) (hcard : S.card < threshold p e) :
    ∃ n z n2 z2 : ℤ, ∃ a b a2 b2 : ℕ,
      ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ z) ∧
      ¬ ((p : ℤ) ∣ n2 ∧ (p : ℤ) ∣ z2) ∧
      a < Q * p ^ e ∧ b < Q * p ^ e ∧
      a2 < Q * p ^ e ∧ b2 < Q * p ^ e ∧
      (∀ k : ℕ, 1 ≤ k →
        Nat.gcd (sourceObservation a b k) (Q * p ^ e) =
          Q * Nat.gcd (signedObservation n z k).natAbs (p ^ e) ∧
        Nat.gcd (sourceObservation a2 b2 k) (Q * p ^ e) =
          Q * Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) ∧
      (∀ k ∈ S,
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e) ∧
        Nat.gcd (sourceObservation a b k) (Q * p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (Q * p ^ e)) ∧
      (∀ B : ℕ, ∃ t : ℕ, B < t ∧ 1 ≤ t ∧ t ∉ S ∧
        Nat.gcd (signedObservation n z t).natAbs (p ^ e) = p ^ e ∧
        Nat.gcd (signedObservation n2 z2 t).natAbs (p ^ e) = p ^ (e - 1) ∧
        Nat.gcd (sourceObservation a b t) (Q * p ^ e) = Q * p ^ e ∧
        Nat.gcd (sourceObservation a2 b2 t) (Q * p ^ e) = (Q * p ^ e) / p) := by
  classical
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
  have recurrence (n z : ℤ) (k : ℕ) :
      signedObservation n z (k + 2) =
        signedObservation n z k + signedObservation n z (k + 1) := by
    unfold signedObservation
    push_cast
    have first := Int.fib_add_two ((k : ℤ) - 1)
    have second := Int.fib_add_two (k : ℤ)
    rw [show (k : ℤ) + 2 - 1 = k + 1 by ring, second]
    have previous : Int.fib ((k : ℤ) + 1) =
        Int.fib ((k : ℤ) - 1) + Int.fib (k : ℤ) := by
      convert first using 1 <;> congr 1 <;> ring
    rw [previous]
    simp only [add_sub_cancel_right]
    ring
  have shift (n z : ℤ) (s d : ℕ) :
      signedObservation n z (s + d) =
        Int.fib ((d : ℤ) - 1) * signedObservation n z s +
          Int.fib (d : ℤ) * signedObservation n z (s + 1) := by
    unfold signedObservation
    push_cast
    have first := Int.fib_add (d : ℤ) ((s : ℤ) - 1)
    have second := Int.fib_add (d : ℤ) (s : ℤ)
    have previous := Int.fib_add_two ((s : ℤ) - 1)
    simp only [sub_add_cancel] at first previous
    rw [show (s : ℤ) + d - 1 = d + (s - 1) by ring,
      show (s : ℤ) + d = d + s by ring, first, second]
    have normalization : Int.fib ((s : ℤ) + 1) =
        Int.fib ((s : ℤ) - 1) + Int.fib (s : ℤ) := by
      convert previous using 1 <;> congr 1 <;> ring
    rw [normalization]
    ring
  let P := p ^ e
  let q := p ^ (e - 1)
  let R := zeroRank q
  let r := zeroRank P
  have hP : 0 < P := pow_pos hp.pos e
  have hq : 0 < q := pow_pos hp.pos (e - 1)
  let : NeZero P := ⟨hP.ne'⟩
  have lowerFacts := ranks q hq
  have topFacts := ranks P hP
  have Rpos : 0 < R := lowerFacts.1
  have rpos : 0 < r := topFacts.1
  have factor : P = q * p := by
    dsimp [P, q]
    rw [← pow_succ]
    congr 1
    omega
  have qdvd : q ∣ P := by rw [factor]; exact dvd_mul_right _ _
  have pdvd : p ∣ q := dvd_pow_self p (by omega)
  let scalar : ℤ := Int.fib ((R : ℤ) - 1)
  let offDiagonal : ℤ := Int.fib (R : ℤ)
  have lowerDivides : (q : ℤ) ∣ offDiagonal := by
    dsimp [offDiagonal, R]
    exact_mod_cast lowerFacts.2.1
  have scalarNat : scalar = (Nat.fib (R - 1) : ℤ) := by
    dsimp [scalar]
    rw [show (R : ℤ) - 1 = ((R - 1 : ℕ) : ℤ) by omega, Int.fib_natCast]
  have scalarPrime : ¬ p ∣ Nat.fib (R - 1) := by
    have adjacent := Nat.fib_coprime_fib_succ (R - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)] at adjacent
    exact fun divides => Nat.not_coprime_of_dvd_of_dvd hp.one_lt divides
      (dvd_trans pdvd lowerFacts.2.1) adjacent
  have scalarUnit : IsUnit (scalar : ZMod P) := by
    rw [scalarNat, Int.cast_natCast]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr scalarPrime
  have annihilate : (p : ZMod P) * (offDiagonal : ZMod P) = 0 := by
    obtain ⟨coefficient, coefficientEq⟩ := lowerDivides
    rw [← Int.cast_natCast p, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [coefficientEq, factor]
    exact ⟨coefficient, by push_cast; ring⟩
  have squareZero : (offDiagonal : ZMod P) ^ 2 = 0 := by
    have lowerSquare : P ∣ q ^ 2 := by
      rw [factor, pow_two]
      exact Nat.mul_dvd_mul_left q pdvd
    obtain ⟨coefficient, coefficientEq⟩ := lowerDivides
    rw [coefficientEq]
    push_cast
    rw [mul_pow]
    have lowerZero : (q : ZMod P) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact lowerSquare
    rw [lowerZero, zero_mul]
  have block (n z : ℤ) (s blocks : ℕ) :
      (scalar : ZMod P) * (signedObservation n z (s + blocks * R) : ZMod P) =
        (scalar : ZMod P) ^ blocks *
          ((scalar : ZMod P) * (signedObservation n z s : ZMod P) +
            (blocks : ZMod P) * (offDiagonal : ZMod P) *
              (signedObservation n z (s + 1) : ZMod P)) := by
    induction blocks generalizing s with
    | zero => simp
    | succ blocks ih =>
      have shifted := shift n z (s + blocks * R) R
      have next := ih (s + 1)
      have previous := ih s
      have recurrenceMod := congrArg (fun value : ℤ => (value : ZMod P)) (recurrence n z s)
      push_cast at recurrenceMod
      rw [show s + (blocks + 1) * R = (s + blocks * R) + R by ring, shifted]
      push_cast
      change (scalar : ZMod P) *
          ((scalar : ZMod P) * (signedObservation n z (s + blocks * R) : ZMod P) +
            (offDiagonal : ZMod P) *
              (signedObservation n z (s + blocks * R + 1) : ZMod P)) = _
      rw [show s + blocks * R + 1 = s + 1 + blocks * R by omega]
      calc
        _ = (scalar : ZMod P) *
              ((scalar : ZMod P) * (signedObservation n z (s + blocks * R) : ZMod P)) +
            (offDiagonal : ZMod P) *
              ((scalar : ZMod P) * (signedObservation n z (s + 1 + blocks * R) : ZMod P)) := by ring
        _ = _ := by
          rw [previous, next, show s + 1 + 1 = s + 2 by omega, recurrenceMod, pow_succ]
          have nilpotent : (offDiagonal : ZMod P) * offDiagonal = 0 := by
            simpa only [pow_two] using squareZero
          linear_combination
            (scalar : ZMod P) ^ blocks * (blocks : ZMod P) *
              (signedObservation n z s + signedObservation n z (s + 1) : ZMod P) * nilpotent
  have upperZero : P ∣ Nat.fib (p * R) := by
    have returning : (signedObservation 0 1 (p * R) : ZMod P) = 0 := by
      apply scalarUnit.mul_left_cancel
      have equality := block 0 1 0 p
      have vanish : (p : ZMod P) * offDiagonal * (signedObservation 0 1 1 : ZMod P) = 0 := by
        rw [annihilate, zero_mul]
      simp only [zero_add] at equality
      rw [vanish] at equality
      simpa [signedObservation] using equality
    have zero : (Nat.fib (p * R) : ZMod P) = 0 := by
      simpa only [signedObservation, Int.fib_natCast, Int.cast_natCast,
        mul_zero, mul_one, add_zero, zero_add, Int.cast_zero] using returning
    exact (ZMod.natCast_eq_zero_iff _ _).mp zero
  have entry (m : ℕ) (hm : 0 < m) (index : ℕ) :
      m ∣ Nat.fib index ↔ zeroRank m ∣ index := by
    have facts := ranks m hm
    exact D5.S3.Arith.FibonacciRank.fibonacci_entry_point facts.1 facts.2.1 facts.2.2
  have dichotomy : r = R ∨ r = p * R := by
    have rankDivides : R ∣ r := (entry q hq r).mp (dvd_trans qdvd topFacts.2.1)
    have topDivides : r ∣ p * R := (entry P hP _).mp upperZero
    obtain ⟨coefficient, coefficientEq⟩ := rankDivides
    have coefficientDivides : coefficient ∣ p := by
      rw [coefficientEq, mul_comm p R] at topDivides
      exact (Nat.mul_dvd_mul_iff_left Rpos).mp topDivides
    rcases (Nat.dvd_prime hp).mp coefficientDivides with one | prime
    · left; simpa [one] using coefficientEq
    · right; simpa [prime, mul_comm] using coefficientEq
  have absFib (index : ℤ) : (Int.fib index).natAbs = Nat.fib index.natAbs := by
    obtain ⟨index, (rfl | rfl)⟩ := index.eq_nat_or_neg
    · simp
    · simp [Int.fib_neg_natCast, Int.natAbs_mul]
  have intEntry (m : ℕ) (hm : 0 < m) (index : ℤ) :
      (m : ℤ) ∣ Int.fib index ↔ (zeroRank m : ℤ) ∣ index := by
    rw [Int.natCast_dvd, absFib, entry m hm, ← Int.natCast_dvd]
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
  have gcdCongruence (m : ℕ) (x y : ℤ) (same : (x : ZMod m) = (y : ZMod m)) :
      Nat.gcd x.natAbs m = Nat.gcd y.natAbs m := by
    apply gcdDivisors
    intro d divides
    exact ((ZMod.intCast_eq_intCast_iff _ _ _).mp same |>.of_dvd
      (Int.natCast_dvd_natCast.mpr divides)).dvd_iff
  have recoverTop (x y : ℤ)
      (lower : Nat.gcd x.natAbs q = Nat.gcd y.natAbs q)
      (top : (P : ℤ) ∣ x ↔ (P : ℤ) ∣ y) :
      Nat.gcd x.natAbs P = Nat.gcd y.natAbs P := by
    apply gcdDivisors
    intro d hd
    obtain ⟨level, hlevel, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    by_cases full : level = e
    · simpa [full, P] using top
    · have divides : p ^ level ∣ q := by
        exact pow_dvd_pow p (by omega)
      rw [Int.natCast_dvd, Int.natCast_dvd]
      constructor
      · intro hx
        have common : p ^ level ∣ Nat.gcd x.natAbs q := Nat.dvd_gcd hx divides
        rw [lower] at common
        exact dvd_trans common (Nat.gcd_dvd_left y.natAbs q)
      · intro hy
        have common : p ^ level ∣ Nat.gcd y.natAbs q := Nat.dvd_gcd hy divides
        rw [← lower] at common
        exact dvd_trans common (Nat.gcd_dvd_left x.natAbs q)
  have exactLower (x : ℤ) (lower : (q : ℤ) ∣ x) (notTop : ¬ (P : ℤ) ∣ x) :
      Nat.gcd x.natAbs P = q := by
    obtain ⟨level, bound, equation⟩ :=
      (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right x.natAbs P)
    have below : level < e := by
      by_contra bad
      have levelEq : level = e := by omega
      have divides := Nat.gcd_dvd_left x.natAbs P
      rw [equation, levelEq] at divides
      exact notTop (Int.natCast_dvd.mpr divides)
    have above : e - 1 ≤ level := by
      have divides : q ∣ Nat.gcd x.natAbs P :=
        Nat.dvd_gcd (Int.natCast_dvd.mp lower) qdvd
      rw [equation] at divides
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp divides
    have levelEq : level = e - 1 := by omega
    simpa [q, levelEq] using equation
  have kernelIdentity (terminal k : ℕ) :
      signedObservation (Int.fib (terminal : ℤ)) (-Int.fib ((terminal : ℤ) - 1)) k =
        (-1 : ℤ) ^ k * Int.fib ((terminal : ℤ) - k) := by
    induction k using Nat.twoStepInduction with
    | zero => simp [signedObservation]
    | one => simp [signedObservation]
    | more k current next =>
      rw [recurrence, current, next]
      have reverse := Int.fib_add_two ((terminal : ℤ) - (k + 2))
      have normalized : Int.fib ((terminal : ℤ) - k) =
          Int.fib ((terminal : ℤ) - (k + 2)) + Int.fib ((terminal : ℤ) - (k + 1)) := by
        convert reverse using 1 <;> congr 1 <;> push_cast <;> ring
      push_cast
      rw [normalized, pow_succ, pow_add]
      ring
  have kernelAbs (terminal k : ℕ) :
      (signedObservation (Int.fib (terminal : ℤ)) (-Int.fib ((terminal : ℤ) - 1)) k).natAbs =
        (Int.fib ((terminal : ℤ) - k)).natAbs := by
    rw [kernelIdentity, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have kernelPhase (m : ℕ) (hm : 0 < m) (terminal k : ℕ) :
      (m : ℤ) ∣ signedObservation (Int.fib (terminal : ℤ))
          (-Int.fib ((terminal : ℤ) - 1)) k ↔
        k % zeroRank m = terminal % zeroRank m := by
    rw [Int.natCast_dvd, kernelAbs, ← Int.natCast_dvd, intEntry m hm]
    exact Nat.modEq_iff_dvd.symm
  have kernelPrimitive (terminal : ℕ) (positive : 0 < terminal) :
      ¬ ((p : ℤ) ∣ Int.fib (terminal : ℤ) ∧
        (p : ℤ) ∣ -Int.fib ((terminal : ℤ) - 1)) := by
    rintro ⟨first, second⟩
    have adjacent := Nat.fib_coprime_fib_succ (terminal - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ terminal)] at adjacent
    have prev : p ∣ Nat.fib (terminal - 1) := by
      have index : (terminal : ℤ) - 1 = ((terminal - 1 : ℕ) : ℤ) := by omega
      simpa [index, Int.natCast_dvd, Int.fib_natCast] using second
    have curr : p ∣ Nat.fib terminal := by
      simpa [Int.natCast_dvd, Int.fib_natCast] using first
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt prev curr adjacent
  have lowerFib (index : ℤ) :
      Nat.gcd (Int.fib index).natAbs q = Nat.gcd (Nat.fib (Int.gcd index (R : ℤ))) q := by
    have strong : Nat.gcd (Int.fib index).natAbs (Nat.fib R) =
        Nat.fib (Int.gcd index (R : ℤ)) := by
      simpa [Int.gcd_def] using Int.gcd_fib index (R : ℤ)
    calc
      _ = Nat.gcd (Int.fib index).natAbs (Nat.gcd (Nat.fib R) q) := by
        rw [Nat.gcd_eq_right lowerFacts.2.1]
      _ = Nat.gcd (Nat.gcd (Int.fib index).natAbs (Nat.fib R)) q :=
        (Nat.gcd_assoc _ _ _).symm
      _ = _ := by rw [strong]
  have lowerKernels (terminal terminal2 k : ℕ)
      (same : terminal % R = terminal2 % R) :
      Nat.gcd (signedObservation (Int.fib (terminal : ℤ))
        (-Int.fib ((terminal : ℤ) - 1)) k).natAbs q =
      Nat.gcd (signedObservation (Int.fib (terminal2 : ℤ))
        (-Int.fib ((terminal2 : ℤ) - 1)) k).natAbs q := by
    rw [kernelAbs, kernelAbs, lowerFib, lowerFib]
    have congruent : Int.ModEq (R : ℤ) (terminal : ℤ) (terminal2 : ℤ) :=
      Int.natCast_modEq_iff.mpr same
    have differences := congruent.sub_right (k : ℤ)
    have equalGcd : Int.gcd ((terminal : ℤ) - k) (R : ℤ) =
        Int.gcd ((terminal2 : ℤ) - k) (R : ℤ) := by
      calc
        _ = Int.gcd (((terminal : ℤ) - k) % R) (R : ℤ) := (Int.gcd_emod _ _).symm
        _ = Int.gcd (((terminal2 : ℤ) - k) % R) (R : ℤ) := by rw [differences.eq]
        _ = _ := Int.gcd_emod _ _
    rw [equalGcd]
  let omitted := Finset.range r \ S.image (fun k => k % r)
  have omittedFacts (phase : ℕ) (member : phase ∈ omitted) :
      phase < r ∧ ∀ k ∈ S, k % r ≠ phase := by
    have facts := Finset.mem_sdiff.mp member
    refine ⟨Finset.mem_range.mp facts.1, ?_⟩
    intro k hk equality
    exact facts.2 (Finset.mem_image.mpr ⟨k, hk, equality⟩)
  have omittedCard : r ≤ omitted.card + S.card := by
    have bound : r ≤ omitted.card + (S.image (fun k => k % r)).card := by
      simpa only [Finset.card_range] using Finset.card_le_card_sdiff_add_card
        (s := Finset.range r) (t := S.image (fun k => k % r))
    have imageBound := Finset.card_image_le (s := S) (f := fun k => k % r)
    omega
  have localCollision : ∃ n z n2 z2 : ℤ,
      ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ z) ∧
      ¬ ((p : ℤ) ∣ n2 ∧ (p : ℤ) ∣ z2) ∧
      (∀ k ∈ S, Nat.gcd (signedObservation n z k).natAbs P =
        Nat.gcd (signedObservation n2 z2 k).natAbs P) ∧
      (∀ B : ℕ, ∃ k : ℕ, B < k ∧ 1 ≤ k ∧ k ∉ S ∧
        Nat.gcd (signedObservation n z k).natAbs P = P ∧
        Nat.gcd (signedObservation n2 z2 k).natAbs P = q) := by
    rcases dichotomy with stagnant | growth
    · have thresholdEq : threshold p e = r := by
        unfold threshold
        change (if r = R then r else r - R) = r
        rw [if_pos stagnant]
      have nonempty : omitted.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨phase, member⟩ := nonempty
      have phaseFacts := omittedFacts phase member
      let terminal := phase + r
      have terminalPositive : 0 < terminal := by dsimp [terminal]; omega
      have terminalPhase : terminal % r = phase := by
        dsimp [terminal]
        simp [Nat.mod_eq_of_lt phaseFacts.1]
      let n := Int.fib (terminal : ℤ)
      let z := -Int.fib ((terminal : ℤ) - 1)
      let n2 := n - (q : ℤ) * Int.fib ((terminal + 1 : ℕ) : ℤ)
      let z2 := z + (q : ℤ) * Int.fib (terminal : ℤ)
      have primitive := kernelPrimitive terminal terminalPositive
      have primitive2 : ¬ ((p : ℤ) ∣ n2 ∧ (p : ℤ) ∣ z2) := by
        rintro ⟨first, second⟩
        apply primitive
        have pq : (p : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.mpr pdvd
        constructor
        · have total := dvd_add first (dvd_mul_of_dvd_left pq (Int.fib (terminal + 1 : ℤ)))
          have restore : n2 + (q : ℤ) * Int.fib (terminal + 1 : ℤ) = n := by
            dsimp [n2]
            push_cast
            ring
          rwa [restore] at total
        · have total := dvd_sub second (dvd_mul_of_dvd_left pq (Int.fib (terminal : ℤ)))
          have restore : z2 - (q : ℤ) * Int.fib (terminal : ℤ) = z := by
            dsimp [z2]
            ring
          rwa [restore] at total
      have perturb (k : ℕ) : signedObservation n2 z2 k =
          signedObservation n z k - (q : ℤ) *
            signedObservation (Int.fib ((terminal + 1 : ℕ) : ℤ))
              (-Int.fib (terminal : ℤ)) k := by
        dsimp [signedObservation, n2, z2]
        ring
      have lowerSame (k : ℕ) : (signedObservation n2 z2 k : ZMod q) =
          (signedObservation n z k : ZMod q) := by
        rw [perturb]
        push_cast
        simp
      have absence (k : ℕ) (hk : k ∈ S) : ¬ (q : ℤ) ∣ signedObservation n z k := by
        intro divides
        have hit := (kernelPhase q hq terminal k).mp divides
        change k % R = terminal % R at hit
        rw [← stagnant, terminalPhase] at hit
        exact phaseFacts.2 k hk hit
      refine ⟨n, z, n2, z2, primitive, primitive2, ?_, ?_⟩
      · intro k hk
        apply recoverTop
        · exact (gcdCongruence q _ _ (lowerSame k)).symm
        · have absent := absence k hk
          have absent2 : ¬ (q : ℤ) ∣ signedObservation n2 z2 k := by
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, lowerSame,
              ZMod.intCast_zmod_eq_zero_iff_dvd]
            exact absent
          have qP : (q : ℤ) ∣ (P : ℤ) := Int.natCast_dvd_natCast.mpr qdvd
          exact iff_of_false (fun h => absent (dvd_trans qP h))
            (fun h => absent2 (dvd_trans qP h))
      · intro B
        let k := phase + (B + 1) * r
        have kPhase : k % r = phase := by
          dsimp [k]
          simp [Nat.mod_eq_of_lt phaseFacts.1]
        have kLarge : B < k ∧ 1 ≤ k := by
          have one : 1 ≤ r := rpos
          dsimp [k]
          constructor <;> nlinarith
        have firstZero : (P : ℤ) ∣ signedObservation n z k :=
          (kernelPhase P hP terminal k).mpr (kPhase.trans terminalPhase.symm)
        have adjacentNotZero : ¬ (p : ℤ) ∣
            signedObservation (Int.fib ((terminal + 1 : ℕ) : ℤ))
              (-Int.fib (terminal : ℤ)) k := by
          intro adjacentZero
          have prevZero : (p : ℤ) ∣ Int.fib ((terminal : ℤ) - k) := by
            apply (intEntry p hp.pos _).mpr
            have topIndex := (intEntry P hP _).mp
              (Int.natCast_dvd.mpr (by
                rw [← kernelAbs terminal k]
                exact Int.natCast_dvd.mp firstZero))
            exact dvd_trans
              (Int.natCast_dvd_natCast.mpr ((entry p hp.pos r).mp
                (dvd_trans (dvd_trans pdvd qdvd) topFacts.2.1))) topIndex
          have nextZero : (p : ℤ) ∣ Int.fib (((terminal + 1 : ℕ) : ℤ) - k) := by
            apply Int.natCast_dvd.mpr
            rw [← kernelAbs (terminal + 1) k]
            have index : ((terminal + 1 : ℕ) : ℤ) - 1 = terminal := by push_cast; ring
            simpa [index] using Int.natCast_dvd.mp adjacentZero
          have adjacent : Int.gcd (Int.fib ((terminal : ℤ) - k))
              (Int.fib (((terminal + 1 : ℕ) : ℤ) - k)) = 1 := by
            rw [Int.gcd_fib]
            push_cast
            rw [show (terminal : ℤ) + 1 - k = 1 + (terminal - k) by ring,
              Int.gcd_add_self_right]
            simp
          have common := Nat.dvd_gcd (Int.natCast_dvd.mp prevZero)
            (Int.natCast_dvd.mp nextZero)
          change p ∣ Int.gcd (Int.fib ((terminal : ℤ) - k))
            (Int.fib (((terminal + 1 : ℕ) : ℤ) - k)) at common
          rw [adjacent] at common
          exact hp.ne_one (Nat.dvd_one.mp common)
        have secondLower : (q : ℤ) ∣ signedObservation n2 z2 k := by
          rw [perturb]
          exact dvd_sub (dvd_trans (Int.natCast_dvd_natCast.mpr qdvd) firstZero)
            (dvd_mul_right _ _)
        have secondNotTop : ¬ (P : ℤ) ∣ signedObservation n2 z2 k := by
          intro bad
          have divides := dvd_sub firstZero bad
          rw [perturb, sub_sub_cancel] at divides
          rw [factor, Nat.cast_mul] at divides
          have qnonzero : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
          exact adjacentNotZero ((mul_dvd_mul_iff_left qnonzero).mp divides)
        refine ⟨k, kLarge.1, kLarge.2, ?_,
          Nat.gcd_eq_right (Int.natCast_dvd.mp firstZero), exactLower _ secondLower secondNotTop⟩
        intro member
        exact phaseFacts.2 k member kPhase
    · have growing : r ≠ R := by rw [growth]; nlinarith [hp.two_le, Rpos]
      have thresholdEq : threshold p e = r - R := by
        unfold threshold
        change (if r = R then r else r - R) = r - R
        rw [if_neg growing]
      have many : R < omitted.card := by rw [thresholdEq] at hcard; omega
      obtain ⟨phase, phaseMember, phase2, phase2Member, different, same⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to
          (s := omitted) (t := Finset.range R) (f := fun k => k % R)
          (by simpa using many) (by
            intro k hk
            exact Finset.mem_range.mpr (Nat.mod_lt _ Rpos))
      have facts := omittedFacts phase phaseMember
      have facts2 := omittedFacts phase2 phase2Member
      let terminal := phase + r
      let terminal2 := phase2 + r
      have terminalPositive : 0 < terminal := by dsimp [terminal]; omega
      have terminal2Positive : 0 < terminal2 := by dsimp [terminal2]; omega
      have terminalPhase : terminal % r = phase := by
        dsimp [terminal]; simp [Nat.mod_eq_of_lt facts.1]
      have terminal2Phase : terminal2 % r = phase2 := by
        dsimp [terminal2]; simp [Nat.mod_eq_of_lt facts2.1]
      have lowerSame : terminal % R = terminal2 % R := by
        dsimp [terminal, terminal2]
        rw [Nat.add_mod, Nat.add_mod, growth]
        simp [same]
      let n := Int.fib (terminal : ℤ)
      let z := -Int.fib ((terminal : ℤ) - 1)
      let n2 := Int.fib (terminal2 : ℤ)
      let z2 := -Int.fib ((terminal2 : ℤ) - 1)
      refine ⟨n, z, n2, z2, kernelPrimitive terminal terminalPositive,
        kernelPrimitive terminal2 terminal2Positive, ?_, ?_⟩
      · intro k hk
        apply recoverTop
        · exact lowerKernels terminal terminal2 k lowerSame
        · have first : ¬ (P : ℤ) ∣ signedObservation n z k := by
            intro zero
            have hit := (kernelPhase P hP terminal k).mp zero
            rw [terminalPhase] at hit
            exact facts.2 k hk hit
          have second : ¬ (P : ℤ) ∣ signedObservation n2 z2 k := by
            intro zero
            have hit := (kernelPhase P hP terminal2 k).mp zero
            rw [terminal2Phase] at hit
            exact facts2.2 k hk hit
          exact iff_of_false first second
      · intro B
        let k := phase + (B + 1) * r
        have kPhase : k % r = phase := by
          dsimp [k]; simp [Nat.mod_eq_of_lt facts.1]
        have kLarge : B < k ∧ 1 ≤ k := by
          have one : 1 ≤ r := rpos
          dsimp [k]
          constructor <;> nlinarith
        have firstZero : (P : ℤ) ∣ signedObservation n z k :=
          (kernelPhase P hP terminal k).mpr (kPhase.trans terminalPhase.symm)
        have secondNotTop : ¬ (P : ℤ) ∣ signedObservation n2 z2 k := by
          intro zero
          have hit := (kernelPhase P hP terminal2 k).mp zero
          rw [kPhase, terminal2Phase] at hit
          exact different hit
        have secondLower : (q : ℤ) ∣ signedObservation n2 z2 k := by
          have equal := lowerKernels terminal terminal2 k lowerSame
          have firstLower : Nat.gcd (signedObservation n z k).natAbs q = q :=
            Nat.gcd_eq_right (Int.natCast_dvd.mp
              (dvd_trans (Int.natCast_dvd_natCast.mpr qdvd) firstZero))
          change Nat.gcd (signedObservation n z k).natAbs q =
            Nat.gcd (signedObservation n2 z2 k).natAbs q at equal
          have answer := equal.symm.trans firstLower
          exact Int.natCast_dvd.mpr (Nat.gcd_eq_right_iff_dvd.mp answer)
        refine ⟨k, kLarge.1, kLarge.2, ?_,
          Nat.gcd_eq_right (Int.natCast_dvd.mp firstZero), exactLower _ secondLower secondNotTop⟩
        intro member
        exact facts.2 k member kPhase
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
  have realization (n z : ℤ) : ∃ a b : ℕ, a < Q * P ∧ b < Q * P ∧
      ∀ k : ℕ, Nat.gcd (sourceObservation a b k) (Q * P) =
        Q * Nat.gcd (signedObservation n z k).natAbs P := by
    let first : ZMod P := 5 * (n : ZMod P) - 3 * (z : ZMod P)
    let second : ZMod P := -3 * (n : ZMod P) + 2 * (z : ZMod P)
    refine ⟨Q * first.val, Q * second.val,
      Nat.mul_lt_mul_of_pos_left (ZMod.val_lt first) hQ,
      Nat.mul_lt_mul_of_pos_left (ZMod.val_lt second) hQ, ?_⟩
    intro k
    have initial : (2 * (first.val : ℤ) + 3 * second.val : ZMod P) = n := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      dsimp [first, second]
      ring
    have next : (3 * (first.val : ℤ) + 5 * second.val : ZMod P) = z := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      dsimp [first, second]
      ring
    have same : (sourceObservation first.val second.val k : ZMod P) =
        (signedObservation n z k : ZMod P) := by
      rw [← Int.cast_natCast, ← naturalIdentity]
      unfold signedObservation
      push_cast
      push_cast at initial next
      rw [initial, next]
    have sameGcd := gcdCongruence P (sourceObservation first.val second.val k : ℤ)
      (signedObservation n z k) (by simpa only [Int.cast_natCast] using same)
    have scaled : sourceObservation (Q * first.val) (Q * second.val) k =
        Q * sourceObservation first.val second.val k := by
      unfold sourceObservation
      ring
    rw [scaled, Nat.gcd_mul_left]
    simpa only [Int.natAbs_natCast] using congrArg (Q * ·) sameGcd
  obtain ⟨n, z, n2, z2, primitive, primitive2, agreement, separation⟩ := localCollision
  obtain ⟨a, b, boundA, boundB, realize⟩ := realization n z
  obtain ⟨a2, b2, boundA2, boundB2, realize2⟩ := realization n2 z2
  refine ⟨n, z, n2, z2, a, b, a2, b2, primitive, primitive2,
    boundA, boundB, boundA2, boundB2, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨realize k, realize2 k⟩
  · intro k hk
    exact ⟨agreement k hk, by rw [realize, realize2, agreement k hk]⟩
  · intro B
    obtain ⟨k, later, positive, omittedTime, first, second⟩ := separation B
    refine ⟨k, later, positive, omittedTime, first, second, ?_, ?_⟩
    · rw [realize, first]
    · rw [realize2, second]
      change Q * q = (Q * P) / p
      rw [factor, ← mul_assoc, Nat.mul_div_left _ hp.pos]

end D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision
