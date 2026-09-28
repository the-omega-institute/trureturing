/- GID: D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Disjoint golden cubic block supports and exact matrix periods of block powers. -/

import Mathlib
import D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
import D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod

namespace D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods

open scoped Matrix
open D5.S1.Scale
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
open D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure

/-- Distinct cubic blocks have disjoint prime supports, and every positive
power of a block has its native Fibonacci matrix period. -/
theorem cubic_block_native_power_periods :
    let C := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 1).natAbs
    let B := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
    let π := fun m : ℕ => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) ∧
    (∀ j a b : ℕ, 1 ≤ j → 1 ≤ a → 1 ≤ b →
      π ((C j) ^ a) = 4 * 3 ^ (j + 1) * (C j) ^ (a - 1) ∧
      π ((B j) ^ b) = 2 * 3 ^ (j + 1) * (B j) ^ (b - 1) ∧
      π ((C j) ^ a * (B j) ^ b) =
        4 * 3 ^ (j + 1) * (C j) ^ (a - 1) * (B j) ^ (b - 1)) := by
  let C (k : ℕ) : ℕ := (goldenLucas (3 ^ k) ^ 2 + 1).natAbs
  let B (k : ℕ) : ℕ := (goldenLucas (3 ^ k) ^ 2 + 3).natAbs
  let π (m : ℕ) : ℕ := orderOf
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
  change (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
    (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
    (∀ i j, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) ∧
    (∀ j a b, 1 ≤ j → 1 ≤ a → 1 ≤ b →
      π (C j ^ a) = 4 * 3 ^ (j + 1) * C j ^ (a - 1) ∧
      π (B j ^ b) = 2 * 3 ^ (j + 1) * B j ^ (b - 1) ∧
      π (C j ^ a * B j ^ b) =
        4 * 3 ^ (j + 1) * C j ^ (a - 1) * B j ^ (b - 1))
  have hCcast (k : ℕ) : (C k : ℤ) = goldenLucas (3 ^ k) ^ 2 + 1 := by
    simp [C, abs_of_nonneg (by positivity : 0 ≤ goldenLucas (3 ^ k) ^ 2 + 1)]
  have hBcast (k : ℕ) : (B k : ℤ) = goldenLucas (3 ^ k) ^ 2 + 3 := by
    simp [B, abs_of_nonneg (by positivity : 0 ≤ goldenLucas (3 ^ k) ^ 2 + 3)]
  have hSupport :
      (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
      (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
      (∀ i j, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) := by
    constructor
    · intro i j hi hj hij
      by_contra hcop
      obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpiInt : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 1 := by
        rw [← hCcast]
        exact Int.natCast_dvd.mpr hpi
      have hpjInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1 := by
        rw [← hCcast]
        exact Int.natCast_dvd.mpr hpj
      have heq : 3 ^ (i + 1) = 3 ^ (j + 1) :=
        (cubic_block_c_prime_rank i p hi hp hpiInt).1.symm.trans
          (cubic_block_c_prime_rank j p hj hp hpjInt).1
      have := Nat.pow_right_injective (by decide : 2 ≤ 3) heq
      exact hij (by omega)
    constructor
    · intro i j hi hj hij
      by_contra hcop
      obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpiInt : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 3 := by
        rw [← hBcast]
        exact Int.natCast_dvd.mpr hpi
      have hpjInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
        rw [← hBcast]
        exact Int.natCast_dvd.mpr hpj
      have heq : 2 * 3 ^ (i + 1) = 2 * 3 ^ (j + 1) :=
        (cubic_block_b_prime_rank i p hi hp hpiInt).1.symm.trans
          (cubic_block_b_prime_rank j p hj hp hpjInt).1
      have hpow : 3 ^ (i + 1) = 3 ^ (j + 1) := by omega
      have := Nat.pow_right_injective (by decide : 2 ≤ 3) hpow
      exact hij (by omega)
    · intro i j hi hj
      by_contra hcop
      obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpiInt : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 1 := by
        rw [← hCcast]
        exact Int.natCast_dvd.mpr hpi
      have hpjInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
        rw [← hBcast]
        exact Int.natCast_dvd.mpr hpj
      have heq : 3 ^ (i + 1) = 2 * 3 ^ (j + 1) :=
        (cubic_block_c_prime_rank i p hi hp hpiInt).1.symm.trans
          (cubic_block_b_prime_rank j p hj hp hpjInt).1
      have hodd : Odd (3 ^ (i + 1)) := (by decide : Odd (3 : ℕ)).pow
      have heven : Even (3 ^ (i + 1)) := by
        rw [heq]
        exact even_two_mul _
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hSize (j : ℕ) (hj : 1 ≤ j) : 1 < C j ∧ 1 < B j := by
    let L : ℤ := goldenLucas (3 ^ j)
    have hL72 : ((L : ℤ) : ZMod 72) = 4 := (golden_cubic_lucas_block j hj).1
    have hLne : L ≠ 0 := by
      intro h
      rw [h] at hL72
      exact (by decide : (0 : ZMod 72) ≠ 4) hL72
    have hsq : 0 < L ^ 2 := sq_pos_of_ne_zero hLne
    dsimp only [L] at hsq
    have hc := hCcast j
    have hb := hBcast j
    constructor <;> omega
  have hCPrimeData (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
      (hpC : p ∣ C j) :
      5 < p ∧ (C j).factorization p =
        padicValNat p (Nat.fib (fibonacciRank p)) := by
    let Cj := C j
    have hcast : (Cj : ℤ) = goldenLucas (3 ^ j) ^ 2 + 1 := hCcast j
    have hpInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1 := by
      rw [← hcast]
      exact Int.natCast_dvd.mpr hpC
    have hrank := (cubic_block_c_prime_rank j p hj hp hpInt).2
    have hL72 := (golden_cubic_lucas_block j hj).1
    have hC72 : (Cj : ZMod 72) = 17 := by
      have hSq : ((goldenLucas (3 ^ j) ^ 2 + 1 : ℤ) : ZMod 72) = 17 := by
        push_cast
        rw [hL72]
        norm_num
      change ((Cj : ℤ) : ZMod 72) = 17
      rw [hcast]
      exact hSq
    have hC2 : (Cj : ZMod 2) = 1 := by
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2)) hC72
      simpa only [map_natCast, map_ofNat, show (17 : ZMod 2) = 1 by decide] using h
    have hC3 : (Cj : ZMod 3) = 2 := by
      have h := congrArg (ZMod.castHom (by decide : 3 ∣ 72) (ZMod 3)) hC72
      simpa only [map_natCast, map_ofNat, show (17 : ZMod 3) = 2 by decide] using h
    have hC5 : (Cj : ZMod 5) = 2 := by
      change ((Cj : ℤ) : ZMod 5) = 2
      rw [hcast]
      have hSq := (golden_cubic_lucas_block j hj).2.2.2.1
      push_cast at hSq
      push_cast
      rw [hSq]
      norm_num
    have hnot2 : ¬ 2 ∣ Cj := by
      intro h
      have hz : (Cj : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [hC2] at hz
      exact (by decide : (1 : ZMod 2) ≠ 0) hz
    have hnot3 : ¬ 3 ∣ Cj := by
      intro h
      have hz : (Cj : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [hC3] at hz
      exact (by decide : (2 : ZMod 3) ≠ 0) hz
    have hnot5 : ¬ 5 ∣ Cj := by
      intro h
      have hz : (Cj : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [hC5] at hz
      exact (by decide : (2 : ZMod 5) ≠ 0) hz
    have hp2 : p ≠ 2 := by rintro rfl; exact hnot2 hpC
    have hp3 : p ≠ 3 := by rintro rfl; exact hnot3 hpC
    have hp5 : p ≠ 5 := by rintro rfl; exact hnot5 hpC
    have hpgt : 5 < p := by
      obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
      have htwo := hp.two_le
      omega
    refine ⟨hpgt, ?_⟩
    change Cj.factorization p = _
    rw [Nat.factorization_def Cj hp]
    rw [← hcast] at hrank
    simpa only [padicValInt.of_nat] using hrank
  have hSubtypeLcm (S : Finset ℕ) (f : ℕ → ℕ) :
      (Finset.univ : Finset S).lcm (fun p => f p) = S.lcm f := by
    symm
    calc
      S.lcm f = (Finset.image (fun p : S => (p : ℕ)) Finset.univ).lcm f := by
        congr 1
        ext p
        simp
      _ = (Finset.univ : Finset S).lcm (f ∘ fun p : S => (p : ℕ)) :=
        Finset.lcm_image _
      _ = (Finset.univ : Finset S).lcm (fun p => f p) := rfl
  have hCRT (m : ℕ) (hm : m ≠ 0) :
      π m = m.primeFactors.lcm (fun p => π (p ^ m.factorization p)) := by
    let E : Matrix (Fin 2) (Fin 2) (ZMod m) ≃+*
        (∀ p : m.primeFactors,
          Matrix (Fin 2) (Fin 2) (ZMod ((p : ℕ) ^ m.factorization p))) :=
      ((ZMod.equivPi m hm).mapMatrix).trans Matrix.piRingEquiv
    let Qm : Matrix (Fin 2) (Fin 2) (ZMod m) := !![1, 1; 1, 0]
    have hQ (p : m.primeFactors) : E Qm p =
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
          (ZMod ((p : ℕ) ^ m.factorization p))) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [E, Qm]
    change orderOf Qm = _
    calc
      orderOf Qm = orderOf (E Qm) := (E.toMulEquiv.orderOf_eq Qm).symm
      _ = (Finset.univ : Finset m.primeFactors).lcm
          (fun p => orderOf (E Qm p)) := Pi.orderOf (E Qm)
      _ = (Finset.univ : Finset m.primeFactors).lcm
          (fun p => π ((p : ℕ) ^ m.factorization p)) := by
            apply Finset.lcm_congr rfl
            intro p hp
            exact congrArg orderOf (hQ p)
      _ = m.primeFactors.lcm (fun p => π (p ^ m.factorization p)) :=
        hSubtypeLcm m.primeFactors (fun p => π (p ^ m.factorization p))
  have hLcm (M τ a : ℕ) (hM : 1 < M) (hcop : M.Coprime τ) :
      M.primeFactors.lcm
        (fun p => τ * p ^ ((a - 1) * M.factorization p)) =
          τ * M ^ (a - 1) := by
    let S := M.primeFactors
    let f := fun p : ℕ => p ^ ((a - 1) * M.factorization p)
    have hMne : M ≠ 0 := by omega
    have hprod : M ^ (a - 1) = ∏ p ∈ S, f p := by
      rw [Nat.prod_primeFactors_pow_factorization hMne, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [f, pow_mul] using pow_right_comm p (M.factorization p) (a - 1)
    have hupper : S.lcm (fun p => τ * f p) ∣ τ * M ^ (a - 1) := by
      apply Finset.lcm_dvd
      intro p hp
      have hf : f p ∣ M ^ (a - 1) := by
        rw [hprod]
        exact Finset.dvd_prod_of_mem f hp
      exact mul_dvd_mul_left τ hf
    have hbase : τ ∣ S.lcm (fun p => τ * f p) := by
      obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hM
      exact (dvd_mul_right τ (f p)).trans (Finset.dvd_lcm hp)
    have hpower : M ^ (a - 1) ∣ S.lcm (fun p => τ * f p) := by
      rw [hprod]
      apply Finset.prod_dvd_of_isRelPrime
      · intro p hp q hq hpq
        have hprimeP : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hprimeQ : q.Prime := Nat.prime_of_mem_primeFactors hq
        exact Nat.coprime_iff_isRelPrime.mp
          (((Nat.coprime_primes hprimeP hprimeQ).mpr hpq).pow _ _)
      · intro p hp
        exact (dvd_mul_left (f p) τ).trans (Finset.dvd_lcm hp)
    change S.lcm (fun p => τ * f p) = τ * M ^ (a - 1)
    exact Nat.dvd_antisymm hupper
      ((hcop.symm.pow_right (a - 1)).mul_dvd_of_dvd_of_dvd hbase hpower)
  have hBPrimeData (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
      (hpB : p ∣ B j) :
      5 < p ∧ (B j).factorization p =
        padicValNat p (Nat.fib (fibonacciRank p)) := by
    let Bj := B j
    have hcast : (Bj : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := hBcast j
    have hpInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
      rw [← hcast]
      exact Int.natCast_dvd.mpr hpB
    have hrank := (cubic_block_b_prime_rank j p hj hp hpInt).2.2
    have hL72 := (golden_cubic_lucas_block j hj).1
    have hB72 : (Bj : ZMod 72) = 19 := by
      have hSq : ((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 72) = 19 := by
        push_cast
        rw [hL72]
        norm_num
      change ((Bj : ℤ) : ZMod 72) = 19
      rw [hcast]
      exact hSq
    have hB2 : (Bj : ZMod 2) = 1 := by
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2)) hB72
      simpa only [map_natCast, map_ofNat, show (19 : ZMod 2) = 1 by decide] using h
    have hB3 : (Bj : ZMod 3) = 1 := by
      have h := congrArg (ZMod.castHom (by decide : 3 ∣ 72) (ZMod 3)) hB72
      simpa only [map_natCast, map_ofNat, show (19 : ZMod 3) = 1 by decide] using h
    have hB5 : (Bj : ZMod 5) = 4 := by
      change ((Bj : ℤ) : ZMod 5) = 4
      rw [hcast]
      have hSq := (golden_cubic_lucas_block j hj).2.2.2.1
      push_cast at hSq
      push_cast
      rw [hSq]
      norm_num
    have hnot2 : ¬ 2 ∣ Bj := by
      intro h
      have hz : (Bj : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [hB2] at hz
      exact (by decide : (1 : ZMod 2) ≠ 0) hz
    have hnot3 : ¬ 3 ∣ Bj := by
      intro h
      have hz : (Bj : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [hB3] at hz
      exact (by decide : (1 : ZMod 3) ≠ 0) hz
    have hnot5 : ¬ 5 ∣ Bj := by
      intro h
      have hz : (Bj : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [hB5] at hz
      exact (by decide : (4 : ZMod 5) ≠ 0) hz
    have hp2 : p ≠ 2 := by rintro rfl; exact hnot2 hpB
    have hp3 : p ≠ 3 := by rintro rfl; exact hnot3 hpB
    have hp5 : p ≠ 5 := by rintro rfl; exact hnot5 hpB
    have hpgt : 5 < p := by
      obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
      have htwo := hp.two_le
      omega
    refine ⟨hpgt, ?_⟩
    change Bj.factorization p = _
    rw [Nat.factorization_def Bj hp]
    rw [← hcast] at hrank
    simpa only [padicValInt.of_nat] using hrank
  have hCLocal (j a p : ℕ) (hj : 1 ≤ j) (ha : 1 ≤ a)
      (hp : p.Prime) (hpC : p ∣ C j) :
      π (p ^ (C j ^ a).factorization p) =
        4 * 3 ^ (j + 1) * p ^ ((a - 1) * (C j).factorization p) := by
    let Cj := C j
    obtain ⟨hp5, hval⟩ := hCPrimeData j p hj hp hpC
    have hpInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1 := by
      rw [← hCcast]
      exact Int.natCast_dvd.mpr hpC
    have hPrime := cubic_block_c_prime_period j p hj hp hpInt
    have hCne : Cj ≠ 0 := by
      have hgt := (hSize j hj).1
      omega
    have hfacPos : 0 < Cj.factorization p := hp.factorization_pos_of_dvd hCne hpC
    have hfacPow : (Cj ^ a).factorization p = a * Cj.factorization p := by
      simp [Nat.factorization_pow]
    have hePos : 1 ≤ (Cj ^ a).factorization p := by
      rw [hfacPow]
      exact Nat.mul_pos (by omega) hfacPos
    obtain ⟨_, _, _, _, _, _, _, _, _, hPeriod⟩ :=
      golden_matrix_prime_power_period p ((Cj ^ a).factorization p) hp hp5 hePos
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
        (ZMod (p ^ (Cj ^ a).factorization p))) = _
    calc
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
          (ZMod (p ^ (Cj ^ a).factorization p))) =
          orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
            p ^ ((Cj ^ a).factorization p -
              padicValNat p (Nat.fib (fibonacciRank p))) := by
            simpa only using hPeriod
      _ = 4 * 3 ^ (j + 1) * p ^ ((a - 1) * Cj.factorization p) := by
        rw [hPrime, ← hval, hfacPow, Nat.sub_mul, one_mul]
  have hBLocal (j b p : ℕ) (hj : 1 ≤ j) (hb : 1 ≤ b)
      (hp : p.Prime) (hpB : p ∣ B j) :
      π (p ^ (B j ^ b).factorization p) =
        2 * 3 ^ (j + 1) * p ^ ((b - 1) * (B j).factorization p) := by
    let Bj := B j
    obtain ⟨hp5, hval⟩ := hBPrimeData j p hj hp hpB
    have hpInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
      rw [← hBcast]
      exact Int.natCast_dvd.mpr hpB
    have hPrime := cubic_block_b_prime_period j p hj hp hpInt
    have hBne : Bj ≠ 0 := by
      have hgt := (hSize j hj).2
      omega
    have hfacPos : 0 < Bj.factorization p := hp.factorization_pos_of_dvd hBne hpB
    have hfacPow : (Bj ^ b).factorization p = b * Bj.factorization p := by
      simp [Nat.factorization_pow]
    have hePos : 1 ≤ (Bj ^ b).factorization p := by
      rw [hfacPow]
      exact Nat.mul_pos (by omega) hfacPos
    obtain ⟨_, _, _, _, _, _, _, _, _, hPeriod⟩ :=
      golden_matrix_prime_power_period p ((Bj ^ b).factorization p) hp hp5 hePos
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
        (ZMod (p ^ (Bj ^ b).factorization p))) = _
    calc
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
          (ZMod (p ^ (Bj ^ b).factorization p))) =
          orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
            p ^ ((Bj ^ b).factorization p -
              padicValNat p (Nat.fib (fibonacciRank p))) := by
            simpa only using hPeriod
      _ = 2 * 3 ^ (j + 1) * p ^ ((b - 1) * Bj.factorization p) := by
        rw [hPrime, ← hval, hfacPow, Nat.sub_mul, one_mul]
  have hPowerPeriod (M τ a : ℕ) (hM : 1 < M) (ha : 1 ≤ a)
      (hcop : M.Coprime τ)
      (hloc : ∀ p ∈ M.primeFactors,
        π (p ^ (M ^ a).factorization p) =
          τ * p ^ ((a - 1) * M.factorization p)) :
      π (M ^ a) = τ * M ^ (a - 1) := by
    have hMne : M ≠ 0 := by omega
    calc
      π (M ^ a) = (M ^ a).primeFactors.lcm
          (fun p => π (p ^ (M ^ a).factorization p)) :=
            hCRT (M ^ a) (pow_ne_zero a hMne)
      _ = M.primeFactors.lcm (fun p => π (p ^ (M ^ a).factorization p)) := by
            rw [Nat.primeFactors_pow M (by omega : a ≠ 0)]
      _ = M.primeFactors.lcm
          (fun p => τ * p ^ ((a - 1) * M.factorization p)) := by
            apply Finset.lcm_congr rfl
            intro p hp
            exact hloc p hp
      _ = τ * M ^ (a - 1) := hLcm M τ a hM hcop
  have hTauCop (M r k : ℕ)
      (hM : ∀ p, p.Prime → p ∣ M → 5 < p) :
      M.Coprime (2 ^ r * 3 ^ k) := by
    by_contra hcop
    obtain ⟨p, hp, hpM, hpTau⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpgt := hM p hp hpM
    rcases hp.dvd_mul.mp hpTau with h2 | h3
    · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
      have := Nat.le_of_dvd (by decide : 0 < 2) hp2
      omega
    · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
      have := Nat.le_of_dvd (by decide : 0 < 3) hp3
      omega
  have hPairCRT (m n : ℕ) (hcop : m.Coprime n) :
      π (m * n) = Nat.lcm (π m) (π n) := by
    let qm : Matrix (Fin 2) (Fin 2) (ZMod m) := !![1, 1; 1, 0]
    let qn : Matrix (Fin 2) (Fin 2) (ZMod n) := !![1, 1; 1, 0]
    let qmn : Matrix (Fin 2) (Fin 2) (ZMod (m * n)) := !![1, 1; 1, 0]
    let fm : Matrix (Fin 2) (Fin 2) (ZMod (m * n)) →+*
        Matrix (Fin 2) (Fin 2) (ZMod m) :=
      (ZMod.castHom (dvd_mul_right m n) (ZMod m)).mapMatrix
    let fn : Matrix (Fin 2) (Fin 2) (ZMod (m * n)) →+*
        Matrix (Fin 2) (Fin 2) (ZMod n) :=
      (ZMod.castHom (dvd_mul_left n m) (ZMod n)).mapMatrix
    have hqm : fm qmn = qm := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fm, qmn, qm]
    have hqn : fn qmn = qn := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fn, qmn, qn]
    have hleft : orderOf qm ∣ orderOf qmn := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hqm, ← map_pow, pow_orderOf_eq_one, map_one]
    have hright : orderOf qn ∣ orderOf qmn := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hqn, ← map_pow, pow_orderOf_eq_one, map_one]
    have hupper : orderOf qmn ∣ Nat.lcm (orderOf qm) (orderOf qn) := by
      apply orderOf_dvd_of_pow_eq_one
      have hm : fm (qmn ^ Nat.lcm (orderOf qm) (orderOf qn)) = 1 := by
        rw [map_pow, hqm]
        exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_left _ _)
      have hn : fn (qmn ^ Nat.lcm (orderOf qm) (orderOf qn)) = 1 := by
        rw [map_pow, hqn]
        exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_right _ _)
      apply Matrix.ext
      intro i j
      apply (ZMod.chineseRemainder hcop).injective
      apply Prod.ext
      · have h := congrArg (fun x => x i j) hm
        have hone := congrArg (fun x => x i j) (map_one fm)
        simpa [ZMod.chineseRemainder, fm] using h.trans hone.symm
      · have h := congrArg (fun x => x i j) hn
        have hone := congrArg (fun x => x i j) (map_one fn)
        simpa [ZMod.chineseRemainder, fn] using h.trans hone.symm
    exact Nat.dvd_antisymm hupper (Nat.lcm_dvd hleft hright)
  refine ⟨hSupport.1, hSupport.2.1, hSupport.2.2, ?_⟩
  intro j a b hj ha hb
  have hCcop : (C j).Coprime (4 * 3 ^ (j + 1)) := by
    simpa [pow_two] using hTauCop (C j) 2 (j + 1)
      (fun p hp hpC => (hCPrimeData j p hj hp hpC).1)
  have hBcop : (B j).Coprime (2 * 3 ^ (j + 1)) := by
    simpa using hTauCop (B j) 1 (j + 1)
      (fun p hp hpB => (hBPrimeData j p hj hp hpB).1)
  have hC : π (C j ^ a) = 4 * 3 ^ (j + 1) * C j ^ (a - 1) := by
    apply hPowerPeriod (C j) (4 * 3 ^ (j + 1)) a (hSize j hj).1 ha hCcop
    intro p hp
    exact hCLocal j a p hj ha (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hB : π (B j ^ b) = 2 * 3 ^ (j + 1) * B j ^ (b - 1) := by
    apply hPowerPeriod (B j) (2 * 3 ^ (j + 1)) b (hSize j hj).2 hb hBcop
    intro p hp
    exact hBLocal j b p hj hb (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have h2B : (2 : ℕ).Coprime (B j ^ (b - 1)) :=
    (Nat.Coprime.of_dvd_left (dvd_mul_right 2 (3 ^ (j + 1))) hBcop.symm).pow_right _
  have hCB : (C j ^ (a - 1)).Coprime (B j ^ (b - 1)) :=
    (hSupport.2.2 j j hj hj).pow _ _
  have hPowCop : (C j ^ a).Coprime (B j ^ b) :=
    (hSupport.2.2 j j hj hj).pow _ _
  have hMixed : π (C j ^ a * B j ^ b) =
      4 * 3 ^ (j + 1) * C j ^ (a - 1) * B j ^ (b - 1) := by
    rw [hPairCRT (C j ^ a) (B j ^ b) hPowCop, hC, hB]
    have hcop : (2 * C j ^ (a - 1)).Coprime (B j ^ (b - 1)) :=
      h2B.mul_left hCB
    calc
      Nat.lcm (4 * 3 ^ (j + 1) * C j ^ (a - 1))
          (2 * 3 ^ (j + 1) * B j ^ (b - 1)) =
          Nat.lcm ((2 * 3 ^ (j + 1)) * (2 * C j ^ (a - 1)))
            ((2 * 3 ^ (j + 1)) * B j ^ (b - 1)) := by congr 1; ring
      _ = (2 * 3 ^ (j + 1)) *
          Nat.lcm (2 * C j ^ (a - 1)) (B j ^ (b - 1)) :=
            Nat.lcm_mul_left _ _ _
      _ = (2 * 3 ^ (j + 1)) *
          ((2 * C j ^ (a - 1)) * B j ^ (b - 1)) := by
            rw [hcop.lcm_eq_mul]
      _ = 4 * 3 ^ (j + 1) * C j ^ (a - 1) * B j ^ (b - 1) := by ring
  exact ⟨hC, hB, hMixed⟩

end D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
