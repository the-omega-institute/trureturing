/- GID: D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockPeriodIteration
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact iteration trajectory of products of distinct golden cubic blocks. -/

import Mathlib
import D5.S3.Arith.GoldenPrimePowerOrder
import D5.S3.Arith.GoldenFibonacciModulusPeriod
import D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods

namespace D5.S3.Arith.Primes.GoldenCubicBlockPeriodIteration

open scoped Matrix
open D5.S3.Arith.GoldenApparition
open D5.S0.Carrier D5.S1.Scale D5.S3.Arith.GoldenPrimePowerOrder
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.GoldenFibonacciModulusPeriod

/-- The matrix period of a product of selected cubic blocks is controlled by
the largest selected index, with the C family supplying the factor four. -/
theorem cubic_block_product_period (I J : Finset ℕ)
    (hUnion : (I ∪ J).Nonempty)
    (hI : ∀ i ∈ I, 1 ≤ i) (hJ : ∀ j ∈ J, 1 ≤ j) :
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
      (ZMod ((∏ i ∈ I, (goldenLucas (3 ^ i) ^ 2 + 1).natAbs) *
        (∏ j ∈ J, (goldenLucas (3 ^ j) ^ 2 + 3).natAbs)))) =
      (if I.Nonempty then 4 else 2) * 3 ^ ((I ∪ J).max' hUnion + 1) := by
  have hMatrixOrder (m : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have hinj : Function.Injective (goldenMatrixHom m) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
      hinj (GoldenMod.phi : GoldenMod m)
    change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
    rw [hphi] at horder
    exact horder.symm
  let K := (I ∪ J).max' hUnion
  let C : ℕ → ℕ := fun i => (goldenLucas (3 ^ i) ^ 2 + 1).natAbs
  let B : ℕ → ℕ := fun j => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
  let PC := ∏ i ∈ I, C i
  let PB := ∏ j ∈ J, B j
  let M := PC * PB
  let π := fun m : ℕ => orderOf
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
  change π M = (if I.Nonempty then 4 else 2) * 3 ^ (K + 1)
  have hKmem : K ∈ I ∪ J := Finset.max'_mem (I ∪ J) hUnion
  have hKpos : 1 ≤ K := by
    rcases Finset.mem_union.mp hKmem with hi | hj
    · exact hI K hi
    · exact hJ K hj
  have hIbound (i : ℕ) (hi : i ∈ I) : 1 ≤ i ∧ i ≤ K :=
    ⟨hI i hi, Finset.le_max' (I ∪ J) i (Finset.mem_union_left J hi)⟩
  have hJbound (j : ℕ) (hj : j ∈ J) : 1 ≤ j ∧ j ≤ K :=
    ⟨hJ j hj, Finset.le_max' (I ∪ J) j (Finset.mem_union_right I hj)⟩
  have hCcast (j : ℕ) : (C j : ℤ) = goldenLucas (3 ^ j) ^ 2 + 1 := by
    simp [C, abs_of_nonneg (by positivity : 0 ≤ goldenLucas (3 ^ j) ^ 2 + 1)]
  have hBcast (j : ℕ) : (B j : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
    simp [B, abs_of_nonneg (by positivity : 0 ≤ goldenLucas (3 ^ j) ^ 2 + 3)]
  have hCprefix (k : ℕ) :
      (Nat.fib (3 ^ (k + 1)) : ℤ) =
        (Nat.fib 3 : ℤ) * ∏ j ∈ Finset.Icc 1 k, (C j : ℤ) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have h := (golden_cubic_fibonacci_block (k + 1) (by omega)).2.2
        calc
          (Nat.fib (3 ^ ((k + 1) + 1)) : ℤ) =
              (Nat.fib (3 ^ (k + 1)) : ℤ) *
                (goldenLucas (3 ^ (k + 1)) ^ 2 + 1) := h
          _ = ((Nat.fib 3 : ℤ) * ∏ j ∈ Finset.Icc 1 k, (C j : ℤ)) *
                (C (k + 1) : ℤ) := by
              calc
                _ = ((Nat.fib 3 : ℤ) * ∏ j ∈ Finset.Icc 1 k, (C j : ℤ)) *
                    (goldenLucas (3 ^ (k + 1)) ^ 2 + 1) :=
                  congrArg (fun z : ℤ => z * (goldenLucas (3 ^ (k + 1)) ^ 2 + 1)) ih
                _ = _ := by rw [hCcast]
          _ = (Nat.fib 3 : ℤ) * ∏ j ∈ Finset.Icc 1 (k + 1), (C j : ℤ) := by
            rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
            ring
  have hBprefix (k : ℕ) :
      goldenLucas (3 ^ (k + 1)) =
        goldenLucas 3 * ∏ j ∈ Finset.Icc 1 k, (B j : ℤ) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have h := (golden_cubic_lucas_block (k + 1) (by omega)).2.2.2.2.2
        calc
          goldenLucas (3 ^ ((k + 1) + 1)) =
              goldenLucas (3 ^ (k + 1)) *
                (goldenLucas (3 ^ (k + 1)) ^ 2 + 3) := h
          _ = (goldenLucas 3 * ∏ j ∈ Finset.Icc 1 k, (B j : ℤ)) *
                (B (k + 1) : ℤ) := by
              calc
                _ = (goldenLucas 3 * ∏ j ∈ Finset.Icc 1 k, (B j : ℤ)) *
                    (goldenLucas (3 ^ (k + 1)) ^ 2 + 3) :=
                  congrArg (fun z : ℤ => z * (goldenLucas (3 ^ (k + 1)) ^ 2 + 3)) ih
                _ = _ := by rw [hBcast]
          _ = goldenLucas 3 * ∏ j ∈ Finset.Icc 1 (k + 1), (B j : ℤ) := by
            rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
            ring
  have hCdivFib : PC ∣ Nat.fib (3 ^ (K + 1)) := by
    have hsubset : I ⊆ Finset.Icc 1 K := by
      intro i hi
      exact Finset.mem_Icc.mpr (hIbound i hi)
    have hdivInt : (PC : ℤ) ∣ (Nat.fib (3 ^ (K + 1)) : ℤ) := by
      rw [hCprefix K]
      have hprod : (∏ j ∈ I, (C j : ℤ)) ∣
          ∏ j ∈ Finset.Icc 1 K, (C j : ℤ) :=
        Finset.prod_dvd_prod_of_subset I (Finset.Icc 1 K) (fun j => (C j : ℤ)) hsubset
      have hfactor : (∏ j ∈ I, (C j : ℤ)) ∣
          (Nat.fib 3 : ℤ) * ∏ j ∈ Finset.Icc 1 K, (C j : ℤ) :=
        dvd_mul_of_dvd_right hprod _
      simpa only [PC, Nat.cast_prod] using hfactor
    exact_mod_cast hdivInt
  have hBdivLucas : PB ∣ (goldenLucas (3 ^ (K + 1))).natAbs := by
    have hsubset : J ⊆ Finset.Icc 1 K := by
      intro j hj
      exact Finset.mem_Icc.mpr (hJbound j hj)
    have hdivInt : (PB : ℤ) ∣ goldenLucas (3 ^ (K + 1)) := by
      rw [hBprefix K]
      have hprod : (∏ j ∈ J, (B j : ℤ)) ∣
          ∏ j ∈ Finset.Icc 1 K, (B j : ℤ) :=
        Finset.prod_dvd_prod_of_subset J (Finset.Icc 1 K) (fun j => (B j : ℤ)) hsubset
      have hfactor : (∏ j ∈ J, (B j : ℤ)) ∣
          goldenLucas 3 * ∏ j ∈ Finset.Icc 1 K, (B j : ℤ) :=
        dvd_mul_of_dvd_right hprod _
      simpa only [PB, Nat.cast_prod] using hfactor
    exact Int.natCast_dvd.mp hdivInt
  have hCupper : π PC ∣ 4 * 3 ^ (K + 1) := by
    let n := 3 ^ (K + 1)
    have hnge : 5 ≤ n := by
      dsimp [n]
      calc
        5 ≤ 3 ^ (2 : ℕ) := by decide
        _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hnodd : Odd n := (by decide : Odd (3 : ℕ)).pow
    let Qf : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n)) := !![1, 1; 1, 0]
    let Qc : Matrix (Fin 2) (Fin 2) (ZMod PC) := !![1, 1; 1, 0]
    let h : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n)) →+*
        Matrix (Fin 2) (Fin 2) (ZMod PC) :=
      (ZMod.castHom hCdivFib (ZMod PC)).mapMatrix
    have hQ : h Qf = Qc := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h, Qf, Qc, ZMod.cast_one hCdivFib]
    have hF : Qf ^ (4 * n) = 1 := by
      rw [← golden_fibonacci_modulus_period n hnge hnodd]
      exact pow_orderOf_eq_one _
    have hC : Qc ^ (4 * n) = 1 := by
      rw [← hQ, ← map_pow, hF, map_one]
    exact orderOf_dvd_of_pow_eq_one hC
  have hBupper : π PB ∣ 2 * 3 ^ (K + 1) := by
    let n := 3 ^ (K + 1)
    have hnodd : Odd n := (by decide : Odd (3 : ℕ)).pow
    have hbLucas : (PB : ℤ) ∣ goldenLucas n := by
      exact Int.natCast_dvd.mpr hBdivLucas
    have htrace : (trace (phi ^ n) : ZMod PB) = 0 := by
      rw [← golden_lucas_eq_trace_phi_pow]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hbLucas
    have htraceMod : ((trace (phi ^ n) : ℤ) : GoldenMod PB) = 0 := by
      apply GoldenMod.ext
      · simpa using htrace
      · simp
    have hnorm : norm (phi ^ n) = -1 := by
      rw [norm_phi_pow, hnodd.neg_one_pow]
    have hreduce : GoldenMod.reduce PB phi = GoldenMod.phi := by
      ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
    have hquad (z : GoldenInt) :
        z ^ 2 = (trace z : GoldenInt) * z - (norm z : GoldenInt) := by
      apply GoldenInt.ext <;>
        simp only [pow_two, sub_eq_add_neg, a_add, a_neg, a_mul,
          b_add, b_neg, b_mul, a_intCast, b_intCast,
          D5.S0.Carrier.trace, D5.S0.Carrier.norm] <;> ring
    have hsq : ((GoldenMod.phi : GoldenMod PB) ^ n) ^ 2 = 1 := by
      have h := congrArg (GoldenMod.reduce PB) (hquad (phi ^ n))
      simp only [map_pow, map_mul, map_sub, map_intCast, hreduce, hnorm,
        htraceMod, zero_mul, zero_sub, Int.cast_neg, Int.cast_one] at h
      simpa using h
    have hreturn : (GoldenMod.phi : GoldenMod PB) ^ (2 * n) = 1 := by
      rw [Nat.mul_comm 2 n, pow_mul]
      exact hsq
    change orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod PB)) ∣ 2 * n
    rw [← hMatrixOrder PB]
    exact orderOf_dvd_of_pow_eq_one hreturn
  have hcop : PC.Coprime PB := by
    rw [Nat.coprime_prod_left_iff]
    intro i hi
    rw [Nat.coprime_prod_right_iff]
    intro j hj
    by_contra hcop
    obtain ⟨p, hp, hpC, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpCInt : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 1 :=
      Int.natCast_dvd.mpr hpC
    have hpBInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 :=
      Int.natCast_dvd.mpr hpB
    have hri := (cubic_block_c_prime_rank i p (hI i hi) hp hpCInt).1
    have hrj := (cubic_block_b_prime_rank j p (hJ j hj) hp hpBInt).1
    have hodd : Odd (3 ^ (i + 1)) := (by decide : Odd (3 : ℕ)).pow
    have heq : 3 ^ (i + 1) = 2 * 3 ^ (j + 1) := hri.symm.trans hrj
    have heven : Even (3 ^ (i + 1)) := by
      rw [heq]
      exact even_two_mul _
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hCRT : π M = Nat.lcm (π PC) (π PB) := by
    let qa : Matrix (Fin 2) (Fin 2) (ZMod PC) := !![1, 1; 1, 0]
    let qb : Matrix (Fin 2) (Fin 2) (ZMod PB) := !![1, 1; 1, 0]
    let qab : Matrix (Fin 2) (Fin 2) (ZMod M) := !![1, 1; 1, 0]
    let fa : Matrix (Fin 2) (Fin 2) (ZMod M) →+*
        Matrix (Fin 2) (Fin 2) (ZMod PC) :=
      (ZMod.castHom (dvd_mul_right PC PB) (ZMod PC)).mapMatrix
    let fb : Matrix (Fin 2) (Fin 2) (ZMod M) →+*
        Matrix (Fin 2) (Fin 2) (ZMod PB) :=
      (ZMod.castHom (dvd_mul_left PB PC) (ZMod PB)).mapMatrix
    have hqa : fa qab = qa := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fa, qab, qa]
    have hqb : fb qab = qb := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fb, qab, qb]
    have hleft : orderOf qa ∣ orderOf qab := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hqa, ← map_pow, pow_orderOf_eq_one, map_one]
    have hright : orderOf qb ∣ orderOf qab := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hqb, ← map_pow, pow_orderOf_eq_one, map_one]
    have hupper : orderOf qab ∣ Nat.lcm (orderOf qa) (orderOf qb) := by
      apply orderOf_dvd_of_pow_eq_one
      have hpowA : fa (qab ^ Nat.lcm (orderOf qa) (orderOf qb)) = 1 := by
        rw [map_pow, hqa]
        exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_left _ _)
      have hpowB : fb (qab ^ Nat.lcm (orderOf qa) (orderOf qb)) = 1 := by
        rw [map_pow, hqb]
        exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_right _ _)
      apply Matrix.ext
      intro i j
      apply (ZMod.chineseRemainder hcop).injective
      apply Prod.ext
      · have h := congrArg (fun m => m i j) hpowA
        have hone := congrArg (fun m => m i j) (map_one fa)
        simpa [ZMod.chineseRemainder, fa] using h.trans hone.symm
      · have h := congrArg (fun m => m i j) hpowB
        have hone := congrArg (fun m => m i j) (map_one fb)
        simpa [ZMod.chineseRemainder, fb] using h.trans hone.symm
    exact Nat.dvd_antisymm hupper (Nat.lcm_dvd hleft hright)
  have hPeriodDiv (p : ℕ) (hpM : p ∣ M) : π p ∣ π M := by
    let Qm : Matrix (Fin 2) (Fin 2) (ZMod M) := !![1, 1; 1, 0]
    let Qp : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 1, 0]
    let f : Matrix (Fin 2) (Fin 2) (ZMod M) →+*
        Matrix (Fin 2) (Fin 2) (ZMod p) :=
      (ZMod.castHom hpM (ZMod p)).mapMatrix
    have hQ : f Qm = Qp := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [f, Qm, Qp, ZMod.cast_one hpM]
    apply orderOf_dvd_of_pow_eq_one
    change Qp ^ orderOf Qm = 1
    rw [← hQ, ← map_pow, pow_orderOf_eq_one, map_one]
  have hLucasPos (n : ℕ) (hn : 0 < n) : 0 < goldenLucas n := by
    cases n with
    | zero => omega
    | succ k =>
        have hf : 0 < Nat.fib (k + 2) := Nat.fib_pos.mpr (by omega)
        have hf' : (0 : ℤ) < (Nat.fib (k + 2) : ℤ) := by exact_mod_cast hf
        have hnonneg : (0 : ℤ) ≤ (Nat.fib k : ℤ) := Nat.cast_nonneg _
        simpa only [Nat.succ_eq_add_one, golden_lucas_succ_eq_fib_add_fib] using
          (show (0 : ℤ) < (Nat.fib k : ℤ) + (Nat.fib (k + 2) : ℤ) by omega)
  have hCgt (i : ℕ) : 1 < C i := by
    have hx : 0 < goldenLucas (3 ^ i) := hLucasPos _ (pow_pos (by decide) _)
    have hs : 0 < goldenLucas (3 ^ i) ^ 2 := sq_pos_of_pos hx
    have hsum : (1 : ℤ) < goldenLucas (3 ^ i) ^ 2 + 1 := by omega
    have hcast : ((goldenLucas (3 ^ i) ^ 2 + 1).natAbs : ℤ) =
        goldenLucas (3 ^ i) ^ 2 + 1 := hCcast i
    dsimp [C]
    omega
  have hBgt (j : ℕ) : 1 < B j := by
    have hsq : 0 ≤ goldenLucas (3 ^ j) ^ 2 := sq_nonneg _
    have hsum : (1 : ℤ) < goldenLucas (3 ^ j) ^ 2 + 3 := by omega
    have hcast : ((goldenLucas (3 ^ j) ^ 2 + 3).natAbs : ℤ) =
        goldenLucas (3 ^ j) ^ 2 + 3 := hBcast j
    dsimp [B]
    omega
  have hClower (i : ℕ) (hi : i ∈ I) : 4 * 3 ^ (i + 1) ∣ π M := by
    obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd (by
      have := hCgt i
      omega : C i ≠ 1)
    have hpM : p ∣ M :=
      (hpC.trans (Finset.dvd_prod_of_mem C hi)).trans (dvd_mul_right _ _)
    have hpCInt : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 1 :=
      Int.natCast_dvd.mpr hpC
    rw [← cubic_block_c_prime_period i p (hI i hi) hp hpCInt]
    exact hPeriodDiv p hpM
  have hBlower (j : ℕ) (hj : j ∈ J) : 2 * 3 ^ (j + 1) ∣ π M := by
    obtain ⟨p, hp, hpB⟩ := Nat.exists_prime_and_dvd (by
      have := hBgt j
      omega : B j ≠ 1)
    have hpM : p ∣ M :=
      (hpB.trans (Finset.dvd_prod_of_mem B hj)).trans (dvd_mul_left _ _)
    have hpBInt : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 :=
      Int.natCast_dvd.mpr hpB
    rw [← cubic_block_b_prime_period j p (hJ j hj) hp hpBInt]
    exact hPeriodDiv p hpM
  by_cases hINe : I.Nonempty
  · have hUpper : π M ∣ 4 * 3 ^ (K + 1) := by
      calc
        π M = Nat.lcm (π PC) (π PB) := hCRT
        _ ∣ 4 * 3 ^ (K + 1) :=
          Nat.lcm_dvd hCupper
            (hBupper.trans
              (mul_dvd_mul_right (by decide : 2 ∣ 4) (3 ^ (K + 1))))
    have hLower : 4 * 3 ^ (K + 1) ∣ π M := by
      rcases Finset.mem_union.mp hKmem with hKI | hKJ
      · exact hClower K hKI
      · obtain ⟨i, hi⟩ := hINe
        have hB := hBlower K hKJ
        have hC := hClower i hi
        have hfour : 4 ∣ π M := (dvd_mul_right 4 (3 ^ (i + 1))).trans hC
        have hpow : 3 ^ (K + 1) ∣ π M :=
          (dvd_mul_left (3 ^ (K + 1)) 2).trans hB
        exact ((by decide : Nat.Coprime 4 3).pow_right (K + 1)).mul_dvd_of_dvd_of_dvd
          hfour hpow
    simpa [hINe] using Nat.dvd_antisymm hUpper hLower
  · have hIEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hINe
    have hM : M = PB := by simp [M, PC, hIEmpty]
    have hKJ : K ∈ J := by simpa [hIEmpty] using hKmem
    have hUpper : π M ∣ 2 * 3 ^ (K + 1) := by simpa [hM] using hBupper
    have hLower : 2 * 3 ^ (K + 1) ∣ π M := hBlower K hKJ
    simpa [hINe] using Nat.dvd_antisymm hUpper hLower

/-- The selected block product first reaches the matrix-period fixed point
after exactly one more step than its largest index. -/
theorem cubic_block_product_first_arrival (I J : Finset ℕ)
    (hUnion : (I ∪ J).Nonempty)
    (hI : ∀ i ∈ I, 1 ≤ i) (hJ : ∀ j ∈ J, 1 ≤ j) :
    let M := (∏ i ∈ I, (goldenLucas (3 ^ i) ^ 2 + 1).natAbs) *
      (∏ j ∈ J, (goldenLucas (3 ^ j) ^ 2 + 3).natAbs)
    let K := (I ∪ J).max' hUnion
    let π := fun m : ℕ => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    π M = (if I.Nonempty then 4 else 2) * 3 ^ (K + 1) ∧
      (∀ t : ℕ, π^[2 + t] M = 8 * 3 ^ max 1 (K - t)) ∧
      (π^[K + 1] M = 24 ∧ ∀ n : ℕ, n < K + 1 → π^[n] M ≠ 24) ∧
      π 24 = 24 := by
  have hMatrixOrder (m : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have hinj : Function.Injective (goldenMatrixHom m) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
      hinj (GoldenMod.phi : GoldenMod m)
    change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
    rw [hphi] at horder
    exact horder.symm
  let C : ℕ → ℕ := fun i => (goldenLucas (3 ^ i) ^ 2 + 1).natAbs
  let B : ℕ → ℕ := fun j => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
  let M := (∏ i ∈ I, C i) * (∏ j ∈ J, B j)
  let K := (I ∪ J).max' hUnion
  let π := fun m : ℕ => orderOf
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
  change π M = (if I.Nonempty then 4 else 2) * 3 ^ (K + 1) ∧
    (∀ t : ℕ, π^[2 + t] M = 8 * 3 ^ max 1 (K - t)) ∧
    (π^[K + 1] M = 24 ∧ ∀ n : ℕ, n < K + 1 → π^[n] M ≠ 24) ∧
    π 24 = 24
  have hKmem : K ∈ I ∪ J := Finset.max'_mem (I ∪ J) hUnion
  have hK : 1 ≤ K := by
    rcases Finset.mem_union.mp hKmem with hi | hj
    · exact hI K hi
    · exact hJ K hj
  have hFirst : π M = (if I.Nonempty then 4 else 2) * 3 ^ (K + 1) :=
    cubic_block_product_period I J hUnion hI hJ
  have hPiThree (k : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod (3 ^ (k + 1))) = 8 * 3 ^ k := by
    let x : GoldenMod (3 ^ (k + 1)) := GoldenMod.phi
    have hpow : x ^ 8 =
        1 + (3 : GoldenMod (3 ^ (k + 1))) *
          (⟨(4 : ZMod (3 ^ (k + 1))), (7 : ZMod (3 ^ (k + 1)))⟩ :
            GoldenMod (3 ^ (k + 1))) := by
      have hInt : phi ^ 8 = (⟨13, 21⟩ : GoldenInt) := by
        have hf7 : Nat.fib 7 = 13 := by decide
        have hf8 : Nat.fib 8 = 21 := by decide
        simpa [hf7, hf8] using golden_phi_pow_eq_fib_pair 7
      have hred : GoldenMod.reduce (3 ^ (k + 1)) phi = GoldenMod.phi := by
        ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
      have hpair : x ^ 8 =
          (⟨13, 21⟩ : GoldenMod (3 ^ (k + 1))) := by
        have h := congrArg (GoldenMod.reduce (3 ^ (k + 1))) hInt
        rw [map_pow, hred] at h
        apply GoldenMod.ext
        · simpa [x, GoldenMod.reduce] using congrArg GoldenMod.a h
        · simpa [x, GoldenMod.reduce] using congrArg GoldenMod.b h
      rw [hpair]
      have hthree : (3 : GoldenMod (3 ^ (k + 1))) =
          (⟨3, 0⟩ : GoldenMod (3 ^ (k + 1))) := by
        apply GoldenMod.ext
        · exact GoldenMod.a_natCast 3
        · exact GoldenMod.b_natCast 3
      rw [hthree]
      apply GoldenMod.ext
      · simp [GoldenMod.a_mul]; ring
      · simp [GoldenMod.b_mul]; ring
    have horderPow : orderOf (x ^ 8) = 3 ^ k := by
      rw [hpow]
      simpa [pow_one] using
        (golden_prime_power_order (p := 3) (m := 1) (n := k)
          (by decide) (by decide) (by decide) 4 7 (Or.inl (by decide)))
    have hreturn : x ^ (8 * 3 ^ k) = 1 := by
      rw [pow_mul, ← horderPow]
      exact pow_orderOf_eq_one _
    have hmod : 3 ∣ 3 ^ (k + 1) := dvd_pow_self 3 (by omega)
    let r : ZMod (3 ^ (k + 1)) →+* ZMod 3 := ZMod.castHom hmod (ZMod 3)
    let f : GoldenMod (3 ^ (k + 1)) →+* GoldenMod 3 :=
      { toFun := fun z => ⟨r z.a, r z.b⟩
        map_zero' := by ext <;> simp
        map_one' := by ext <;> simp
        map_add' := by intro a b; ext <;> simp
        map_mul' := by intro a b; ext <;> simp [GoldenMod.a_mul, GoldenMod.b_mul] }
    have hphi : f x = GoldenMod.phi := by
      apply GoldenMod.ext <;> simp [f, x, GoldenMod.phi]
    have horderThree : orderOf (GoldenMod.phi : GoldenMod 3) = 8 := by
      rw [orderOf_eq_iff (by decide)]
      refine ⟨by decide, ?_⟩
      intro n hn hpos
      interval_cases n
      all_goals decide
    have h8Dvd : 8 ∣ orderOf x := by
      rw [← horderThree, ← hphi]
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hdiv : orderOf (x ^ 8) = orderOf x / 8 :=
      orderOf_pow_of_dvd (by decide) h8Dvd
    have hmul := Nat.div_mul_cancel h8Dvd
    rw [← hdiv, horderPow] at hmul
    have hordeq : orderOf x = 8 * 3 ^ k := by omega
    exact hordeq
  have hPiThreePower (u : ℕ) (hu : 1 ≤ u) :
      π (3 ^ u) = 8 * 3 ^ (u - 1) := by
    have h := hPiThree (u - 1)
    have hidx : u - 1 + 1 = u := by omega
    rw [hidx] at h
    change orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ u))) =
        8 * 3 ^ (u - 1)
    rw [← hMatrixOrder (3 ^ u)]
    exact h
  have hPiTwo : π 2 = 3 := by
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 3
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro n hn hpos
    interval_cases n
    all_goals decide
  have hPiFour : π 4 = 6 := by
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4)) = 6
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro n hn hpos
    interval_cases n
    all_goals decide
  have hPiEight : π 8 = 12 := by
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 8)) = 12
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro n hn hpos
    interval_cases n
    all_goals decide
  have hCRT (a b : ℕ) (hcop : a.Coprime b) :
      π (a * b) = Nat.lcm (π a) (π b) := by
    let qa : Matrix (Fin 2) (Fin 2) (ZMod a) := !![1, 1; 1, 0]
    let qb : Matrix (Fin 2) (Fin 2) (ZMod b) := !![1, 1; 1, 0]
    let qab : Matrix (Fin 2) (Fin 2) (ZMod (a * b)) := !![1, 1; 1, 0]
    let fa : Matrix (Fin 2) (Fin 2) (ZMod (a * b)) →+*
        Matrix (Fin 2) (Fin 2) (ZMod a) :=
      (ZMod.castHom (dvd_mul_right a b) (ZMod a)).mapMatrix
    let fb : Matrix (Fin 2) (Fin 2) (ZMod (a * b)) →+*
        Matrix (Fin 2) (Fin 2) (ZMod b) :=
      (ZMod.castHom (dvd_mul_left b a) (ZMod b)).mapMatrix
    have hqa : fa qab = qa := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fa, qab, qa]
    have hqb : fb qab = qb := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fb, qab, qb]
    have hleft : orderOf qa ∣ orderOf qab := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hqa, ← map_pow, pow_orderOf_eq_one, map_one]
    have hright : orderOf qb ∣ orderOf qab := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hqb, ← map_pow, pow_orderOf_eq_one, map_one]
    have hupper : orderOf qab ∣ Nat.lcm (orderOf qa) (orderOf qb) := by
      apply orderOf_dvd_of_pow_eq_one
      have hpowA : fa (qab ^ Nat.lcm (orderOf qa) (orderOf qb)) = 1 := by
        rw [map_pow, hqa]
        exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_left _ _)
      have hpowB : fb (qab ^ Nat.lcm (orderOf qa) (orderOf qb)) = 1 := by
        rw [map_pow, hqb]
        exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_right _ _)
      apply Matrix.ext
      intro i j
      apply (ZMod.chineseRemainder hcop).injective
      apply Prod.ext
      · have h := congrArg (fun m => m i j) hpowA
        have hone := congrArg (fun m => m i j) (map_one fa)
        simpa [ZMod.chineseRemainder, fa] using h.trans hone.symm
      · have h := congrArg (fun m => m i j) hpowB
        have hone := congrArg (fun m => m i j) (map_one fb)
        simpa [ZMod.chineseRemainder, fb] using h.trans hone.symm
    exact Nat.dvd_antisymm hupper (Nat.lcm_dvd hleft hright)
  have hLcmThree (k : ℕ) (hk : 1 ≤ k) :
      Nat.lcm 3 (8 * 3 ^ k) = 8 * 3 ^ k ∧
        Nat.lcm 6 (8 * 3 ^ k) = 8 * 3 ^ k := by
    have hpow : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have hthree : 3 ∣ 8 * 3 ^ k := dvd_mul_of_dvd_right hpow 8
    constructor
    · exact Nat.lcm_eq_right_iff_dvd.mpr hthree
    · apply Nat.lcm_eq_right_iff_dvd.mpr
      have htwo : 2 ∣ 8 * 3 ^ k :=
        (by decide : 2 ∣ 8).trans (dvd_mul_right 8 (3 ^ k))
      simpa only [show 2 * 3 = 6 by decide] using
        (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have hLcmTwelve (u : ℕ) (hu : 1 ≤ u) :
      Nat.lcm 12 (8 * 3 ^ (u - 1)) = 8 * 3 ^ max 1 (u - 1) := by
    by_cases hu1 : u = 1
    · subst u
      norm_num
    · have hu2 : 2 ≤ u := by omega
      have hpow : 3 ∣ 3 ^ (u - 1) := dvd_pow_self 3 (by omega)
      have hthree : 3 ∣ 8 * 3 ^ (u - 1) := dvd_mul_of_dvd_right hpow 8
      have hfour : 4 ∣ 8 * 3 ^ (u - 1) :=
        (by decide : 4 ∣ 8).trans (dvd_mul_right 8 (3 ^ (u - 1)))
      have hdiv : 12 ∣ 8 * 3 ^ (u - 1) := by
        simpa only [show 4 * 3 = 12 by decide] using
          (by decide : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd hfour hthree
      rw [Nat.lcm_eq_right_iff_dvd.mpr hdiv, max_eq_right (by omega : 1 ≤ u - 1)]
  let e := if I.Nonempty then 4 else 2
  have he : e = 2 ∨ e = 4 := by
    by_cases h : I.Nonempty
    · exact Or.inr (by simp [e, h])
    · exact Or.inl (by simp [e, h])
  have hFirstE : π M = e * 3 ^ (K + 1) := hFirst
  have hSecond : π (e * 3 ^ (K + 1)) = 8 * 3 ^ K := by
    rcases he with he | he
    · rw [he]
      have hcop : Nat.Coprime 2 (3 ^ (K + 1)) :=
        (by decide : Nat.Coprime 2 3).pow_right (K + 1)
      calc
        π (2 * 3 ^ (K + 1)) = Nat.lcm (π 2) (π (3 ^ (K + 1))) := hCRT 2 _ hcop
        _ = Nat.lcm 3 (8 * 3 ^ K) := by
          rw [hPiTwo, hPiThreePower (K + 1) (by omega),
            show K + 1 - 1 = K by omega]
        _ = 8 * 3 ^ K := (hLcmThree K hK).1
    · rw [he]
      have hcop : Nat.Coprime 4 (3 ^ (K + 1)) :=
        (by decide : Nat.Coprime 4 3).pow_right (K + 1)
      calc
        π (4 * 3 ^ (K + 1)) = Nat.lcm (π 4) (π (3 ^ (K + 1))) := hCRT 4 _ hcop
        _ = Nat.lcm 6 (8 * 3 ^ K) := by
          rw [hPiFour, hPiThreePower (K + 1) (by omega),
            show K + 1 - 1 = K by omega]
        _ = 8 * 3 ^ K := (hLcmThree K hK).2
  have hStep (u : ℕ) (hu : 1 ≤ u) :
      π (8 * 3 ^ u) = 8 * 3 ^ max 1 (u - 1) := by
    have hcop : Nat.Coprime 8 (3 ^ u) :=
      (by decide : Nat.Coprime 8 3).pow_right u
    calc
      π (8 * 3 ^ u) = Nat.lcm (π 8) (π (3 ^ u)) := hCRT 8 _ hcop
      _ = Nat.lcm 12 (8 * 3 ^ (u - 1)) := by rw [hPiEight, hPiThreePower u hu]
      _ = 8 * 3 ^ max 1 (u - 1) := hLcmTwelve u hu
  have hTrajectory (t : ℕ) :
      π^[2 + t] M = 8 * 3 ^ max 1 (K - t) := by
    induction t with
    | zero =>
        have hmax : max 1 K = K := max_eq_right hK
        calc
          π^[2 + 0] M = π (π M) := by simp [Function.iterate_succ_apply']
          _ = π (e * 3 ^ (K + 1)) := by rw [hFirstE]
          _ = 8 * 3 ^ K := hSecond
          _ = 8 * 3 ^ max 1 (K - 0) := by simp [hmax]
    | succ t ih =>
        have hpos : 1 ≤ max 1 (K - t) := le_max_left _ _
        calc
          π^[2 + (t + 1)] M = π (π^[2 + t] M) := by
            rw [show 2 + (t + 1) = (2 + t) + 1 by omega,
              Function.iterate_succ_apply']
          _ = π (8 * 3 ^ max 1 (K - t)) := by rw [ih]
          _ = 8 * 3 ^ max 1 (max 1 (K - t) - 1) := hStep _ hpos
          _ = 8 * 3 ^ max 1 (K - (t + 1)) := by
            congr 1
            congr 1
            omega
  have hOddBlock (j : ℕ) (hj : 1 ≤ j) : Odd (C j) ∧ Odd (B j) := by
    have hx72 : ((goldenLucas (3 ^ j) : ℤ) : ZMod 72) = 4 :=
      (golden_cubic_lucas_block j hj).1
    have hx2 : (goldenLucas (3 ^ j) : ZMod 2) = 0 := by
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 2) = 0 by decide] using h
    constructor
    · apply Int.natAbs_odd.mpr
      apply ZMod.intCast_eq_one_iff_odd.mp
      push_cast
      rw [hx2]
      decide
    · apply Int.natAbs_odd.mpr
      apply ZMod.intCast_eq_one_iff_odd.mp
      push_cast
      rw [hx2]
      decide
  have hOddProd (S : Finset ℕ) (f : ℕ → ℕ) :
      (∀ j ∈ S, Odd (f j)) → Odd (∏ j ∈ S, f j) := by
    classical
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
        intro hf
        rw [Finset.prod_insert ha]
        exact (hf a (Finset.mem_insert_self _ _)).mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
  have hMOdd : Odd M := by
    exact (hOddProd I C (fun i hi => (hOddBlock i (hI i hi)).1)).mul
      (hOddProd J B (fun j hj => (hOddBlock j (hJ j hj)).2))
  have hArrival : π^[K + 1] M = 24 ∧
      ∀ n : ℕ, n < K + 1 → π^[n] M ≠ 24 := by
    constructor
    · have h := hTrajectory (K - 1)
      have hindex : 2 + (K - 1) = K + 1 := by omega
      have hexp : max 1 (K - (K - 1)) = 1 := by omega
      rw [hindex, hexp] at h
      norm_num at h ⊢
      exact h
    · intro n hn
      rcases n with _ | n
      · intro h
        have hm : M = 24 := by simpa using h
        rcases hMOdd with ⟨v, hv⟩
        omega
      rcases n with _ | t
      · intro h
        have hv : e * 3 ^ (K + 1) = 24 := by
          have h' : π M = 24 := by simpa using h
          rw [hFirstE] at h'
          exact h'
        have hodd : Odd (3 ^ (K + 1)) := (by decide : Odd (3 : ℕ)).pow
        rcases hodd with ⟨v, hvpow⟩
        rcases he with he | he <;> rw [he, hvpow] at hv <;> omega
      · intro h
        have hidx : 2 + t = Nat.succ (Nat.succ t) := by omega
        have hval := hTrajectory t
        rw [hidx, h] at hval
        have hexp : 2 ≤ max 1 (K - t) := by omega
        have hbound : 3 ^ 2 ≤ 3 ^ max 1 (K - t) :=
          Nat.pow_le_pow_right (by decide) hexp
        norm_num at hbound
        omega
  have hFixed : π 24 = 24 := by
    have h := hStep 1 (by decide)
    norm_num at h ⊢
    exact h
  exact ⟨hFirst, hTrajectory, hArrival, hFixed⟩

#print axioms cubic_block_product_period
#print axioms cubic_block_product_first_arrival

end D5.S3.Arith.Primes.GoldenCubicBlockPeriodIteration
