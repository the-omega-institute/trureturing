/- GID: D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.NumberTheory.ArithmeticFunction.Misc, Mathlib.Data.Finset.NatDivisors, Mathlib.Data.Nat.Factorization.PrimePow, Mathlib.Data.Nat.Squarefree, Mathlib.RingTheory.MvPolynomial.Symmetric.Defs, Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: A prime divisor-pair product sum of a composite has exactly its composite and prime preimages. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.DivisorPairProductPrimePreimages

open scoped ArithmeticFunction.sigma

/-- The second elementary symmetric function of the positive divisors of `n` (OEIS A119616). -/
noncomputable def S2 (n : ℕ) : ℕ :=
  n.divisors.val.esymm 2

/-- A composite argument whose divisor-pair product sum is prime is twice an odd prime. -/
theorem eq_two_mul_prime_of_composite_of_s2_prime {n : ℕ} (hncomp : ¬ n.Prime)
    (hn : 1 < n) (hprime : (S2 n).Prime) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ n = 2 * q := by
  have pair_identity (s : Multiset ℕ) :
      s.sum ^ 2 = 2 * s.esymm 2 + (s.map fun x => x ^ 2).sum := by
    induction s using Multiset.induction_on with
    | empty =>
        simp only [Multiset.sum_zero, Multiset.map_zero]
        rw [Multiset.esymm, show (2 : ℕ) = 1 + 1 by rfl,
          Multiset.powersetCard_zero_right]
        simp
    | @cons a s ih =>
        have hes : (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
          change (Multiset.map Multiset.prod
              (Multiset.powersetCard (1 + 1) (a ::ₘ s))).sum = _
          simp only [Multiset.esymm, Multiset.powersetCard_cons,
            Multiset.map_add, Multiset.sum_add, Multiset.map_map,
            Function.comp_apply, Multiset.prod_cons, Multiset.powersetCard_one,
            Multiset.prod_singleton]
          congr 1
          simpa using
            (Multiset.sum_map_mul_left (s := s) (a := a) (f := fun x : ℕ => x))
        simp only [Multiset.sum_cons, hes, Multiset.map_cons]
        calc
          (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2 := by ring
          _ = 2 * (s.esymm 2 + a * s.sum) +
              (a ^ 2 + (Multiset.map (fun x => x ^ 2) s).sum) := by rw [ih]; ring
  have sigma_identity (x : ℕ) :
      ArithmeticFunction.sigma 1 x ^ 2 =
        2 * S2 x + ArithmeticFunction.sigma 2 x := by
    rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
    simp only [pow_one, S2, Finset.sum_eq_multiset_sum]
    rw [Multiset.map_id']
    change x.divisors.val.sum ^ 2 =
      2 * x.divisors.val.esymm 2 + (x.divisors.val.map fun y => y ^ 2).sum
    exact pair_identity x.divisors.val
  have s2_lower {x p : ℕ} (hx : 1 < x) (hp : p.Prime) (hpd : p ∣ x)
      (hplt : p < x) : x + p * x ≤ S2 x := by
    have hx0 : x ≠ 0 := by omega
    have hp1 : p ≠ 1 := hp.ne_one
    have hpx : p ≠ x := ne_of_lt hplt
    have hone : 1 ∈ x.divisors := Nat.one_mem_divisors.mpr hx0
    have hxmem : x ∈ x.divisors := Nat.mem_divisors_self x hx0
    have hpmem : p ∈ x.divisors := Nat.mem_divisors.mpr ⟨hpd, hx0⟩
    have hfirst : ({1, x} : Finset ℕ) ∈ x.divisors.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.insert_subset_iff.mpr
        ⟨hone, Finset.singleton_subset_iff.mpr hxmem⟩,
        Finset.card_pair (by omega)⟩
    have hsecond : ({p, x} : Finset ℕ) ∈ x.divisors.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.insert_subset_iff.mpr
        ⟨hpmem, Finset.singleton_subset_iff.mpr hxmem⟩,
        Finset.card_pair hpx⟩
    have hsets : ({1, x} : Finset ℕ) ≠ {p, x} := by
      intro heq
      have : p ∈ ({1, x} : Finset ℕ) := heq.symm ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact this.elim hp1 hpx
    have hsubset : ({{1, x}, {p, x}} : Finset (Finset ℕ)) ⊆
        x.divisors.powersetCard 2 := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hfirst
      · exact hsecond
    have hsum := Finset.sum_le_sum_of_subset hsubset
      (f := fun t : Finset ℕ => t.prod id)
    have hesymm : S2 x =
        ∑ t ∈ x.divisors.powersetCard 2, t.prod id := by
      have h := Finset.esymm_map_val (fun y : ℕ => y) x.divisors 2
      rw [Multiset.map_id'] at h
      exact h
    rw [hesymm]
    simpa [hsets, hp1, hpx] using hsum
  have geom_upper (p a : ℕ) (hp : 2 ≤ p) :
      (∑ i ∈ Finset.range (a + 1), p ^ i) ≤ 2 * p ^ a := by
    induction a with
    | zero => simp
    | succ a ih =>
        rw [Finset.sum_range_succ, pow_succ]
        calc
          (∑ i ∈ Finset.range (a + 1), p ^ i) + p ^ a * p ≤
              2 * p ^ a + p ^ a * p := Nat.add_le_add_right ih _
          _ ≤ 2 * (p ^ a * p) := by
            have hmul := Nat.mul_le_mul_left (p ^ a) hp
            omega
  have geom_double (x N : ℕ) :
      (∑ i ∈ Finset.range (2 * N), x ^ i) =
        (∑ i ∈ Finset.range N, x ^ i) * (x ^ N + 1) := by
    rw [show 2 * N = N + N by omega, Finset.sum_range_add]
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    ring
  have geom_cross (x N : ℕ) :
      (∑ i ∈ Finset.range N, x ^ i) * (x ^ N + 1) =
        (∑ i ∈ Finset.range N, (x ^ 2) ^ i) * (x + 1) := by
    by_cases hx : x = 1
    · subst x
      simp
    have hxi :
        ((∑ i ∈ Finset.range N, x ^ i : ℕ) : ℤ) =
          ∑ i ∈ Finset.range N, (x : ℤ) ^ i := by norm_num
    have hx2i :
        ((∑ i ∈ Finset.range N, (x ^ 2) ^ i : ℕ) : ℤ) =
          ∑ i ∈ Finset.range N, ((x : ℤ) ^ 2) ^ i := by norm_num
    apply Int.ofNat_inj.mp
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, hxi, hx2i]
    have hxne : (x : ℤ) - 1 ≠ 0 := by omega
    apply mul_right_cancel₀ hxne
    calc
      ((∑ i ∈ Finset.range N, (x : ℤ) ^ i) * ((x : ℤ) ^ N + 1)) *
            ((x : ℤ) - 1) =
          (((∑ i ∈ Finset.range N, (x : ℤ) ^ i) * ((x : ℤ) - 1)) *
            ((x : ℤ) ^ N + 1)) := by ring
      _ = ((x : ℤ) ^ N - 1) * ((x : ℤ) ^ N + 1) := by rw [geom_sum_mul]
      _ = (x : ℤ) ^ (2 * N) - 1 := by rw [pow_mul]; ring
      _ = ((x : ℤ) ^ 2) ^ N - 1 := by rw [pow_mul]
      _ = (∑ i ∈ Finset.range N, ((x : ℤ) ^ 2) ^ i) *
            ((x : ℤ) ^ 2 - 1) := (geom_sum_mul _ _).symm
      _ = ((∑ i ∈ Finset.range N, ((x : ℤ) ^ 2) ^ i) *
            ((x : ℤ) + 1)) * ((x : ℤ) - 1) := by ring
  have common_factor_of_sq_dvd {x p : ℕ} (hx : 1 < x) (hp : p.Prime)
      (hsq : p ^ 2 ∣ x) :
      ∃ g : ℕ, 2 < g ∧ g < S2 x ∧
        g ∣ ArithmeticFunction.sigma 1 x ∧
        g ∣ ArithmeticFunction.sigma 2 x := by
    let a := x.factorization p
    let t := ordCompl[p] x
    have hx0 : x ≠ 0 := by omega
    have ha2 : 2 ≤ a := (hp.pow_dvd_iff_le_factorization hx0).mp hsq
    have hdecomp : p ^ a * t = x := Nat.ordProj_mul_ordCompl_eq_self x p
    have hcop : Nat.Coprime (p ^ a) t := (Nat.coprime_ordCompl hp hx0).pow_left a
    have hsigma_mul (k : ℕ) :
        ArithmeticFunction.sigma k x =
          ArithmeticFunction.sigma k (p ^ a) * ArithmeticFunction.sigma k t := by
      rw [← hdecomp]
      exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
    have hpa_dvd : p ^ a ∣ x := ⟨t, hdecomp.symm⟩
    have hpa_le : p ^ a ≤ x := Nat.le_of_dvd (by omega) hpa_dvd
    have hplt : p < x := by
      have hpsq : p < p ^ 2 := by
        rw [pow_two]
        exact lt_mul_of_one_lt_right hp.pos hp.one_lt
      exact hpsq.trans_le (Nat.le_of_dvd (by omega) hsq)
    have hs2lower : x + p * x ≤ S2 x :=
      s2_lower hx hp ((dvd_pow_self p (by omega)).trans hsq) hplt
    have hprimepow_upper : ArithmeticFunction.sigma 1 (p ^ a) ≤ 2 * p ^ a := by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
      exact geom_upper p a hp.two_le
    rcases Nat.even_or_odd a with haeven | haodd
    · let g := ∑ i ∈ Finset.range (a + 1), p ^ i
      have hg_sigma1pp : g ∣ ArithmeticFunction.sigma 1 (p ^ a) := by
        rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
      obtain ⟨b, hb⟩ := haeven
      have hNodd : Odd (a + 1) := by
        simpa only [hb, two_mul] using (odd_two_mul_add_one b)
      have hcross := geom_cross p (a + 1)
      have hpdvd_nat : p + 1 ∣ p ^ (a + 1) + 1 := by
        rw [← Int.natCast_dvd_natCast]
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, one_pow] using
          hNodd.add_dvd_pow_add_pow (p : ℤ) 1
      obtain ⟨Q, hQ⟩ := hpdvd_nat
      have hg_sigma2pp : g ∣ ArithmeticFunction.sigma 2 (p ^ a) := by
        rw [ArithmeticFunction.sigma_apply_prime_pow hp]
        simp only [Nat.mul_comm _ 2, pow_mul]
        refine ⟨Q, ?_⟩
        apply Nat.mul_right_cancel (by omega : 0 < p + 1)
        calc
          (∑ j ∈ Finset.range (a + 1), (p ^ 2) ^ j) * (p + 1) =
              g * (p ^ (a + 1) + 1) := hcross.symm
          _ = g * ((p + 1) * Q) := by rw [hQ]
          _ = g * Q * (p + 1) := by ring
      have hg2 : 2 < g := by
        have hrange : Finset.range 2 ⊆ Finset.range (a + 1) :=
          Finset.range_mono (by omega)
        have hsum := Finset.sum_le_sum_of_subset hrange (f := fun i => p ^ i)
        have hpg : p < g := by simpa [g] using hsum
        exact hp.two_le.trans_lt hpg
      have hgle : g ≤ 2 * x :=
        (Nat.le_of_dvd
          (ArithmeticFunction.sigma_pos 1 (p ^ a) (pow_ne_zero _ hp.ne_zero))
          hg_sigma1pp).trans
          (hprimepow_upper.trans (Nat.mul_le_mul_left 2 hpa_le))
      have hglt : g < S2 x := by
        have : 2 * x < x + p * x := by
          have hpx := Nat.mul_le_mul_right x hp.two_le
          omega
        exact hgle.trans_lt (this.trans_le hs2lower)
      refine ⟨g, hg2, hglt, ?_, ?_⟩
      · rw [hsigma_mul 1]
        exact dvd_mul_of_dvd_left hg_sigma1pp _
      · rw [hsigma_mul 2]
        exact dvd_mul_of_dvd_left hg_sigma2pp _
    · obtain ⟨b, hb⟩ := haodd
      let N := b + 1
      let g := ∑ i ∈ Finset.range N, (p ^ 2) ^ i
      have haform : a + 1 = 2 * N := by simp [hb, N]; omega
      have hg_sigma1pp : g ∣ ArithmeticFunction.sigma 1 (p ^ a) := by
        rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, haform]
        refine ⟨p + 1, ?_⟩
        rw [geom_double, geom_cross]
      have hg_sigma2pp : g ∣ ArithmeticFunction.sigma 2 (p ^ a) := by
        rw [ArithmeticFunction.sigma_apply_prime_pow hp]
        simp only [Nat.mul_comm _ 2, pow_mul, haform]
        refine ⟨(p ^ 2) ^ N + 1, ?_⟩
        rw [geom_double]
      have hb1 : 1 ≤ b := by omega
      have hg2 : 2 < g := by
        have hrange : Finset.range 2 ⊆ Finset.range N :=
          Finset.range_mono (by simp [N, hb1])
        have hsum := Finset.sum_le_sum_of_subset hrange
          (f := fun i => (p ^ 2) ^ i)
        have hp2 : 2 ≤ p ^ 2 := by
          have hmul := Nat.mul_le_mul_left p hp.one_le
          have hpp : p ≤ p * p := by simpa using hmul
          simpa [pow_two] using hp.two_le.trans hpp
        have hpg : p ^ 2 < g := by simpa [g] using hsum
        exact hp2.trans_lt hpg
      have hgle : g ≤ 2 * x :=
        (Nat.le_of_dvd
          (ArithmeticFunction.sigma_pos 1 (p ^ a) (pow_ne_zero _ hp.ne_zero))
          hg_sigma1pp).trans
          (hprimepow_upper.trans (Nat.mul_le_mul_left 2 hpa_le))
      have hglt : g < S2 x := by
        have : 2 * x < x + p * x := by
          have hpx := Nat.mul_le_mul_right x hp.two_le
          omega
        exact hgle.trans_lt (this.trans_le hs2lower)
      refine ⟨g, hg2, hglt, ?_, ?_⟩
      · rw [hsigma_mul 1]
        exact dvd_mul_of_dvd_left hg_sigma1pp _
      · rw [hsigma_mul 2]
        exact dvd_mul_of_dvd_left hg_sigma2pp _
  have squarefree_of_prime_s2 {x : ℕ} (hx : 1 < x) (hxprime : (S2 x).Prime) :
      Squarefree x := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hsq
    obtain ⟨g, hg2, hglt, hg1, hg2sigma⟩ :=
      common_factor_of_sq_dvd hx hp (by simpa [pow_two] using hsq)
    have hg1sq : g ∣ ArithmeticFunction.sigma 1 x ^ 2 := by
      simpa [pow_two] using
        dvd_mul_of_dvd_left hg1 (ArithmeticFunction.sigma 1 x)
    rw [sigma_identity x] at hg1sq
    have hgtwo : g ∣ 2 * S2 x :=
      (Nat.dvd_add_iff_left hg2sigma).mpr hg1sq
    rcases Nat.even_or_odd g with hgeven | hgodd
    · obtain ⟨k, hk⟩ := hgeven
      have hgk : g = 2 * k := by simpa [two_mul] using hk
      obtain ⟨c, hc⟩ := hgtwo
      have hcancel : S2 x = k * c := by
        apply Nat.mul_left_cancel (by decide : 0 < 2)
        simpa [hgk, mul_assoc] using hc
      have hk_dvd : k ∣ S2 x := ⟨c, hcancel⟩
      have hk2 : 2 ≤ k := by omega
      have hkeq : k = S2 x := (Nat.dvd_prime_two_le hxprime hk2).mp hk_dvd
      omega
    · have hg_dvd : g ∣ S2 x :=
        hgodd.coprime_two_right.dvd_of_dvd_mul_left hgtwo
      have hgeq : g = S2 x :=
        (Nat.dvd_prime_two_le hxprime hg2.le).mp hg_dvd
      omega
  have hn0 : n ≠ 0 := by omega
  have hsq : Squarefree n := squarefree_of_prime_s2 hn hprime
  let oddFactors := n.primeFactors.erase 2
  have hprod : ∏ p ∈ n.primeFactors, p = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hcardFactors : 2 ≤ n.primeFactors.card := by
    have hcard0 : n.primeFactors.card ≠ 0 := by
      intro hzero
      rw [Finset.card_eq_zero] at hzero
      simp only [hzero, Finset.prod_empty] at hprod
      omega
    have hcard1 : n.primeFactors.card ≠ 1 := by
      intro hone
      obtain ⟨p, hpFactors⟩ := Finset.card_eq_one.mp hone
      have hpMem : p ∈ n.primeFactors := by rw [hpFactors]; simp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      have hpn : p = n := by simpa [hpFactors] using hprod
      exact hncomp (hpn ▸ hp)
    omega
  have hcardOdd : oddFactors.card ≤ 1 := by
    by_contra hnot
    have htwoCard : 2 ≤ oddFactors.card := by omega
    have hfourSigma (k : ℕ) : 4 ∣ ArithmeticFunction.sigma k n := by
      have htwoPow : 2 ^ oddFactors.card ∣
          ∏ p ∈ oddFactors, ArithmeticFunction.sigma k p := by
        rw [← Finset.prod_const]
        exact Finset.prod_dvd_prod_of_dvd (s := oddFactors)
          (fun _ : ℕ => 2) (fun p => ArithmeticFunction.sigma k p)
          (fun p hpOddFactors => by
            have hpne : p ≠ 2 := (Finset.mem_erase.mp hpOddFactors).1
            have hpFactors : p ∈ n.primeFactors :=
              (Finset.mem_erase.mp hpOddFactors).2
            have hp : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
            have hpodd : Odd p := Nat.not_even_iff_odd.mp fun hpeven =>
              hpne (hp.even_iff.mp hpeven)
            rw [show ArithmeticFunction.sigma k p = 1 + p ^ k by
              calc
                ArithmeticFunction.sigma k p =
                    ArithmeticFunction.sigma k (p ^ 1) := by rw [pow_one]
                _ = ∑ j ∈ Finset.range (1 + 1), p ^ (j * k) :=
                  ArithmeticFunction.sigma_apply_prime_pow hp
                _ = 1 + p ^ k := by norm_num [Finset.sum_range_succ]]
            exact even_iff_two_dvd.mp hpodd.pow.one_add)
      have hfourPow : 4 ∣ 2 ^ oddFactors.card := by
        refine ⟨2 ^ (oddFactors.card - 2), ?_⟩
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
        congr
        omega
      have hoddSubset : oddFactors ⊆ n.primeFactors := Finset.erase_subset 2 _
      have hsubProd : (∏ p ∈ oddFactors, ArithmeticFunction.sigma k p) ∣
          ∏ p ∈ n.primeFactors, ArithmeticFunction.sigma k p :=
        Finset.prod_dvd_prod_of_subset _ _ _ hoddSubset
      have hallProd : (∏ p ∈ n.primeFactors, ArithmeticFunction.sigma k p) =
          ArithmeticFunction.sigma k n :=
        ArithmeticFunction.isMultiplicative_sigma.prod_primeFactors hsq
      rw [← hallProd]
      exact hfourPow.trans (htwoPow.trans hsubProd)
    have hfourSigma1sq : 4 ∣ ArithmeticFunction.sigma 1 n ^ 2 :=
      dvd_pow (hfourSigma 1) (by omega)
    rw [sigma_identity n] at hfourSigma1sq
    have hfourTwice : 4 ∣ 2 * S2 n :=
      (Nat.dvd_add_iff_left (hfourSigma 2)).mpr hfourSigma1sq
    have htwoS2 : 2 ∣ S2 n := by
      obtain ⟨c, hc⟩ := hfourTwice
      refine ⟨c, ?_⟩
      apply Nat.mul_left_cancel (by decide : 0 < 2)
      calc
        2 * S2 n = 4 * c := hc
        _ = 2 * (2 * c) := by ring
    have hs2eq : S2 n = 2 :=
      hprime.even_iff.mp (even_iff_two_dvd.mpr htwoS2)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hrlt : r < n := by
      have hrle : r ≤ n := Nat.le_of_dvd (by omega) hrdvd
      exact lt_of_le_of_ne hrle fun heq => hncomp (heq ▸ hr)
    have hlower := s2_lower hn hr hrdvd hrlt
    have hr2 := hr.two_le
    rw [hs2eq] at hlower
    omega
  have htwoMem : 2 ∈ n.primeFactors := by
    by_contra hnot
    have herase : oddFactors = n.primeFactors := Finset.erase_eq_self.mpr hnot
    rw [herase] at hcardOdd
    omega
  have hcardOddPos : 0 < oddFactors.card := by
    have heraseCard := Finset.card_erase_of_mem htwoMem
    change (n.primeFactors.erase 2).card = n.primeFactors.card - 1 at heraseCard
    change 0 < (n.primeFactors.erase 2).card
    omega
  have hcardOddEq : oddFactors.card = 1 := by omega
  obtain ⟨q, hoddFactors⟩ := Finset.card_eq_one.mp hcardOddEq
  have hqMemOdd : q ∈ oddFactors := by simp [hoddFactors]
  have hqne : q ≠ 2 := (Finset.mem_erase.mp hqMemOdd).1
  have hqMem : q ∈ n.primeFactors := (Finset.mem_erase.mp hqMemOdd).2
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqMem
  have hqodd : Odd q := Nat.not_even_iff_odd.mp fun hqeven =>
    hqne (hq.even_iff.mp hqeven)
  have hFactors : n.primeFactors = {2, q} := by
    rw [← Finset.insert_erase htwoMem,
      show n.primeFactors.erase 2 = oddFactors by rfl, hoddFactors]
  have hnprod : n = 2 * q := by
    rw [hFactors] at hprod
    simpa [hqne.symm] using hprod.symm
  exact ⟨q, hq, hqodd, hnprod⟩

end D5.S1.Recurrence.Invariants.DivisorPairProductPrimePreimages
