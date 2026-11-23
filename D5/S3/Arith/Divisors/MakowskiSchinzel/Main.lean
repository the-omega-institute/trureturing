/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Main
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/Main
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: The sigma-totient inequality with at most forty-two non-Fermat prime factors. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction
import D5.S3.Arith.Divisors.MakowskiSchinzel.Fermat
import D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
import D5.S3.Arith.Divisors.MakowskiSchinzel.Deletion
import D5.S3.Arith.Divisors.MakowskiSchinzel.SupportModel
import D5.S3.Arith.Divisors.MakowskiSchinzel.SupportSieve
import D5.S3.Arith.Divisors.MakowskiSchinzel.TailFactorization

/-! Mąkowski–Schinzel's inequality under the non-Fermat prime-support budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel

open Finset UniqueFactorizationMonoid

/-- At an odd integer, adjoining the prime two halves the ratio exactly. -/
theorem alpha_two_mul {m : ℕ} (hm : Odd m) : alpha (2 * m) = alpha m / 2 := by
  simp only [alpha, Nat.totient_two_mul_of_odd hm, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The non-Fermat count is unchanged on passing to the radical. -/
theorem eta_radical (n : ℕ) : eta (radical n) = eta n := by
  classical
  simp [eta, nonFermatFactors, Nat.primeFactors_radical]


/-- The non-Fermat count ignores an adjoined prime two, including the zero case. -/
theorem eta_two_mul (m : ℕ) : eta (2 * m) = eta m := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  unfold eta nonFermatFactors
  rw [Nat.primeFactors_mul (by decide : 2 ≠ 0) hm, Nat.prime_two.primeFactors]
  congr 1
  ext q
  simp only [mem_filter, mem_union, mem_singleton]
  tauto

/-- The two sigma-totient bounds are equivalent to their odd squarefree restriction.
The closure assumption asks only for the odd squarefree core of each nonzero input:
its radical if odd, or its radical with the single factor two removed. Closure under
arbitrary divisors is unnecessary. Omitting either core case would leave the corresponding
parity of the radical outside the hypothesis of the restricted inequality. -/
theorem lift_odd_squarefree_iff (P : ℕ → Prop)
    (hP : ∀ n : ℕ, n ≠ 0 → P n → ∀ m : ℕ, Odd m →
      radical n = m ∨ radical n = 2 * m → P m) :
    (∀ m : ℕ, Odd m → Squarefree m → P m → 1 ≤ alpha m) ↔
      ∀ n : ℕ, P n → n ≤ 2 * ArithmeticFunction.sigma 1 n.totient ∧
        (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient) := by
  constructor
  · intro hodd n hnP
    by_cases hn0 : n = 0
    · subst n
      simp
    have hnq : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    let d := radical n
    have hdsq : Squarefree d := squarefree_radical
    have hlift : alpha d ≤ alpha n := alpha_radical_le hn0
    have hhalf : (1 / 2 : ℚ) ≤ alpha d := by
      rcases Nat.even_or_odd d with heven | hdo
      · obtain ⟨m, hm⟩ := heven
        have hdm : d = 2 * m := by omega
        have hmsq : Squarefree m := Squarefree.squarefree_of_dvd
          (by rw [hdm]; exact dvd_mul_left m 2) hdsq
        have hmo : Odd m := by
          rcases Nat.even_or_odd m with ⟨k, hk⟩ | ho
          · exfalso
            apply Nat.squarefree_iff_prime_squarefree.mp hdsq 2 Nat.prime_two
            exact ⟨k, by omega⟩
          · exact ho
        have hh := hodd m hmo hmsq (hP n hn0 hnP m hmo (Or.inr hdm))
        rw [hdm, alpha_two_mul hmo]
        linarith
      · have hh := hodd d hdo hdsq (hP n hn0 hnP d hdo (Or.inl rfl))
        linarith
    constructor
    · have hh := hhalf.trans hlift
      rw [alpha, le_div_iff₀ hnq] at hh
      have h' : (n : ℚ) ≤ 2 * (ArithmeticFunction.sigma 1 n.totient : ℚ) := by
        linarith
      exact_mod_cast h'
    · intro hnodd
      have hdo : Odd d := hnodd.of_dvd_nat radical_dvd_self
      have hh := (hodd d hdo hdsq (hP n hn0 hnP d hdo (Or.inl rfl))).trans hlift
      rw [alpha, le_div_iff₀ hnq] at hh
      norm_num at hh
      exact_mod_cast hh
  · intro h m hm hsq hmP
    have hle := (h m hmP).2 hm
    have hmq : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hsq.ne_zero
    rw [alpha, le_div_iff₀ hmq, one_mul]
    exact_mod_cast hle

/-- A strong inequality on odd squarefree integers lifts to all multiplicities and parities. -/
theorem lift_odd_squarefree (T : ℕ)
    (hodd : ∀ m : ℕ, Odd m → Squarefree m → eta m ≤ T → 1 ≤ alpha m)
    (n : ℕ) (heta : eta n ≤ T) :
    n ≤ 2 * ArithmeticFunction.sigma 1 n.totient ∧
      (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient) := by
  apply (lift_odd_squarefree_iff (fun k => eta k ≤ T) ?_).mp hodd n heta
  intro k _ hk m _ hcore
  rcases hcore with hcore | hcore
  · simpa only [← hcore, eta_radical] using hk
  · have he : eta m = eta k := by
      rw [← eta_two_mul m, ← hcore, eta_radical]
    simpa only [he] using hk

/-- An odd predecessor divisor greater than one forces a non-Fermat prime factor. -/
theorem primeSources_subset_nonFermat (m : ℕ) {r : ℕ} (hr : 1 < r) (hro : Odd r) :
    primeSources m r ⊆ nonFermatFactors m := by
  exact Certificate.sources_subset_interesting hr hro

/-- The source size is controlled by the non-Fermat support, without multiplicities. -/
theorem primeSources_card_le_eta (m : ℕ) {r : ℕ} (hr : 1 < r) (hro : Odd r) :
    (primeSources m r).card ≤ eta m :=
  card_le_card (primeSources_subset_nonFermat m hr hro)

/-- A predecessor of a prime divisor contributes all its divisors to the totient. -/
theorem predecessor_dvd_totient {m q : ℕ} (hq : q.Prime) (hqm : q ∣ m) :
    q - 1 ∣ m.totient := by
  rw [← Nat.totient_prime hq]
  exact Nat.totient_dvd_of_dvd hqm

/-- For squarefree integers, a totient prime has at least one predecessor source. -/
theorem primeSources_nonempty_iff {m r : ℕ} (hm : Squarefree m) (hr : r.Prime) :
    (primeSources m r).Nonempty ↔ r ∣ m.totient := by
  have hphi :=
    D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hm.ne_zero hm
  rw [hphi, hr.prime.dvd_finsetProd_iff]
  simp only [primeSources, filter_nonempty_iff]

/-- A minimal counterexample supplies exactly the strict product consumed by the checker. -/
theorem source_certificate_obstruction {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime)
    (hrd : r ∣ m.totient) (hbad : alpha m < 1)
    (hmin : ∀ d : ℕ, d ∣ m → d < m → 1 ≤ alpha d) :
    geom r (primeSources m r).card *
      Certificate.lowerProduct ((primeSources m r).sort (· ≤ ·)) < 1 := by
  have hd := prime_deletion_necessary hm hr hrd hbad hmin
  have hp (q : ℕ) (hq : q ∈ primeSources m r) : q.Prime :=
    Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
  have hB : 0 < ∏ q ∈ primeSources m r, ((q : ℚ) - 1) / q := by
    apply prod_pos
    intro q hq
    have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast (hp q hq).two_le
    exact div_pos (by linarith) (by linarith)
  have hcancel : (∏ q ∈ primeSources m r, (q : ℚ) / (q - 1 : ℕ)) *
      (∏ q ∈ primeSources m r, ((q : ℚ) - 1) / q) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    have hq2 := (hp q hq).two_le
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (hp q hq).ne_zero
    have hq1 : (q : ℚ) - 1 ≠ 0 := by
      have hqrat : (2 : ℚ) ≤ q := by exact_mod_cast hq2
      linarith
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    field_simp
  have hh := mul_lt_mul_of_pos_right hd hB
  rw [hcancel] at hh
  simpa only [geom, one_div, Certificate.lowerProduct_sort] using hh




/-- Divisibility can only decrease the non-Fermat prime support. -/
theorem eta_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) : eta a ≤ eta b := by
  classical
  apply card_le_card
  intro p hp
  simp only [nonFermatFactors, mem_filter] at hp ⊢
  exact ⟨(Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp.1, dvd_trans
      (Nat.dvd_of_mem_primeFactors hp.1) hab, hb⟩), hp.2⟩


/-- Odd integers satisfy the stronger inequality under the non-Fermat support budget. -/
theorem odd_alpha_eta_le_42 (n : ℕ) (hn : Odd n) (heta : eta n ≤ 42) :
    1 ≤ alpha n := by
  by_contra hbad
  obtain ⟨m, hmo, hmeta, hmsq, hmbad, hmin, _hglobal⟩ := exists_minimal_odd_counterexample
    (fun k => eta k ≤ 42)
    (fun hb hab hpb => (eta_le_of_dvd
      (by obtain ⟨k, hk⟩ := hb; omega) hab).trans hpb)
    ⟨n, hn, heta, lt_of_not_ge hbad⟩
  have hm0 : m ≠ 0 := hmsq.ne_zero
  have hp (q : ℕ) (hq : q ∈ m.primeFactors) : q.Prime :=
    Nat.prime_of_mem_primeFactors hq
  have hbudget : (Certificate.interesting m.primeFactors).card ≤ 42 := hmeta
  have hdel (r : ℕ) (hr : r.Prime) (_hro : Odd r)
      (hs : (Certificate.sources m.primeFactors r).Nonempty) :
      geom r (Certificate.sourceList m.primeFactors r).length *
        Certificate.lowerProduct (Certificate.sourceList m.primeFactors r) < 1 := by
    have hrd : r ∣ m.totient :=
      (primeSources_nonempty_iff hmsq hr).mp hs
    simpa only [Certificate.sourceList, Certificate.sources, primeSources,
      length_sort] using source_certificate_obstruction hm0 hr hrd hmbad hmin
  have hsieve (s : ℕ) (hs : s.Prime) (hso : Odd s) (hslt : s < 131) :
      Certificate.sources m.primeFactors s = ∅ :=
    Certificate.small_support_empty hp hbudget hdel hs hso hslt
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd m.totient with htwo | hex
  · obtain ⟨E, hE⟩ := htwo
    have hle := odd_le_sigma_totient_of_two_pow hmo hE
    have hmq : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hge : 1 ≤ alpha m := by
      rw [alpha, le_div_iff₀ hmq, one_mul]
      exact_mod_cast hle
    exact (not_lt_of_ge hge) hmbad
  · let r := Nat.find hex
    have hrSpec := Nat.find_spec hex
    change r.Prime ∧ r ∣ m.totient ∧ Odd r at hrSpec
    obtain ⟨hr, hrd, hro⟩ := hrSpec
    have hr131 : 131 ≤ r := by
      by_contra h
      have he := hsieve r hr hro (by omega)
      have hne := (primeSources_nonempty_iff hmsq hr).mpr hrd
      change (Certificate.sources m.primeFactors r).Nonempty at hne
      simpa [he] using hne
    have hcard : (primeSources m r).card ≤ 42 :=
      (primeSources_card_le_eta m hr.one_lt hro).trans hmeta
    have hqp (q : ℕ) (hq : q ∈ primeSources m r) : q.Prime :=
      hp q (mem_filter.mp hq).1
    have hmass := necessary_mass hr.pos (primeSources m r)
      (prime_deletion_necessary hm0 hr hrd hmbad hmin)
    have htail := large_support_tail (primeSources m r) r hr hr131 hcard hqp
      (fun q hq => (mem_filter.mp hq).2) (by
        intro q hq s hs hs2 hsd
        have hsdm : s ∣ m.totient :=
          hsd.trans (predecessor_dvd_totient (hp q (mem_filter.mp hq).1)
            (Nat.dvd_of_mem_primeFactors (mem_filter.mp hq).1))
        have hso : Odd s := hs.odd_of_ne_two hs2
        exact Nat.find_min' hex ⟨hs, hsdm, hso⟩)
    have htailBound := htail.2.1
    norm_num at htailBound
    linarith

/-- At most forty-two non-Fermat odd prime factors suffice, with no multiplicity bound. -/
theorem makowski_schinzel_eta_le_42 (n : ℕ) (heta : eta n ≤ 42) :
    n ≤ 2 * ArithmeticFunction.sigma 1 n.totient ∧
      (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient) := by
  exact lift_odd_squarefree 42 (fun m hmo _ hme => odd_alpha_eta_le_42 m hmo hme) n heta


end D5.S3.Arith.MakowskiSchinzel
