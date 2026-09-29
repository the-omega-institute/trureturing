/- GID: D5/S3/Arith/ExponentExchange/ForcedCoreNormalization
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/ForcedCoreNormalization
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: [D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman]
   utility: none
   digest: A constrained divisor-sum maximum has an exact ordered prime-prefix representative. -/

import D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman

namespace D5.S3.Arith.ExponentExchange.ForcedCoreNormalization

open D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman

noncomputable section

/-- An actual maximum over multiples of a nonincreasing mandatory prime-power core
is represented by the same integer's nonincreasing consecutive-prime prefix. -/
theorem forced_core_normalization (ell : List ℕ)
    (hell : Ordered (ell.headD 0) ell) (B : ℕ) :
    let M := suffixNumber 1 0 ell
    (B < M ↔ ¬∃ n : ℕ, 1 ≤ n ∧ n ≤ B ∧ M ∣ n) ∧
    (M ≤ B → ∃ (n : ℕ) (t : List ℕ),
      1 ≤ n ∧ n ≤ B ∧ M ∣ n ∧
      (∀ p q : ℕ, p.Prime → q.Prime → p < q →
        n.factorization q ≤ n.factorization p) ∧
      Ordered (rootCap 1 B) t ∧ suffixNumber 1 0 t = n ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n = suffixWeight 1 0 t ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ B → M ∣ m →
        (ArithmeticFunction.sigma 1 m : ℝ) / m ≤
          (ArithmeticFunction.sigma 1 n : ℝ) / n)) := by
  classical
  dsimp only
  let M := suffixNumber 1 0 ell
  have hM : 0 < M := (suffix_prime_factors 1 0 ell).1
  have hM0 : M ≠ 0 := by omega
  have hmono : StrictMono (prime 1) := by
    intro i j hij
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  have hprofile (h : ℕ) (t : List ℕ) (ht : Ordered h t) :
      (∀ j : ℕ, (t[j]?).getD 0 ≤ h) ∧
      Antitone (fun j : ℕ => (t[j]?).getD 0) := by
    induction t generalizing h with
    | nil =>
        constructor
        · intro j; simp
        · intro i j hij; simp
    | cons a t ih =>
        obtain ⟨_, hah, htail⟩ := ht
        obtain ⟨hbound, hanti⟩ := ih a htail
        constructor
        · intro j
          cases j with
          | zero => simpa using hah
          | succ j => simpa using (hbound j).trans hah
        · intro i j hij
          cases i with
          | zero =>
              cases j with
              | zero => exact le_rfl
              | succ j => simpa using hbound j
          | succ i =>
              cases j with
              | zero => omega
              | succ j => simpa using hanti (Nat.le_of_succ_le_succ hij)
  have hval (i : ℕ) (t : List ℕ) (k : ℕ) :
      (suffixNumber 1 i t).factorization (prime 1 (i + k)) =
        (t[k]?).getD 0 := by
    induction t generalizing i k with
    | nil => simp [suffixNumber]
    | cons a t ih =>
        have hp : (prime 1 i).Prime := Nat.prime_nth_prime _
        have htpos : 0 < suffixNumber 1 (i + 1) t :=
          (suffix_prime_factors 1 (i + 1) t).1
        cases k with
        | zero =>
            have hnot : ¬prime 1 i ∣ suffixNumber 1 (i + 1) t := by
              intro hd
              obtain ⟨j, _, heq⟩ :=
                (suffix_prime_factors 1 (i + 1) t).2.1 _ hp hd
              exact (hmono (show i < i + 1 + j by omega)).ne heq
            change (prime 1 i ^ a * suffixNumber 1 (i + 1) t).factorization
              (prime 1 i) = a
            rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) htpos.ne']
            simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnot]
        | succ k =>
            have hne : prime 1 (i + (k + 1)) ≠ prime 1 i :=
              (hmono (show i < i + (k + 1) by omega)).ne'
            have hprime : (prime 1 (i + (k + 1))).Prime := Nat.prime_nth_prime _
            change (prime 1 i ^ a * suffixNumber 1 (i + 1) t).factorization
              (prime 1 (i + (k + 1))) = t[k]?.getD 0
            rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) htpos.ne']
            have hhead : (prime 1 i ^ a).factorization (prime 1 (i + (k + 1))) = 0 := by
              simp [hp.factorization_pow, hne.symm]
            simp only [Finsupp.add_apply]
            rw [hhead]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1) k
  have hcoreval (i : ℕ) : M.factorization (prime 1 i) = (ell[i]?).getD 0 := by
    simpa [M] using hval 0 ell i
  have hcoreorder : Antitone (fun i => M.factorization (prime 1 i)) := by
    intro i j hij
    change M.factorization (prime 1 j) ≤ M.factorization (prime 1 i)
    rw [hcoreval j, hcoreval i]
    exact (hprofile (ell.headD 0) ell hell).2 hij
  have hiff : B < M ↔ ¬∃ n : ℕ, 1 ≤ n ∧ n ≤ B ∧ M ∣ n := by
    constructor
    · intro h ⟨n, hn, hnB, hMn⟩
      exact (not_lt_of_ge ((Nat.le_of_dvd (by omega) hMn).trans hnB)) h
    · intro h
      by_contra hBM
      exact h ⟨M, hM, by omega, dvd_refl M⟩
  refine ⟨hiff, ?_⟩
  intro hMB
  let s := (Finset.Icc 1 B).filter (fun n => M ∣ n)
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.sigma 1 n : ℝ) / n
  have hs : s.Nonempty :=
    ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hM, hMB⟩, dvd_refl M⟩⟩
  obtain ⟨n, hn, hnmax⟩ := Finset.exists_max_image s f hs
  obtain ⟨hnrange, hMn⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnB⟩ := Finset.mem_Icc.mp hnrange
  have hn0 : n ≠ 0 := by omega
  have hfacLe (r : ℕ) : M.factorization r ≤ n.factorization r :=
    (Nat.factorization_le_iff_dvd hM0 hn0).mpr hMn r
  have hEnum := (rough_prime_suffix_complete 1 1 (by decide) (by decide)).2.1
  have horder : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      n.factorization q ≤ n.factorization p := by
    intro p q hp hq hpq
    by_contra hbad
    have hab : n.factorization p < n.factorization q := Nat.lt_of_not_ge hbad
    let a := n.factorization p
    let b := n.factorization q
    let u := n / (p ^ a * q ^ b)
    let n' := u * p ^ b * q ^ a
    have hswap := IntegerSwap.prime_exponent_swap hn1 hp hq hpq hab
    change 1 ≤ u ∧ Nat.gcd u (p * q) = 1 ∧ n = u * p ^ a * q ^ b ∧
      (0 < n' ∧ n' < n) ∧ f n < f n' at hswap
    obtain ⟨hu, huc, hnfactor, ⟨hn'1, hn'lt⟩, hgain⟩ := hswap
    have huc' : u.Coprime (p * q) := huc
    have hup : u.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpd
      exact ((hp.coprime_iff_not_dvd.mp
        ((Nat.coprime_mul_iff_right.mp huc').1).symm) hpd)
    have huq : u.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hqd
      exact ((hq.coprime_iff_not_dvd.mp
        ((Nat.coprime_mul_iff_right.mp huc').2).symm) hqd)
    have hcorepq : M.factorization q ≤ M.factorization p := by
      obtain ⟨i, hi⟩ := hEnum p |>.mp ⟨hp, hp.one_lt⟩
      obtain ⟨j, hj⟩ := hEnum q |>.mp ⟨hq, hq.one_lt⟩
      have hij : i < j := hmono.lt_iff_lt.mp (by simpa [← hi, ← hj] using hpq)
      rw [hi, hj]
      exact hcoreorder hij.le
    have hMnew : M ∣ n' := by
      apply (Nat.factorization_le_iff_dvd hM0 (by omega)).mp
      intro r
      by_cases hrp : r = p
      · subst r
        have hnp : n'.factorization p = b := by
          change (u * p ^ b * q ^ a).factorization p = b
          rw [Nat.factorization_mul (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
            (pow_ne_zero _ hq.ne_zero),
            Nat.factorization_mul (by omega : u ≠ 0) (pow_ne_zero _ hp.ne_zero)]
          simp [hp.factorization_pow, hq.factorization_pow, hpq.ne, hup]
        rw [hnp]
        exact (hfacLe p).trans hab.le
      by_cases hrq : r = q
      · subst r
        have hnq : n'.factorization q = a := by
          change (u * p ^ b * q ^ a).factorization q = a
          rw [Nat.factorization_mul (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
            (pow_ne_zero _ hq.ne_zero),
            Nat.factorization_mul (by omega : u ≠ 0) (pow_ne_zero _ hp.ne_zero)]
          simp [hp.factorization_pow, hq.factorization_pow, hpq.ne.symm, huq]
        rw [hnq]
        exact hcorepq.trans (hfacLe p)
      · have heq : n.factorization r = n'.factorization r := by
          rw [hnfactor]
          change (u * p ^ a * q ^ b).factorization r =
            (u * p ^ b * q ^ a).factorization r
          rw [Nat.factorization_mul (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
            (pow_ne_zero _ hq.ne_zero),
            Nat.factorization_mul (by omega : u ≠ 0) (pow_ne_zero _ hp.ne_zero),
            Nat.factorization_mul (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
            (pow_ne_zero _ hq.ne_zero),
            Nat.factorization_mul (by omega : u ≠ 0) (pow_ne_zero _ hp.ne_zero)]
          simp [hp.factorization_pow, hq.factorization_pow, hrp, hrq]
        rw [← heq]
        exact hfacLe r
    have hn'mem : n' ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn'1, hn'lt.le.trans hnB⟩,
        hMnew⟩
    exact (not_lt_of_ge (hnmax n' hn'mem)) hgain
  let g : ℕ → ℕ := fun i => n.factorization (prime 1 i)
  have hg : Antitone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact horder _ _ (Nat.prime_nth_prime _) (Nat.prime_nth_prime _) (hmono hij)
  have hcover : n.factorization.support ⊆
      (Finset.range (Nat.primeCounting n)).image (prime 1) := by
    intro p hpp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hpp
    obtain ⟨i, hi⟩ := (hEnum p).mp ⟨hp, hp.one_lt⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_range.mpr ?_, hi.symm⟩
    have hcount : Nat.count Nat.Prime p < Nat.primeCounting n := by
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpd
      have hc := Nat.count_monotone Nat.Prime (Nat.succ_le_succ hpn)
      rw [Nat.count_succ, if_pos hp] at hc
      change Nat.count Nat.Prime p + 1 ≤ Nat.primeCounting n at hc
      omega
    have hindex : Nat.primeCounting 1 + i = Nat.count Nat.Prime p := by
      rw [hi]
      exact (Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime _).symm
    omega
  have hprod : (∏ j ∈ Finset.range (Nat.primeCounting n), prime 1 j ^ g j) = n := by
    calc
      _ = n.factorization.prod (fun p a => p ^ a) := by
        rw [Finsupp.prod_of_support_subset _ hcover (fun p a => p ^ a)
          (by intros; simp)]
        rw [Finset.prod_image (by intros a ha b hb hab; exact hmono.injective hab)]
      _ = n := Nat.prod_factorization_pow_eq_self hn0
  have hbuild (k i h : ℕ) (hhead : g i ≤ h) :
      ∃ t : List ℕ, Ordered h t ∧ suffixNumber 1 i t =
        ∏ j ∈ Finset.range k, prime 1 (i + j) ^ g (i + j) := by
    induction k generalizing i h with
    | zero => exact ⟨[], trivial, by simp [suffixNumber]⟩
    | succ k ih =>
        by_cases hz : g i = 0
        · refine ⟨[], trivial, ?_⟩
          simp only [suffixNumber]
          symm
          apply Finset.prod_eq_one
          intro j hj
          have hzero : g (i + j) = 0 := by have := hg (show i ≤ i + j by omega); omega
          rw [hzero, pow_zero]
        · obtain ⟨t, ht, htn⟩ := ih (i + 1) (g i) (hg (by omega))
          refine ⟨g i :: t, ⟨by omega, hhead, ht⟩, ?_⟩
          rw [suffixNumber, htn, Finset.prod_range_succ']
          simp only [Nat.add_zero]
          rw [Nat.mul_comm]
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          congr 2 <;> omega
  have hcap : g 0 ≤ rootCap 1 B := by
    apply Nat.le_log_of_pow_le (Nat.prime_nth_prime _).one_lt
    exact (Nat.le_of_dvd (by omega)
      (((Nat.prime_nth_prime _).pow_dvd_iff_le_factorization hn0).mpr le_rfl)).trans hnB
  obtain ⟨t, htorder, htn⟩ := hbuild (Nat.primeCounting n) 0 (rootCap 1 B) hcap
  have htn' : suffixNumber 1 0 t = n := by
    simp only [Nat.zero_add] at htn
    exact htn.trans hprod
  obtain ⟨_, _, _, hsigma, _, _⟩ :=
    rough_prime_suffix_complete 1 1 (by decide) (by decide)
  refine ⟨n, t, hn1, hnB, hMn, horder, htorder, htn', ?_, ?_⟩
  · rw [← htn']
    exact hsigma 0 t
  · intro m hm1 hmB hMm
    exact hnmax m (Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hm1, hmB⟩, hMm⟩)

#print axioms forced_core_normalization

end

end D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
