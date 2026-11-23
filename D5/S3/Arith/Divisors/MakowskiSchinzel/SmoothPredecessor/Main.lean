/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Both sigma-totient bounds for integers with smooth prime predecessors. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Main
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.SmoothedGroups
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Certificate
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count00
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count01
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count02
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count03
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count04
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count05
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count06
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count07
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count08
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count09
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Count10

/-! Multiplicity-free and odd reduction without imposing smoothness on the totient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

open Finset UniqueFactorizationMonoid

/-- Any finite collection of full valuation components divides the original integer. -/
private theorem prime_power_components_dvd (n : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, p ^ n.factorization p) ∣ n := by
  classical
  let f := n.factorization.filter (fun p => p ∈ s)
  have hf : f ≤ n.factorization := by
    intro p
    simp only [f, Finsupp.filter_apply]
    split <;> omega
  have hsupport : f.support ⊆ s := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hprod := f.prod_of_support_subset hsupport (fun p k => p ^ k)
    (fun _ _ => pow_zero _)
  have heq : f.prod (fun p k => p ^ k) = ∏ p ∈ s, p ^ n.factorization p := by
    rw [hprod]
    apply prod_congr rfl
    intro p hp
    simp only [f, Finsupp.filter_apply, if_pos hp]
  rw [← heq]
  exact Nat.prod_pow_dvd_of_le_factorization hf

/-- A grouped product bound suffices for every odd squarefree integer. -/
private theorem alpha_of_grouped_bound {m : ℕ} (hm : Odd m) (hsq : Squarefree m)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2)
    (hgroup : (∏ q ∈ nonFermatFactors m, (q : ℚ) / (q - 1 : ℕ)) ≤
      ∏ p ∈ s, geom p (∑ q ∈ nonFermatFactors m, (q - 1).factorization p)) :
    1 ≤ alpha m := by
  classical
  let A := m.primeFactors
  let Q := nonFermatFactors m
  let T := A \ Q
  let f := ∏ q ∈ T, q
  let b := ∏ q ∈ Q, (q - 1)
  let e := fun p => ∑ q ∈ Q, (q - 1).factorization p
  let d := ∏ p ∈ s, p ^ e p
  have hsub : Q ⊆ A := filter_subset _ _
  have hp (q : ℕ) (hq : q ∈ A) : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpT (q : ℕ) (hq : q ∈ T) : q.Prime := hp q (mem_sdiff.mp hq).1
  have hpQ (q : ℕ) (hq : q ∈ Q) : q.Prime := hp q (hsub hq)
  have hqpos (q : ℕ) (hq : q ∈ Q) : 0 < q - 1 := by
    have := (hpQ q hq).two_le
    omega
  have hf0 : f ≠ 0 := (prod_pos fun q hq => (hpT q hq).pos).ne'
  have hb0 : b ≠ 0 := (prod_pos hqpos).ne'
  have hfmul : f * (∏ q ∈ Q, q) = m :=
    (prod_sdiff hsub).trans (Nat.prod_primeFactors_of_squarefree hsq)
  have hfdvd : f ∣ m := ⟨_, hfmul.symm⟩
  have hfo : Odd f := hm.of_dvd_nat hfdvd
  have hfsq : Squarefree f := hsq.squarefree_of_dvd hfdvd
  have hfpf : f.primeFactors = T := Nat.primeFactors_prod hpT
  have hphiF : f.totient = ∏ q ∈ T, (q - 1) := by
    rw [D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hf0 hfsq, hfpf]
  have hphiM : m.totient = f.totient * b := by
    rw [D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hsq.ne_zero hsq, hphiF]
    exact (prod_sdiff hsub).symm
  have hFermat (q : ℕ) (hq : q ∈ T) : ∃ k : ℕ, q - 1 = 2 ^ k := by
    have hqA := (mem_sdiff.mp hq).1
    have hqne : q ≠ 2 := by
      intro he
      exact hm.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors hqA)
    by_contra hno
    exact (mem_sdiff.mp hq).2 (mem_filter.mpr ⟨hqA, hqne, hno⟩)
  have hphiF0 : f.totient ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf0)).ne'
  have hphiFpow : f.totient = 2 ^ f.totient.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hphiF0
    intro r hr hrd
    rw [hphiF] at hrd
    obtain ⟨q, hq, hrq⟩ := (hr.prime.dvd_finsetProd_iff _).mp hrd
    obtain ⟨k, hk⟩ := hFermat q hq
    rw [hk] at hrq
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrq)
  have hFbound : 1 ≤ alpha f := by
    have hb := odd_le_sigma_totient_of_two_pow hfo hphiFpow
    rw [alpha, le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hf0 : (0 : ℚ) < f)]
    simpa only [one_mul] using (show (f : ℚ) ≤ ArithmeticFunction.sigma 1 f.totient by
      exact_mod_cast hb)
  have he (p : ℕ) : b.factorization p = e p :=
    Nat.factorization_prod_apply fun q hq => (hqpos q hq).ne'
  have hdvd : d ∣ b := by
    have hd := prime_power_components_dvd b s
    simpa only [he] using hd
  have hcop : Nat.Coprime f.totient d := by
    rw [hphiFpow]
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro p hp
    exact ((Nat.coprime_primes Nat.prime_two (hs p hp).1).mpr
      (hs p hp).2.symm).pow_right (e p)
  have hdphi : f.totient * d ∣ m.totient := by
    rw [hphiM]
    exact Nat.mul_dvd_mul_left _ hdvd
  have hab : f.totient.abundancyIndex * (∏ p ∈ s, geom p (e p)) ≤
      m.totient.abundancyIndex := by
    rw [← abundancy_prime_power_product s e (fun p hp _ => (hs p hp).1),
      ← abundancy_mul hcop]
    exact Nat.abundancyIndex_le_of_dvd
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hsq.ne_zero)).ne' hdphi
  have hT0 : 0 ≤ ∏ q ∈ T, (1 - (q : ℚ)⁻¹) := by
    apply prod_nonneg
    intro q hq
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀
      (by exact_mod_cast (hpT q hq).one_lt.le))
  have hQpos : 0 < ∏ q ∈ Q, (1 - (q : ℚ)⁻¹) := by
    apply prod_pos
    intro q hq
    have hq1 : (1 : ℚ) < q := by exact_mod_cast (hpQ q hq).one_lt
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hq1)
  have hcancel : (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) *
      (∏ q ∈ Q, (1 - (q : ℚ)⁻¹)) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    have hq1 := (hpQ q hq).two_le
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (hpQ q hq).ne_zero
    have hqsub : (q : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ q := by exact_mod_cast hq1
      linarith
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    field_simp [hq0, hqsub]
  have hgroup' : 1 ≤ (∏ p ∈ s, geom p (e p)) *
      (∏ q ∈ Q, (1 - (q : ℚ)⁻¹)) := by
    have hg := mul_le_mul_of_nonneg_right hgroup hQpos.le
    rw [hcancel] at hg
    exact hg
  rw [alpha_factorization f, hfpf] at hFbound
  have hFnonneg : 0 ≤ f.totient.abundancyIndex *
      (∏ q ∈ T, (1 - (q : ℚ)⁻¹)) := le_trans (by norm_num) hFbound
  have hjoin := mul_le_mul hFbound hgroup' (by norm_num : (0 : ℚ) ≤ 1) hFnonneg
  have hlast := mul_le_mul_of_nonneg_right hab (mul_nonneg hT0 hQpos.le)
  rw [alpha_factorization m, ← prod_sdiff hsub]
  calc
    1 ≤ (f.totient.abundancyIndex * (∏ q ∈ T, (1 - (q : ℚ)⁻¹))) *
        ((∏ p ∈ s, geom p (e p)) * (∏ q ∈ Q, (1 - (q : ℚ)⁻¹))) := by
      simpa only [one_mul] using hjoin
    _ ≤ m.totient.abundancyIndex *
        ((∏ q ∈ T, (1 - (q : ℚ)⁻¹)) * (∏ q ∈ Q, (1 - (q : ℚ)⁻¹))) := by
      nlinarith [hlast]


/-- Successful arbitrary certificates imply both inequalities for all smooth predecessors. -/
private theorem checked_smooth_predecessors (E : List ℕ) (tl : List (ℕ × ℕ × ℕ))
    (fs : List (ℕ × ℕ)) (hv : E.all validEntry = true)
    (hi : (E.map entryValue).Pairwise (· < ·))
    (hc : smoothSum candidateWeight allPrimes bound 2 ≤ E.length)
    (ht : oddPrimes.map tailData = tl)
    (hr : stepTable tl E initialState = some fs) (hf : finalOk tl fs = true)
    (n : ℕ) (h : ∀ q ∈ n.primeFactors, q - 1 ∈ Nat.smoothNumbers 98) :
    n ≤ 2 * ArithmeticFunction.sigma 1 n.totient ∧
      (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient) := by
  classical
  apply (lift_odd_squarefree_iff
    (fun k => ∀ q ∈ k.primeFactors, q - 1 ∈ Nat.smoothNumbers 98) ?_).mp ?_ n h
  · intro k hk0 hk m _ hcore q hq
    apply hk q
    have hdiv : m ∣ radical k := by
      rcases hcore with he | he
      · rw [he]
      · rw [he]
        exact dvd_mul_left m 2
    have hmem := Nat.primeFactors_mono hdiv (Nat.radical_pos k).ne' hq
    simpa only [Nat.primeFactors_radical] using hmem
  · intro m hm hsq hsm
    have hn : (E.map entryValue).Nodup := hi.imp (fun h => ne_of_lt h)
    have hsOrder (i : ℕ) : (groupValues i E).Pairwise (· ≤ ·) := by
      have hsub : List.Sublist (groupValues i E) (E.map entryValue) :=
        List.Sublist.map entryValue List.filter_sublist
      exact List.Pairwise.sublist hsub (hi.imp (fun h => h.le))
    have hQ (q : ℕ) (hq : q ∈ nonFermatFactors m) : q.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    have hQsm (q : ℕ) (hq : q ∈ nonFermatFactors m) :
        q - 1 ∈ Nat.smoothNumbers 98 := hsm q (Finset.mem_filter.mp hq).1
    have hQpow (q : ℕ) (hq : q ∈ nonFermatFactors m) : ¬∃ k : ℕ, q - 1 = 2 ^ k :=
      (Finset.mem_filter.mp hq).2.2
    apply alpha_of_grouped_bound hm hsq oddPrimes.toFinset ?_
      (smooth_group_product E tl fs hv hn hsOrder hc ht hr hf (nonFermatFactors m) hQsm
        (fun q hq => ⟨fun _ => (candidate_of_prime (hQ q hq)).mpr (hQpow q hq),
          fun _ => ⟨(hQ q hq).odd_of_ne_two (Finset.mem_filter.mp hq).2.1,
            hQpow q hq⟩⟩))
    intro p hp
    have hall : oddPrimes.all (fun r => decide (r.Prime ∧ r ≠ 2)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hall p (List.mem_toFinset.mp hp))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Smoothness of the prime predecessors gives both sigma-totient inequalities. -/
theorem makowski_schinzel_of_smooth_predecessors (n : ℕ)
    (h : ∀ q ∈ n.primeFactors, q - 1 ∈ Nat.smoothNumbers 98) :
    n ≤ 2 * ArithmeticFunction.sigma 1 n.totient ∧
      (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient) := by
  classical
  have count00_checked :
      (nodes00.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 638 := by
    decide +kernel
  have count01_checked :
      (nodes01.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 528 := by
    decide +kernel
  have count02_checked :
      (nodes02.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 1226 := by
    decide +kernel
  have count03_checked :
      (nodes03.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 1235 := by
    decide +kernel
  have count04_checked :
      (nodes04.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 773 := by
    decide +kernel
  have count05_checked :
      (nodes05.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 1512 := by
    decide +kernel
  have count06_checked :
      (nodes06.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 591 := by
    decide +kernel
  have count07_checked :
      (nodes07.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 975 := by
    decide +kernel
  have count08_checked :
      (nodes08.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 958 := by
    decide +kernel
  have count09_checked :
      (nodes09.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 1010 := by
    decide +kernel
  have count10_checked :
      (nodes10.map fun x => smoothSum candidateWeight x.1 bound x.2).sum = 573 := by
    decide +kernel
  have table00_valid : table00.all validEntry = true := by decide +kernel
  have table00_increasing : increasingFrom 6 (table00.map entryValue) = true :=
    by decide +kernel
  have table00_step :
      stepTable tails table00 state00 = some state01 := by decide +kernel
  have table01_valid : table01.all validEntry = true := by decide +kernel
  have table01_increasing : increasingFrom 27528 (table01.map entryValue) = true :=
    by decide +kernel
  have table01_step :
      stepTable tails table01 state01 = some state02 := by decide +kernel
  have table02_valid : table02.all validEntry = true := by decide +kernel
  have table02_increasing : increasingFrom 87150 (table02.map entryValue) = true :=
    by decide +kernel
  have table02_step :
      stepTable tails table02 state02 = some state03 := by decide +kernel
  have table03_valid : table03.all validEntry = true := by decide +kernel
  have table03_increasing : increasingFrom 174048 (table03.map entryValue) = true :=
    by decide +kernel
  have table03_step :
      stepTable tails table03 state03 = some state04 := by decide +kernel
  have table04_valid : table04.all validEntry = true := by decide +kernel
  have table04_increasing : increasingFrom 284592 (table04.map entryValue) = true :=
    by decide +kernel
  have table04_step :
      stepTable tails table04 state04 = some state05 := by decide +kernel
  have table05_valid : table05.all validEntry = true := by decide +kernel
  have table05_increasing : increasingFrom 423108 (table05.map entryValue) = true :=
    by decide +kernel
  have table05_step :
      stepTable tails table05 state05 = some state06 := by decide +kernel
  have table06_valid : table06.all validEntry = true := by decide +kernel
  have table06_increasing : increasingFrom 586710 (table06.map entryValue) = true :=
    by decide +kernel
  have table06_step :
      stepTable tails table06 state06 = some state07 := by decide +kernel
  have table07_valid : table07.all validEntry = true := by decide +kernel
  have table07_increasing : increasingFrom 770880 (table07.map entryValue) = true :=
    by decide +kernel
  have table07_step :
      stepTable tails table07 state07 = some state08 := by decide +kernel
  have table08_valid : table08.all validEntry = true := by decide +kernel
  have table08_increasing : increasingFrom 995566 (table08.map entryValue) = true :=
    by decide +kernel
  have table08_step :
      stepTable tails table08 state08 = some finalState := by decide +kernel
  have tail0_checked : tailLabels0.map tailData = tailBlock0 := by decide +kernel
  have tail1_checked : tailLabels1.map tailData = tailBlock1 := by decide +kernel
  have tail2_checked : tailLabels2.map tailData = tailBlock2 := by decide +kernel
  have tail3_checked : tailLabels3.map tailData = tailBlock3 := by decide +kernel
  have final_checked : finalOk tails finalState = true := by decide +kernel
  have table_valid : table.all validEntry = true := by
    simp only [table, List.all_append, table00_valid, table01_valid, table02_valid,
      table03_valid, table04_valid, table05_valid, table06_valid, table07_valid,
      table08_valid, Bool.and_self]
  have tailData_map : oddPrimes.map tailData = tails := by
    have h0 := tail0_checked
    have h1 := tail1_checked
    have h2 := tail2_checked
    have h3 := tail3_checked
    change ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).map tailData = _ at h0
    change ([37, 41, 43, 47, 53] : List ℕ).map tailData = _ at h1
    change ([59, 61, 67, 71, 73] : List ℕ).map tailData = _ at h2
    change ([79, 83, 89, 97] : List ℕ).map tailData = _ at h3
    have he : oddPrimes =
        [3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ++ [37, 41, 43, 47, 53] ++
          [59, 61, 67, 71, 73] ++ [79, 83, 89, 97] := rfl
    rw [he, List.map_append, List.map_append, List.map_append, h0, h1, h2, h3]
    rfl
  have table_checked :
      stepTable tails table initialState = some finalState ∧ finalOk tails finalState = true := by
    have h0 := table00_step
    change stepTable tails table00 initialState = _ at h0
    refine ⟨?_, final_checked⟩
    simp only [table, stepTable_append, h0, Option.bind_some, table01_step,
      table02_step, table03_step, table04_step, table05_step, table06_step,
      table07_step, table08_step]
  have table_increasing : increasingFrom 6 (table.map entryValue) = true := by
    have e0 (a : ℕ) : (table00.map entryValue).getLastD a = 27509 := rfl
    have e1 (a : ℕ) : (table01.map entryValue).getLastD a = 87121 := rfl
    have e2 (a : ℕ) : (table02.map entryValue).getLastD a = 174019 := rfl
    have e3 (a : ℕ) : (table03.map entryValue).getLastD a = 284377 := rfl
    have e4 (a : ℕ) : (table04.map entryValue).getLastD a = 423097 := rfl
    have e5 (a : ℕ) : (table05.map entryValue).getLastD a = 586603 := rfl
    have e6 (a : ℕ) : (table06.map entryValue).getLastD a = 770801 := rfl
    have e7 (a : ℕ) : (table07.map entryValue).getLastD a = 995329 := rfl
    have lower {a b : ℕ} {xs : List ℕ} (hab : a ≤ b)
        (h : increasingFrom b xs = true) : increasingFrom a xs = true := by
      obtain ⟨hp, hm⟩ := increasingFrom_sound.mp h
      exact increasingFrom_sound.mpr ⟨hp, fun x hx => hab.trans_lt (hm x hx)⟩
    have h1 := lower (show 27509 ≤ 27528 by decide) table01_increasing
    have h2 := lower (show 87121 ≤ 87150 by decide) table02_increasing
    have h3 := lower (show 174019 ≤ 174048 by decide) table03_increasing
    have h4 := lower (show 284377 ≤ 284592 by decide) table04_increasing
    have h5 := lower (show 423097 ≤ 423108 by decide) table05_increasing
    have h6 := lower (show 586603 ≤ 586710 by decide) table06_increasing
    have h7 := lower (show 770801 ≤ 770880 by decide) table07_increasing
    have h8 := lower (show 995329 ≤ 995566 by decide) table08_increasing
    simp only [table, List.append_assoc, List.map_append, increasingFrom_append,
      e0, e1, e2, e3, e4, e5, e6, e7, table00_increasing, h1, h2, h3, h4, h5,
      h6, h7, h8, Bool.and_self]
  have candidate_count : smoothSum candidateWeight allPrimes bound 2 = 10019 := by
    have hfrontier : frontierOk bound 3 (allPrimes, 2) (nodes00 ++ nodes01 ++ nodes02 ++
        nodes03 ++ nodes04 ++ nodes05 ++ nodes06 ++ nodes07 ++ nodes08 ++ nodes09 ++
        nodes10) = true := by
      decide +kernel
    have hroot := smoothSum_eq_of_frontierOk candidateWeight hfrontier
    simp only [List.map_append, List.sum_append, count00_checked, count01_checked, count02_checked,
      count03_checked, count04_checked, count05_checked, count06_checked, count07_checked,
      count08_checked, count09_checked, count10_checked] at hroot
    exact hroot
  have hlen : table.length = 10019 := by
    have h0 : table00.length = 1250 := by decide
    have h1 : table01.length = 1250 := by decide
    have h2 : table02.length = 1250 := by decide
    have h3 : table03.length = 1250 := by decide
    have h4 : table04.length = 1250 := by decide
    have h5 : table05.length = 1250 := by decide
    have h6 : table06.length = 1250 := by decide
    have h7 : table07.length = 1250 := by decide
    have h8 : table08.length = 19 := by decide
    simp only [table, List.length_append, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have hcount : smoothSum candidateWeight allPrimes bound 2 ≤ table.length := by
    rw [candidate_count, hlen]
  exact checked_smooth_predecessors table tails finalState table_valid
    (increasingFrom_sound.mp table_increasing).1 hcount tailData_map
    table_checked.1 table_checked.2 n h

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
