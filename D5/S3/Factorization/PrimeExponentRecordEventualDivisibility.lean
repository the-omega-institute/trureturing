/- GID: D5/S3/Factorization/PrimeExponentRecordEventualDivisibility
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimeExponentRecordEventualDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every positive integer divides all sufficiently large strict prime-exponent records. -/

import D5.S3.Factorization.PrimeExponentRecordLimitOne
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Eventual divisibility of prime-exponent records

OEIS A384669 attributes to Hal M. Switkay, dated 2025-06-06, the conjecture
that every positive natural divides all sufficiently large strict records of
the prime-exponent score. This module proves that statement. The proof is
repository-derived; no claim of priority is made, and subsequent literature
has not been systematically searched.

The resulting threshold has no explicit closed form here. Intermediate bounds
`B` and `C` are extracted from eventual real estimates using
`Classical.choose`, so the proof is nonconstructive.
-/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set

noncomputable section

namespace D5.S3.Factorization.PrimeExponentRecordEventualDivisibility

open D5.S3.Factorization.PrimeExponentRecordLimitOne

private lemma fixed_step_rpow_loss_tendsto_zero (x c : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hc : 0 ≤ c) :
    Tendsto (fun E : ℝ => E ^ x - (E - c) ^ x) atTop (nhds 0) := by
  have hpow : Tendsto (fun E : ℝ => E ^ (x - 1)) atTop (nhds 0) := by
    convert tendsto_rpow_neg_atTop (sub_pos.mpr hx1) using 1
    · funext E
      congr 1
      ring
  have hbound : ∀ᶠ E : ℝ in atTop,
      E ^ x - (E - c) ^ x ≤ c * x * (E - c) ^ (x - 1) := by
    filter_upwards [eventually_gt_atTop (max c 0 + 1)] with E hE
    have hEc : 0 < E - c := by linarith [le_max_left c 0]
    have hcE : E - c ≤ E := sub_le_self E hc
    have hcont : ContinuousOn (fun t : ℝ => t ^ x) (Ici (E - c)) := by
      intro t ht
      exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt (hEc.trans_le ht)))).continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ x) (interior (Ici (E - c))) := by
      intro t ht
      have htpos : 0 < t := hEc.trans (by simpa using ht)
      exact (Real.hasDerivAt_rpow_const (Or.inl htpos.ne')).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ interior (Ici (E - c)),
        deriv (fun u : ℝ => u ^ x) t ≤ x * (E - c) ^ (x - 1) := by
      intro t ht
      have hEt : E - c < t := by simpa only [interior_Ici, mem_Ioi] using ht
      have htpos : 0 < t := hEc.trans hEt
      rw [Real.deriv_rpow_const]
      have hanti : t ^ (x - 1) ≤ (E - c) ^ (x - 1) :=
        (Real.rpow_le_rpow_iff_of_neg htpos hEc (sub_neg.mpr hx1)).mpr hEt.le
      exact mul_le_mul_of_nonneg_left hanti hx0.le
    have hmv := (convex_Ici (E - c)).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hderiv (E - c) (mem_Ici.mpr le_rfl) E hcE hcE
    convert hmv using 1
    all_goals ring
  have hright : Tendsto (fun E : ℝ => c * x * (E - c) ^ (x - 1)) atTop (nhds 0) := by
    have hshift : Tendsto (fun E : ℝ => (E - c) ^ (x - 1)) atTop (nhds 0) :=
      hpow.comp (by simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-c) tendsto_id))
    have hcst : Tendsto (fun _ : ℝ => c * x) atTop (nhds (c * x)) := tendsto_const_nhds
    simpa only [mul_zero] using hcst.mul hshift
  have hleft : ∀ᶠ E : ℝ in atTop, 0 ≤ E ^ x - (E - c) ^ x := by
    filter_upwards [eventually_gt_atTop (max c 0 + 1)] with E hE
    have hEc : 0 < E - c := by linarith [le_max_left c 0]
    exact sub_nonneg.mpr (Real.rpow_le_rpow hEc.le (sub_le_self E hc) hx0.le)
  exact squeeze_zero' hleft hbound hright

private lemma f_eq_range_sum_of_le (x : ℝ) (hx : 0 < x) (n B : ℕ) (hnB : n ≤ B) :
    f x n = ∑ q ∈ Finset.range (B + 1), ((n.factorization q : ℝ) ^ x) := by
  rw [f]
  rw [← Nat.support_factorization]
  apply Finset.sum_subset
  · intro q hq
    rw [Finset.mem_range]
    exact lt_of_le_of_lt
      ((Nat.le_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)).trans hnB)
      (Nat.lt_succ_self B)
  · intro q hqB hq
    have hz : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    simp [hz, Real.zero_rpow hx.ne']

private lemma sum_eq_sub_add_two {B p r : ℕ} (hpr : p ≠ r)
    (hp : p ∈ Finset.range B) (hr : r ∈ Finset.range B)
    (A C : ℕ → ℝ)
    (hAC : ∀ q ∈ Finset.range B, q ≠ p → q ≠ r → A q = C q) :
    ∑ q ∈ Finset.range B, A q =
      (∑ q ∈ Finset.range B, C q) - C p - C r + A p + A r := by
  let S := Finset.range B
  have hr' : r ∈ S.erase p := by simp [S, hr, hpr.symm]
  calc
    ∑ q ∈ S, A q = A p + ∑ q ∈ S.erase p, A q := by
      simpa [add_comm] using (Finset.sum_erase_add S A hp).symm
    _ = A p + (A r + ∑ q ∈ (S.erase p).erase r, A q) := by
      rw [← Finset.sum_erase_add (S.erase p) A hr']
      ring
    _ = A p + (A r + ∑ q ∈ (S.erase p).erase r, C q) := by
      congr 2
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Finset.mem_erase] at hq
      exact hAC q (by simpa [S] using hq.2.2) hq.2.1 hq.1
    _ = (C p + (C r + ∑ q ∈ (S.erase p).erase r, C q)) - C p - C r + A p + A r := by
      ring
    _ = (∑ q ∈ S, C q) - C p - C r + A p + A r := by
      rw [← Finset.sum_erase_add S C hp, ← Finset.sum_erase_add (S.erase p) C hr']
      ring

private def transfer (n r c p k : ℕ) : ℕ := n / r ^ c * p ^ k

private lemma transfer_pos {n r c p k : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hp : 0 < p) (hdiv : r ^ c ∣ n) :
    0 < transfer n r c p k := by
  apply Nat.mul_pos
  · exact Nat.div_pos (Nat.le_of_dvd hn hdiv) (pow_pos hr c)
  · exact pow_pos hp k

private lemma transfer_lt {n r c p k : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hdiv : r ^ c ∣ n) (hpow : p ^ k < r ^ c) :
    transfer n r c p k < n := by
  let u := n / r ^ c
  have hu : 0 < u := Nat.div_pos (Nat.le_of_dvd hn hdiv) (pow_pos hr c)
  calc
    transfer n r c p k = u * p ^ k := rfl
    _ < u * r ^ c := (Nat.mul_lt_mul_left hu).mpr hpow
    _ = n := Nat.div_mul_cancel hdiv

private lemma factorization_transfer_apply {n r c p k q : ℕ}
    (hn : n ≠ 0) (hr : Nat.Prime r) (hp : Nat.Prime p) (hpr : p ≠ r)
    (hdiv : r ^ c ∣ n) :
    (transfer n r c p k).factorization q =
      if q = r then n.factorization r - c
      else if q = p then n.factorization p + k
      else n.factorization q := by
  have hu : n / r ^ c ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv) (pow_pos hr.pos c)).ne'
  rw [transfer, Nat.factorization_mul hu (pow_ne_zero _ hp.ne_zero),
    Nat.factorization_div hdiv, hr.factorization_pow, hp.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hqr : q = r
  · subst q
    simp [hpr]
  by_cases hqp : q = p
  · subst q
    simp [hpr]
  simp [hqr, hqp, Ne.symm hqp]

private lemma f_transfer {x : ℝ} (hx : 0 < x) {n r c p k : ℕ}
    (hn : n ≠ 0) (hr : Nat.Prime r) (hp : Nat.Prime p) (hpr : p ≠ r)
    (hdiv : r ^ c ∣ n) :
    f x (transfer n r c p k) =
      f x n - ((n.factorization r : ℝ) ^ x) - ((n.factorization p : ℝ) ^ x) +
        (((n.factorization r - c : ℕ) : ℝ) ^ x) +
        (((n.factorization p + k : ℕ) : ℝ) ^ x) := by
  have hmpos := transfer_pos (k := k) (Nat.pos_of_ne_zero hn) hr.pos hp.pos hdiv
  let B := max (max n (transfer n r c p k)) (max p r)
  rw [f_eq_range_sum_of_le x hx n B
      ((le_max_left n (transfer n r c p k)).trans (le_max_left _ _)),
    f_eq_range_sum_of_le x hx (transfer n r c p k) B
      ((le_max_right n (transfer n r c p k)).trans (le_max_left _ _))]
  have hrB : r ∈ Finset.range (B + 1) := by
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (le_trans (le_max_right p r) (le_max_right _ _)) (Nat.lt_succ_self B)
  have hpB : p ∈ Finset.range (B + 1) := by
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (le_trans (le_max_left p r) (le_max_right _ _)) (Nat.lt_succ_self B)
  rw [sum_eq_sub_add_two hpr hpB hrB]
  · rw [factorization_transfer_apply hn hr hp hpr hdiv,
      factorization_transfer_apply hn hr hp hpr hdiv]
    simp [hpr]
    ring
  · intro q hq hqp hqr
    rw [factorization_transfer_apply hn hr hp hpr hdiv]
    simp [hqp, hqr]

/-- At a strict record, prime exponents weakly decrease as the primes increase. -/
theorem strictRecord_factorization_antitone {x : ℝ} (hx : 0 < x) {n p q : ℕ}
    (hrec : StrictRecord x n) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) :
    n.factorization q ≤ n.factorization p := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hrec.1
  have hn0 : n ≠ 0 := hnpos.ne'
  by_contra hle
  have hab : n.factorization p < n.factorization q := Nat.lt_of_not_ge hle
  let c := n.factorization q - n.factorization p
  have hc : 0 < c := Nat.sub_pos_of_lt hab
  have hcq : c ≤ n.factorization q := Nat.sub_le _ _
  have hdiv : q ^ c ∣ n :=
    (hq.pow_dvd_iff_le_factorization hn0).mpr hcq
  have hpow : p ^ c < q ^ c := Nat.pow_lt_pow_left hpq hc.ne'
  have hm_lt : transfer n q c p c < n :=
    transfer_lt hrec.1 hq.pos hdiv hpow
  have hm_pos : 0 < transfer n q c p c :=
    transfer_pos hrec.1 hq.pos hp.pos hdiv
  have hscore := f_transfer (k := c) hx hn0 hq hp (ne_of_lt hpq) hdiv
  have hqc : n.factorization q - c = n.factorization p := by
    simp [c, Nat.sub_sub_self (Nat.le_of_lt hab)]
  have hpc : n.factorization p + c = n.factorization q := by
    simp [c, Nat.add_sub_of_le (Nat.le_of_lt hab)]
  rw [hqc, hpc] at hscore
  have hlt := hrec.2 (transfer n q c p c) hm_pos hm_lt
  linarith

private lemma exists_bound_at_smaller_prime {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {p r a : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r) (hrp : r < p) :
    ∃ K : ℕ, ∀ n : ℕ, StrictRecord x n → n.factorization p < a →
      n.factorization r < K := by
  let c := (Nat.log r p).succ
  have hc : p < r ^ c := Nat.lt_pow_succ_log_self hr.one_lt p
  have hc0 : 0 < c := Nat.succ_pos _
  have hev : ∀ᶠ E : ℝ in atTop, ∀ b ∈ Finset.range a,
      E ^ x - (E - c) ^ x < (b + 1 : ℝ) ^ x - (b : ℝ) ^ x := by
    rw [Filter.eventually_all_finset]
    intro b hb
    have hgain : 0 < (b + 1 : ℝ) ^ x - (b : ℝ) ^ x := by
      apply sub_pos.mpr
      exact Real.rpow_lt_rpow (by positivity) (by norm_num) hx0
    exact (fixed_step_rpow_loss_tendsto_zero x c hx0 hx1 (by positivity)).eventually
      (Iio_mem_nhds hgain)
  rcases (eventually_atTop.1 hev) with ⟨R, hR⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (max R (c : ℝ))
  refine ⟨K, ?_⟩
  intro n hrec hpa
  by_contra hEr
  have hKE : K ≤ n.factorization r := Nat.le_of_not_gt hEr
  have hcE : c ≤ n.factorization r := by
    have hcK_real : (c : ℝ) < (K : ℝ) :=
      lt_of_le_of_lt (le_max_right R (c : ℝ)) hK
    have hcK : c < K := by exact_mod_cast hcK_real
    exact hcK.le.trans hKE
  have hdiv : r ^ c ∣ n :=
    (hr.pow_dvd_iff_le_factorization (by
      have : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hrec.1
      exact this.ne')).mpr hcE
  have hpow : p ^ 1 < r ^ c := by simpa using hc
  have hm_lt : transfer n r c p 1 < n := transfer_lt hrec.1 hr.pos hdiv hpow
  have hm_pos : 0 < transfer n r c p 1 := transfer_pos hrec.1 hr.pos hp.pos hdiv
  have hscore := f_transfer (k := 1) hx0 (by
      have : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hrec.1
      exact this.ne') hr hp (ne_of_gt hrp) hdiv
  have hbmem : n.factorization p ∈ Finset.range a := by simpa using hpa
  have hRE : R ≤ (n.factorization r : ℝ) := by
    have hRK : R < K := lt_of_le_of_lt (le_max_left R (c : ℝ)) hK
    exact hRK.le.trans (by exact_mod_cast hKE)
  have hloss := hR (n.factorization r : ℝ) hRE (n.factorization p) hbmem
  have hcast : ((n.factorization r : ℝ) - c) = (n.factorization r - c : ℕ) := by
    exact (Nat.cast_sub hcE).symm
  rw [hcast] at hloss
  have hlt := hrec.2 (transfer n r c p 1) hm_pos hm_lt
  norm_num at hscore
  linarith

private lemma exists_uniform_factorization_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {p a : ℕ} (hp : Nat.Prime p) :
    ∃ B : ℕ, ∀ n : ℕ, StrictRecord x n → n.factorization p < a →
      ∀ q : ℕ, Nat.Prime q → n.factorization q ≤ B := by
  let K : ℕ → ℕ := fun r =>
    if h : Nat.Prime r ∧ r < p then
      Classical.choose (exists_bound_at_smaller_prime (p := p) (r := r) (a := a)
        hx0 hx1 hp h.1 h.2)
    else 0
  have hK : ∀ r : ℕ, Nat.Prime r → r < p →
      ∀ n : ℕ, StrictRecord x n → n.factorization p < a → n.factorization r < K r := by
    intro r hr hrp
    have hh : Nat.Prime r ∧ r < p := ⟨hr, hrp⟩
    simp only [K, dif_pos hh]
    exact Classical.choose_spec (exists_bound_at_smaller_prime (p := p) (r := r) (a := a)
      hx0 hx1 hp hr hrp)
  let B := max a ((Finset.range p).sup K)
  refine ⟨B, ?_⟩
  intro n hrec hpa q hq
  by_cases hqp : q < p
  · have hqK : n.factorization q < K q := hK q hq hqp n hrec hpa
    have hKsup : K q ≤ (Finset.range p).sup K := Finset.le_sup (by simpa using hqp)
    exact (Nat.le_of_lt hqK).trans (hKsup.trans (le_max_right _ _))
  · have hpq : p ≤ q := Nat.le_of_not_gt hqp
    have hfac : n.factorization q ≤ n.factorization p := by
      rcases hpq.eq_or_lt with rfl | hpq
      · exact le_rfl
      · exact strictRecord_factorization_antitone hx0 hrec hp hq hpq
    exact hfac.trans (Nat.le_of_lt hpa) |>.trans (le_max_left _ _)

private lemma exists_uniform_rpow_gain {x : ℝ} (hx : 0 < x) (B : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ E : ℕ, E ≤ B →
      (B : ℝ) ^ x < (E + C : ℕ) ^ x - (E : ℝ) ^ x := by
  have hev : ∀ᶠ C : ℝ in atTop, ∀ E ∈ Finset.range (B + 1),
      (B : ℝ) ^ x + (E : ℝ) ^ x < (E + C) ^ x := by
    rw [Filter.eventually_all_finset]
    intro E hE
    have ht : Tendsto (fun C : ℝ => (E + C) ^ x) atTop atTop :=
      (tendsto_rpow_atTop hx).comp (tendsto_atTop_add_const_left atTop (E : ℝ) tendsto_id)
    exact ht.eventually_gt_atTop ((B : ℝ) ^ x + (E : ℝ) ^ x)
  rcases (eventually_atTop.1 hev) with ⟨R, hR⟩
  obtain ⟨C, hC⟩ := exists_nat_gt (max R 1)
  have hC1 : 1 ≤ C := by
    have : (1 : ℝ) < (C : ℝ) := (le_max_right R 1).trans_lt hC
    exact_mod_cast this.le
  refine ⟨C, hC1, ?_⟩
  intro E hEB
  have hRC : R ≤ (C : ℝ) := (le_max_left R 1).trans hC.le
  have hmain := hR (C : ℝ) hRC E (by simpa using Nat.lt_succ_iff.mpr hEB)
  norm_num at hmain ⊢
  linarith

private lemma nat_le_of_prime_factorization_bounds {n B Q : ℕ} (hn : n ≠ 0) (hQ : 1 ≤ Q)
    (hsupp : ∀ q ∈ n.primeFactors, q ≤ Q)
    (hexp : ∀ q : ℕ, Nat.Prime q → n.factorization q ≤ B) :
    n ≤ (Q ^ B) ^ (Q + 1) := by
  rw [← Nat.prod_factorization_pow_eq_self hn]
  change (∏ q ∈ n.primeFactors, q ^ n.factorization q) ≤ _
  calc
    (∏ q ∈ n.primeFactors, q ^ n.factorization q) ≤
        ∏ q ∈ n.primeFactors, Q ^ B := by
      apply Finset.prod_le_prod
      · simp
      · intro q hq
        exact pow_le_pow (hsupp q hq) hQ (hexp q (Nat.prime_of_mem_primeFactors hq))
    _ ≤ ∏ _q ∈ Finset.range (Q + 1), Q ^ B := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro q hq
        simpa using Nat.lt_succ_iff.mpr (hsupp q hq)
      · simp
      · intro q hq hnot
        simpa using (pow_le_pow_left' hQ B)
    _ = (Q ^ B) ^ (Q + 1) := by simp

/-- Every fixed prime power divides all sufficiently large strict records. -/
theorem eventually_prime_power_dvd_records {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {p a : ℕ} (hp : Nat.Prime p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → StrictRecord x n → p ^ a ∣ n := by
  obtain ⟨B, hB⟩ := exists_uniform_factorization_bound hx0 hx1 hp
  obtain ⟨C, hC1, hgain⟩ := exists_uniform_rpow_gain hx0 B
  let Q := 2 ^ C
  let M := (Q ^ B) ^ (Q + 1)
  refine ⟨M + 1, ?_⟩
  intro n hnlarge hrec
  by_contra hpdvd
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hrec.1
  have hn0 : n ≠ 0 := hnpos.ne'
  have hpa : n.factorization p < a := by
    exact Nat.lt_of_not_ge (mt (hp.pow_dvd_iff_le_factorization hn0).mpr hpdvd)
  have hexp : ∀ q : ℕ, Nat.Prime q → n.factorization q ≤ B := hB n hrec hpa
  have h2Q : 2 ≤ Q := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hC1
    simpa [Q] using this
  have hsupp : ∀ q ∈ n.primeFactors, q ≤ Q := by
    intro q hqmem
    by_contra hqQ
    have hQq : Q < q := Nat.lt_of_not_ge hqQ
    have hq : Nat.Prime q := Nat.prime_of_mem_primeFactors hqmem
    have hqdiv : q ∣ n := Nat.dvd_of_mem_primeFactors hqmem
    let e := n.factorization q
    have hepos : 0 < e := hq.factorization_pos_of_dvd hn0 hqdiv
    have heB : e ≤ B := hexp q hq
    have hdiv : q ^ e ∣ n := (hq.pow_dvd_iff_le_factorization hn0).mpr le_rfl
    have hpow : 2 ^ C < q ^ e := by
      exact hQq.trans_le (Nat.le_pow hepos)
    have h2q : 2 ≠ q := ne_of_lt (h2Q.trans_lt hQq)
    have hm_lt : transfer n q e 2 C < n := transfer_lt hnpos hq.pos hdiv hpow
    have hm_pos : 0 < transfer n q e 2 C :=
      transfer_pos hnpos hq.pos Nat.prime_two.pos hdiv
    have hscore := f_transfer (k := C) hx0 hn0 hq Nat.prime_two h2q hdiv
    have hgain2 := hgain (n.factorization 2) (hexp 2 Nat.prime_two)
    have hepow : (e : ℝ) ^ x ≤ (B : ℝ) ^ x := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast heB) hx0.le
    have heq : n.factorization q - e = 0 := by simp [e]
    rw [heq] at hscore
    simp only [Nat.cast_zero, Real.zero_rpow hx0.ne'] at hscore
    have hlt := hrec.2 (transfer n q e 2 C) hm_pos hm_lt
    linarith
  have hnM : n ≤ M := nat_le_of_prime_factorization_bounds hn0 (by omega) hsupp hexp
  omega

/-- Every positive integer divides all sufficiently large A384669 strict records. -/
theorem prime_exponent_record_eventual_divisibility :
    ∀ x : ℝ, 0 < x → x < 1 → ∀ d : ℕ, 1 ≤ d →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → StrictRecord x n → d ∣ n := by
  intro x hx0 hx1 d hd
  let threshold : ℕ → ℕ := fun p =>
    if hp : Nat.Prime p then
      Classical.choose (eventually_prime_power_dvd_records hx0 hx1
        (a := d.factorization p) hp)
    else 0
  have hthreshold : ∀ p : ℕ, Nat.Prime p →
      ∀ n : ℕ, threshold p ≤ n → StrictRecord x n → p ^ d.factorization p ∣ n := by
    intro p hp
    have hhp : Nat.Prime p := hp
    simp only [threshold, dif_pos hhp]
    exact Classical.choose_spec (eventually_prime_power_dvd_records hx0 hx1
      (a := d.factorization p) hp)
  let N := d.primeFactors.sup threshold
  refine ⟨N, ?_⟩
  intro n hnN hrec
  have hd0 : d ≠ 0 := by omega
  have hn0 : n ≠ 0 := by
    have : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hrec.1
    exact this.ne'
  apply (Nat.factorization_prime_le_iff_dvd hd0 hn0).mp
  intro p hp
  by_cases hpd : p ∣ d
  · have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩
    have hpN : threshold p ≤ N := Finset.le_sup hpmem
    have hpow := hthreshold p hp n (hpN.trans hnN) hrec
    exact (hp.pow_dvd_iff_le_factorization hn0).mp hpow
  · simp [Nat.factorization_eq_zero_of_not_dvd hpd]

end D5.S3.Factorization.PrimeExponentRecordEventualDivisibility
