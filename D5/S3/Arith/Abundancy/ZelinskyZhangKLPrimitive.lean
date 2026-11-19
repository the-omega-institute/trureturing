/- GID: D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive
   mirror-E: none(waiver:symbolic-existence-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Infinitely many positive deficient integers are KL-primitive. -/

import D5.S3.Divergence.StrictGibbs
import D5.S3.Arith.Robin.FibonacciRankEulerTail
import D5.S3.Arith.Robin.GA2ForcedPrimeSource
import D5.S3.Factorization.ReciprocalSigmaThreshold
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! A normalized divisor sum and small prime increments separate the two thresholds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real
open scoped BigOperators

namespace D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive

/-- The divisor-weighted logarithmic sum in equation (6). -/
def KL (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ) * Real.log ((d : ℝ) / (2 * Nat.totient d))

/-- Definition 1, with all positive proper divisors tested. -/
def KLPrimitive (n : ℕ) : Prop :=
  0 ≤ KL n ∧ ∀ d ∈ n.divisors, d < n → KL d < 0

/-- The strict divisor-sum inequality defining deficient integers. -/
def Deficient (n : ℕ) : Prop := (ArithmeticFunction.sigma 1 n : ℝ) < 2 * n

def sig (n : ℕ) : ℝ := ArithmeticFunction.sigma 1 n

private def f (p : ℕ) : ℝ := (p : ℝ) / (p + 1) * log ((p : ℝ) / (p - 1))

private def g (p : ℕ) : ℝ := log (1 + 1 / (p : ℝ))

private lemma sig_sum (n : ℕ) : sig n = ∑ d ∈ n.divisors, (d : ℝ) := by
  simp [sig, ArithmeticFunction.sigma_one_apply]

private lemma kl_one : KL 1 = -log 2 := by
  simp [KL]

private lemma sum_coprime {a b : ℕ} (hab : a.Coprime b) (w : ℕ → ℝ) :
    (∑ d ∈ (a * b).divisors, w d) =
      ∑ x ∈ a.divisors, ∑ y ∈ b.divisors, w (x * y) := by
  rw [hab.divisors_mul]
  rw [sum_map]
  change (∑ x ∈ (a.divisors ×ˢ b.divisors).attach, w (x.val.1 * x.val.2)) = _
  calc
    _ = ∑ z ∈ a.divisors ×ˢ b.divisors, w (z.1 * z.2) :=
      Finset.sum_attach _ (fun z : ℕ × ℕ => w (z.1 * z.2))
    _ = _ := sum_product ..

lemma sig_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : p.Coprime n) :
    sig (p * n) = ((p : ℝ) + 1) * sig n := by
  dsimp [sig]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hpn,
    D5.S3.Factorization.ReciprocalSigmaThreshold.sigma_prime hp]
  push_cast
  rfl

lemma kl_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : p.Coprime n) :
    KL (p * n) = ((p : ℝ) + 1) * KL n +
      (p : ℝ) * sig n * log ((p : ℝ) / (p - 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have term (d : ℕ) (hd : d ∈ n.divisors) :
      ((p * d : ℕ) : ℝ) * log (((p * d : ℕ) : ℝ) /
          (2 * Nat.totient (p * d))) =
        (p : ℝ) * ((d : ℝ) * log ((d : ℝ) / (2 * Nat.totient d))) +
          (p : ℝ) * d * log ((p : ℝ) / (p - 1)) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have ht0 : (0 : ℝ) < Nat.totient d := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hd)
    have hcop := hpn.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]
    simp only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    have heq : (p : ℝ) * d / (2 * ((p - 1) * Nat.totient d)) =
        ((d : ℝ) / (2 * Nat.totient d)) * ((p : ℝ) / (p - 1)) := by
      field_simp
    rw [heq, log_mul (by positivity) (by positivity)]
    ring
  rw [KL, sum_coprime hpn, hp.divisors]
  simp only [sum_insert, mem_singleton, hp.ne_one.symm, not_false_eq_true,
    sum_singleton, one_mul]
  rw [sum_congr rfl term, sum_add_distrib]
  simp only [← mul_sum, ← sum_mul, ← sig_sum]
  change KL n + ((p : ℝ) * KL n +
    (p : ℝ) * sig n * log ((p : ℝ) / (p - 1))) = _
  ring

private lemma g_lt_f {p : ℕ} (hp : 2 ≤ p) : g p < f p := by
  let x : ℝ := p
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hp
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  let P : Fin 2 → ℝ := ![1 / (x + 1), x / (x + 1)]
  let Q : Fin 2 → ℝ := ![1 / x, (x - 1) / x]
  have hP : (∀ i, 0 ≤ P i) ∧ ∑ i, P i = 1 := by
    constructor
    · intro i
      fin_cases i <;> dsimp [P] <;> positivity
    · simp only [Fin.sum_univ_two, P, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring
  have hQpos : ∀ i, 0 < Q i := by
    intro i
    fin_cases i <;> dsimp [Q] <;> positivity
  have hQ : (∀ i, 0 ≤ Q i) ∧ ∑ i, Q i = 1 := by
    refine ⟨fun i => (hQpos i).le, ?_⟩
    simp only [Fin.sum_univ_two, Q, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hne : P ≠ Q := by
    intro h
    have hzero : 1 / (x + 1) = 1 / x := congrFun h 0
    have hlt : 1 / (x + 1) < 1 / x :=
      one_div_lt_one_div_of_lt hx0 (by linarith)
    exact hlt.ne hzero
  have hpos := D5.S3.Divergence.StrictGibbs.kl_divergence_pos_of_ne P Q hP hQ
    (fun i hi => False.elim ((hQpos i).ne' hi)) hne
  have hKL : D5.S3.Divergence.ClassicalDPI.klDivergence P Q = f p - g p := by
    rw [D5.S3.Divergence.ClassicalDPI.klDivergence, Fin.sum_univ_two]
    change 1 / (x + 1) * log ((1 / (x + 1)) / (1 / x)) +
      x / (x + 1) * log ((x / (x + 1)) / ((x - 1) / x)) = _
    have hfirst : (1 / (x + 1)) / (1 / x) = (1 + 1 / x)⁻¹ := by
      field_simp
    have hsecond : (x / (x + 1)) / ((x - 1) / x) =
        (x / (x - 1)) / (1 + 1 / x) := by
      field_simp
    rw [hfirst, hsecond, log_inv, log_div (div_pos hx0 hxm).ne'
      (by positivity : (1 + 1 / x : ℝ) ≠ 0)]
    change _ = x / (x + 1) * log (x / (x - 1)) - log (1 + 1 / x)
    field_simp
    ring
  rw [hKL] at hpos
  linarith

private lemma f_bounds {p : ℕ} (hp : 2 ≤ p) :
    2 / (3 * (p : ℝ)) ≤ f p ∧ f p ≤ 2 / (p : ℝ) ∧
      0 < f p ∧ f p < log 2 := by
  let x : ℝ := p
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hp
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hr : 0 < x / (x - 1) := div_pos hx0 hxm
  have hr1 : 1 < x / (x - 1) := (lt_div_iff₀ hxm).mpr (by linarith)
  have hl : 0 < log (x / (x - 1)) := log_pos hr1
  have hw : 0 < x / (x + 1) := div_pos hx0 hxp
  have hw1 : x / (x + 1) < 1 := (div_lt_one hxp).mpr (by linarith)
  have hlo : 1 / x ≤ log (x / (x - 1)) := by
    have h := one_sub_inv_le_log_of_pos hr
    have he : 1 - (x / (x - 1))⁻¹ = 1 / x := by
      field_simp
      ring
    simpa only [he] using h
  have hhi : log (x / (x - 1)) ≤ 1 / (x - 1) :=
    (D5.S3.Arith.Robin.FibonacciRankEulerTail.euler_log_bounds p hp).2
  have hlow : 2 / (3 * x) ≤ x / (x + 1) * log (x / (x - 1)) := by
    calc
      _ ≤ 1 / (x + 1) :=
        (div_le_div_iff₀ (by positivity : 0 < 3 * x) hxp).mpr (by nlinarith)
      _ = x / (x + 1) * (1 / x) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hw.le
  have hhigh : x / (x + 1) * log (x / (x - 1)) ≤ 2 / x := by
    calc
      _ ≤ log (x / (x - 1)) := mul_le_of_le_one_left hl.le hw1.le
      _ ≤ 1 / (x - 1) := hhi
      _ ≤ 2 / x := (div_le_div_iff₀ hxm hx0).mpr (by nlinarith)
  have hlast : x / (x + 1) * log (x / (x - 1)) < log 2 := by
    calc
      _ < log (x / (x - 1)) := mul_lt_of_lt_one_left hl hw1
      _ ≤ log 2 := log_le_log hr ((div_le_iff₀ hxm).mpr (by nlinarith))
  exact ⟨hlow, hhigh, mul_pos hw hl, hlast⟩

private lemma tail_mass (Q k : ℕ) :
    ∃ s : Finset ℕ, (∀ q ∈ s, q.Prime ∧ Q < q) ∧
      (k : ℝ) / 3 ≤ ∑ q ∈ s, f q := by
  classical
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs, hsum⟩ := ih
    let K := max (Q + 1) (s.sup id + 1)
    let t := (4 ^ (K.primesBelow.card + 1)).succ.primesBelow \ K.primesBelow
    have ht (q : ℕ) (hq : q ∈ t) : q.Prime ∧ K ≤ q := by
      rcases mem_sdiff.mp hq with ⟨hqa, hqb⟩
      have hp := Nat.prime_of_mem_primesBelow hqa
      refine ⟨hp, ?_⟩
      by_contra! hlt
      exact hqb (Nat.mem_primesBelow.mpr ⟨hlt, hp⟩)
    have hdis : Disjoint s t := by
      apply disjoint_left.mpr
      intro q hqs hqt
      have hq := (ht q hqt).2
      have hle : q ≤ s.sup id := Finset.le_sup (f := id) hqs
      have : s.sup id + 1 ≤ K := le_max_right _ _
      omega
    have hblock : (1 : ℝ) / 3 ≤ ∑ q ∈ t, f q := by
      calc
        _ = (2 / 3 : ℝ) * (1 / 2) := by norm_num
        _ ≤ (2 / 3 : ℝ) * ∑ q ∈ t, 1 / (q : ℝ) :=
          mul_le_mul_of_nonneg_left (one_half_le_sum_primes_ge_one_div K)
            (by norm_num)
        _ = ∑ q ∈ t, 2 / (3 * (q : ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q hq
          ring
        _ ≤ ∑ q ∈ t, f q :=
          sum_le_sum (fun q hq => (f_bounds (ht q hq).1.two_le).1)
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro q hq
      rcases mem_union.mp hq with hq | hq
      · exact hs q hq
      · have hq' := ht q hq
        have : Q + 1 ≤ K := le_max_left _ _
        exact ⟨hq'.1, by omega⟩
    · rw [sum_union hdis]
      push_cast
      linarith

private lemma crossing (B : ℕ) :
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ B < q ∧ 2 < q) ∧
      log 2 ≤ ∑ q ∈ S, f q ∧ (∑ q ∈ S, g q) < log 2 := by
  classical
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (max B 2 + 1)
  have hpB' : max B 2 < p := by omega
  let e := (f p - g p) / 2
  have he : 0 < e := by
    dsimp [e]
    linarith [g_lt_f hp.two_le]
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / e)
  let Q := max p N
  obtain ⟨s, hs, hsum⟩ := tail_mass Q 3
  have hseed := (f_bounds hp.two_le).2.2.2
  have hcross : ∃ k : ℕ, ∃ t : Finset ℕ,
      t ⊆ s ∧ t.card = k ∧ log 2 ≤ f p + ∑ q ∈ t, f q := by
    refine ⟨s.card, s, Subset.rfl, rfl, ?_⟩
    norm_num at hsum
    have hlog := log_lt_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
      (by norm_num : (2 : ℝ) ≠ 1)
    have hpos := (f_bounds hp.two_le).2.2.1
    linarith
  obtain ⟨t, hts, htcard, htcross⟩ := Nat.find_spec hcross
  have htne : t.Nonempty := by
    by_contra h
    have hempty := not_nonempty_iff_eq_empty.mp h
    simp only [hempty, sum_empty, add_zero] at htcross
    linarith
  obtain ⟨q, hqt⟩ := htne
  have hprev : f p + (∑ r ∈ t.erase q, f r) < log 2 := by
    by_contra! h
    have hcard : (t.erase q).card < Nat.find hcross := by
      rw [card_erase_of_mem hqt, htcard]
      have hpos := card_pos.mpr (show t.Nonempty from ⟨q, hqt⟩)
      omega
    exact Nat.find_min hcross hcard
      ⟨t.erase q, (erase_subset _ _).trans hts, rfl, h⟩
  have hqdata := hs q (hts hqt)
  have hqN : N < q := lt_of_le_of_lt (le_max_right _ _) hqdata.2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqdata.1.pos
  have hstep : f q < e := by
    have hlarge : 2 / e < (q : ℝ) := hN.trans (by exact_mod_cast hqN)
    have hlarge' : 2 < (q : ℝ) * e := (div_lt_iff₀ he).mp hlarge
    apply (f_bounds hqdata.1.two_le).2.1.trans_lt
    apply (div_lt_iff₀ hq0).mpr
    nlinarith
  have hsumt : (∑ r ∈ t, f r) = (∑ r ∈ t.erase q, f r) + f q :=
    (sum_erase_add t f hqt).symm
  have htotal : f p + (∑ r ∈ t, f r) < log 2 + e := by
    rw [hsumt]
    linarith
  have hpnot : p ∉ t := by
    intro hpt
    have hlt := (hs p (hts hpt)).2
    have : p ≤ Q := le_max_left _ _
    omega
  refine ⟨insert p t, ?_, ?_, ?_⟩
  · intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact ⟨hp, lt_of_le_of_lt (le_max_left _ _) hpB',
        lt_of_le_of_lt (le_max_right _ _) hpB'⟩
    · have hr' := hs r (hts hr)
      have hpQ : p ≤ Q := le_max_left _ _
      exact ⟨hr'.1, by omega, by omega⟩
  · simpa only [sum_insert hpnot] using htcross
  · rw [sum_insert hpnot]
    have hgt : (∑ r ∈ t, g r) ≤ ∑ r ∈ t, f r :=
      sum_le_sum (fun r hr => (g_lt_f (hs r (hts hr)).1.two_le).le)
    dsimp [e] at htotal
    linarith

private lemma product_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < ∏ p ∈ s, p := prod_pos (fun p hp => (hs p hp).pos)

private lemma normalized (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    KL (∏ p ∈ s, p) = sig (∏ p ∈ s, p) * ((∑ p ∈ s, f p) - log 2) ∧
      log (sig (∏ p ∈ s, p) / (∏ p ∈ s, p)) = ∑ p ∈ s, g p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kl_one, sig]
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self _ _)
    have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (Nat.coprime_primes hpp (hsp q hq)).mpr
      intro he
      exact hp (he ▸ hq)
    have hn := product_pos s hsp
    have hnR : (0 : ℝ) < ∏ q ∈ s, q := by exact_mod_cast hn
    have hsR : 0 < sig (∏ q ∈ s, q) := by
      dsimp [sig]
      exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (by omega : (∏ q ∈ s, q) ≠ 0)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have ih' := ih hsp
    simp only [prod_insert hp, sum_insert hp]
    constructor
    · rw [kl_prime_mul hpp hcop, sig_prime_mul hpp hcop, ih'.1]
      dsimp [f]
      field_simp
      ring
    · rw [sig_prime_mul hpp hcop, Nat.cast_mul]
      have heq : (((p : ℝ) + 1) * sig (∏ q ∈ s, q)) /
          ((p : ℝ) * (∏ q ∈ s, q)) =
            (1 + 1 / (p : ℝ)) * (sig (∏ q ∈ s, q) / (∏ q ∈ s, q)) := by
        field_simp
      rw [heq, log_mul (by positivity) (by positivity), ih'.2]
      rfl

private lemma deficient_of_dvd {d n : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ∣ n) (hdef : Deficient n) : Deficient d := by
  have hle : sig d / d ≤ sig n / n :=
    D5.S3.Arith.Robin.GA2ForcedPrimeSource.abundancy_mono hd hn hdn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  change sig d < 2 * d
  change sig n < 2 * n at hdef
  exact (div_lt_iff₀ hdR).mp (hle.trans_lt ((div_lt_iff₀ hnR).mpr hdef))

private lemma primitive_divisor {m : ℕ} (hm : 0 < m) (hkm : 0 ≤ KL m)
    (hdef : Deficient m) :
    ∃ d : ℕ, 0 < d ∧ d ∣ m ∧ Deficient d ∧ KLPrimitive d := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ d ∣ m ∧ 0 ≤ KL d := ⟨m, hm, dvd_rfl, hkm⟩
  let d := Nat.find hex
  obtain ⟨hd, hdm, hkd⟩ := Nat.find_spec hex
  refine ⟨d, hd, hdm, deficient_of_dvd hm hd hdm hdef, hkd, ?_⟩
  intro e he hed
  by_contra! hke
  exact Nat.find_min hex hed
    ⟨Nat.pos_of_mem_divisors he, (Nat.dvd_of_mem_divisors he).trans hdm, hke⟩

/-- Conjecture 15: positive deficient KL-primitive integers are unbounded. -/
theorem result : ∀ B : ℕ, ∃ n : ℕ, B < n ∧ 0 < n ∧ Deficient n ∧ KLPrimitive n := by
  intro B
  obtain ⟨s, hs, hf, hg⟩ := crossing B
  have hsp : ∀ p ∈ s, p.Prime := fun p hp => (hs p hp).1
  let m := ∏ p ∈ s, p
  have hm : 0 < m := product_pos s hsp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsig : 0 < sig m := by
    dsimp [sig]
    exact_mod_cast ArithmeticFunction.sigma_pos 1 m (by omega)
  obtain ⟨hkl, hlog⟩ := normalized s hsp
  have hkm : 0 ≤ KL m := by
    rw [hkl]
    exact mul_nonneg hsig.le (sub_nonneg.mpr hf)
  have hdef : Deficient m := by
    have hratio : sig m / m < 2 := by
      apply (log_lt_log_iff (div_pos hsig hmR) (by norm_num)).mp
      exact hlog ▸ hg
    exact (div_lt_iff₀ hmR).mp hratio
  obtain ⟨d, hd, hdm, hdd, hdp⟩ := primitive_divisor hm hkm hdef
  have hd1 : d ≠ 1 := by
    intro he
    have hk := hdp.1
    rw [he, kl_one] at hk
    have := log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hd1
  obtain ⟨q, hqs, hrq⟩ := (hr.prime.dvd_finsetProd_iff _).mp (hrd.trans hdm)
  have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr (hsp q hqs)).mp hrq
  refine ⟨d, ?_, hd, hdd, hdp⟩
  exact (hrq' ▸ (hs q hqs).2.1).trans_le (Nat.le_of_dvd hd hrd)

end D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
