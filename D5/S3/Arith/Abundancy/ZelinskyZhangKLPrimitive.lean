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
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import Mathlib.Analysis.SpecificLimits.Basic
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

def f (p : ℕ) : ℝ := (p : ℝ) / (p + 1) * log ((p : ℝ) / (p - 1))

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

lemma f_bounds {p : ℕ} (hp : 2 ≤ p) :
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

lemma tail_mass (Q k : ℕ) :
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

lemma deficient_of_dvd {d n : ℕ} (hn : 0 < n) (hd : 0 < d)
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

private def coreH (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 + 1 / (p : ℝ))

private def coreAlpha (s : Finset ℕ) : ℝ := coreH s / (2 - coreH s)

private lemma core_step_numeric {a p : ℝ} (ha : 2 ≤ a)
    (hp : 2 * a < p) (hp' : p ≤ 3 * a) :
    (3 / 2 : ℝ) * a ≤ a * (p + 1) / (p - a) ∧
      a * (p + 1) / (p - a) ≤ 3 * a ∧
      p < 2 * (a * (p + 1) / (p - a)) := by
  have ha0 : 0 < a := by linarith
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - a := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hp')]
  constructor
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hp.le)]
  · rw [← mul_div_assoc, lt_div_iff₀ hd]
    have hpp : p * p ≤ p * (3 * a) := mul_le_mul_of_nonneg_left hp' hp0.le
    nlinarith

private lemma core_step_prime : ∃ Y : ℝ, ∀ a : ℝ, Y ≤ a →
    ∃ p : ℕ, p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a := by
  obtain ⟨Y, hY⟩ :=
    D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity.fixed_cardinality_prime_window
      (A := 2) (B := 3) (by norm_num) (by norm_num) 1
  refine ⟨Y, fun a ha => ?_⟩
  obtain ⟨s, hs, hsp⟩ := hY a ha
  have hne : s.Nonempty := card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hsp p hp⟩

private lemma coreH_pos (s : Finset ℕ) : 0 < coreH s := by
  apply prod_pos
  intro p hp
  positivity

private lemma coreH_insert (s : Finset ℕ) {p : ℕ} (hp : p ∉ s) :
    coreH (insert p s) = coreH s * (1 + 1 / (p : ℝ)) := by
  simp only [coreH, prod_insert hp]
  ring

private lemma core_step_ratio {h p : ℝ} (hh : 0 < h) (hh2 : h < 2)
    (hp : h / (2 - h) < p) :
    h * (1 + 1 / p) < 2 ∧
      h * (1 + 1 / p) / (2 - h * (1 + 1 / p)) =
        (h / (2 - h)) * (p + 1) / (p - h / (2 - h)) := by
  have hd : 0 < 2 - h := by linarith
  have ha : 0 < h / (2 - h) := div_pos hh hd
  have hp0 : 0 < p := ha.trans hp
  have hpa : 0 < p - h / (2 - h) := sub_pos.mpr hp
  have hcross : h < p * (2 - h) := (div_lt_iff₀ hd).mp hp
  have hhnew : h * (1 + 1 / p) < 2 := by
    rw [mul_add, mul_one]
    have hdiv : h / p < 2 - h := (div_lt_iff₀ hp0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using (by linarith : h + h / p < 2)
  refine ⟨hhnew, ?_⟩
  have hbase : p * 2 - p * h - h ≠ 0 := by nlinarith [hcross]
  field_simp [hd.ne', hp0.ne', hpa.ne', (sub_pos.mpr hhnew).ne', hbase]
  <;> try field_simp [hbase]
  <;> ring
  have hden : p * 2 - h * (p + 1) ≠ 0 := by nlinarith [hcross]
  apply (div_eq_one_iff_eq hden).mpr
  ring

private lemma core_reciprocal_tail (B : ℕ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B < p) ∧
      1 ≤ ∑ p ∈ s, 1 / (p : ℝ) := by
  obtain ⟨s, hs, hmass⟩ := tail_mass B 6
  refine ⟨s, hs, ?_⟩
  have hbound : (∑ p ∈ s, f p) ≤ 2 * ∑ p ∈ s, 1 / (p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    simpa only [div_eq_mul_inv, one_mul] using (f_bounds (hs p hp).1.two_le).2.1
  norm_num at hmass
  linarith

private lemma core_sum_le (s : Finset ℕ) :
    1 + (∑ p ∈ s, 1 / (p : ℝ)) ≤ coreH s := by
  classical
  rw [coreH, prod_one_add_ordered]
  gcongr with p hp
  have hprod : (1 : ℝ) ≤ ∏ q ∈ s with q < p, (1 + 1 / (q : ℝ)) :=
    Finset.one_le_prod₀ (fun q _ => by positivity)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 1 / p by positivity)

private lemma core_seed (B : ℕ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B < p) ∧ coreH s < 2 ∧
      (B : ℝ) < coreAlpha s ∧
      (∀ p ∈ s, (p : ℝ) < 2 * coreAlpha s) := by
  classical
  obtain ⟨s, hs, hmass⟩ := core_reciprocal_tail B
  have hcross : ∃ k : ℕ, ∃ t : Finset ℕ,
      t ⊆ s ∧ t.card = k ∧ 2 ≤ coreH t :=
    ⟨s.card, s, Subset.rfl, rfl, by linarith [core_sum_le s]⟩
  obtain ⟨t, hts, htcard, htH⟩ := Nat.find_spec hcross
  have htne : t.Nonempty := by
    by_contra hn
    have ht0 := not_nonempty_iff_eq_empty.mp hn
    simp only [ht0, coreH, prod_empty] at htH
    norm_num at htH
  obtain ⟨r, hrt, hrmax⟩ := Finset.exists_mem_eq_sup t htne id
  change t.sup id = r at hrmax
  let u := t.erase r
  have huH : coreH u < 2 := by
    by_contra! hn
    have hcard : u.card < Nat.find hcross := by
      dsimp [u]
      rw [card_erase_of_mem hrt, htcard]
      have hpos := card_pos.mpr htne
      omega
    exact Nat.find_min hcross hcard
      ⟨u, (erase_subset _ _).trans hts, rfl, hn⟩
  have hrP := (hs r (hts hrt)).1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrP.pos
  have hde : 0 < 2 - coreH u := by linarith
  have huins : insert r u = t := insert_erase hrt
  have hrec : 2 ≤ coreH u * (1 + 1 / (r : ℝ)) := by
    rw [← coreH_insert u (by simp [u]), huins]
    exact htH
  have hralpha : (r : ℝ) ≤ coreAlpha u := by
    apply (le_div_iff₀ hde).mpr
    have hrec' : 2 - coreH u ≤ coreH u / r := by
      rw [mul_add, mul_one] at hrec
      rw [← div_eq_mul_one_div] at hrec
      linarith
    have hmul := (le_div_iff₀ hr0).mp hrec'
    nlinarith
  have hBr : (B : ℝ) < r := by exact_mod_cast (hs r (hts hrt)).2
  refine ⟨u, ?_, huH, hBr.trans_le hralpha, ?_⟩
  · intro p hp
    exact hs p (hts (mem_of_mem_erase hp))
  · intro p hp
    have hpt := mem_of_mem_erase hp
    have hpr : p ≤ r := by
      rw [← hrmax]
      exact Finset.le_sup (f := id) hpt
    have hprR : (p : ℝ) ≤ r := by exact_mod_cast hpr
    have halpha : 0 < coreAlpha u := hr0.trans_le hralpha
    linarith

private def coreLog (s : Finset ℕ) : ℝ := ∑ p ∈ s, log (p : ℝ)

private structure CoreState (B : ℕ) (Y : ℝ) where
  support : Finset ℕ
  prime_data : ∀ p ∈ support, p.Prime ∧ B < p
  deficient : coreH support < 2
  large : max (B : ℝ) (max 2 Y) ≤ coreAlpha support
  largest : ∀ p ∈ support, (p : ℝ) < 2 * coreAlpha support

private lemma core_extend {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    ∃ u : CoreState B Y,
      (3 / 2 : ℝ) * coreAlpha s.support ≤ coreAlpha u.support ∧
      coreAlpha u.support ≤ 3 * coreAlpha s.support ∧
      coreLog u.support ≤ coreLog s.support + log (3 * coreAlpha s.support) := by
  have ha2 : 2 ≤ coreAlpha s.support :=
    (le_max_left 2 Y).trans ((le_max_right _ _).trans s.large)
  have ha0 : 0 < coreAlpha s.support := by linarith
  have haY : Y ≤ coreAlpha s.support :=
    (le_max_right 2 Y).trans ((le_max_right _ _).trans s.large)
  obtain ⟨p, hp, hplo, hphi⟩ := hY _ haY
  have hpn : p ∉ s.support := by
    intro hps
    exact (s.largest p hps).not_gt hplo
  have hratio := core_step_ratio (coreH_pos s.support) s.deficient
    (by linarith : coreAlpha s.support < (p : ℝ))
  have hnH : coreH (insert p s.support) < 2 := by
    rw [coreH_insert _ hpn]
    exact hratio.1
  have hnA : coreAlpha (insert p s.support) =
      coreAlpha s.support * (p + 1) / (p - coreAlpha s.support) := by
    unfold coreAlpha
    rw [coreH_insert _ hpn]
    exact hratio.2
  obtain ⟨hlo, hhi, hpbound⟩ := core_step_numeric ha2 hplo hphi
  rw [← hnA] at hlo hhi hpbound
  have hainc : coreAlpha s.support ≤ coreAlpha (insert p s.support) := by linarith
  let u : CoreState B Y :=
    { support := insert p s.support
      prime_data := by
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · refine ⟨hp, ?_⟩
          have hBa : (B : ℝ) ≤ coreAlpha s.support :=
            (le_max_left _ _).trans s.large
          have : (B : ℝ) < q := by linarith
          exact_mod_cast this
        · exact s.prime_data q hq
      deficient := hnH
      large := s.large.trans hainc
      largest := by
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact hpbound
        · exact (s.largest q hq).trans_le (by linarith) }
  refine ⟨u, hlo, hhi, ?_⟩
  change coreLog (insert p s.support) ≤ _
  simp only [coreLog, sum_insert hpn]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  linarith [log_le_log hp0 hphi]

private def coreNext {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) : CoreState B Y := (core_extend hY s).choose

private lemma coreNext_spec {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    (3 / 2 : ℝ) * coreAlpha s.support ≤ coreAlpha (coreNext hY s).support ∧
      coreAlpha (coreNext hY s).support ≤ 3 * coreAlpha s.support ∧
      coreLog (coreNext hY s).support ≤
        coreLog s.support + log (3 * coreAlpha s.support) :=
  (core_extend hY s).choose_spec

private def coreIter {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) : ℕ → CoreState B Y
  | 0 => s
  | j + 1 => coreNext hY (coreIter hY s j)

private lemma coreIter_bounds {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) (j : ℕ) :
    coreAlpha s.support * (3 / 2 : ℝ) ^ j ≤
        coreAlpha (coreIter hY s j).support ∧
      coreAlpha (coreIter hY s j).support ≤ coreAlpha s.support * 3 ^ j ∧
      coreLog (coreIter hY s j).support ≤ coreLog s.support +
        (j : ℝ) * (log (3 * coreAlpha s.support) + j * log 3) := by
  let a (i : ℕ) := coreAlpha (coreIter hY s i).support
  let L (i : ℕ) := coreLog (coreIter hY s i).support
  let A := log (3 * coreAlpha s.support)
  let Q (i : ℕ) := coreLog s.support + (i : ℝ) * (A + i * log 3)
  have hlo : coreAlpha s.support * (3 / 2 : ℝ) ^ j ≤ a j := by
    simpa only [a, coreIter, mul_comm] using
      (geom_le (u := a) (by norm_num : (0 : ℝ) ≤ 3 / 2) j
        (fun i _ => (coreNext_spec hY (coreIter hY s i)).1))
  have hhi (i : ℕ) : a i ≤ coreAlpha s.support * 3 ^ i := by
    simpa only [a, coreIter, mul_comm] using
      (le_geom (u := a) (by norm_num : (0 : ℝ) ≤ 3) i
        (fun k _ => (coreNext_spec hY (coreIter hY s k)).2.1))
  refine ⟨hlo, hhi j, ?_⟩
  have hstep (i : ℕ) : L (i + 1) - Q (i + 1) ≤ L i - Q i := by
    have ha2 : 2 ≤ a i :=
      (le_max_left 2 Y).trans ((le_max_right _ _).trans (coreIter hY s i).large)
    have ha0 : 0 < coreAlpha s.support :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
        ((le_max_left 2 Y).trans ((le_max_right _ _).trans s.large))
    have hlogbound : log (3 * a i) ≤ A + (i : ℝ) * log 3 := by
      have hmul : 3 * a i ≤ (3 * coreAlpha s.support) * 3 ^ i := by
        nlinarith [hhi i]
      have hmono := log_le_log (by linarith : 0 < 3 * a i) hmul
      have heq : log ((3 * coreAlpha s.support) * 3 ^ i) =
          A + (i : ℝ) * log 3 := by
        rw [log_mul (by positivity) (by positivity), log_pow]
      rw [heq] at hmono
      exact hmono
    have hlog := (coreNext_spec hY (coreIter hY s i)).2.2
    change L (i + 1) ≤ L i + log (3 * a i) at hlog
    dsimp only [Q]
    push_cast
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
    nlinarith [mul_nonneg hi h3.le]
  have hbound : L j - Q j ≤ 0 := by
    have h := monotone_id.seq_le_seq j (x := fun i => L i - Q i)
      (y := fun _ => (0 : ℝ)) (by simp [L, Q, coreIter])
      (fun i _ => hstep i) (fun _ _ => le_rfl)
    exact h
  change L j ≤ Q j
  linarith

private lemma coreLog_nonneg {B : ℕ} {Y : ℝ} (s : CoreState B Y) :
    0 ≤ coreLog s.support := by
  apply sum_nonneg
  intro p hp
  exact log_natCast_nonneg p

private lemma coreIter_log_bound {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ,
      coreLog (coreIter hY s j).support ≤ K * ((j : ℝ) + 1) ^ 2 := by
  let A := log (3 * coreAlpha s.support)
  let L := coreLog s.support
  have ha2 : 2 ≤ coreAlpha s.support :=
    (le_max_left 2 Y).trans ((le_max_right _ _).trans s.large)
  have hA : 0 ≤ A := log_nonneg (by
    change 1 ≤ 3 * coreAlpha s.support
    linarith)
  have hL : 0 ≤ L := coreLog_nonneg s
  have h3 : 0 ≤ log (3 : ℝ) := (log_pos (by norm_num)).le
  refine ⟨L + A + log 3 + 1, by positivity, fun j => ?_⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hj2 : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hj3 : (j : ℝ) ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have h := (coreIter_bounds hY s j).2.2
  change _ ≤ L + j * (A + j * log 3) at h
  nlinarith [mul_le_mul_of_nonneg_right hj1 hL,
    mul_le_mul_of_nonneg_right hj2 hA, mul_le_mul_of_nonneg_right hj3 h3,
    sq_nonneg ((j : ℝ) + 1)]

private lemma core_stop {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∃ u : CoreState B Y,
        exp t ≤ coreAlpha u.support ∧ coreAlpha u.support ≤ 3 * exp t ∧
        coreLog u.support ≤ K * t ^ 2 := by
  obtain ⟨K, hK, hcost⟩ := coreIter_log_bound hY s
  have hb : 0 < log (3 / 2 : ℝ) := log_pos (by norm_num)
  let D : ℝ := 1 / log (3 / 2 : ℝ) + 2
  have hD : 0 < D := by dsimp [D]; positivity
  have ha2 : 2 ≤ coreAlpha s.support :=
    (le_max_left 2 Y).trans ((le_max_right _ _).trans s.large)
  have ha0 : 0 < coreAlpha s.support := by linarith
  refine ⟨K * D ^ 2, by positivity, max 1 (log (coreAlpha s.support)), ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith
  let J : ℕ := ⌈t / log (3 / 2 : ℝ)⌉₊
  have hJ : exp t ≤ coreAlpha (coreIter hY s J).support := by
    have hpow : exp t ≤ (3 / 2 : ℝ) ^ J := by
      apply (le_log_iff_exp_le (by positivity)).mp
      rw [log_pow]
      exact (div_le_iff₀ hb).mp (Nat.le_ceil (t / log (3 / 2 : ℝ)))
    have hpow0 : 0 ≤ (3 / 2 : ℝ) ^ J := by positivity
    have hmul : (3 / 2 : ℝ) ^ J ≤
        coreAlpha s.support * (3 / 2 : ℝ) ^ J := by nlinarith
    exact hpow.trans (hmul.trans (coreIter_bounds hY s J).1)
  have hex : ∃ j : ℕ, exp t ≤ coreAlpha (coreIter hY s j).support := ⟨J, hJ⟩
  let j := Nat.find hex
  have hj : exp t ≤ coreAlpha (coreIter hY s j).support := Nat.find_spec hex
  have hjJ : j ≤ J := Nat.find_min' hex hJ
  have hu : coreAlpha (coreIter hY s j).support ≤ 3 * exp t := by
    cases hj0 : j with
    | zero =>
      have hstart : coreAlpha s.support ≤ exp t :=
        (log_le_iff_le_exp ha0).mp ((le_max_right _ _).trans ht)
      simpa only [hj0, coreIter] using (by linarith [exp_pos t] :
        coreAlpha s.support ≤ 3 * exp t)
    | succ i =>
      have hprev : coreAlpha (coreIter hY s i).support < exp t := by
        apply lt_of_not_ge
        apply Nat.find_min hex
        change i < j
        omega
      have hstep := (coreNext_spec hY (coreIter hY s i)).2.1
      change coreAlpha (coreIter hY s (i + 1)).support ≤ _
      change coreAlpha (coreNext hY (coreIter hY s i)).support ≤ _
      linarith
  have hjreal : (j : ℝ) + 1 ≤ D * t := by
    have hcast : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hceil := Nat.ceil_lt_add_one (div_nonneg ht0 hb.le)
    change (J : ℝ) < t / log (3 / 2 : ℝ) + 1 at hceil
    dsimp [D]
    rw [div_eq_mul_inv] at hceil ⊢
    nlinarith
  refine ⟨coreIter hY s j, hj, hu, ?_⟩
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ (D * t) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hD.le ht0)).mpr hjreal
  calc
    _ ≤ K * ((j : ℝ) + 1) ^ 2 := hcost j
    _ ≤ K * (D * t) ^ 2 := mul_le_mul_of_nonneg_left hsq hK.le
    _ = K * D ^ 2 * t ^ 2 := by ring

private lemma core_exists (B : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B < p) ∧ coreH s < 2 ∧
        exp t ≤ coreAlpha s ∧ coreAlpha s ≤ 3 * exp t ∧
        (∀ p ∈ s, (p : ℝ) < 2 * coreAlpha s) ∧ coreLog s ≤ K * t ^ 2 := by
  obtain ⟨Y, hY⟩ := core_step_prime
  let B' := max B (max 2 ⌈Y⌉₊)
  have hB'2 : 2 ≤ B' := (le_max_left _ _).trans (le_max_right _ _)
  have hBB' : B ≤ B' := le_max_left _ _
  have hYB' : Y ≤ (B' : ℝ) :=
    (Nat.le_ceil Y).trans (by exact_mod_cast
      ((le_max_right 2 ⌈Y⌉₊).trans (le_max_right B (max 2 ⌈Y⌉₊))))
  obtain ⟨s, hs, hsH, hsA, hsP⟩ := core_seed B'
  have hBB'R : (B : ℝ) ≤ B' := by exact_mod_cast hBB'
  have hB'2R : (2 : ℝ) ≤ B' := by exact_mod_cast hB'2
  let seed : CoreState B Y :=
    { support := s
      prime_data := fun p hp => ⟨(hs p hp).1, hBB'.trans_lt (hs p hp).2⟩
      deficient := hsH
      large := max_le (hBB'R.trans hsA.le)
        (max_le (hB'2R.trans hsA.le) (hYB'.trans hsA.le))
      largest := hsP }
  obtain ⟨K, hK, T, hT⟩ := core_stop hY seed
  refine ⟨K, hK, T, fun t ht => ?_⟩
  obtain ⟨u, hu, hu', hlog⟩ := hT t ht
  exact ⟨u.support, u.prime_data, u.deficient, hu, hu', u.largest, hlog⟩

/-- Rough deficient cores attain every large exponential threshold with quadratic log cost. -/
theorem rough_deficient_core (B : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∃ s : Finset ℕ,
        let h := ∏ p ∈ s, (1 + 1 / (p : ℝ))
        let a := h / (2 - h)
        (∀ p ∈ s, p.Prime ∧ B < p) ∧ h < 2 ∧
          exp t ≤ a ∧ a ≤ 3 * exp t ∧
          (∀ p ∈ s, (p : ℝ) < 2 * a) ∧
          (∑ p ∈ s, log (p : ℝ)) ≤ K * t ^ 2 := by
  simpa only [coreAlpha, coreH, coreLog] using core_exists B

end D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
