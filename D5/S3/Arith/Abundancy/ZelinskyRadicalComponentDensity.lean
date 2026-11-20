/- GID: D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity
   mirror-E: none(waiver:symbolic-asymptotic-theorem)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Radical component inequalities have density one minus log two. -/

import D5.S1.Deficit.AlmostAdditivity
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Weil.Mertens.Third
import D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality
import D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity

/-! Prime-factor critical sets and radical component asymptotics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity

open D5.S1.Deficit.AlmostAdditivity (primeRadical)
open D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality
  (naturalCountingRatio primeNaturals primeNaturals_countingRatio sparse_prime_support_diverges)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open StrongPseudoperfectEulerDensity (largeSquares)
attribute [local instance] Classical.propDecidable

/-- Integers whose prime-power components are strictly below the radical threshold. -/
def radicalComponentSet (lam : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ ∀ p ∈ n.primeFactors,
    (p : ℝ) ^ (n.factorization p + 1) < lam * primeRadical n}

/-- The inclusive positive initial-segment count. -/
def count (S : Set ℕ) (X : ℕ) : ℕ := ((Icc 1 X).filter (fun n => n ∈ S)).card

/-- The counting function of the radical component set. -/
def radicalComponentCount (lam : ℝ) (X : ℕ) : ℕ := count (radicalComponentSet lam) X


private lemma largestPrime_mem {n : ℕ} (hn : 2 ≤ n) :
    largestPrime n ∈ n.primeFactors := by
  obtain ⟨p, hp, hP⟩ := n.primeFactors.exists_mem_eq_sup
    (Nat.nonempty_primeFactors.mpr (by omega)) id
  simpa only [largestPrime, hP, id_eq] using hp

private lemma largestPrime_mul {p m : ℕ} (hp : p.Prime)
    (hm : 1 ≤ m) (hmp : m ≤ p) : largestPrime (p * m) = p := by
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqdvd := Nat.dvd_of_mem_primeFactors hq
    rcases hqp.dvd_mul.mp hqdvd with h | h
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hqp hp).mp h)
    · exact (Nat.le_of_dvd (by omega : 0 < m) h).trans hmp
  · exact Finset.le_sup (f := id)
      (hp.mem_primeFactors (dvd_mul_right p m)
        (mul_ne_zero hp.ne_zero (by omega : m ≠ 0)))

private def criticalPairs (X : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Nat.primesLE X).sigma fun p => Icc 1 (min p (X / p))

private def criticalNumbers (X : ℕ) : Finset ℕ :=
  (Icc 2 X).filter fun n => n ≤ largestPrime n ^ 2

private lemma criticalPairs_mem {X p m : ℕ} :
    (⟨p, m⟩ : Σ _ : ℕ, ℕ) ∈ criticalPairs X ↔
      p.Prime ∧ 1 ≤ m ∧ m ≤ p ∧ p * m ≤ X := by
  simp only [criticalPairs, mem_sigma, Nat.mem_primesLE, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨⟨hpX, hp⟩, hm, hmp, hmX⟩
    refine ⟨hp, hm, hmp, ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hmX
  · rintro ⟨hp, hm, hmp, hX⟩
    refine ⟨⟨?_, hp⟩, hm, hmp, ?_⟩
    · calc p = p * 1 := by simp
           _ ≤ p * m := Nat.mul_le_mul_left p hm
           _ ≤ X := hX
    · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [Nat.mul_comm] using hX)

private lemma critical_count (X : ℕ) :
    (criticalNumbers X).card = ∑ p ∈ Nat.primesLE X, min p (X / p) := by
  have hcard : (criticalPairs X).card = (criticalNumbers X).card := by
    apply Finset.card_bij (fun a _ => a.1 * a.2)
    · intro a ha
      obtain ⟨hp, hm, hmp, hX⟩ := criticalPairs_mem.mp ha
      have hP := largestPrime_mul hp hm hmp
      simp only [criticalNumbers, mem_filter, mem_Icc]
      refine ⟨⟨?_, hX⟩, ?_⟩
      · have := hp.two_le
        nlinarith
      · rw [hP]
        nlinarith
    · intro a ha b hb hab
      obtain ⟨hp, hm, hmp, _⟩ := criticalPairs_mem.mp ha
      obtain ⟨hq, hn, hnq, _⟩ := criticalPairs_mem.mp hb
      have hpq : a.1 = b.1 := by
        calc a.1 = largestPrime (a.1 * a.2) := (largestPrime_mul hp hm hmp).symm
             _ = largestPrime (b.1 * b.2) := congrArg largestPrime hab
             _ = b.1 := largestPrime_mul hq hn hnq
      have hmn : a.2 = b.2 := by
        rw [hpq] at hab
        exact Nat.eq_of_mul_eq_mul_left hq.pos hab
      exact Sigma.ext hpq (heq_of_eq hmn)
    · intro n hn
      simp only [criticalNumbers, mem_filter, mem_Icc] at hn
      have hPmem := largestPrime_mem hn.1.1
      have hp := Nat.prime_of_mem_primeFactors hPmem
      have hpdvd := Nat.dvd_of_mem_primeFactors hPmem
      have he : largestPrime n * (n / largestPrime n) = n := Nat.mul_div_cancel' hpdvd
      refine ⟨⟨largestPrime n, n / largestPrime n⟩, ?_, he⟩
      apply criticalPairs_mem.mpr
      refine ⟨hp, ?_, ?_, ?_⟩
      · have := Nat.le_of_dvd (by omega : 0 < n) hpdvd
        exact Nat.div_pos this hp.pos
      · nlinarith [hn.2]
      · simpa only [he] using hn.1.2
  rw [← hcard, criticalPairs, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  simp

private lemma critical_count_split (X : ℕ) :
    (criticalNumbers X).card = (∑ p ∈ Nat.primesLE X.sqrt, p) +
      ∑ p ∈ Nat.primesLE X with X.sqrt < p, X / p := by
  rw [critical_count]
  have hsmall : (Nat.primesLE X).filter (fun p => p ≤ X.sqrt) =
      Nat.primesLE X.sqrt := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE]
    have hs := Nat.sqrt_le_self X
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨h.1.trans hs, h.2⟩, h.1⟩
  rw [← Finset.sum_filter_add_sum_filter_not
    (Nat.primesLE X) (fun p => p ≤ X.sqrt) (fun p => min p (X / p)), hsmall]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    exact min_eq_left ((Nat.le_div_iff_mul_le
      (Nat.prime_of_mem_primesLE hp).pos).mpr
        (Nat.le_sqrt.mp (Nat.le_of_mem_primesLE hp)))
  · simp only [not_le]
    apply Finset.sum_congr rfl
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesLE hmem.1
    apply min_eq_right
    have h := (Nat.sqrt_lt.mp hmem.2)
    have hdiv := Nat.div_lt_iff_lt_mul hprime.pos |>.mpr h
    omega

private lemma small_prime_sum_le (Y : ℕ) :
    ∑ p ∈ Nat.primesLE Y, p ≤ Y * Nat.primeCounting Y := by
  calc
    _ ≤ ∑ _p ∈ Nat.primesLE Y, Y :=
      Finset.sum_le_sum fun p hp => Nat.le_of_mem_primesLE hp
    _ = Y * Nat.primeCounting Y := by
      simp [Nat.mul_comm]


private lemma prime_count_ratio :
    Tendsto (fun X : ℕ => (Nat.primeCounting X : ℝ) / X) atTop (𝓝 0) := by
  have heq : (fun X : ℕ => (Nat.primeCounting X : ℝ) / X) =
      naturalCountingRatio primeNaturals := by
    funext X
    exact (primeNaturals_countingRatio X).symm
  rw [heq]
  exact sparse_prime_support_diverges.1

private lemma prime_reciprocal_window :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) -
      ∑ p ∈ Ioc 0 ⌊sqrt x⌋₊ with p.Prime, (1 : ℝ) / p)
      atTop (𝓝 (log 2)) := by
  have he := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h := (he.sub (he.comp tendsto_sqrt_atTop)).add_const (log 2)
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 < log (sqrt x) := by
    rw [log_sqrt hx0.le]
    positivity
  have hlog : log (log (sqrt x)) = log (log x) - log 2 := by
    rw [log_sqrt hx0.le, log_div hl.ne' (by norm_num)]
  dsimp [Mertens.E₂p]
  rw [hlog]
  ring

private def primeWindow (X : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p => X.sqrt < p

private lemma prime_window_limit :
    Tendsto (fun X : ℕ => ∑ p ∈ primeWindow X, (1 : ℝ) / p)
      atTop (𝓝 (log 2)) := by
  have h := prime_reciprocal_window.comp tendsto_natCast_atTop_atTop
  have heq (X : ℕ) :
      (∑ p ∈ Ioc 0 ⌊(X : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p) -
        (∑ p ∈ Ioc 0 ⌊sqrt (X : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p) =
        ∑ p ∈ primeWindow X, (1 : ℝ) / p := by
    have hset (Y : ℕ) : (Ioc 0 Y).filter Nat.Prime = Nat.primesLE Y := by
      ext p
      simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_, hpY⟩, hp⟩
        exact ⟨hpY, hp⟩
      · rintro ⟨hpY, hp⟩
        exact ⟨⟨hp.pos, hpY⟩, hp⟩
    simp only [Nat.floor_natCast, nat_floor_real_sqrt_eq_nat_sqrt, hset]
    have hsub : Nat.primesLE X.sqrt ⊆ Nat.primesLE X := by
      intro p hp
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_of_mem_primesLE hp).trans (Nat.sqrt_le_self X),
          Nat.prime_of_mem_primesLE hp⟩
    rw [← sum_sdiff hsub]
    have hw : Nat.primesLE X \ Nat.primesLE X.sqrt = primeWindow X := by
      apply Finset.ext
      intro p
      rw [Finset.mem_sdiff, primeWindow, Finset.mem_filter]
      simp only [Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hpX, hp⟩, hn⟩
        exact ⟨⟨hpX, hp⟩, lt_of_not_ge (fun hps => hn ⟨hps, hp⟩)⟩
      · rintro ⟨⟨hpX, hp⟩, hs⟩
        exact ⟨⟨hpX, hp⟩, fun h => (not_lt_of_ge h.1) hs⟩
    rw [hw]
    ring
  exact h.congr (fun X => heq X)

private lemma prime_floor_sum_bounds (X : ℕ) :
    (X : ℝ) * (∑ p ∈ primeWindow X, (1 : ℝ) / p) - Nat.primeCounting X ≤
        (∑ p ∈ primeWindow X, (X / p : ℕ) : ℕ) ∧
      ((∑ p ∈ primeWindow X, (X / p : ℕ) : ℕ) : ℝ) ≤
        X * ∑ p ∈ primeWindow X, (1 : ℝ) / p := by
  have hlower (p : ℕ) (hp : p ∈ primeWindow X) :
      (X : ℝ) / p - 1 ≤ (X / p : ℕ) := by
    have hpp := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
    have hN : X < (X / p + 1) * p :=
      (Nat.div_lt_iff_lt_mul hpp.pos).mp (Nat.lt_succ_self _)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hR : (X : ℝ) < ((X / p : ℕ) + 1 : ℝ) * p := by exact_mod_cast hN
    have hd := (div_lt_iff₀ hpR).mpr hR
    linarith
  have hcard : (primeWindow X).card ≤ Nat.primeCounting X := by
    exact (card_filter_le _ _).trans_eq (Nat.primesLE_card_eq_primeCounting X)
  constructor
  · calc
      _ ≤ X * (∑ p ∈ primeWindow X, (1 : ℝ) / p) - (primeWindow X).card := by
        exact sub_le_sub_left (by exact_mod_cast hcard) _
      _ = ∑ p ∈ primeWindow X, ((X : ℝ) / p - 1) := by
        rw [sum_sub_distrib, mul_sum]
        simp only [mul_one_div, sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ primeWindow X, ((X / p : ℕ) : ℝ) := sum_le_sum hlower
      _ = _ := by simp
  · push_cast
    rw [mul_sum]
    exact sum_le_sum fun p _ => by simpa only [mul_one_div] using
      (Nat.cast_div_le : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / p)

private lemma sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with X hX
  exact Nat.le_sqrt.mpr hX

private lemma critical_density :
    Tendsto (fun X : ℕ => ((criticalNumbers X).card : ℝ) / X)
      atTop (𝓝 (log 2)) := by
  have hlo := prime_window_limit.sub prime_count_ratio
  have hhi := prime_window_limit.add (prime_count_ratio.comp sqrt_atTop)
  simp only [sub_zero, add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hb := (prime_floor_sum_bounds X).1
    have hcount : ((∑ p ∈ primeWindow X, (X / p : ℕ) : ℕ) : ℝ) ≤
        (criticalNumbers X).card := by
      have hN : (∑ p ∈ primeWindow X, (X / p : ℕ) : ℕ) ≤
          (criticalNumbers X).card := by
        rw [critical_count_split]
        dsimp [primeWindow]
        omega
      exact_mod_cast hN
    apply (le_div_iff₀ hXR).mpr
    calc
      _ = (X : ℝ) * (∑ p ∈ primeWindow X, (1 : ℝ) / p) -
          Nat.primeCounting X := by field_simp <;> ring
      _ ≤ _ := hb.trans hcount
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hsN : 0 < X.sqrt := Nat.sqrt_pos.mpr (by omega)
    have hsR : (0 : ℝ) < X.sqrt := by exact_mod_cast hsN
    have hsquare : (X.sqrt : ℝ) ^ 2 ≤ X := by
      have hN : X.sqrt ^ 2 ≤ X := by nlinarith [Nat.sqrt_le X]
      exact_mod_cast hN
    have hsmall : ((∑ p ∈ Nat.primesLE X.sqrt, p : ℕ) : ℝ) / X ≤
        (Nat.primeCounting X.sqrt : ℝ) / X.sqrt := by
      apply (div_le_div_iff₀ hXR hsR).mpr
      have hb : ((∑ p ∈ Nat.primesLE X.sqrt, p : ℕ) : ℝ) ≤
          X.sqrt * (Nat.primeCounting X.sqrt : ℝ) := by
        exact_mod_cast small_prime_sum_le X.sqrt
      have hm := mul_le_mul_of_nonneg_left hsquare
        (Nat.cast_nonneg (Nat.primeCounting X.sqrt) : (0 : ℝ) ≤ _)
      nlinarith [mul_le_mul_of_nonneg_right hb hsR.le]
    have hfloor := (prime_floor_sum_bounds X).2
    have hf : ((∑ p ∈ primeWindow X, (X / p : ℕ) : ℕ) : ℝ) / X ≤
        ∑ p ∈ primeWindow X, (1 : ℝ) / p := by
      apply (div_le_iff₀ hXR).mpr
      simpa only [mul_comm] using hfloor
    rw [critical_count_split, Nat.cast_add, add_div]
    exact (add_le_add hsmall hf).trans_eq (add_comm _ _)

private def criticalShell (a b : ℝ) (X : ℕ) : Finset ℕ :=
  (Icc 2 X).filter fun n =>
    a * n ≤ (largestPrime n : ℝ) ^ 2 ∧
      (largestPrime n : ℝ) ^ 2 ≤ b * n

private lemma critical_shell_bound (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (X : ℕ) :
    (criticalShell a b X).card ≤
      Nat.primeCounting ⌊Real.sqrt (b * X)⌋₊ *
        ⌊(⌊Real.sqrt (b * X)⌋₊ : ℝ) / a⌋₊ := by
  let Y := ⌊Real.sqrt (b * X)⌋₊
  let Z := ⌊(Y : ℝ) / a⌋₊
  have hbound : (criticalShell a b X).card ≤
      ((Nat.primesLE Y) ×ˢ Icc 1 Z).card := by
    apply Finset.card_le_card_of_injOn
      (fun n => (largestPrime n, n / largestPrime n))
    · intro n hn
      change n ∈ criticalShell a b X at hn
      simp only [criticalShell, mem_filter, mem_Icc] at hn
      have hPmem := largestPrime_mem hn.1.1
      have hp := Nat.prime_of_mem_primeFactors hPmem
      have hpdvd := Nat.dvd_of_mem_primeFactors hPmem
      have hn0 : 0 < n := by omega
      have hpR : (0 : ℝ) < largestPrime n := by exact_mod_cast hp.pos
      have hm : largestPrime n * (n / largestPrime n) = n :=
        Nat.mul_div_cancel' hpdvd
      have hmR : (largestPrime n : ℝ) * (n / largestPrime n : ℕ) = n :=
        by exact_mod_cast hm
      have hnX : (n : ℝ) ≤ X := by exact_mod_cast hn.1.2
      have hpY : largestPrime n ≤ Y := by
        apply Nat.le_floor
        have hsq := Real.sq_sqrt (mul_nonneg hb (Nat.cast_nonneg X))
        have hnonneg := Real.sqrt_nonneg (b * X)
        have hle := mul_le_mul_of_nonneg_left hnX hb
        nlinarith [hn.2.2]
      have hmZ : n / largestPrime n ≤ Z := by
        apply Nat.le_floor
        apply (le_div_iff₀ ha).mpr
        have hpY' : (largestPrime n : ℝ) ≤ Y := by exact_mod_cast hpY
        have hsmall : a * (n / largestPrime n : ℕ) ≤ largestPrime n := by
          apply (mul_le_mul_iff_left₀ hpR).mp
          have hlow := hn.2.1
          rw [← hmR] at hlow
          simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hlow
        nlinarith
      change (largestPrime n, n / largestPrime n) ∈
        (Nat.primesLE Y) ×ˢ Icc 1 Z
      simp only [mem_product, Nat.mem_primesLE, mem_Icc]
      refine ⟨⟨hpY, hp⟩, ?_, hmZ⟩
      exact Nat.div_pos (Nat.le_of_dvd hn0 hpdvd) hp.pos
    · intro n hn m hm he
      have hn' := mem_filter.mp hn
      have hm' := mem_filter.mp hm
      have hndvd := Nat.dvd_of_mem_primeFactors
        (largestPrime_mem (mem_Icc.mp hn'.1).1)
      have hmdvd := Nat.dvd_of_mem_primeFactors
        (largestPrime_mem (mem_Icc.mp hm'.1).1)
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      have hnrec := Nat.mul_div_cancel' hndvd
      have hmrec := Nat.mul_div_cancel' hmdvd
      change largestPrime n = largestPrime m at he1
      change n / largestPrime n = m / largestPrime m at he2
      rw [he2, he1] at hnrec
      exact hnrec.symm.trans hmrec
  simpa only [Finset.card_product, Nat.primesLE_card_eq_primeCounting,
    Nat.card_Icc, Nat.add_sub_cancel] using hbound

private def subcriticalNumbers (c : ℝ) (X : ℕ) : Finset ℕ :=
  (Icc 2 X).filter fun n => (largestPrime n : ℝ) ^ 2 < c * n

private lemma subcritical_difference_cover (c : ℝ) (X : ℕ) :
    (subcriticalNumbers c X \ subcriticalNumbers 1 X) ∪
      (subcriticalNumbers 1 X \ subcriticalNumbers c X) ⊆
        criticalShell (min 1 c) (max 1 c) X := by
  intro n hn
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hn
  simp only [subcriticalNumbers, mem_filter, mem_Icc] at hn
  simp only [criticalShell, mem_filter, mem_Icc]
  have hmin1 := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) c)
    (Nat.cast_nonneg n)
  have hminc := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) c)
    (Nat.cast_nonneg n)
  have hmax1 := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) c)
    (Nat.cast_nonneg n)
  have hmaxc := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) c)
    (Nat.cast_nonneg n)
  rcases hn with ⟨hnc, hn1⟩ | ⟨hn1, hnc⟩
  · refine ⟨hnc.1, ?_, ?_⟩
    · have hnot : ¬ (largestPrime n : ℝ) ^ 2 < (1 : ℝ) * n := by
        exact fun h => hn1 ⟨hnc.1, h⟩
      linarith
    · linarith [hnc.2]
  · refine ⟨hn1.1, ?_, ?_⟩
    · have hnot : ¬ (largestPrime n : ℝ) ^ 2 < c * n := by
        exact fun h => hnc ⟨hn1.1, h⟩
      linarith
    · linarith [hn1.2]

private lemma subcritical_one_partition (X : ℕ) :
    (subcriticalNumbers 1 X).card + (criticalNumbers X).card = X - 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Icc 2 X) (fun n => n ≤ largestPrime n ^ 2)
  have hfilter : (Icc 2 X).filter (fun n => ¬ n ≤ largestPrime n ^ 2) =
      subcriticalNumbers 1 X := by
    ext n
    simp only [mem_filter, subcriticalNumbers, mem_Icc, one_mul, not_le]
    norm_cast
  rw [hfilter] at h
  have hcard : (Icc 2 X).card = X - 1 := by
    rw [Nat.card_Icc]
    omega
  rw [hcard] at h
  change (criticalNumbers X).card + (subcriticalNumbers 1 X).card = X - 1 at h
  omega

private lemma subcritical_count_difference_bound (c : ℝ) (hc : 0 < c) (X : ℕ) :
    |((subcriticalNumbers c X).card : ℝ) - (subcriticalNumbers 1 X).card| ≤
      (Nat.primeCounting ⌊Real.sqrt (max 1 c * X)⌋₊ : ℝ) *
        ((⌊Real.sqrt (max 1 c * X)⌋₊ : ℝ) / min 1 c) := by
  let A := subcriticalNumbers c X
  let B := subcriticalNumbers 1 X
  let S := criticalShell (min 1 c) (max 1 c) X
  let Y := ⌊Real.sqrt (max 1 c * X)⌋₊
  have hcover := subcritical_difference_cover c X
  have hAB : A ⊆ B ∪ S := by
    intro n hn
    by_cases hnB : n ∈ B
    · exact mem_union_left S hnB
    · exact mem_union_right B (hcover (mem_union_left _ (mem_sdiff.mpr ⟨hn, hnB⟩)))
  have hBA : B ⊆ A ∪ S := by
    intro n hn
    by_cases hnA : n ∈ A
    · exact mem_union_left S hnA
    · exact mem_union_right A (hcover (mem_union_right _ (mem_sdiff.mpr ⟨hn, hnA⟩)))
  have hcardAB := (card_le_card hAB).trans (card_union_le B S)
  have hcardBA := (card_le_card hBA).trans (card_union_le A S)
  have hdiff : |(A.card : ℝ) - B.card| ≤ S.card := by
    have h1 : (A.card : ℝ) ≤ B.card + S.card := by exact_mod_cast hcardAB
    have h2 : (B.card : ℝ) ≤ A.card + S.card := by exact_mod_cast hcardBA
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have ha : 0 < min (1 : ℝ) c := lt_min (by norm_num) hc
  have hb : 0 ≤ max (1 : ℝ) c := le_trans (by norm_num) (le_max_left _ _)
  have hS := critical_shell_bound (min 1 c) (max 1 c) ha hb X
  have hSR : (S.card : ℝ) ≤
      (Nat.primeCounting Y : ℝ) * ⌊(Y : ℝ) / min 1 c⌋₊ := by exact_mod_cast hS
  apply hdiff.trans (hSR.trans ?_)
  exact mul_le_mul_of_nonneg_left
    (Nat.floor_le (div_nonneg (Nat.cast_nonneg Y) ha.le)) (Nat.cast_nonneg _)


private lemma squarefree_le_radical {a n : ℕ} (ha : Squarefree a)
    (hn : 0 < n) (had : a ∣ n) : a ≤ primeRadical n := by
  have hsub := Nat.primeFactors_mono had hn.ne'
  have hd : a ∣ primeRadical n := by
    rw [← Nat.prod_primeFactors_of_squarefree ha]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  apply Nat.le_of_dvd _ hd
  unfold primeRadical
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

private lemma bounded_square_radical {n a b T : ℕ}
    (hn : 0 < n) (he : b ^ 2 * a = n) (ha : Squarefree a) (hbT : b ≤ T) :
    n ≤ T ^ 2 * primeRadical n := by
  have had : a ∣ n := by
    rw [← he]
    exact dvd_mul_left a (b ^ 2)
  have har : a ≤ primeRadical n := squarefree_le_radical ha hn had
  calc
    n = b ^ 2 * a := he.symm
    _ ≤ T ^ 2 * primeRadical n :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbT 2) har

private lemma repeated_prime_bound {n a b p : ℕ}
    (hn : 0 < n) (he : b ^ 2 * a = n) (ha : Squarefree a)
    (hp : p.Prime) (hk : 2 ≤ n.factorization p) :
    p ^ (n.factorization p + 1) ≤ b ^ 4 := by
  have hb : b ≠ 0 := by intro h; simp [h] at he; omega
  have hfac : n.factorization p = 2 * b.factorization p + a.factorization p := by
    rw [← he, Nat.factorization_mul (pow_ne_zero _ hb) ha.ne_zero,
      Finsupp.add_apply, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
  have has := ha.natFactorization_le_one p
  have hexp : n.factorization p + 1 ≤ b.factorization p * 4 := by omega
  have hpow : p ^ b.factorization p ≤ b :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hb)
      ((hp.pow_dvd_iff_le_factorization hb).mpr le_rfl)
  calc
    p ^ (n.factorization p + 1) ≤ p ^ (b.factorization p * 4) :=
      Nat.pow_le_pow_right hp.pos hexp
    _ = (p ^ b.factorization p) ^ 4 := pow_mul _ _ _
    _ ≤ b ^ 4 := Nat.pow_le_pow_left hpow 4

private lemma square_decomposition_small {n X T : ℕ}
    (hn : 0 < n) (hnX : n ≤ X) (hnot : n ∉ largeSquares X T) :
    ∃ a b : ℕ, Squarefree a ∧ 0 < b ∧ b ≤ T ∧ b ^ 2 * a = n := by
  obtain ⟨b, a, he, ha⟩ := exists_sq_mul_squarefree n
  have hb : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hb
    simp [hb] at he
    omega
  refine ⟨a, b, ha, hb, ?_, he⟩
  by_contra! hbT
  apply hnot
  apply mem_biUnion.mpr
  have hapos : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hbX : b ≤ X := by
    have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) b
    nlinarith
  refine ⟨b, mem_Icc.mpr ⟨by omega, hbX⟩, mem_image.mpr ?_⟩
  refine ⟨a, mem_Icc.mpr ⟨hapos, ?_⟩, ?_⟩
  · apply (Nat.le_div_iff_mul_le (pow_pos hb 2)).mpr
    nlinarith
  · simpa [mul_comm] using he

private lemma radical_sandwich {lam : ℝ} {n X T : ℕ}
    (hlam : 0 < lam) (hn : 2 ≤ n) (hnX : n ≤ X)
    (hnot : n ∉ largeSquares X T)
    (hlarge : (T : ℝ) ^ 6 < lam * n)
    (hcritical : (largestPrime n : ℝ) ^ 2 <
      (lam / (T : ℝ) ^ 2) * n) :
    ∀ p ∈ n.primeFactors,
      (p : ℝ) ^ (n.factorization p + 1) < lam * primeRadical n := by
  obtain ⟨a, b, ha, hb, hbT, he⟩ := square_decomposition_small (by omega) hnX hnot
  have hT : 0 < T := lt_of_lt_of_le hb hbT
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hnrad : (n : ℝ) ≤ (T : ℝ) ^ 2 * primeRadical n := by
    exact_mod_cast bounded_square_radical (by omega : 0 < n) he ha hbT
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hk : 1 ≤ n.factorization p :=
    hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
  by_cases hk1 : n.factorization p = 1
  · have hpmax : p ≤ largestPrime n := Finset.le_sup (f := id) hp
    have hpr : (p : ℝ) ≤ largestPrime n := by exact_mod_cast hpmax
    have hsquare : (p : ℝ) ^ 2 ≤ (largestPrime n : ℝ) ^ 2 := by
      gcongr
    rw [hk1]
    norm_num only [Nat.reduceAdd]
    apply hsquare.trans_lt (hcritical.trans_le ?_)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hTR)).mp
    calc
      lam / (T : ℝ) ^ 2 * n * (T : ℝ) ^ 2 = lam * n := by field_simp
      _ ≤ lam * ((T : ℝ) ^ 2 * primeRadical n) :=
        mul_le_mul_of_nonneg_left hnrad hlam.le
      _ = lam * primeRadical n * (T : ℝ) ^ 2 := by ring
  · have hpbound : (p : ℝ) ^ (n.factorization p + 1) ≤ (T : ℝ) ^ 4 := by
      have hh := repeated_prime_bound (by omega : 0 < n) he ha hpp (by omega)
      exact_mod_cast hh.trans (Nat.pow_le_pow_left hbT 4)
    apply hpbound.trans_lt
    have hmul := mul_le_mul_of_nonneg_left hnrad hlam.le
    have hlt : (T : ℝ) ^ 6 < (T : ℝ) ^ 2 * (lam * primeRadical n) := by
      nlinarith
    have hpow : (T : ℝ) ^ 6 = (T : ℝ) ^ 2 * (T : ℝ) ^ 4 := by ring
    rw [hpow] at hlt
    exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos hTR)).mp hlt

private lemma scaled_sqrt_prime_error (b : ℝ) (hb : 0 < b)
    (hpi : Tendsto (fun X : ℕ => (Nat.primeCounting X : ℝ) / X)
      atTop (𝓝 0)) :
    Tendsto (fun X : ℕ =>
      (⌊sqrt (b * X)⌋₊ : ℝ) * Nat.primeCounting ⌊sqrt (b * X)⌋₊ / X)
      atTop (𝓝 0) := by
  let Y : ℕ → ℕ := fun X => ⌊sqrt (b * X)⌋₊
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hY : Tendsto Y atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_sqrt_atTop.comp (hnat.const_mul_atTop hb))
  have hlim : Tendsto (fun X => b * ((Nat.primeCounting (Y X) : ℝ) / Y X))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (hpi.comp hY).const_mul b
  apply squeeze_zero' (Eventually.of_forall (fun X => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ), hY.eventually_ge_atTop 1] with X hX hy
  have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hyR : (0 : ℝ) < Y X := by exact_mod_cast (by omega : 0 < Y X)
  have hfloor : (Y X : ℝ) ≤ sqrt (b * X) := Nat.floor_le (sqrt_nonneg _)
  have hysq : (Y X : ℝ) ^ 2 ≤ b * X := by
    calc
      (Y X : ℝ) ^ 2 ≤ (sqrt (b * X)) ^ 2 := by gcongr
      _ = b * X := sq_sqrt (mul_nonneg hb.le hx.le)
  change (Y X : ℝ) * Nat.primeCounting (Y X) / X ≤
    b * ((Nat.primeCounting (Y X) : ℝ) / Y X)
  apply (div_le_iff₀ hx).mpr
  apply (mul_le_mul_iff_left₀ hyR).mp
  calc
    (Y X : ℝ) * Nat.primeCounting (Y X) * Y X =
        (Y X : ℝ) ^ 2 * Nat.primeCounting (Y X) := by ring
    _ ≤ (b * X) * Nat.primeCounting (Y X) :=
      mul_le_mul_of_nonneg_right hysq (by positivity)
    _ = b * ((Nat.primeCounting (Y X) : ℝ) / Y X) * X * Y X := by
      field_simp
      <;> ring


private lemma subcritical_one_density :
    Tendsto (fun X : ℕ => ((subcriticalNumbers 1 X).card : ℝ) / X)
      atTop (𝓝 (1 - log 2)) := by
  have htotal : Tendsto (fun X : ℕ => ((X - 1 : ℕ) : ℝ) / X)
      atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    rw [Nat.cast_sub hX, Nat.cast_one]
    field_simp
  have h := htotal.sub critical_density
  apply h.congr
  intro X
  have hpart : ((subcriticalNumbers 1 X).card : ℝ) +
      (criticalNumbers X).card = (X - 1 : ℕ) := by
    exact_mod_cast subcritical_one_partition X
  rw [← hpart, add_div]
  ring

private lemma subcritical_density (c : ℝ) (hc : 0 < c) :
    Tendsto (fun X : ℕ => ((subcriticalNumbers c X).card : ℝ) / X)
      atTop (𝓝 (1 - log 2)) := by
  let a := min (1 : ℝ) c
  let b := max (1 : ℝ) c
  let E : ℕ → ℝ := fun X =>
    (Nat.primeCounting ⌊sqrt (b * X)⌋₊ : ℝ) * (⌊sqrt (b * X)⌋₊ : ℝ) / a / X
  have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := (scaled_sqrt_prime_error b hb prime_count_ratio).div_const a
    simp only [zero_div] at h
    convert h using 1
    funext X
    dsimp [E]
    ring
  have hlow := subcritical_one_density.sub hE
  have hhigh := subcritical_one_density.add hE
  simp only [sub_zero, add_zero] at hlow hhigh
  have hbound : ∀ᶠ X : ℕ in atTop,
      |((subcriticalNumbers c X).card : ℝ) / X -
        (subcriticalNumbers 1 X).card / X| ≤ E X := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    rw [← sub_div, abs_div, abs_of_pos hXR]
    have h := div_le_div_of_nonneg_right
      (subcritical_count_difference_bound c hc X) hXR.le
    convert h using 1 <;> dsimp [E, a, b] <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [hbound] with X hX
    have := (abs_le.mp hX).1
    linarith
  · filter_upwards [hbound] with X hX
    have := (abs_le.mp hX).2
    linarith

private lemma radical_count_upper (lam : ℝ) (hlam : 0 < lam) (X : ℕ) :
    radicalComponentCount lam X ≤ (subcriticalNumbers lam X).card := by
  change ((Icc 1 X).filter (fun n => n ∈ radicalComponentSet lam)).card ≤ _
  apply card_le_card
  intro n hn
  obtain ⟨hnI, hn2, hnB⟩ := mem_filter.mp hn
  have hp := largestPrime_mem hn2
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he : 1 ≤ n.factorization (largestPrime n) :=
    hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
  have hpower : (largestPrime n : ℝ) ^ 2 ≤
      (largestPrime n : ℝ) ^ (n.factorization (largestPrime n) + 1) := by
    apply pow_le_pow_right₀ (by exact_mod_cast hpp.one_le)
    omega
  have hrad : primeRadical n ≤ n :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  have hradR : (primeRadical n : ℝ) ≤ n := by exact_mod_cast hrad
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨hn2, (mem_Icc.mp hnI).2⟩, ?_⟩
  exact (hpower.trans_lt (hnB _ hp)).trans_le
    (mul_le_mul_of_nonneg_left hradR hlam.le)

private lemma radical_count_lower (lam : ℝ) (hlam : 0 < lam) (T : ℕ)
    (hT : 0 < T) : ∃ N : ℕ, ∀ X : ℕ,
      ((subcriticalNumbers (lam / (T : ℝ) ^ 2) X).card : ℝ) ≤
        radicalComponentCount lam X + 2 * (X : ℝ) / (T + 1) + N := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) ^ 6 / lam)
  refine ⟨N, fun X => ?_⟩
  have hcover : subcriticalNumbers (lam / (T : ℝ) ^ 2) X ⊆
      ((Icc 1 X).filter (fun n => n ∈ radicalComponentSet lam)) ∪
        StrongPseudoperfectEulerDensity.largeSquares X T ∪ Icc 1 N := by
    intro n hn
    have hn' := mem_filter.mp hn
    have hnI := mem_Icc.mp hn'.1
    by_cases hsmall : n ≤ N
    · exact mem_union_right _ (mem_Icc.mpr ⟨by omega, hsmall⟩)
    apply mem_union_left
    by_cases hsq : n ∈ StrongPseudoperfectEulerDensity.largeSquares X T
    · exact mem_union_right _ hsq
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, hnI.2⟩, hnI.1, ?_⟩
    have hlarge : (T : ℝ) ^ 6 < lam * n := by
      have hnR : (N : ℝ) < n := by exact_mod_cast (lt_of_not_ge hsmall)
      have h := (div_lt_iff₀ hlam).mp (hN.trans hnR)
      simpa only [mul_comm] using h
    exact radical_sandwich hlam hnI.1 hnI.2 hsq hlarge hn'.2
  have hc := (card_le_card hcover).trans
    ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hcR : ((subcriticalNumbers (lam / (T : ℝ) ^ 2) X).card : ℝ) ≤
      radicalComponentCount lam X +
        (StrongPseudoperfectEulerDensity.largeSquares X T).card + N := by
    have hc' : (subcriticalNumbers (lam / (T : ℝ) ^ 2) X).card ≤
        radicalComponentCount lam X +
          (StrongPseudoperfectEulerDensity.largeSquares X T).card + N := by
      simpa only [radicalComponentCount, count, Nat.card_Icc, Nat.add_sub_cancel] using hc
    exact_mod_cast hc'
  have hs := StrongPseudoperfectEulerDensity.largeSquares_card X T
  linarith

/-- Every positive radical threshold has the same natural density. -/
theorem result (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun X : ℕ => (radicalComponentCount lam X : ℝ) / X)
      atTop (𝓝 (1 - log 2)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨T, hT⟩ := exists_nat_gt (max 1 (2 / ((1 - log 2) - l)))
    have hTpos : 0 < T := by
      have h := (le_max_left (1 : ℝ) _).trans_lt hT
      exact_mod_cast (by linarith : (0 : ℝ) < T)
    have hTR : (0 : ℝ) < T := by exact_mod_cast hTpos
    have hgap : 2 / ((T : ℝ) + 1) < (1 - log 2) - l := by
      have hg : 0 < (1 - log 2) - l := by linarith
      have ht := (le_max_right (1 : ℝ) _).trans_lt hT
      have hm := (div_lt_iff₀ hg).mp ht
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < T + 1)).mpr
      nlinarith
    obtain ⟨N, hN⟩ := radical_count_lower lam hlam T hTpos
    have hc : 0 < lam / (T : ℝ) ^ 2 := div_pos hlam (sq_pos_of_pos hTR)
    have hlim := ((subcritical_density _ hc).sub
      (tendsto_natCast_atTop_atTop.const_div_atTop (N : ℝ))).sub_const
        (2 / ((T : ℝ) + 1))
    simp only [sub_zero] at hlim
    have hevent := hlim.eventually (eventually_gt_nhds (by linarith :
      l < (1 - log 2) - 2 / ((T : ℝ) + 1)))
    filter_upwards [hevent, eventually_ge_atTop (1 : ℕ)] with X hX hXpos
    have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
    have hb := div_le_div_of_nonneg_right (hN X) hXR.le
    have he : (2 * (X : ℝ) / ((T : ℝ) + 1)) / X = 2 / ((T : ℝ) + 1) := by
      field_simp
    rw [add_div, add_div, he] at hb
    linarith
  · intro u hu
    have he := (subcritical_density lam hlam).eventually (eventually_lt_nhds hu)
    filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with X hX hXpos
    have hXR : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right
      (by exact_mod_cast radical_count_upper lam hlam X) hXR) hX

end D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
