/- GID: D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity
   generality: G
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
attribute [local instance] Classical.propDecidable

/-- Integers whose prime-power components are strictly below the radical threshold. -/
def radicalComponentSet (lam : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ ∀ p ∈ n.primeFactors,
    (p : ℝ) ^ (n.factorization p + 1) < lam * primeRadical n}

/-- The inclusive positive initial-segment count. -/
def count (S : Set ℕ) (X : ℕ) : ℕ := ((Icc 1 X).filter (fun n => n ∈ S)).card

/-- The counting function of the radical component set. -/
def radicalComponentCount (lam : ℝ) (X : ℕ) : ℕ := count (radicalComponentSet lam) X

private def criticalSet (c : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ (largestPrime n : ℝ) ^ 2 < c * n}


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
        exact ⟨⟨hpX, hp⟩, by omega⟩
      · rintro ⟨⟨hpX, hp⟩, hs⟩
        exact ⟨⟨hpX, hp⟩, by omega⟩
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

end D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
