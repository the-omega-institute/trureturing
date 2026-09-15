/- GID: D5/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjoining omitted upper-half primes gives the same exact change in both Mobius certificates. -/

import D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Weil.Mertens.CoprimeMobiusCertificateError

noncomputable section
namespace D5.S3.Weil.Mertens.UpperHalfPrimeCertificateExtension

/-- The absolute truncated Mobius kernels summed over positive squarefree coprime indices. -/
def W (Q N : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime Q ∧ Squarefree d),
    |(B Q ((N : ℝ) / d) : ℝ)|

/-- Adjoining any finite set of omitted primes in the upper half of the window changes
both absolute Mobius certificates by the same cardinality and endpoint-kernel expression. -/
theorem certificate_extension (Q N : ℕ) (T : Finset ℕ)
    (hQ : Squarefree Q) (hQ1 : 1 ≤ Q) (hN : 2 ≤ N)
    (hT : ∀ p ∈ T, p.Prime ∧ N < 2 * p ∧ p ≤ N ∧ ¬ p ∣ Q) :
    let R := ∏ p ∈ T, p
    let delta : ℝ := T.card + |(B Q N : ℝ)| - |(B Q N : ℝ) - T.card|
    U Q N - U (Q * R) N = delta ∧ W Q N - W (Q * R) N = delta := by
  classical
  let R := ∏ p ∈ T, p
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hT p hp).1.ne_zero)
  have hQR0 : Q * R ≠ 0 := Nat.mul_ne_zero hQ0 hR0
  have hsmall (a p : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) (hp : p ∈ T)
      (hpa : p ∣ a) : a = p := by
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) hpa
      (haN.trans_lt (hT p hp).2.1)
  have hcop (a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) (hat : a ∉ T) :
      a.Coprime R := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    apply Nat.Coprime.symm
    apply (hT p hp).1.coprime_iff_not_dvd.mpr
    intro hpa
    exact hat ((hsmall a p ha haN hp hpa).symm ▸ hp)
  have hpdvd (p : ℕ) (hp : p ∈ T) : p ∣ Q * R :=
    dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p : ℕ => p) hp) Q
  have hdiv (a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) :
      a ∣ Q * R ↔ a ∣ Q ∨ a ∈ T := by
    by_cases hat : a ∈ T
    · simp [hat, hpdvd a hat]
    · simpa [hat] using (hcop a ha haN hat).dvd_mul_right
  have hcut (u : ℝ) (hu : u ≤ N) :
      (Q * R).divisors.filter (fun a : ℕ => (a : ℝ) ≤ u) =
        Q.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u) ∪
          T.filter (fun a : ℕ => (a : ℝ) ≤ u) := by
    ext a
    simp only [mem_filter, mem_union, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨had, _⟩, hau⟩
      have ha : 1 ≤ a := Nat.pos_of_dvd_of_pos had (Nat.pos_of_ne_zero hQR0)
      have haN : a ≤ N := Nat.cast_le.mp (hau.trans hu)
      rcases (hdiv a ha haN).mp had with hd | ht
      · exact Or.inl ⟨⟨hd, hQ0⟩, hau⟩
      · exact Or.inr ⟨ht, hau⟩
    · rintro (⟨⟨hd, _⟩, hau⟩ | ⟨ht, hau⟩)
      · exact ⟨⟨dvd_mul_of_dvd_left hd R, hQR0⟩, hau⟩
      · exact ⟨⟨hpdvd a ht, hQR0⟩, hau⟩
  have hB (u : ℝ) (hu : u ≤ N) :
      B (Q * R) u = B Q u - ((T.filter (fun p : ℕ => (p : ℝ) ≤ u)).card : ℤ) := by
    have hdis : Disjoint (Q.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u))
        (T.filter (fun a : ℕ => (a : ℝ) ≤ u)) := by
      apply disjoint_left.mpr
      intro p hp hpt
      exact (hT p (mem_filter.mp hpt).1).2.2.2
        (Nat.dvd_of_mem_divisors (mem_filter.mp hp).1)
    rw [B, hcut u hu, sum_union hdis]
    have hmu : (∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ u),
        ArithmeticFunction.moebius p) = -((T.filter (fun p : ℕ => (p : ℝ) ≤ u)).card : ℤ) := by
      calc
        _ = ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ u), (-1 : ℤ) := by
          apply sum_congr rfl
          intro p hp
          exact ArithmeticFunction.moebius_apply_prime (hT p (mem_filter.mp hp).1).1
        _ = _ := by simp
    rw [hmu]
    rfl
  have hBtop : (B (Q * R) N : ℝ) = (B Q N : ℝ) - T.card := by
    have ht : T.filter (fun p : ℕ => (p : ℝ) ≤ N) = T := by
      apply filter_eq_self.mpr
      intro p hp
      exact Nat.cast_le.mpr (hT p hp).2.2.1
    rw [hB N le_rfl, ht]
    push_cast <;> rfl
  have hlow (d : ℕ) (hd : 2 ≤ d) : B (Q * R) ((N : ℝ) / d) = B Q ((N : ℝ) / d) := by
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hu : (N : ℝ) / d ≤ N := div_le_self (Nat.cast_nonneg N) hd1
    have ht : T.filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ) / d) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp hpu
      have hn := (le_div_iff₀ hd0).mp hpu
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hh : (N : ℝ) < 2 * p := by exact_mod_cast (hT p hp).2.1
      nlinarith
    rw [hB _ hu, ht]
    simp
  have hone (q : ℕ) (hq : q ≠ 0) (u : ℝ) (hu1 : 1 ≤ u) (hu2 : u < 2) : B q u = 1 := by
    have hs : q.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u) = {1} := by
      ext a
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨ha, hau⟩
        have ha1 := Nat.pos_of_mem_divisors ha
        have ha2 : a < 2 := by exact_mod_cast (hau.trans_lt hu2)
        omega
      · rintro rfl
        exact ⟨Nat.one_mem_divisors.mpr hq, by simpa using hu1⟩
    simp [B, hs]
  have hpone (p : ℕ) (hp : p ∈ T) : B Q ((N : ℝ) / p) = 1 := by
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (hT p hp).1.pos
    apply hone Q hQ0
    · apply (le_div_iff₀ hp0).mpr
      simpa using (Nat.cast_le.mpr (hT p hp).2.2.1 : (p : ℝ) ≤ N)
    · apply (div_lt_iff₀ hp0).mpr
      exact_mod_cast (hT p hp).2.1
  have hsum (P : ℕ → Prop) [DecidablePred P] (hP1 : P 1) (hPT : ∀ p ∈ T, P p) :
      (∑ d ∈ Icc 1 N, if d.Coprime Q ∧ P d then |(B Q ((N : ℝ) / d) : ℝ)| else 0) -
        (∑ d ∈ Icc 1 N, if d.Coprime (Q * R) ∧ P d then
          |(B (Q * R) ((N : ℝ) / d) : ℝ)| else 0) =
        (T.card : ℝ) + |(B Q N : ℝ)| - |(B Q N : ℝ) - T.card| := by
    have hpoint (d : ℕ) (hd : d ∈ Icc 1 N) :
        (if d.Coprime Q ∧ P d then |(B Q ((N : ℝ) / d) : ℝ)| else 0) -
          (if d.Coprime (Q * R) ∧ P d then
            |(B (Q * R) ((N : ℝ) / d) : ℝ)| else 0) =
          (if d ∈ T then (1 : ℝ) else 0) +
            (if d = 1 then |(B Q N : ℝ)| - |(B Q N : ℝ) - T.card| else 0) := by
      obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
      by_cases hdt : d ∈ T
      · have hdc : d.Coprime Q := (hT d hdt).1.coprime_iff_not_dvd.mpr (hT d hdt).2.2.2
        have hdnc : ¬d.Coprime (Q * R) := by
          rw [(hT d hdt).1.coprime_iff_not_dvd]
          exact not_not.mpr (hpdvd d hdt)
        simp [hdt, (hT d hdt).1.ne_one, hdc, hdnc, hPT d hdt, hpone d hdt]
      · by_cases hdEq : d = 1
        · subst d
          simp [hdt, hP1, hBtop]
        · have hd2 : 2 ≤ d := by omega
          have hdc : d.Coprime (Q * R) ↔ d.Coprime Q := by
            exact ⟨fun h => (Nat.coprime_mul_iff_right.mp h).1,
              fun h => Nat.coprime_mul_iff_right.mpr ⟨h, hcop d hd1 hdN hdt⟩⟩
          simp [hdt, hdEq, hdc, hlow d hd2]
    have ht : (Icc 1 N).filter (fun d => d ∈ T) = T := by
      ext d
      simp only [mem_filter, mem_Icc]
      constructor
      · exact fun h => h.2
      · intro hd
        exact ⟨⟨(hT d hd).1.one_lt.le, (hT d hd).2.2.1⟩, hd⟩
    rw [← sum_sub_distrib]
    calc
      _ = ∑ d ∈ Icc 1 N, ((if d ∈ T then (1 : ℝ) else 0) +
          (if d = 1 then |(B Q N : ℝ)| - |(B Q N : ℝ) - T.card| else 0)) :=
        sum_congr rfl hpoint
      _ = _ := by
        rw [sum_add_distrib, ← sum_filter, ht]
        simp [show 1 ≤ N by omega] <;> ring
  have hU (q : ℕ) : U q N =
      ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime q), |(B q ((N : ℝ) / d) : ℝ)| := by
    by_cases hq : q = 1
    · subst q
      rw [U, if_pos rfl]
      have hf : (Icc 1 N).filter (fun d => d.Coprime 1) = Icc 1 N :=
        filter_eq_self.mpr (fun d _ => Nat.coprime_one_right d)
      rw [hf]
      calc
        (N : ℝ) = ∑ d ∈ Icc 1 N, (1 : ℝ) := by simp
        _ = _ := by
          apply sum_congr rfl
          intro d hd
          obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
          have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
          have hu : (1 : ℝ) ≤ (N : ℝ) / d := (le_div_iff₀ hd0).mpr
            (by simpa using (Nat.cast_le.mpr hdN : (d : ℝ) ≤ N))
          have hf1 : (1 : ℕ).divisors.filter
              (fun a : ℕ => (a : ℝ) ≤ (N : ℝ) / d) = {1} := by
            rw [Nat.divisors_one]
            apply filter_eq_self.mpr
            intro a ha
            simpa only [mem_singleton.mp ha, Nat.cast_one] using hu
          rw [B, hf1]
          simp
    · rw [U, if_neg hq]
  constructor
  · rw [hU Q, hU (Q * R)]
    simpa only [sum_filter, and_true] using hsum (fun _ => True) trivial (by simp)
  · simpa only [W, sum_filter] using hsum Squarefree squarefree_one
      (fun p hp => (hT p hp).1.squarefree)

end D5.S3.Weil.Mertens.UpperHalfPrimeCertificateExtension
