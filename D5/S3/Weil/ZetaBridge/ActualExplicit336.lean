/- GID: D5/S3/Weil/ZetaBridge/ActualExplicit336
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualExplicit336
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: The actual explicit336 allowance controls paired-symbol and nodal infinite tails uniformly over all vectors. -/

import D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
import D5.S3.Weil.ZetaBridge.ActualFunctionMetric

noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators Interval
namespace D5.S3.Weil.ZetaBridge.ActualExplicit336
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Analytic.PolynomialReciprocalBounds

private lemma pairedEnergy_nonneg {c : ℕ} (hc : 3 ≤ c) (A B : ℂ[X]) :
    0 ≤ pairedEnergy c A B := by
  have hmean : 0 ≤ mean c :=
    (by positivity : (0:ℝ) ≤ (Real.log (2:ℝ))^2/4).trans
      (prime_symbol_mean_lower_bound hc)
  unfold pairedEnergy functionEnergy
  exact add_nonneg
    (add_nonneg (energy_nonneg _) (mul_nonneg hmean (energy_nonneg _)))
    (add_nonneg (energy_nonneg _) (mul_nonneg hmean (energy_nonneg _)))

/-- Infinite actual paired-symbol enclosure with the cutoff-only explicit allowance. -/
theorem actual_paired_symbol_enclosure_explicit336 {c d N : ℕ}
    (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N)
    (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) :
    Summable (pairedTerm c N A B) ∧
    |(N:ℝ)*(∑' j : ℕ, pairedTerm c N A B j)-pairedEnergy c A B| ≤
      (d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ)*
        pairedEnergy c A B := by
  have henc := actual_paired_symbol_enclosure hc hd hN A B hA hB
  refine ⟨henc.1, henc.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (pairedEnergy_nonneg hc A B)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact mul_le_mul_of_nonneg_left (U_le_explicit336 hc) (sq_nonneg (d:ℝ))

/-- Both paired-symbol bounds, retaining the entire infinite tail. -/
theorem actual_paired_symbol_bounds_explicit336 {c d N : ℕ}
    (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N)
    (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) :
    let ε := (d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ)
    Summable (pairedTerm c N A B) ∧
    (1-ε)*pairedEnergy c A B/(N:ℝ) ≤ (∑' j : ℕ, pairedTerm c N A B j) ∧
    (∑' j : ℕ, pairedTerm c N A B j) ≤ (1+ε)*pairedEnergy c A B/(N:ℝ) := by
  dsimp only
  have hdpos : 0 < d := by omega
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos hdpos 2) hN
  have hn : (0:ℝ) < N := by exact_mod_cast hNpos
  have henc := actual_paired_symbol_enclosure_explicit336 hc hd hN A B hA hB
  obtain ⟨hl,hu⟩ := abs_le.mp henc.2
  refine ⟨henc.1, ?_, ?_⟩
  · apply (div_le_iff₀ hn).2
    nlinarith only [hl]
  · apply (le_div_iff₀ hn).2
    nlinarith only [hu]

/-- Actual nodal upper/lower column tail with U replaced by 336 c² (1+log c)³.
The head bound and N hypotheses imply both nodal denominators are positive.
No positivity of a dense head or nonzero-vector hypothesis is needed. -/
theorem actual_paired_column_enclosure_explicit336 {c N : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (hSne : S.Nonempty) (v : ℤ → ℂ)
    (hNdim : S.card^2 ≤ N) {B : ℝ} (hB : 0 ≤ B) (hBN : 2*B ≤ N)
    (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) :
    let d := S.card
    let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v)
    let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v)
    let H := pairedEnergy c A Q
    let ε := (d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ)
    Summable (pairedColumnTerm c N S v) ∧
    (1-ε)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤
      (∑' j : ℕ, pairedColumnTerm c N S v j) ∧
    (∑' j : ℕ, pairedColumnTerm c N S v j) ≤
      (1+ε)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d)) := by
  dsimp only
  have hdpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos hdpos 2) hNdim
  have hn : (0:ℝ) < N := by exact_mod_cast hNpos
  have hL : 0 < 1-B/(N:ℝ) := sub_pos.mpr ((div_lt_one hn).2 (by linarith))
  have hε : (S.card:ℝ)^2*U c/(N:ℝ) ≤
      (S.card:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (U_le_explicit336 hc) (sq_nonneg (S.card:ℝ))) hn.le
  let A := reciprocalPolynomial S.card N (ActualNodalCoercivity.P c S v)
  let Q := reciprocalPolynomial S.card N (ActualNodalCoercivity.Q S v)
  have hH := pairedEnergy_nonneg hc A Q
  have hh := mul_le_mul_of_nonneg_right hε hH
  dsimp only [A,Q] at hh
  have henc := actual_paired_column_enclosure hc S hSne v hNdim hB hBN hS
  dsimp only at henc
  refine ⟨henc.1, ?_, ?_⟩
  · refine le_trans ?_ henc.2.1
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hh]
  · refine henc.2.2.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hh]

/-- A cutoff chosen from the explicit arithmetic allowance before every vector.
This keeps the original head and denominator hypotheses, with no energy division. -/
theorem actual_paired_column_uniform_enclosure_explicit336 {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (hSne : S.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ v : ℤ → ℂ, ∀ N : ℕ, N0 ≤ N →
      let d := S.card
      let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v)
      let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v)
      let H := pairedEnergy c A Q
      Summable (pairedColumnTerm c N S v) ∧
      (1-η)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤
        (∑' j : ℕ, pairedColumnTerm c N S v j) ∧
      (∑' j : ℕ, pairedColumnTerm c N S v j) ≤
        (1+η)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d)) := by
  obtain ⟨kB, hkB⟩ := exists_nat_ge (2*B)
  obtain ⟨kE, hkE⟩ := exists_nat_ge
    ((S.card:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/η)
  let N0 := max 1 (max (S.card^2) (max kB kE))
  refine ⟨N0, ?_⟩
  intro v N hcut
  dsimp only
  have hN : 0 < N := by dsimp [N0] at hcut; omega
  have hdN : S.card^2 ≤ N := by dsimp [N0] at hcut; omega
  have hkBN : kB ≤ N := by dsimp [N0] at hcut; omega
  have hkEN : kE ≤ N := by dsimp [N0] at hcut; omega
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hBN : 2*B ≤ (N:ℝ) := hkB.trans (by exact_mod_cast hkBN)
  have hε : (S.card:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ) ≤ η := by
    apply (div_le_iff₀ hn).2
    have hh : (S.card:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/η ≤ (N:ℝ) :=
      hkE.trans (by exact_mod_cast hkEN)
    simpa only [mul_comm] using (div_le_iff₀ hη).1 hh
  let A := reciprocalPolynomial S.card N (ActualNodalCoercivity.P c S v)
  let Q := reciprocalPolynomial S.card N (ActualNodalCoercivity.Q S v)
  have hH := pairedEnergy_nonneg hc A Q
  have hh := mul_le_mul_of_nonneg_right hε hH
  dsimp only [A,Q] at hh
  have hL : 0 < 1-B/(N:ℝ) := sub_pos.mpr ((div_lt_one hn).2 (by linarith))
  have henc := actual_paired_column_enclosure_explicit336 hc S hSne v hdN hB hBN hS
  dsimp only at henc
  refine ⟨henc.1, ?_, ?_⟩
  · refine le_trans ?_ henc.2.1
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hh]
  · refine henc.2.2.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hh]

end D5.S3.Weil.ZetaBridge.ActualExplicit336
