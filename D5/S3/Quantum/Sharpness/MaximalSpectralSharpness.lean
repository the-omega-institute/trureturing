/- GID: D5/S3/Quantum/Sharpness/MaximalSpectralSharpness
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/MaximalSpectralSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Spectral sharpness is the attained normalized capacity with its witnesses and laws. -/

/- Library and duplicate search audit (2026-09-04):
   * Repository searches for `spectralSharpness`, `spectral_sharpness`, central distance, median
     cuts, qubit Bloch radius, and doubly-stochastic monotonicity found four canonical partial
     owners in this directory, but no theorem carrying all clauses together.
   * `SpectralSharpnessDuality` gives the bounded-pairing maximum; `SpectralSharpnessSaturation`
     and `SpectralSharpness` give the two endpoints; `SpectralPairingCapacity` gives the
     doubly-stochastic comparison. All four are applied below.
   * Pinned-Mathlib searches for total variation against reversal, finite central distance,
     median-split maximizers, and unital-channel spectral majorization found no exact theorem.
     The finite-order, absolute-value, square-root, and `IsLeast`/`IsGreatest` primitives used
     below are supplied by Mathlib through the canonical owners.
   * The public dimension is `n + 2`: the normalized ratio ranges over noncentral observables,
     so dimension at least two is load-bearing and is encoded rather than left implicit.
-/

import D5.S3.Quantum.Sharpness.SpectralSharpnessDuality
import D5.S3.Quantum.Sharpness.SpectralSharpnessSaturation

noncomputable section

open Finset Matrix
open D5.S3.Quantum.Sharpness.SpectralPairingCapacity
open D5.S3.Quantum.Sharpness.SpectralSharpness
open D5.S3.Quantum.Sharpness.SpectralSharpnessDuality
open D5.S3.Quantum.Sharpness.SpectralSharpnessSaturation

namespace D5.S3.Quantum.Sharpness.MaximalSpectralSharpness

/-- Half the endpoint range of a decreasing observable spectrum. The main theorem proves that
this is exactly its distance to the constant spectra in the supremum norm. -/
def spectralCenterDistance {n : ℕ} (a : Fin (n + 2) → ℝ) : ℝ :=
  (a 0 - a (Fin.last (n + 1))) / 2

/-- The median-cut yes/no question on a finite spectrum. -/
def medianCutQuestion {n : ℕ} (i : Fin (n + 2)) : ℝ :=
  if i.val < (n + 2) / 2 then 1 else -1

private theorem medianCutQuestion_antitone {n : ℕ} :
    Antitone (medianCutQuestion (n := n)) := by
  intro i j hij
  change
    (if j.val < (n + 2) / 2 then (1 : ℝ) else -1) ≤
      if i.val < (n + 2) / 2 then 1 else -1
  by_cases hi : i.val < (n + 2) / 2
  · rw [if_pos hi]
    by_cases hj : j.val < (n + 2) / 2
    · rw [if_pos hj]
    · rw [if_neg hj]
      norm_num
  · have hj : ¬j.val < (n + 2) / 2 := by omega
    rw [if_neg hi, if_neg hj]

private theorem spectralPairingCapacity_eq_signedPairing {n : ℕ}
    (r a : Fin n → ℝ) :
    spectralPairingCapacity r a =
      (1 / 2 : ℝ) * ∑ i, (r i - r (Fin.rev i)) * a i := by
  unfold spectralPairingCapacity
  congr 1
  calc
    ∑ i, r i * (a i - a (Fin.rev i)) =
        ∑ i, (r i * a i - r i * a (Fin.rev i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, r i * a i) - ∑ i, r i * a (Fin.rev i) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, r i * a i) - ∑ i, r (Fin.rev i) * a i := by
      congr 1
      simpa using (Equiv.sum_comp Fin.revPerm (fun i => r (Fin.rev i) * a i))
    _ = ∑ i, (r i - r (Fin.rev i)) * a i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem medianCutQuestion_signed_gap {n : ℕ} (r : Fin (n + 2) → ℝ)
    (hmono : Antitone r) (i : Fin (n + 2)) :
    (r i - r (Fin.rev i)) * medianCutQuestion i = |r i - r (Fin.rev i)| := by
  by_cases hi : i.val < (n + 2) / 2
  · have hindex : i ≤ Fin.rev i := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.rev]
      omega
    have hgap : 0 ≤ r i - r (Fin.rev i) := sub_nonneg.mpr (hmono hindex)
    rw [medianCutQuestion, if_pos hi, mul_one, abs_of_nonneg hgap]
  · have hindex : Fin.rev i ≤ i := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.rev]
      omega
    have hgap : r i - r (Fin.rev i) ≤ 0 := sub_nonpos.mpr (hmono hindex)
    rw [medianCutQuestion, if_neg hi, mul_neg, mul_one, abs_of_nonpos hgap]

private theorem medianCutQuestion_attains {n : ℕ} (r : Fin (n + 2) → ℝ)
    (hmono : Antitone r) :
    spectralPairingCapacity r medianCutQuestion = spectralSharpness r := by
  rw [spectralPairingCapacity_eq_signedPairing, spectralSharpness]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact medianCutQuestion_signed_gap r hmono i

private theorem medianCutQuestion_distance {n : ℕ} :
    spectralCenterDistance (medianCutQuestion (n := n)) = 1 := by
  have hzero : (0 : ℕ) < (n + 2) / 2 := by omega
  have hlast : ¬(Fin.last (n + 1)).val < (n + 2) / 2 := by
    simp
    omega
  change
    ((if (0 : ℕ) < (n + 2) / 2 then 1 else -1) -
      (if (Fin.last (n + 1)).val < (n + 2) / 2 then 1 else -1)) / 2 = 1
  rw [if_pos hzero, if_neg hlast]
  norm_num

private theorem spectralCenterDistance_isLeast {n : ℕ} (a : Fin (n + 2) → ℝ)
    (ha : Antitone a) :
    IsLeast {d : ℝ | ∃ c : ℝ, ∀ i, |a i - c| ≤ d} (spectralCenterDistance a) := by
  constructor
  · refine ⟨(a 0 + a (Fin.last (n + 1))) / 2, ?_⟩
    intro i
    have hiUpper : a i ≤ a 0 := ha (Fin.zero_le i)
    have hiLower : a (Fin.last (n + 1)) ≤ a i := ha (Fin.le_last i)
    rw [abs_le]
    unfold spectralCenterDistance
    constructor <;> linarith
  · intro d hd
    rcases hd with ⟨c, hc⟩
    have hzero := abs_le.mp (hc 0)
    have hlast := abs_le.mp (hc (Fin.last (n + 1)))
    unfold spectralCenterDistance
    linarith

private theorem normalized_capacity_isGreatest {n : ℕ} (r : Fin (n + 2) → ℝ)
    (hmono : Antitone r) :
    IsGreatest
      {value : ℝ | ∃ a : Fin (n + 2) → ℝ,
        Antitone a ∧ 0 < spectralCenterDistance a ∧
          spectralPairingCapacity r a / spectralCenterDistance a = value}
      (spectralSharpness r) := by
  constructor
  · refine ⟨medianCutQuestion, medianCutQuestion_antitone, ?_, ?_⟩
    · rw [medianCutQuestion_distance]
      norm_num
    · rw [medianCutQuestion_distance, medianCutQuestion_attains r hmono]
      simp
  · rintro value ⟨a, ha, hd, rfl⟩
    let d : ℝ := spectralCenterDistance a
    let c : ℝ := (a 0 + a (Fin.last (n + 1))) / 2
    let b : Fin (n + 2) → ℝ := fun i => (a i - c) / d
    have hd' : 0 < d := by simpa [d] using hd
    have hb : ∀ i, |b i| ≤ 1 := by
      intro i
      have hiUpper : a i ≤ a 0 := ha (Fin.zero_le i)
      have hiLower : a (Fin.last (n + 1)) ≤ a i := ha (Fin.le_last i)
      rw [abs_le]
      constructor
      · rw [le_div_iff₀ hd']
        dsimp only [c, d]
        unfold spectralCenterDistance
        linarith
      · rw [div_le_iff₀ hd']
        dsimp only [c, d]
        unfold spectralCenterDistance
        linarith
    have hscale :
        spectralPairingCapacity r b = spectralPairingCapacity r a / d := by
      rw [spectralPairingCapacity, spectralPairingCapacity]
      calc
        (1 / 2 : ℝ) * ∑ i, r i * (b i - b (Fin.rev i)) =
            (1 / 2 : ℝ) * ∑ i, (r i * (a i - a (Fin.rev i))) / d := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [b]
          field_simp
          ring
        _ = ((1 / 2 : ℝ) * ∑ i, r i * (a i - a (Fin.rev i))) / d := by
          rw [← Finset.sum_div]
          ring
    have hgreat := spectral_sharpness_isGreatest_bounded_pairing r
    have hmember : spectralPairingCapacity r b ∈
        {value : ℝ | ∃ a : Fin (n + 2) → ℝ, (∀ i, |a i| ≤ 1) ∧
          spectralPairingCapacity r a = value} := ⟨b, hb, rfl⟩
    have hle := hgreat.2 hmember
    rwa [hscale] at hle

private theorem qubit_sharpness_eq_purity_radius (q : Fin 2 → ℝ)
    (hsum : ∑ i, q i = 1) :
    spectralSharpness q = Real.sqrt (2 * ∑ i, (q i) ^ 2 - 1) := by
  have hsum' : q 0 + q 1 = 1 := by simpa [Fin.sum_univ_two] using hsum
  have hradicand : 2 * ∑ i, (q i) ^ 2 - 1 = (q 0 - q 1) ^ 2 := by
    simp only [Fin.sum_univ_two]
    nlinarith
  rw [spectralSharpness, hradicand, Real.sqrt_sq_eq_abs]
  have hrevZero : Fin.rev (0 : Fin 2) = 1 := by decide
  have hrevOne : Fin.rev (1 : Fin 2) = 0 := by decide
  simp only [Fin.sum_univ_two, hrevZero, hrevOne]
  rw [abs_sub_comm (q 1) (q 0)]
  ring

private example :
    ∃ r : Fin 2 → ℝ, (∀ i, 0 ≤ r i) ∧ Antitone r ∧ ∑ i, r i = 1 := by
  refine ⟨fun _ => 1 / 2, ?_, antitone_const, ?_⟩
  · intro i
    norm_num
  · norm_num [Fin.sum_univ_two]

/-- For every probability spectrum in dimension at least two, spectral sharpness is the attained
maximum of pairing capacity divided by distance from the constant spectra. The median-cut
plus-or-minus-one question attains it. The same public statement gives the qubit purity-radius
formula, both endpoint characterisations, and monotonicity under doubly-stochastic spectral
mixing, the spectral form of the unital-channel data-processing law. -/
theorem maximal_spectral_sharpness {n : ℕ} (r : Fin (n + 2) → ℝ)
    (hnn : ∀ i, 0 ≤ r i) (hmono : Antitone r) (hsum : ∑ i, r i = 1) :
    (∀ a : Fin (n + 2) → ℝ, Antitone a →
      IsLeast {d : ℝ | ∃ c : ℝ, ∀ i, |a i - c| ≤ d} (spectralCenterDistance a)) ∧
    IsGreatest
      {value : ℝ | ∃ a : Fin (n + 2) → ℝ,
        Antitone a ∧ 0 < spectralCenterDistance a ∧
          spectralPairingCapacity r a / spectralCenterDistance a = value}
      (spectralSharpness r) ∧
    ((∀ i, medianCutQuestion (n := n) i = 1 ∨ medianCutQuestion (n := n) i = -1) ∧
      Antitone (medianCutQuestion (n := n)) ∧
      spectralPairingCapacity r medianCutQuestion /
          spectralCenterDistance (medianCutQuestion (n := n)) = spectralSharpness r) ∧
    (∀ q : Fin 2 → ℝ, (∑ i, q i = 1) →
      spectralSharpness q = Real.sqrt (2 * ∑ i, (q i) ^ 2 - 1)) ∧
    (spectralSharpness r = 1 ↔
      (Finset.univ.filter (fun i => r i ≠ 0)).card ≤ (n + 2) / 2) ∧
    (spectralSharpness r = 0 ↔ ∀ i, r i = 1 / (n + 2)) ∧
    (∀ (r' : Fin (n + 2) → ℝ) (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ),
      Antitone r' → S ∈ doublyStochastic ℝ (Fin (n + 2)) → r = S *ᵥ r' →
        spectralSharpness r ≤ spectralSharpness r') := by
  refine ⟨fun a ha => spectralCenterDistance_isLeast a ha,
    normalized_capacity_isGreatest r hmono, ?_,
    qubit_sharpness_eq_purity_radius, ?_, ?_, ?_⟩
  · refine ⟨?_, medianCutQuestion_antitone, ?_⟩
    · intro i
      by_cases hi : i.val < (n + 2) / 2
      · left
        rw [medianCutQuestion, if_pos hi]
      · right
        rw [medianCutQuestion, if_neg hi]
    · rw [medianCutQuestion_distance, medianCutQuestion_attains r hmono]
      simp
  · exact spectral_sharpness_one_iff_support_le_half r hnn hmono hsum
  · simpa using spectral_sharpness_zero_iff_uniform r hmono hsum
  · intro r' S hr' hS hr
    rw [← medianCutQuestion_attains r hmono,
      ← medianCutQuestion_attains r' hr']
    exact spectral_pairing_capacity_monotone_of_doubly_stochastic
      hr' medianCutQuestion_antitone hS hr

#print axioms maximal_spectral_sharpness

end D5.S3.Quantum.Sharpness.MaximalSpectralSharpness
