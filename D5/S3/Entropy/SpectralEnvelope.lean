/- GID: D5/S3/Entropy/SpectralEnvelope
   generality: G
   mirror-B: D5/B/S3/Entropy/SpectralEnvelope
   mirror-E: none(waiver:analytic-countable-limit)
   anchors: []
   utility: none
   digest: Sharp countable trace/purity envelope by mass-preserving finite approximants. -/

import D5.S3.Entropy.FiniteSpectralEnvelope
import Batteries.Tactic.OpenPrivate

noncomputable section
open scoped BigOperators
open Filter Topology

namespace D5.S3.Entropy.SpectralEnvelope
open CountableSpectralMoments SpectralEnvelopeParameters FiniteSpectralEnvelope
open private summable_square summable_cube from D5.S3.Entropy.CountableSpectralMoments
open private coordinate_bounds coordinate_purity coordinate_value three_summable
  three_mass three_purity three_third envelope_antitone endpoint_constants
  threshold_bounds threshold_value from D5.S3.Entropy.SpectralEnvelopeParameters

private theorem equal_tail_length {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1) (n : ℕ) :
    let T := 1 - ∑ i ∈ Finset.range n, p i
    let R := purity p - ∑ i ∈ Finset.range n, p i ^ 2
    ∃ L : ℕ, 0 < L ∧ T ^ 2 / L ≤ R := by
  dsimp
  let T := 1 - ∑ i ∈ Finset.range n, p i
  let R := purity p - ∑ i ∈ Finset.range n, p i ^ 2
  have hs := summable_square hp hn hm.le
  have hT : 0 ≤ T := sub_nonneg.mpr (by
    rw [← hm]
    exact hp.sum_le_tsum (Finset.range n) (fun i _ => hn i))
  have hR : 0 ≤ R := sub_nonneg.mpr (hs.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg _))
  by_cases hR0 : R = 0
  · have ht2 := hs.sum_add_tsum_nat_add n
    have ht1 := hp.sum_add_tsum_nat_add n
    have hzsum : (∑' k, p (k + n) ^ 2) = 0 := by
      change (∑' k, p (k + n) ^ 2) = 0
      dsimp [R, purity] at hR0
      linarith
    have htail := (summable_nat_add_iff n).2 hs
    have hz (k : ℕ) : p (k + n) = 0 := by
      have hle := htail.le_tsum k (fun j _ => sq_nonneg (p (j + n)))
      rw [hzsum] at hle
      nlinarith
    have hz1 : (∑' k, p (k + n)) = 0 := by simp [hz]
    have hT0 : T = 0 := by
      rw [hz1, show (∑' i, p i) = 1 from hm] at ht1
      dsimp [T]
      linarith
    refine ⟨1, by omega, ?_⟩
    change T ^ 2 / (1 : ℝ) ≤ R
    simp [hT0, hR0]
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    obtain ⟨L, hL⟩ := exists_nat_gt (T ^ 2 / R)
    have hLp : (0 : ℝ) < L := (div_nonneg (sq_nonneg _) hR).trans_lt hL
    refine ⟨L, by exact_mod_cast hLp, ?_⟩
    apply (div_le_iff₀ hLp).mpr
    have hmul := (div_lt_iff₀ hRp).mp hL
    nlinarith

private theorem finite_approximation_bound {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1)
    (hq0 : 1 / 3 ≤ purity p) (hq1 : purity p ≤ 3 / 8) (n : ℕ) :
    envelope (purity p) ≤ third p +
      (purity p - ∑ i ∈ Finset.range n, p i ^ 2) / 2 +
      (1 - ∑ i ∈ Finset.range n, p i) ^ 3 / 3 := by
  let T := 1 - ∑ i ∈ Finset.range n, p i
  let R := purity p - ∑ i ∈ Finset.range n, p i ^ 2
  have hT : 0 ≤ T := sub_nonneg.mpr (by
    rw [← hm]
    exact hp.sum_le_tsum (Finset.range n) (fun i _ => hn i))
  obtain ⟨L, hL, hLR⟩ := equal_tail_length hp hn hm n
  change T ^ 2 / (L : ℝ) ≤ R at hLR
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := hLr.ne'
  let v : Fin n ⊕ Fin L → ℝ := Sum.elim (fun i => p i) (fun _ => T / L)
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    cases i with
    | inl i => exact hn i
    | inr i => exact div_nonneg hT hLr.le
  have hsum : (∑ i, v i) = 1 := by
    simp only [v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range, mul_div_cancel₀ T hLne]
    dsimp [T]
    ring
  have hq : finitePurity v = (∑ i ∈ Finset.range n, p i ^ 2) + T ^ 2 / L := by
    unfold finitePurity
    simp only [v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range]
    field_simp
    <;> ring
  have hr : (∑ i, v i ^ 3) = (∑ i ∈ Finset.range n, p i ^ 3) + T ^ 3 / (L : ℝ) ^ 2 := by
    simp only [v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range]
    field_simp
    <;> ring
  have hvq : finitePurity v ≤ purity p := by rw [hq]; dsimp [R] at hLR; linarith
  have hvql : purity p - R ≤ finitePurity v := by rw [hq]; dsimp [R]; positivity
  have hvc : (∑ i, v i ^ 3) ≤ cubicMoment p + T ^ 3 := by
    have hpartial := (summable_cube hp hn hm.le).sum_le_tsum
      (Finset.range n) (fun i _ => pow_nonneg (hn i) 3)
    have hrep : T ^ 3 / (L : ℝ) ^ 2 ≤ T ^ 3 :=
      div_le_self (pow_nonneg hT 3) (by nlinarith)
    rw [hr]
    change (∑ i ∈ Finset.range n, p i ^ 3) ≤ cubicMoment p at hpartial
    linarith
  have hfinite := finite_budget_envelope v hv0 hsum hq0 hq1 hvq
  have hnewton := countable_newton hp hn hm.le
  rw [hm] at hnewton
  unfold finiteThird at hfinite
  rw [hsum] at hfinite
  change envelope (purity p) ≤ third p + R / 2 + T ^ 3 / 3
  nlinarith

/-- The sharp moment envelope on every countable probability spectrum. The
approximants have exactly unit mass and no greater purity; no mass is discarded. -/
theorem countable_budget_envelope {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1)
    (hq0 : 1 / 3 ≤ purity p) (hq1 : purity p ≤ 3 / 8) :
    envelope (purity p) ≤ third p := by
  have hs := hp.hasSum.tendsto_sum_nat
  have hq := (summable_square hp hn hm.le).hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun n => third p +
      (purity p - ∑ i ∈ Finset.range n, p i ^ 2) / 2 +
      (1 - ∑ i ∈ Finset.range n, p i) ^ 3 / 3) atTop (𝓝 (third p)) := by
    have h := (tendsto_const_nhds.add ((tendsto_const_nhds.sub hq).div_const 2)).add
      (((tendsto_const_nhds.sub hs).pow 3).div_const 3)
    simpa [mass, purity, hm] using h
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall (finite_approximation_bound hp hn hm hq0 hq1))

/-- Abstract sharpness does not assert that these spectra are Fock outputs. -/
theorem envelope_sharp {q : ℝ} (hq0 : 1 / 3 ≤ q) (hq1 : q ≤ 3 / 8) :
    ∃ p : ℕ → ℝ, Summable p ∧ (∀ i, 0 ≤ p i) ∧ mass p = 1 ∧
      purity p = q ∧ third p = envelope q := by
  let x := upperCoordinate q
  have hx := coordinate_bounds hq0 hq1
  refine ⟨threeSpectrum x, three_summable x, ?_, three_mass x, ?_, ?_⟩
  · intro i
    unfold threeSpectrum
    split_ifs <;> nlinarith
  · rw [three_purity]
    exact coordinate_purity hq0
  · rw [three_third]
    exact coordinate_value hq0

/-- The uniform constant obtained from the trace and purity constraints alone. -/
theorem third_lower_of_purity_le_three_eighths {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1) (hq : purity p ≤ 3 / 8) :
    25 / 864 ≤ third p := by
  by_cases hlow : purity p ≤ 1 / 3
  · have hb := third_lower_of_purity_le_third hp hn hm hlow
    linarith
  · have he := countable_budget_envelope hp hn hm (lt_of_not_ge hlow).le hq
    have hm := envelope_antitone (lt_of_not_ge hlow).le hq
    rw [endpoint_constants.1] at hm
    linarith

/-- The exact scalar threshold is sufficient, including its boundary. -/
theorem third_lower_of_purity_le_threshold {p : ℕ → ℝ} (hp : Summable p)
    (hn : ∀ i, 0 ≤ p i) (hm : mass p = 1) (hq : purity p ≤ threshold) :
    1 / 32 ≤ third p := by
  by_cases hlow : purity p ≤ 1 / 3
  · have hb := third_lower_of_purity_le_third hp hn hm hlow
    linarith
  · have he := countable_budget_envelope hp hn hm (lt_of_not_ge hlow).le
      (hq.trans threshold_bounds.2)
    have hmono := envelope_antitone (lt_of_not_ge hlow).le hq
    rw [threshold_value] at hmono
    linarith

end D5.S3.Entropy.SpectralEnvelope
