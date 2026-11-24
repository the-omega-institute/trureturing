/- GID: D5/S3/Quantum/Measurement/Auric/DisjointPhysicalBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/DisjointPhysicalBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Excess deficits force the disjoint regime and yield its fixed-law physical optimum. -/

import D5.S3.Quantum.Measurement.Auric.DisjointEffects
import D5.S3.Quantum.Measurement.Auric.UnequalPhysicalTargets

/-! The disjoint support maximum in the fixed-law coherent projective record budget.
The score-set equality of the unequal projection geometry enters as GeometryStatement. -/

namespace D5.S3.Quantum.Measurement.Auric

open scoped BigOperators
open DisjointEffects (sum_three_labels)

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The previously specified effect target, including equality of the cap sum with the working
dimension and the empty working dimension. -/
theorem disjoint_effects_statement (d : ℕ) (m : Fin 3 → ℕ) (t : Fin 3 → ℝ) :
    DisjointEffectsStatement d m t := by
  intro i k a hik hia hka ha hfit ht htotal flip
  exact DisjointEffects.isGreatest_disjoint (n := Fin d) m t hik hia hka
    (by simpa using ha) (by simpa using hfit) ht (by simpa using htotal) flip

/-- When the working dimension is at most half of the total capacity, excess kernel deficits
force one large cap and two small caps whose sum is strictly below the working dimension. -/
theorem excess_deficits_disjoint (d : ℕ) (m : Fin 3 → ℕ)
    (hsize : 2 * d ≤ ∑ j, m j) (hdef : d < ∑ j, (d - m j)) :
    ∃ a i k : Fin 3, i ≠ k ∧ i ≠ a ∧ k ≠ a ∧ d ≤ m a ∧ m i + m k < d := by
  have hlarge : ∃ a, d ≤ m a := by
    by_contra! hn
    have he : (∑ j, (d - m j)) + (∑ j, m j) = 3 * d := by
      rw [← Finset.sum_add_distrib]
      have hterm (j : Fin 3) : (d - m j) + m j = d := Nat.sub_add_cancel (hn j).le
      simp [hterm]
    omega
  obtain ⟨a, ha⟩ := hlarge
  have hothers : ∃ i k : Fin 3, i ≠ k ∧ i ≠ a ∧ k ≠ a := by
    fin_cases a
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  obtain ⟨i, k, hik, hia, hka⟩ := hothers
  rw [sum_three_labels hik hia hka, Nat.sub_eq_zero_of_le ha, add_zero] at hdef
  exact ⟨a, i, k, hik, hia, hka, ha, by omega⟩

theorem capacity_total (c : ι → Fin 3) :
    (∑ j, capacity c j) = Fintype.card ι := by
  calc
    (∑ j, capacity c j) = Fintype.card (Σ j : Fin 3, {p : ι // c p = j}) := by
      simp [capacity, Fintype.card_sigma]
    _ = Fintype.card ι := Fintype.card_congr (Equiv.sigmaFiberEquiv c)

theorem working_traces_of_law (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (hrN : r ≤ Fintype.card ι) (hq : FeasibleLaw c r q) (flip : Bool) :
    let d := if flip then Fintype.card ι - r else r
    let t := fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
    (∀ j, 0 ≤ t j ∧ t j ≤ (capacity c j : ℝ)) ∧ (∑ j, t j) = (d : ℝ) := by
  have hnonneg (j : Fin 3) : 0 ≤ (r : ℝ) * q j :=
    mul_nonneg (Nat.cast_nonneg r) (hq.1 j).1
  cases flip
  · change (∀ j, 0 ≤ (r : ℝ) * q j ∧ (r : ℝ) * q j ≤ (capacity c j : ℝ)) ∧
      (∑ j, (r : ℝ) * q j) = (r : ℝ)
    exact ⟨fun j => ⟨hnonneg j, (hq.1 j).2⟩, by rw [← Finset.mul_sum, hq.2, mul_one]⟩
  · change (∀ j, 0 ≤ (capacity c j : ℝ) - (r : ℝ) * q j ∧
        (capacity c j : ℝ) - (r : ℝ) * q j ≤ (capacity c j : ℝ)) ∧
      (∑ j, ((capacity c j : ℝ) - (r : ℝ) * q j)) = ((Fintype.card ι - r : ℕ) : ℝ)
    refine ⟨fun j => ⟨sub_nonneg.mpr (hq.1 j).2, sub_le_self _ (hnonneg j)⟩, ?_⟩
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, capacity_total c, ← Finset.mul_sum, hq.2,
      mul_one, Nat.cast_sub hrN]

/-- The physical disjoint branch uses the original rank in both normalizations. -/
theorem sharp_record_budget_of_disjoint (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (hGeometry : GeometryStatement c r q) (hr : 0 < r) (hrN : r ≤ Fintype.card ι)
    (hq : FeasibleLaw c r q) (flip : Bool) {i k a : Fin 3}
    (hik : i ≠ k) (hia : i ≠ a) (hka : k ≠ a) :
    let d := if flip then Fintype.card ι - r else r
    let t := fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
    d ≤ capacity c a → capacity c i + capacity c k ≤ d →
    SharpRecordBudget c r q (binaryTerm (capacity c i) (t i) + binaryTerm (capacity c k) (t k)) := by
  let d := if flip then Fintype.card ι - r else r
  let t := fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
  let B := binaryTerm (capacity c i) (t i) + binaryTerm (capacity c k) (t k)
  change d ≤ capacity c a → capacity c i + capacity c k ≤ d → SharpRecordBudget c r q B
  intro ha hfit
  obtain ⟨ht, htotal⟩ := working_traces_of_law c r q hrN hq flip
  have hmax : IsGreatest (effectValues flip d (capacity c) t) B :=
    disjoint_effects_statement d (capacity c) t i k a hik hia hka ha hfit ht htotal flip
  have hrange : gainValues c r q = (fun x : ℝ => x / r) '' effectValues flip d (capacity c) t :=
    hGeometry hr hrN flip
  apply physical_of_gain c r q B hr
  rw [hrange]
  refine ⟨⟨B, hmax.1, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact div_le_div_of_nonneg_right (hmax.2 hv) (Nat.cast_nonneg r)

/-- Selection and physical transfer for the excess-deficit disjunct of the sharp budget.
The working spectral dimension is the smaller of rank and corank. -/
theorem sharp_record_budget_of_excess_deficits (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (hGeometry : GeometryStatement c r q) (hr : 0 < r) (hrN : r ≤ Fintype.card ι)
    (hq : FeasibleLaw c r q) :
    let flip := decide (Fintype.card ι - r < r)
    let d := if flip then Fintype.card ι - r else r
    let t := fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
    d < (∑ j, (d - capacity c j)) →
    ∃ B, SpectralBudgetCertificate flip d (capacity c) t B ∧ SharpRecordBudget c r q B := by
  let flip := decide (Fintype.card ι - r < r)
  let d := if flip then Fintype.card ι - r else r
  let t := fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
  change d < (∑ j, (d - capacity c j)) →
    ∃ B, SpectralBudgetCertificate flip d (capacity c) t B ∧ SharpRecordBudget c r q B
  intro hdef
  have hsize : 2 * d ≤ ∑ j, capacity c j := by
    rw [capacity_total c]
    by_cases h : Fintype.card ι - r < r <;> simp [d, flip, h] <;> omega
  obtain ⟨a, i, k, hik, hia, hka, ha, hfit⟩ := excess_deficits_disjoint d (capacity c) hsize hdef
  have hd : 0 < d := by
    by_contra! hn
    have hzero : d = 0 := Nat.eq_zero_of_le_zero hn
    simp [hzero] at hdef
  let B := binaryTerm (capacity c i) (t i) + binaryTerm (capacity c k) (t k)
  have hcert : SpectralBudgetCertificate flip d (capacity c) t B :=
    Or.inr (Or.inl ⟨hd, hdef, a, i, k, hia.symm, hka.symm, hik, ha, hfit, rfl⟩)
  exact ⟨B, hcert, sharp_record_budget_of_disjoint c r q hGeometry hr hrN hq
    flip hik hia hka ha hfit.le⟩

end

end D5.S3.Quantum.Measurement.Auric
