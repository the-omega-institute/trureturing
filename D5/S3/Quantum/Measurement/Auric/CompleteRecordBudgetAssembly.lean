/- GID: D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The case split produces a certificate and transports every certified maximum to the actual record. -/

import D5.S3.Quantum.Measurement.Auric.DisjointPhysicalBudget
import D5.S3.Quantum.Measurement.Auric.StrictCertificateBudgets
import D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary

/-! Exhaust the working trace cases and transfer every certified maximum to the record. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
  (effect_le_one eigenvalues_mem_unit entropyIntegrand)
open D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_other_labels (j : Fin 3) :
    ∃ i k : Fin 3, j ≠ i ∧ j ≠ k ∧ i ≠ k := by
  fin_cases j
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

private theorem exists_last_label {j i : Fin 3} (hji : j ≠ i) :
    ∃ k : Fin 3, j ≠ k ∧ i ≠ k := by
  obtain ⟨a, b, hja, hjb, hab⟩ := exists_other_labels j
  by_cases h : i = a
  · exact ⟨b, hjb, fun hib => hab (h.symm.trans hib)⟩
  · exact ⟨a, hja, h⟩

private theorem trace_le_effective_cap {d : ℕ} {m : Fin 3 → ℕ} {t : Fin 3 → ℝ}
    (ht : ∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ)) (htotal : ∑ j, t j = (d : ℝ))
    (j : Fin 3) : t j ≤ (min d (m j) : ℝ) := by
  have hd : t j ≤ (d : ℝ) := by
    rw [← htotal]
    exact single_le_sum (fun i _ => (ht i).1) (mem_univ j)
  have hmin : t j ≤ ((min d (m j) : ℕ) : ℝ) := by
    by_cases h : d ≤ m j
    · simpa only [min_eq_left h] using hd
    · simpa only [min_eq_right (le_of_not_ge h)] using (ht j).2
  simpa only [Nat.cast_min] using hmin

private theorem effective_cap_eq (d m : ℕ) :
    (min d m : ℝ) = (d : ℝ) - (d - m : ℕ) := by
  have h : min d m + (d - m) = d := by omega
  have h' : ((min d m : ℕ) : ℝ) + (d - m : ℕ) = (d : ℝ) := by exact_mod_cast h
  have he : ((min d m : ℕ) : ℝ) = (d : ℝ) - (d - m : ℕ) := by linarith only [h']
  simpa only [Nat.cast_min] using he

private theorem common_maximum_to_effectValues {d : ℕ} {m : Fin 3 → ℕ}
    {t : Fin 3 → ℝ} {B : ℝ} (h : Boundary.CommonMaximum (n := Fin d) m t B)
    (flip : Bool) : IsGreatest (effectValues flip d m t) B := by
  obtain ⟨⟨A, hA, hdir, hcomp⟩, hbound⟩ := h
  constructor
  · refine ⟨A, hA, ?_⟩
    cases flip
    · exact hdir
    · exact hcomp
  · rintro v ⟨C, hC, rfl⟩
    obtain ⟨heq, hle⟩ := hbound C hC
    cases flip
    · exact hle
    · change spectralSum (fun x => Real.negMulLog (1 - x)) C hC.1 ≤ B
      exact heq.symm.trans_le hle

private theorem zero_dimension_maximum (flip : Bool) (m : Fin 3 → ℕ) (t : Fin 3 → ℝ)
    (ht : ∀ j, 0 ≤ t j) (htotal : ∑ j, t j = 0) :
    IsGreatest (effectValues flip 0 m t) 0 := by
  have htzero (j : Fin 3) : t j = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun j _ => ht j)).mp htotal j (mem_univ j)
  let A : Fin 3 → Matrix (Fin 0) (Fin 0) ℂ := fun _ => 0
  have hA : Feasible m t A := by
    refine ⟨fun _ => Matrix.PosSemidef.zero, ?_, ?_, ?_⟩
    · ext i
      exact Fin.elim0 i
    · intro j
      simp [A, htzero j]
    · intro j
      simp [A]
  refine ⟨⟨A, hA, by simp [spectralSum]⟩, ?_⟩
  rintro v ⟨C, hC, rfl⟩
  simp [spectralSum]

/-- For admissible trace data in the smaller dimension, at least one case supplies a value. -/
theorem exists_spectral_budget_certificate (flip : Bool) (d : ℕ) (m : Fin 3 → ℕ)
    (t : Fin 3 → ℝ) (hsize : 2 * d ≤ ∑ j, m j)
    (ht : ∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ)) (htotal : ∑ j, t j = (d : ℝ)) :
    ∃ B, SpectralBudgetCertificate flip d m t B := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ j, l j
  by_cases hd : d = 0
  · exact ⟨0, Or.inl ⟨hd, rfl⟩⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  by_cases hdef : d < ∑ j, l j
  · obtain ⟨a, i, k, hik, hia, hka, ha, hfit⟩ := excess_deficits_disjoint d m hsize hdef
    exact ⟨_, Or.inr (Or.inl ⟨hdpos, hdef, a, i, k, hia.symm, hka.symm, hik, ha, hfit, rfl⟩)⟩
  have hcap : (∑ j, l j) ≤ d := le_of_not_gt hdef
  by_cases hsat : ∃ j, t j = (min d (m j) : ℝ)
  · obtain ⟨j, hj⟩ := hsat
    obtain ⟨i, k, hji, hjk, hik⟩ := exists_other_labels j
    exact ⟨_, Or.inr (Or.inr ⟨hdpos, hcap, Or.inl ⟨j, i, hji, hj, rfl⟩⟩)⟩
  by_cases hzero : ∃ j, t j = 0
  · obtain ⟨j, hj⟩ := hzero
    obtain ⟨i, k, hji, hjk, hik⟩ := exists_other_labels j
    exact ⟨_, Or.inr (Or.inr ⟨hdpos, hcap, Or.inr (Or.inl
      ⟨j, i, k, hji, hjk, hik, hj, rfl⟩)⟩)⟩
  have hstrict (j : Fin 3) : 0 < t j ∧ t j < (min d (m j) : ℝ) :=
    ⟨lt_of_le_of_ne (ht j).1 (fun h => hzero ⟨j, h.symm⟩),
      lt_of_le_of_ne (trace_le_effective_cap ht htotal j) (fun h => hsat ⟨j, h⟩)⟩
  have hupper (j : Fin 3) : t j < (d : ℝ) - (l j : ℝ) := by
    change t j < (d : ℝ) - (d - m j : ℕ)
    rw [← effective_cap_eq d (m j)]
    exact (hstrict j).2
  cases flip
  · obtain ⟨w, hw, hwt, hrow⟩ :=
      exists_direct_certificate d m t hcap (fun j => (hstrict j).1) hupper htotal
    refine ⟨allocationValue (entropyIntegrand false) l b (weightEntries w), ?_⟩
    exact Or.inr (Or.inr ⟨hdpos, hcap, Or.inr (Or.inr
      ⟨hstrict, w, hw, hwt, hrow, rfl⟩)⟩)
  · obtain ⟨w, k, hw, hk, hcol, hrow⟩ :=
      exists_complement_certificate d m t hcap (fun j => (hstrict j).1) hupper htotal
    refine ⟨allocationValue (entropyIntegrand true) l b (complementEntries w k), ?_⟩
    exact Or.inr (Or.inr ⟨hdpos, hcap, Or.inr (Or.inr
      ⟨hstrict, w, k, hw, hk, hcol, hrow, rfl⟩)⟩)

/-- Every supplied certificate gives an attained maximum of the selected spectral score. -/
theorem spectral_budget_certificate_maximum (flip : Bool) (d : ℕ) (m : Fin 3 → ℕ)
    (t : Fin 3 → ℝ) {B : ℝ} (ht : ∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ))
    (htotal : ∑ j, t j = (d : ℝ)) (hB : SpectralBudgetCertificate flip d m t B) :
    IsGreatest (effectValues flip d m t) B := by
  rcases hB with ⟨rfl, rfl⟩ | ⟨_, _, a, i, k, hai, hak, hik, ha, hfit, rfl⟩ | ⟨_, hcap, hB⟩
  · exact zero_dimension_maximum flip m t (fun j => (ht j).1) (by simpa using htotal)
  · exact disjoint_effects_statement d m t i k a hik hai.symm hak.symm ha hfit.le ht htotal flip
  rcases hB with ⟨j, i, hji, hj, rfl⟩ | ⟨j, i, k, hji, hjk, hik, hj, rfl⟩ | ⟨_, hstrict⟩
  · obtain ⟨k, hjk, hik⟩ := exists_last_label hji
    have hmax := Boundary.saturated_face_maximum (n := Fin d) m t hji hjk hik
      (by simpa only [Fintype.card_fin, Boundary.missing] using hcap)
      (fun j => (ht j).1) (by simpa only [Fintype.card_fin] using htotal)
      (by simpa only [Fintype.card_fin, Boundary.cap, Nat.cast_min] using hj)
    simpa only [Fintype.card_fin, Boundary.missing, Boundary.boundaryValue, binaryTerm]
      using common_maximum_to_effectValues hmax flip
  · have hmax := Boundary.zero_row_face_maximum (n := Fin d) m t hji hjk hik
      (by simpa only [Fintype.card_fin, Boundary.missing] using hcap)
      (fun j => (ht j).1)
      (by simpa only [Fintype.card_fin, Boundary.cap, Nat.cast_min]
        using trace_le_effective_cap ht htotal)
      (by simpa only [Fintype.card_fin] using htotal) hj
    simpa only [Fintype.card_fin, Boundary.missing, Boundary.boundaryValue, binaryTerm]
      using common_maximum_to_effectValues hmax flip
  · cases flip
    · obtain ⟨w, hw, hwt, hrow, rfl⟩ := hstrict
      exact direct_certificate_maximum d m t w hcap hw hwt hrow
    · obtain ⟨w, k, hw, hk, hcol, hrow, rfl⟩ := hstrict
      exact complement_certificate_maximum d m t w k hcap hw hk hcol hrow

private theorem feasible_effect_trace_data {d : ℕ} {m : Fin 3 → ℕ} {t : Fin 3 → ℝ}
    {A : Fin 3 → Matrix (Fin d) (Fin d) ℂ} (hA : Feasible m t A) :
    (∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ)) ∧ (∑ j, t j) = (d : ℝ) := by
  constructor
  · intro j
    let hAj := (hA.1 j).isHermitian
    let e := hAj.eigenvalues
    let S := (univ : Finset (Fin d)).filter (fun i => e i ≠ 0)
    have hrank : S.card = (A j).rank := by
      rw [hAj.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    have he (i : Fin d) : e i ∈ Set.Icc (0 : ℝ) 1 :=
      eigenvalues_mem_unit (hA.1 j) (effect_le_one A hA.1 hA.2.1 j) i
    have htrace : ∑ i, e i = t j := by
      rw [← hA.2.2.1 j, hAj.trace_eq_sum_eigenvalues, Complex.re_sum]
      rfl
    constructor
    · rw [← htrace]
      exact sum_nonneg fun i _ => (he i).1
    · calc
        t j = ∑ i, e i := htrace.symm
        _ = ∑ i ∈ S, e i := by
          symm
          apply sum_subset (filter_subset _ _)
          intro i hi hn
          by_contra hne
          exact hn (mem_filter.mpr ⟨hi, hne⟩)
        _ ≤ ∑ _i ∈ S, (1 : ℝ) := sum_le_sum fun i _ => (he i).2
        _ = (S.card : ℝ) := by simp
        _ ≤ (m j : ℝ) := by exact_mod_cast hrank.trans_le (hA.2.2.2 j)
  · calc
      (∑ j, t j) = (Matrix.trace (∑ j, A j)).re := by
        simp only [Matrix.trace_sum, Complex.re_sum, hA.2.2.1]
      _ = (d : ℝ) := by rw [hA.2.1]; simp

private theorem law_of_admissible_input (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (hGeometry : GeometryStatement c r q) (hr : 0 < r) (hrN : r ≤ Fintype.card ι)
    (ρ : DensityState ι) (hρ : InputAtLaw c r q ρ) : FeasibleLaw c r q := by
  have hval : D5.S3.Quantum.Measurement.Auric.EqualBlockProjection.gain c ρ ∈ gainValues c r q :=
    ⟨ρ, hρ, rfl⟩
  rw [hGeometry hr hrN false] at hval
  obtain ⟨v, ⟨A, hA, _⟩, _⟩ := hval
  have hA' : Feasible (capacity c) (fun j => (r : ℝ) * q j) A := hA
  obtain ⟨ht, htotal⟩ := feasible_effect_trace_data hA'
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨fun j => ⟨nonneg_of_mul_nonneg_right (ht j).1 hr', (ht j).2⟩, ?_⟩
  rw [← Finset.mul_sum] at htotal
  exact mul_left_cancel₀ hr'.ne' (htotal.trans (mul_one (r : ℝ)).symm)

/-- Assemble the spectral cases using the exact geometry range equality. -/
theorem complete_budget_of_geometry (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (hGeometry : GeometryStatement c r q) : CompleteBudgetStatement c r q := by
  intro hr hrN
  let flip := decide (Fintype.card ι - r < r)
  let d := if flip then Fintype.card ι - r else r
  let t := fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
  have hsize : 2 * d ≤ ∑ j, capacity c j := by
    rw [capacity_total c]
    by_cases h : Fintype.card ι - r < r <;> simp [d, flip, h] <;> omega
  have hsol (hq : FeasibleLaw c r q) :
      (∃ B, SpectralBudgetCertificate flip d (capacity c) t B) ∧
      ∀ B, SpectralBudgetCertificate flip d (capacity c) t B → SharpRecordBudget c r q B := by
    obtain ⟨ht, htotal⟩ := working_traces_of_law c r q hrN hq flip
    refine ⟨exists_spectral_budget_certificate flip d (capacity c) t hsize ht htotal, ?_⟩
    intro B hB
    have hmax := spectral_budget_certificate_maximum flip d (capacity c) t ht htotal hB
    apply physical_of_gain c r q B hr
    rw [hGeometry hr hrN flip]
    refine ⟨⟨B, hmax.1, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact div_le_div_of_nonneg_right (hmax.2 hv) (Nat.cast_nonneg r)
  refine ⟨⟨?_, ?_⟩, hsol⟩
  · rintro ⟨ρ, hρ⟩
    exact law_of_admissible_input c r q hGeometry hr hrN ρ hρ
  · intro hq
    obtain ⟨⟨B, hB⟩, hall⟩ := hsol hq
    obtain ⟨ρ, hρ, _⟩ := hall B hB
    exact ⟨ρ, hρ⟩

end

end D5.S3.Quantum.Measurement.Auric
