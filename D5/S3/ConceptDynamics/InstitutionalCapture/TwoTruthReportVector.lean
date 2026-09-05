/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/TwoTruthReportVector
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/TwoTruthReportVector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: At the half-honest boundary, one report vector is admissible for both Boolean truths. -/

import D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery
import Mathlib.Data.Fintype.Fin

/- Library-search audit trail (2026-09-05):
   * D5 searches for both-truth report bounds found the construction only
     inside the proof of `deterministic_recovery_impossible`; no public theorem
     exposes the common report vector and its two bounds.
   * The canonical `byzantineCount` primitive is reused from
     `ByzantineMajorityRecovery`; no report-counting primitive is restated.
   * Pinned Mathlib searches for Byzantine report vectors and two compatible
     truths found no domain theorem. `Fin.card_filter_val_lt` and
     `Finset.card_filter_add_card_filter_not` supply the finite counts.
   * GitHub Lean-code search for `byzantineCount` exited 0 with no hits.
   * The complete construction compiled in
     `/private/tmp/w73a38-two-truth-report-vector-probe.lean` with exit 0. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.TwoTruthReportVector

open D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery

/-- If the population is at most twice the allowed fault bound, one report
vector has at most `f` disagreements with each of the two Boolean truths. -/
private theorem ambiguous_report_bounds
    {n f : Nat} (threshold : n <= 2 * f) :
    Exists fun reports : Fin n -> Bool =>
      byzantineCount reports false <= f /\
        byzantineCount reports true <= f := by
  by_cases small : n <= f
  · refine ⟨fun _ => false, ?_, ?_⟩
    · simp [byzantineCount]
    · simpa [byzantineCount] using small
  · have f_lt_n : f < n := Nat.lt_of_not_ge small
    let reports : Fin n -> Bool := fun reporter => decide (reporter < f)
    have true_count :
        (Finset.univ.filter fun reporter => reports reporter = true).card = f := by
      simp [reports, Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt f_lt_n)]
    have false_bound : byzantineCount reports false <= f := by
      simpa [byzantineCount] using true_count.le
    have partition :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (fun reporter => reports reporter = true)
    have partition_count :
        (Finset.univ.filter fun reporter => reports reporter = true).card +
          (Finset.univ.filter fun reporter => Not (reports reporter = true)).card = n := by
      simpa using partition
    have true_bound : byzantineCount reports true <= f := by
      have mismatch_count : byzantineCount reports true = n - f := by
        simp only [byzantineCount, ne_eq]
        omega
      omega
    exact ⟨reports, false_bound, true_bound⟩

/-- At the half-honest boundary, two disjoint groups of `n - f` reporters can
support opposite Boolean truth worlds through one shared report vector. -/
theorem two_truth_report_vector_exists
    {n f : Nat} (threshold : n <= 2 * f) :
    Exists fun H0 : Finset (Fin n) =>
      Exists fun H1 : Finset (Fin n) =>
        Disjoint H0 H1 /\
          H0.card = n - f /\
          H1.card = n - f /\
          Exists fun reports : Fin n -> Bool =>
            (forall reporter, reporter ∈ H0 -> reports reporter = false) /\
              (forall reporter, reporter ∈ H1 -> reports reporter = true) /\
              byzantineCount reports false <= f /\
              byzantineCount reports true <= f := by
  obtain ⟨reports, false_bound, true_bound⟩ := ambiguous_report_bounds threshold
  let falseReports := Finset.univ.filter fun reporter => reports reporter = false
  let trueReports := Finset.univ.filter fun reporter => reports reporter = true
  have false_partition :
      falseReports.card + byzantineCount reports false = n := by
    simpa [falseReports, byzantineCount] using
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (fun reporter => reports reporter = false)
  have true_partition :
      trueReports.card + byzantineCount reports true = n := by
    simpa [trueReports, byzantineCount] using
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (fun reporter => reports reporter = true)
  have false_card : n - f <= falseReports.card := by omega
  have true_card : n - f <= trueReports.card := by omega
  obtain ⟨H0, H0_subset, H0_card⟩ := Finset.exists_subset_card_eq false_card
  obtain ⟨H1, H1_subset, H1_card⟩ := Finset.exists_subset_card_eq true_card
  have H0_reports (reporter : Fin n) (membership : reporter ∈ H0) :
      reports reporter = false :=
    (Finset.mem_filter.mp (H0_subset membership)).2
  have H1_reports (reporter : Fin n) (membership : reporter ∈ H1) :
      reports reporter = true :=
    (Finset.mem_filter.mp (H1_subset membership)).2
  have sets_disjoint : Disjoint H0 H1 := by
    refine Finset.disjoint_left.mpr ?_
    intro reporter in_H0 in_H1
    exact Bool.false_ne_true ((H0_reports reporter in_H0).symm.trans
      (H1_reports reporter in_H1))
  exact ⟨H0, H1, sets_disjoint, H0_card, H1_card, reports,
    H0_reports, H1_reports, false_bound, true_bound⟩

/-- Two reporters with one allowed disagreement admit disjoint honest groups
supporting opposite Boolean truths through the same report vector. -/
example :
    Exists fun H0 : Finset (Fin 2) =>
      Exists fun H1 : Finset (Fin 2) =>
        Disjoint H0 H1 /\ H0.card = 1 /\ H1.card = 1 /\
          Exists fun reports : Fin 2 -> Bool =>
            (forall reporter, reporter ∈ H0 -> reports reporter = false) /\
              (forall reporter, reporter ∈ H1 -> reports reporter = true) /\
              byzantineCount reports false <= 1 /\
              byzantineCount reports true <= 1 := by
  exact two_truth_report_vector_exists (n := 2) (f := 1) (by decide)

#print axioms two_truth_report_vector_exists

end D5.S3.ConceptDynamics.InstitutionalCapture.TwoTruthReportVector
