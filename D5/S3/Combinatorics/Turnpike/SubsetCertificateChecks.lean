/- GID: D5/S3/Combinatorics/Turnpike/SubsetCertificateChecks
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coverage and arithmetic bridge for all subset transport cuts -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetCertificatePair12
/-! Omega original.
# Coverage and arithmetic bridge for all subset transport cuts
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
noncomputable section

theorem numerator_rows : ∀ e : Interval 7, ∑ q, numerator e q = 50 := by
  decide +kernel

theorem flow_checks (τ : Triangle 7) (u v w : Fin 3)
    (huv : u < v) (hwu : w ≠ u) (hwv : w ≠ v) :
    ∀ U ∈ (positiveSupport (edge τ u)).powerset,
      ∃ L, PartialFlowCheck (numericAtoms τ) (fun z => numerator (edge τ z))
        u v w U L := by
  fin_cases u <;> fin_cases v <;> fin_cases w <;>
    simp_all [Fin.lt_def, Fin.ext_iff]
  · simpa using checks_01 τ
  · simpa using checks_02 τ
  · simpa using checks_12 τ

theorem all_subset_cuts : SubsetCuts y μ assignment := by
  classical
  apply subsetCuts_of_support assignment positiveSupport numericAtoms
  · intro e q
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · intro e q hq
    have hz : numerator e q = 0 := by
      simpa [positiveSupport] using hq
    simp [assignment,hz]
  · intro τ r hr
    obtain ⟨he,hg,hm⟩ := (numericAtoms_complete τ r).mp hr
    refine ⟨?_,hg,hm⟩
    change (values _ : ℝ) + values _ = values _
    exact_mod_cast he
  · intro τ u v w huv hwu hwv U hU V hV
    obtain ⟨L, hL⟩ := flow_checks τ u v w huv hwu hwv U hU
    have h := partialFlow_cut (numericAtoms τ) (fun z => numerator (edge τ z))
      u v w U L 50 hL (numerator_rows (edge τ v)) V
    have hu : (∑ q ∈ U, assignment (edge τ u) q) =
        (∑ q ∈ U, numerator (edge τ u) q : ℕ) / (50 : ℝ) := by
      simp [assignment, Nat.cast_sum, Finset.sum_div]
    have hv : (∑ q ∈ V, assignment (edge τ v) q) =
        (∑ q ∈ V, numerator (edge τ v) q : ℕ) / (50 : ℝ) := by
      simp [assignment, Nat.cast_sum, Finset.sum_div]
    have hw : (∑ q ∈ tableCompletion (numericAtoms τ) u v w U V,
        assignment (edge τ w) q) =
        (∑ q ∈ tableCompletion (numericAtoms τ) u v w U V,
          numerator (edge τ w) q : ℕ) / (50 : ℝ) := by
      simp [assignment, Nat.cast_sum, Finset.sum_div]
    rw [hu,hv,hw]
    have hh : ((∑ q ∈ U, numerator (edge τ u) q : ℕ) : ℝ) +
        (∑ q ∈ V, numerator (edge τ v) q : ℕ) ≤
          50 + (∑ q ∈ tableCompletion (numericAtoms τ) u v w U V,
            numerator (edge τ w) q : ℕ) := by exact_mod_cast h
    linarith
end
end Omega.Turnpike.SubsetCertificate
