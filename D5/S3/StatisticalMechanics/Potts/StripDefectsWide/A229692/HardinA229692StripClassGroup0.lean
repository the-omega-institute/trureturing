/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup0
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
transition_counts0: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts1: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts2: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts3: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts4: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts5: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup0
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229692StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts0 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨32, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 32 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts1 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨33, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 33 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts2 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨34, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 34 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts3 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨35, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 35 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts4 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨36, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 36 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts5 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨37, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 37 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup0
