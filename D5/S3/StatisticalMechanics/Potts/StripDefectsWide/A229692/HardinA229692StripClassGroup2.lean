/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup2
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
transition_counts12: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts13: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts14: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts15: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts16: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts17: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup2
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229692StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts12 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨44, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 44 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts13 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨45, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 45 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts14 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨46, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 46 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts15 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨47, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 47 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts16 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨48, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 48 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts17 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨49, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 49 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup2
