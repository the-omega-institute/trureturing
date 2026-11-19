/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup5
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup5
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
transition_counts30: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts31: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts32: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts33: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts34: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
transition_counts35: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup5
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229692StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts30 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨62, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 62 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts31 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨63, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 63 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts32 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨64, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 64 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts33 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨65, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 65 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts34 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨66, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 66 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


/-- The appended exhausted-budget output class, for canonical boundaries. -/
theorem transition_counts35 : ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨67, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = T (cl p d.val) 67 := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +revert +kernel


end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup5
