/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.finite_certificate
   digest: Exact width-five two-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229634Strip.result)
class_relabel: proof_shape=bind-only; consumers=transition_counts
bond_relabel: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229634Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripCut
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass0
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass1
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass2
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass3
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass4
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass5
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass6
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass7
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass8
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass9
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass10
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass11
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass12

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClasses
open DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA233177Canonical (Canonical canonical_exists_unique)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229634StripData
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefects
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData (Row horizontal between)
private theorem class_relabel (e : Equiv.Perm (Fin 3)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, HardinA229531StripData.cl, HardinA233126SquareStrip.boundaryClass,
    bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem bond_relabel (e : Equiv.Perm (Fin 3))
    (E : Finset (Fin 5 × Fin 5)) (p r : Row) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

theorem transition_counts : ∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 33,
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  intro p d hp s
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ := canonical_exists_unique p
  have hv : Valid p' d.val := by
    rw [he]
    simpa only [Valid, bond_relabel] using hp
  have ht : (∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p' r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p' d.val) s := by
    by_cases hs : s.val < 20
    · let j : Fin 20 := ⟨s.val, hs⟩
      have he : s = j.castAdd 13 := rfl
      rw [he]
      exact HardinA229634StripCut.inherited_counts p' d hv j
    · interval_cases s <;> first
      | exact HardinA229634StripClass0.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass1.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass2.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass3.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass4.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass5.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass6.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass7.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass8.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass9.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass10.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass11.transition_counts p' d hv hnormal
      | exact HardinA229634StripClass12.transition_counts p' d hv hnormal
  rw [he] at ht
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 5 => e
  rw [← E.sum_comp] at ht
  change (∑ r : Row, if bondDefects between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
    cl (e ∘ r) (d.val - (bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d.val) s at ht
  simpa only [bond_relabel, class_relabel] using ht
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClasses
