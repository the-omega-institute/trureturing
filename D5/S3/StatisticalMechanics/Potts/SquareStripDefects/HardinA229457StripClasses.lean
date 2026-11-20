/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
class_relabel: proof_shape=bind-only; consumers=transition_counts, HardinA229604StripClasses.transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229457Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass0
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass1
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass2
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass3
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass4
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass5
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass6
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass7

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
open DefectTransfer (bondDefects)
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
  (bond_relabel)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229457StripData
open HardinA233177Canonical (canonical_exists_unique)
theorem class_relabel (e : Equiv.Perm (Fin 3)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl,
    D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses.class_relabel,
    bond_relabel, ProperTransfer.cl, HardinA233127SquareStrip.boundaryClass,
    Function.comp_apply, e.injective.eq_iff]

theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 42,
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  intro p d hp s
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ := canonical_exists_unique p
  have hv : Valid p' d.val := by
    rw [he]
    simpa only [Valid, D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData.Valid, bond_relabel] using hp
  have ht : (∑ r : Row, if bondDefects ProperTransfer.between p' r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p' r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p' d.val) s := by
    by_cases hs : s.val < 10
    · let j : Fin 10 := ⟨s.val, hs⟩
      have he : s = j.castAdd 32 := rfl
      rw [he]
      exact HardinA229457StripCut.active_counts j p' d hv
    · obtain ⟨j, hj⟩ : ∃ j : Fin 32, s = j.natAdd 10 := by
        refine ⟨⟨s.val - 10, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp
        omega
      rw [hj]
      fin_cases j <;> first
      | exact HardinA229457StripClass0.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass0.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass0.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass0.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass1.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass1.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass1.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass1.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass2.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass2.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass2.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass2.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass3.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass3.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass3.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass3.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass4.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass4.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass4.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass4.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass5.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass5.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass5.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass5.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass6.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass6.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass6.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass6.transition_counts 3 p' d hv hnormal
      | exact HardinA229457StripClass7.transition_counts 0 p' d hv hnormal
      | exact HardinA229457StripClass7.transition_counts 1 p' d hv hnormal
      | exact HardinA229457StripClass7.transition_counts 2 p' d hv hnormal
      | exact HardinA229457StripClass7.transition_counts 3 p' d hv hnormal
  rw [he] at ht
  let g : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
  rw [← g.sum_comp] at ht
  change (∑ r : Row, if bondDefects ProperTransfer.between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
    cl (e ∘ r) (d.val - (bondDefects ProperTransfer.between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d.val) s at ht
  simpa only [bond_relabel, class_relabel] using ht

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
