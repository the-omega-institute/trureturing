/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229604Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass0
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass1
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass2
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass3
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass4
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass5
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass6
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass7
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass8
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass9
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass10
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass11
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass12
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass13
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass14
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass15
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass16
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass17
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass18
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass19
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass20
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass21
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass22
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass23
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass24
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass25
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Last.HardinA229604StripClass26

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripClasses
open DefectTransfer (bondDefects)
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
  (bond_relabel)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229604StripData
open HardinA233177Canonical (canonical_exists_unique)
theorem transition_counts : ∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 96,
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  intro p d hp s
  by_cases hs : s.val < 42
  · let j : Fin 42 := ⟨s.val, hs⟩
    have he : s = j.castAdd 54 := rfl
    rw [he]
    exact HardinA229604StripCut.leading_counts p d hp j
  · obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ := canonical_exists_unique p
    have hv : Valid p' d.val := by
      rw [he]
      simpa only [Valid, bond_relabel] using hp
    have ht : (∑ r : Row, if bondDefects ProperTransfer.between p' r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects ProperTransfer.between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p' d.val) s := by
      obtain ⟨j, hj⟩ : ∃ j : Fin 54, s = j.natAdd 42 := by
        refine ⟨⟨s.val - 42, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp
        omega
      rw [hj]
      fin_cases j <;> first
      | exact TwoDefects.First.HardinA229604StripClass0.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass0.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass1.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass1.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass2.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass2.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass3.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass3.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass4.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass4.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass5.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass5.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass6.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass6.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass7.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass7.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass8.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass8.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass9.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass9.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass10.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass10.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass11.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass11.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass12.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass12.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass13.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.First.HardinA229604StripClass13.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass14.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass14.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass15.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass15.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass16.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass16.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass17.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass17.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass18.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass18.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass19.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass19.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass20.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass20.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass21.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass21.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass22.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass22.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass23.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass23.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass24.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass24.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass25.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass25.transition_counts 1 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass26.transition_counts 0 p' d hv hnormal
      | exact TwoDefects.Last.HardinA229604StripClass26.transition_counts 1 p' d hv hnormal
    rw [he] at ht
    let g : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
    rw [← g.sum_comp] at ht
    change (∑ r : Row, if bondDefects ProperTransfer.between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
      cl (e ∘ r) (d.val - (bondDefects ProperTransfer.between (e ∘ p) (e ∘ r) +
        bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
      T (cl (e ∘ p) d.val) s at ht
    simpa only [cl, HardinA229457StripClasses.class_relabel, bond_relabel,
      Function.comp_apply, ne_eq, e.injective.eq_iff] using ht

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripClasses
