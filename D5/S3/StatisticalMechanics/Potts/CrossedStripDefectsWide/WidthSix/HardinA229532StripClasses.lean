/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
class_relabel: proof_shape=bind-only; consumers=HardinA229532Strip.result
bond_relabel: proof_shape=bind-only; consumers=HardinA229532Strip.result
transition_counts: proof_shape=bind-only; consumers=HardinA229532Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripTop
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass10
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass11
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass12
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass13
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass14
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass15
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass16
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass17
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass18
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass19
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass20
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass21
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass22
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass23
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass24
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass25
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass26
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass27
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass28
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass29
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass30
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! Exact width-six HDA residual-budget transfer. -/
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
open HardinA233177Canonical (Canonical canonical_exists_unique)
private theorem class_relabel (e : Equiv.Perm (Fin 3)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, HardinA233172DiagonalStrip.boundaryClass,
    bondDefects, Function.comp_apply, ne_eq, e.injective.eq_iff]

private theorem bond_relabel (e : Equiv.Perm (Fin 3))
    (E : Finset (Fin 6 × Fin 6)) (p r : Row) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, ne_eq, e.injective.eq_iff]

theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 31,
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
    by_cases hs : s.val < 10
    · let j : Fin 10 := ⟨s.val, hs⟩
      have he : s = j.castAdd 21 := rfl
      rw [he]
      exact HardinA229532StripTop.transition_counts j p' d hv
    · obtain ⟨j, hj⟩ : ∃ j : Fin 21, s = j.natAdd 10 := by
        refine ⟨⟨s.val - 10, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp
        omega
      rw [hj]
      fin_cases j <;> first
      | exact HardinA229532StripClass10.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass11.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass12.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass13.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass14.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass15.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass16.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass17.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass18.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass19.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass20.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass21.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass22.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass23.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass24.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass25.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass26.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass27.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass28.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass29.transition_counts p' d hv hnormal
      | exact HardinA229532StripClass30.transition_counts p' d hv hnormal
  rw [he] at ht
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
  rw [← E.sum_comp] at ht
  change (∑ r : Row, if bondDefects between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
    cl (e ∘ r) (d.val - (bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d.val) s at ht
  simpa only [bond_relabel, class_relabel] using ht
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
