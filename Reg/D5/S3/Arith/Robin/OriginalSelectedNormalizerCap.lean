import D5.S3.Arith.Robin.OriginalSelectedNormalizerCap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open _root_.D5.S3.Arith.Robin.OriginalFirstClockTransport
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.Arith.Robin.OriginalSelectedNormalizerCap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalSelectedNormalizerCap

abbrev signature : Signature where
  Params := Unit
  State _ := OriginalWindow
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => selectedDomain X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Icc (0 : ℝ) 1) (fun e => nomatch e)

/-- The exact full source telescope, with the actual set observed in both
the volume and the integral. The label window is neither shortened nor replaced. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀ (X : OriginalWindow), 0 ≤ X.labelStart →
    volume.real (V.readout () () X) ≤ X.labelStart ∧
      ∀ x : ℝ, 4 ≤ x →
        0 ≤ (∫ t in V.readout () () X, kernel t x) ∧
        (∫ t in V.readout () () X, kernel t x) ≤
          x ^ (-3 / 10 : ℝ) * X.labelStart

private theorem actual_law : arena.Law actual :=
  @original_selected_normalizer_cap

private theorem source_bridge :
    (type_of% (@original_selected_normalizer_cap)) ↔ arena.Law actual := Iff.rfl

private def emptyWindow : OriginalWindow where
  labelStart := 0
  labels := ∅
  complete_labels := by norm_num [originalLabelWindow, Nat.primesLE]
  prime_labels := by simp
  attained := by simp

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hbad := (h emptyWindow (by norm_num [emptyWindow])).1
  change volume.real (Icc (0 : ℝ) 1) ≤ 0 at hbad
  rw [Real.volume_real_Icc_of_le (by norm_num)] at hbad
  norm_num at hbad

private theorem whole_family_variation : Variation arena actual :=
  ⟨actual_law, rejected, rejected_fails⟩

private theorem whole_family_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_fails⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

/- The full source bridge, actual law, variation and sensitivity are proved.
A DependentFamily.Registration would additionally need actual observational
dependence: two attained OriginalWindows with unequal literal selectedDomain.
No such pair is supplied here. In particular a nonempty good-edge window is
not an assumption of the source theorem and is not manufactured for this audit.
Contract.Registration, lawful sourceSelection and canonical current binding
remain unfinished; no declared_validated status is asserted. -/

#print axioms source_bridge
#print axioms whole_family_variation
#print axioms whole_family_sensitivity

end Reg.D5.S3.Arith.Robin.OriginalSelectedNormalizerCap
