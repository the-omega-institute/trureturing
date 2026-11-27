import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts
import Reg.Support.DependentFamily

/-! Dependence of the single-coordinate spectrum on the seed budget. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 ≤ k) (fun e => nomatch e)

def emptySpectrum : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (i : Fin 4),
    RealizableSeedCounts 2 k (fun j => if j = i then 4 else 0) ↔ R.readout () () k

private theorem empty_spectrum_fails : ¬ arena.Law emptySpectrum := by
  intro law
  exact (law 2 0).mp ((exact_four_sparse 2 0).mpr le_rfl)

def family : Registration arena (type_of% exact_four_sparse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_four_sparse, emptySpectrum, empty_spectrum_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨emptySpectrum, ?_, rfl, empty_spectrum_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 1, 2, ?_⟩
    change ((2 : ℕ) ≤ 1) ≠ ((2 : ℕ) ≤ 2)
    simp

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_four_sparse (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts.budgetThreshold
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => 2 ≤ k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts
