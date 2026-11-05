import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination
import Reg.Support.DependentFamily

/-! Source-bound audit of the optimal success bound for sequences without repetition. -/

namespace Reg.D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination

open _root_.D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open _root_.Matrix
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the optimal success bound as the overlap varies at fixed sequence dimensions. -/
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => value p.1 p.2 s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Keep every hypothesis and attainment clause, varying the upper-bound coordinate. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    ∀ (N k : ℕ), 3 ≤ N → 2 ≤ k → k ≤ N →
    ∀ s : ℝ, 0 < s → s < 1 →
    ∀ ψ : Fin N → Fin N → ℂ, IsEquiangular ψ s →
      (∀ E E₀, IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ →
        averageSuccess (productState (k := k) ψ) E ≤ r.readout () ⟨N, k⟩ s) ∧
      ∃ F d E E₀, IsProductProtocol (k := k) F d E E₀ ∧
        IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ ∧
        averageSuccess (productState (k := k) ψ) E = value N k s

private def testEnsemble (i j : Fin 3) : ℂ :=
  if i = j then 1 / 3 else 2 / 3

private theorem testEnsemble_equiangular : IsEquiangular testEnsemble (8 / 9) := by
  constructor
  · intro i
    fin_cases i <;>
      norm_num [testEnsemble, dotProduct, Fin.sum_univ_succ, map_ofNat]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [testEnsemble, dotProduct, Fin.sum_univ_succ, map_ofNat] at *

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : IsUnambiguousMeasurement (productState (k := 2) testEnsemble)
      (fun _ => 0) 1 := by
    refine ⟨fun _ => Matrix.PosSemidef.zero, Matrix.PosSemidef.one, ?_, ?_⟩
    · simp
    · intro x y _
      simp
  have hbad := (h 3 2 (by norm_num) (by norm_num) (by norm_num)
    (8 / 9) (by norm_num) (by norm_num) testEnsemble testEnsemble_equiangular).1
      (fun _ => 0) 1 hzero
  norm_num [averageSuccess, readout, rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, 2⟩, 1 / 2, 1 / 3, ?_⟩
  change value 3 2 (1 / 2) ≠ value 3 2 (1 / 3)
  norm_num [value]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination.unit
  realizationName :=
    `Reg.D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p s => value p.1 p.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination
    definition := some {
      owner := `D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination
      name := `D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination
