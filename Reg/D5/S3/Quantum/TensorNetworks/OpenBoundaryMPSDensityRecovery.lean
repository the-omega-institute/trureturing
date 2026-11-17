import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
import Reg.Support.DependentFamily

/-! Source-faithful audit of the observable chart predicate. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery

open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Bond Word wordMatrix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, (Word (3 + m) → ℂ) → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := (Word (3 + m) → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m predicates => predicates m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

def originalStatement : Prop :=
  ∀ (m : ℕ) (ψ φ : Word (3 + m) → ℂ),
    ψ ∈ openBoundaryMPS (3 + m) → φ ∈ openBoundaryMPS (3 + m) →
    ObservableChart m ψ →
    (rawPrefix 3 m φ = rawPrefix 3 m ψ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (ψ φ : Word (3 + m) → ℂ),
    ψ ∈ openBoundaryMPS (3 + m) → φ ∈ openBoundaryMPS (3 + m) →
    R.readout () m ObservableChart ψ →
    (rawPrefix 3 m φ = rawPrefix 3 m ψ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ)

theorem source_equivalence : originalStatement ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := observable_chart_phase_recovery

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ _ => False), (fun _ _ => True), ?_⟩
  intro he
  have hbad := congrFun he (0 : Word 3 → ℂ)
  exact Eq.mpr hbad trivial

private def ghzCore : Fin 2 → Bond := ![!![1, 0; 0, 0], !![0, 0; 0, 1]]
private def ghz (c : ℂ) : Word 4 → ℂ :=
  mpsState 4 (ghzCore 0) (ghzCore 1) ![1, 1] ![1, c]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmem (c : ℂ) : ghz c ∈ openBoundaryMPS 4 := ⟨_, _, _, _, rfl⟩
  have hraw : rawPrefix 3 1 (ghz (-1)) = rawPrefix 3 1 (ghz 1) := by
    have hcolumns (c : ℂ) : amplitudeColumns 3 1 (ghz c) =
        prefixMap ghzCore ![1, 1] 3 * tailMap ghzCore ![1, c] 1 := by
      ext u b
      change dotProduct ![1, 1]
          ((List.ofFn fun j => ghzCore ((Fin.append u b) j)).prod *ᵥ ![1, c]) =
        dotProduct (![1, 1] ᵥ* wordMatrix ghzCore u) (wordMatrix ghzCore b *ᵥ ![1, c])
      have hw : (List.ofFn fun j => ghzCore ((Fin.append u b) j)).prod =
          wordMatrix ghzCore u * wordMatrix ghzCore b := by
        simp [wordMatrix, List.ofFn_succ, Fin.append, Fin.addCases, Matrix.mul_assoc]
        rfl
      rw [hw, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have htail : tailMap ghzCore ![1, (-1 : ℂ)] 1 *
          (tailMap ghzCore ![1, (-1 : ℂ)] 1)ᴴ =
        tailMap ghzCore ![1, (1 : ℂ)] 1 * (tailMap ghzCore ![1, (1 : ℂ)] 1)ᴴ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tailMap]
      rw [← (Fin.consEquiv (fun _ : Fin 1 => Fin 2)).sum_comp,
        ← (Fin.consEquiv (fun _ : Fin 1 => Fin 2)).sum_comp]
      fin_cases i <;> fin_cases j <;>
        norm_num [Fintype.sum_prod_type, wordMatrix, List.ofFn_succ,
          Fin.consEquiv_apply, ghzCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp only [rawPrefix, hcolumns, Matrix.conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using
      congrArg (fun X => prefixMap ghzCore ![1, 1] 3 * X *
        (prefixMap ghzCore ![1, 1] 3)ᴴ) htail
  obtain ⟨z, _, hz⟩ := (h 1 (ghz 1) (ghz (-1)) (hmem 1) (hmem (-1)) trivial).mp hraw
  have h0 := congrFun hz (fun _ => 0)
  have h1 := congrFun hz (fun _ => 1)
  norm_num [ghz, ghzCore, mpsState, List.ofFn_succ, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h0 h1
  exact (by norm_num : (-1 : ℂ) ≠ 1) (h1.trans h0.symm)

def source_registration : Registration arena originalStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨observable_chart_phase_recovery, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@observable_chart_phase_recovery)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m predicates => predicates m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
