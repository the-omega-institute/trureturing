import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
import Reg.Support.DependentFamily

/-! Source-bound audit of the amplitude-damping Choi family in the cloning obstruction. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning

open _root_.D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder
open Matrix
open _root_.D5.S3.Quantum.Recovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the Choi matrix as the damping parameter varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ γ => adChoi γ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℂ) • 1) (fun e => nomatch e)

/-- Retain every measurement, channel, positivity, and normalization condition. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ N M : ℕ, 1 ≤ M → ¬ ∃ (L : ℕ)
    (T : Fin L → Matrix (Fin N → Fin 2 × Fin 2) (Fin N → Fin 2 × Fin 2) ℂ)
    (K : Fin L → Matrix (Fin M → Fin 2 × Fin 2) (Fin M → Fin 2 × Fin 2) ℂ),
    (∀ ℓ, IsChannelChoi (K ℓ)) ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      (∀ ℓ, 0 ≤ Matrix.trace (T ℓ * ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2)
          (fun _ : Fin N => adChoi γ))) ∧
      (∑ ℓ, Matrix.trace (T ℓ * ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2)
          (fun _ : Fin N => adChoi γ))) = 1 ∧
      (∑ ℓ, Matrix.trace (T ℓ * ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2)
          (fun _ : Fin N => adChoi γ)) • K ℓ) =
        ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2)
          (fun _ : Fin M => R.readout () () γ)

private theorem rejected_pow_one :
    ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2) (T := fun _ => Fin 2 × Fin 2)
      (fun _ : Fin 1 => (1 / 2 : ℂ) • 1) = (1 / 2 : ℂ) • 1 := by
  ext x y
  have hxy : x = y ↔ x 0 = y 0 := by
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext i
      fin_cases i
      exact h
  simp [ProductPrefixRigidity.productMap, Matrix.one_apply, ← hxy]

private theorem mixed_channel :
    IsChannelChoi ((1 / 2 : ℂ) •
      (1 : Matrix (Fin 1 → Fin 2 × Fin 2) (Fin 1 → Fin 2 × Fin 2) ℂ)) := by
  constructor
  · exact Matrix.PosSemidef.one.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2)
  · intro r r'
    rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
    by_cases h : r 0 = r' 0 <;>
      norm_num [Matrix.one_apply, funext_iff, Fin.forall_fin_one, Fin.sum_univ_two,
        Equiv.funUnique, Equiv.piUnique, h]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h 0 1 (by norm_num)
  refine ⟨1, fun _ => 1, fun _ => (1 / 2 : ℂ) • 1, ?_, ?_⟩
  · intro _
    exact mixed_channel
  · intro γ _
    have hp : ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2)
          (fun _ : Fin 0 => adChoi γ) = 1 := by
      ext x y
      simp [ProductPrefixRigidity.productMap, Matrix.one_apply, Subsingleton.elim x y]
    dsimp only [rejected, realize]
    rw [rejected_pow_one]
    simp [hp, Matrix.trace]

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hentry := congrArg (fun J => J (1, 0) (1, 0)) he
  norm_num [actual, realize, adChoi, Fin.sum_univ_two] at hentry

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
      (@_root_.D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ γ => adChoi γ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
      name := `D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "body", "arg", "arg", "arg", "arg", "body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
