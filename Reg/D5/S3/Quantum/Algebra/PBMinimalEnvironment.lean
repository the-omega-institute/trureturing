import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.PBMinimalEnvironment
import Reg.Support.SingleDependentReadout

/-! Source audit of the endpoint-rank observation in the minimal-environment theorem. -/

namespace Reg.D5.S3.Quantum.Algebra.PBMinimalEnvironment

open _root_.D5.S3.Quantum.Algebra.PBMinimalEnvironment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Matrix Actor Actor ℂ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ M => M.rank) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M₀ M₁ M₂ : Matrix Actor Actor ℂ),
    let Γ := momentGram M₀ M₁ M₂
    let r := R.readout () () M₀
    let k := Γ.rank
    ((∃ (m : ℕ) (D : Matrix (Fin m) (Fin m) ℂ) (V : Matrix Actor (Fin m) ℂ),
        Realizes D V M₀ M₁ M₂) ↔
      Γ.PosSemidef ∧ M₀.toEuclideanLin.ker = M₂.toEuclideanLin.ker) ∧
    ((Γ.PosSemidef ∧ M₀.toEuclideanLin.ker = M₂.toEuclideanLin.ker) →
      (∃ (D : Matrix (Fin k) (Fin k) ℂ) (V : Matrix Actor (Fin k) ℂ),
        IsUnit D ∧ Realizes D V M₀ M₁ M₂ ∧ PhysicalCompatibility D V M₁) ∧
      M₂.rank = r ∧ r ≤ k ∧ k ≤ 2 * r ∧ 2 * r ≤ 4) ∧
    (∀ (m : ℕ) (D : Matrix (Fin m) (Fin m) ℂ) (V : Matrix Actor (Fin m) ℂ),
      Realizes D V M₀ M₁ M₂ →
        M₀.IsHermitian ∧ M₁.IsHermitian ∧ M₂.IsHermitian ∧
        k ≤ D.rank ∧ D.rank ≤ m ∧ LabeledGramIdentification D V M₀ M₁ M₂)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (momentGram 0 0 0).PosSemidef := by
    simpa [momentGram, Matrix.fromBlocks_zero] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Actor ⊕ Actor) (Actor ⊕ Actor) ℂ).PosSemidef)
  have hh := ((h 0 0 0).2.1 ⟨hp, rfl⟩).2.1
  have hbad : (0 : Matrix Actor Actor ℂ).rank = 1 := hh
  simp at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : Matrix Actor Actor ℂ).rank ≠ (1 : Matrix Actor Actor ℂ).rank
  simp

def source_registration : Registration arena (type_of% @pb_three_moment_minimal_realization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pb_three_moment_minimal_realization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pb_three_moment_minimal_realization) (Realization signature) Unit Unit := {
  unitName := .str `D5.S3.Quantum.Algebra.PBMinimalEnvironment.pb_three_moment_minimal_realization
    "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.rank) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PBMinimalEnvironment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Algebra.PBMinimalEnvironment
