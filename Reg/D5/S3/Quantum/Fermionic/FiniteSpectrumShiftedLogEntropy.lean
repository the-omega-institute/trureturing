import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy

open _root_.D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

private abbrev signature : Signature where
  Params := Σ ι : Type u, Fintype ι
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] {a b : ι → ℝ},
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → (∑ i, a i) = (∑ i, b i) →
    (∀ s : ℝ, 0 < s → (∏ i, (s + b i)) ≤ ∏ i, (s + a i)) →
    R.readout () ⟨ι, inferInstance⟩ (-(∑ i, b i * Real.log (b i)))
      (-(∑ i, a i * Real.log (a i)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} Unit → ℝ := fun _ => 0
  exact h (a := a) (b := a) (fun _ => le_rfl) (fun _ => le_rfl) rfl
    (fun _ _ => le_rfl)

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena.{u} (type_of% (@entropy_le_of_shifted_product_le.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_le_of_shifted_product_le.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entropy_le_of_shifted_product_le.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy.entropy_le_of_shifted_product_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
