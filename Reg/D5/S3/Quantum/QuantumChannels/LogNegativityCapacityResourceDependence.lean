import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence

namespace Reg.D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open _root_.D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
open LeanInformationAudit Matrix
open scoped Kronecker ComplexOrder

universe u_1 u_2
noncomputable section

/-- The factor types determine the joint matrix space. -/
abbrev signature : Signature where
  Params := Σ _A : Type u_1, Type u_2
  State p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization (signature.{u_1,u_2}) :=
  realize signature (fun _ _ σ i j => σ (i.1, j.2) (j.1, i.2)) (fun e => nomatch e)

def rejected : Realization (signature.{u_1,u_2}) :=
  realize signature (fun _ _ _ _ _ => -1) (fun e => nomatch e)

/-- All finite dictionaries, the separability premise and positivity are retained. -/
abbrev arena : Arena where
  signature := signature.{u_1,u_2}
  Law O := ∀ {A : Type u_1} {B : Type u_2} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (σ : Matrix (A × B) (A × B) ℂ),
    IsSeparable σ → (O.readout () ⟨A, B⟩ σ).PosSemidef

private theorem rejected_law : ¬ arena.{u_1,u_2}.Law rejected := by
  intro h
  let A := ULift.{u_1} Unit
  let B := ULift.{u_2} Unit
  have hs : IsSeparable (1 : Matrix (A × B) (A × B) ℂ) := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, by simp, by simp, ?_, ?_⟩
    · intro i
      exact ⟨⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩,
        ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩⟩
    · simp
  have hp := h (1 : Matrix (A × B) (A × B) ℂ) hs
  have hd := hp.diag_nonneg (i := (ULift.up (), ULift.up ()))
  change (0 : ℂ) ≤ -1 at hd
  norm_num at hd

private theorem actual_dependence : ObservationalDependence signature.{u_1,u_2} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Unit, ULift.{u_2} Unit⟩, 0, (fun _ _ => 1), ?_⟩
  intro he
  have hd := congrFun (congrFun he (ULift.up (), ULift.up ())) (ULift.up (), ULift.up ())
  change (0 : ℂ) = 1 at hd
  exact zero_ne_one hd

private theorem actual_sensitivity : Sensitivity arena.{u_1,u_2} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u_1,u_2} (type_of% (@separable_ppt.{u_1,u_2})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separable_ppt, rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@separable_ppt.{u_1,u_2}) (Realization signature.{u_1,u_2}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
