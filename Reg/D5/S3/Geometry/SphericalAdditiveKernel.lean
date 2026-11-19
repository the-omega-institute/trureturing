import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.SphericalAdditiveKernel

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.SphericalAdditiveKernel

namespace Reg.D5.S3.Geometry.SphericalAdditiveKernel

universe u

structure Parameters where
  E : Type u
  [group : NormedAddCommGroup E]

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => by letI := p.group; exact ‖x‖) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : AddSubgroup E) {r : ℝ}, 0 < r →
    (∀ x : E, R.readout () ⟨E⟩ x = r → x ∈ K) →
    (∀ x : E, R.readout () ⟨E⟩ x = r / 2 → x ∉ K) →
    Module.finrank ℝ E ≤ 1

private theorem bridge : (type_of% (@finrank_le_one_of_sphere_mem.{u})) ↔
    arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℝ (ULift.{u} (Fin 2))
  have hh := h (E := E) (⊥ : AddSubgroup E) (r := 1) (by norm_num)
    (by intro x hx; change (0 : ℝ) = 1 at hx; norm_num at hx)
    (by intro x hx; change (0 : ℝ) = 1 / 2 at hx; norm_num at hx)
  norm_num [E] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℝ⟩, ULift.up 0, ULift.up 1, ?_⟩
  change ‖(0 : ℝ)‖ ≠ ‖(1 : ℝ)‖
  norm_num

def family : Registration arena.{u} (type_of% (@finrank_le_one_of_sphere_mem.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@finrank_le_one_of_sphere_mem.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finrank_le_one_of_sphere_mem.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.SphericalAdditiveKernel.unit
  realizationName := `Reg.D5.S3.Geometry.SphericalAdditiveKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => by letI := p.group; exact ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.SphericalAdditiveKernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "domain", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "domain", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Geometry.SphericalAdditiveKernel
