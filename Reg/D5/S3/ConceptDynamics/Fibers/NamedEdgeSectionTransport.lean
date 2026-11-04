import D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
import Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
open Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

namespace Reg.D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
universe u v w

abbrev arena : Arena where
  signature := predicateSignature.{w}
  Law q := ∀ {V : Type u} {E : Type v} {s t : E → V} {F : V → Type w}
    [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℂ (F a)]
    (U : ∀ e, F (s e) ≃ₗᵢ[ℂ] F (t e)) (r : V)
    (hc : ∀ a, Nonempty (NamedPath s t r a)),
    ∃ ev : NamedSection (underlying U) ≃ holonomyKernel U r,
      (∀ σ, q.readout () ⟨F r, fun y => y = σ.1 r⟩ (ev σ).1) ∧
      (∀ x a (p : NamedPath s t r a), (ev.symm x).1 a = unitaryTransport U p x.1) ∧
      (∀ (σ : NamedSection (underlying U)) a, ‖σ.1 a‖ = ‖σ.1 r‖) ∧
      (∀ σ τ, ‖(ev σ).1 - (ev τ).1‖ = ‖σ.1 r - τ.1 r‖) ∧
      ((∀ a (p q : NamedPath s t r a) (x : F r),
          unitaryTransport U p x = unitaryTransport U q x) ↔
        ∀ p : NamedPath s t r r, unitaryTransport U p = LinearIsometryEquiv.refl ℂ (F r))

private theorem rejected_law : ¬ arena.{u,v,w}.Law predicateRejected := by
  intro h
  let V := ULift.{u} Unit
  let E := ULift.{v} Empty
  let s : E → V := fun e => nomatch e.down
  let t : E → V := s
  let F : V → Type w := fun _ => ULift.{w} ℂ
  let U : ∀ e, F (s e) ≃ₗᵢ[ℂ] F (t e) := fun e => nomatch e.down
  let r : V := ULift.up ()
  have hc : ∀ a, Nonempty (NamedPath s t r a) := by
    intro a
    have ha : a = r := Subsingleton.elim _ _
    subst a
    exact ⟨.nil⟩
  obtain ⟨ev, heval, _⟩ := h (V := V) (E := E) (s := s) (t := t) (F := F) U r hc
  let σ : NamedSection (s := s) (t := t) (F := F) (underlying (s := s) (t := t) (F := F) U) := ⟨fun _ => 0, fun e => nomatch e.down⟩
  exact heval σ

def family : Registration arena.{u,v,w}
    (type_of% (@named_unitary_root_classification.{u,v,w})) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨@named_unitary_root_classification, predicateRejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := executionFamily.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@named_unitary_root_classification.{u,v,w})
    (type_of% (predicateActual.{w})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport.named_unitary_root_classification.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10,11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg","body","fn","arg","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration


namespace Incidence
open _root_.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
abbrev arena : Arena where
  signature := predicateSignature.{w}
  Law q := ∀ {V : Type u} {E : Type v} {s t : E → V} {F : V → Type w}
    (U : ∀ e, F (s e) ≃ F (t e)),
    (∀ {a b : IncidenceVertex V E} (p : Walk (incidenceGraph s t) a b),
      q.readout () ⟨F (endpoint s t a) ≃ F (endpoint s t b), fun f => f = (incidenceTransport U).walk p⟩ (namedTransport U (projectWalk p))) ∧
    (∀ {a b : V} (p : NamedPath s t a b),
      (incidenceTransport U).walk (liftPath p) = namedTransport U p) ∧
    (∀ {a b : V} (p : NamedPath s t a b), projectWalk (liftPath p) = p)

private theorem rejected_law : ¬ arena.{u,v,w}.Law predicateRejected := by
  intro h
  let V := ULift.{u} Unit
  let E := ULift.{v} Empty
  let s : E → V := fun e => nomatch e.down
  let t : E → V := s
  let F : V → Type w := fun _ => ULift.{w} Unit
  let U : ∀ e, F (s e) ≃ F (t e) := fun e => nomatch e.down
  exact (h (V := V) (E := E) (s := s) (t := t) (F := F) U).1
    (Walk.nil (IncidenceVertex.vertex (ULift.up ())))

def family : Registration arena.{u,v,w} (type_of% (@incidence_path_transport.{u,v,w})) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨@incidence_path_transport, predicateRejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := executionFamily.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0} (@incidence_path_transport.{u,v,w})
    (type_of% (predicateActual.{w})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport.incidence_path_transport.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport.Incidence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Incidence
end Reg.D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
