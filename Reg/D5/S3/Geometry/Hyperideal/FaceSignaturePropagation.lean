import D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Hyperideal.FaceSignaturePropagation

open _root_.D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

abbrev signature : Signature where
  Params := Σ T : Type u, Σ E : Type v,
    Σ _ : SimpleGraph T, Σ _ : T → Fin 6 → E, E → Bool
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature.{u, v}
    (fun _ p t => lowPairCount p.2.2.2.1 p.2.2.2.2 t)
    (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature.{u, v} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {T : Type u} {E : Type v}
    (G : SimpleGraph T) (edge : T → Fin 6 → E) (low : E → Bool)
    (_glued : faceGluingCompatible G edge)
    {s t : T} (_connected : (balancedGraph G edge low).Reachable s t),
      lowPairCount edge low s = R.readout () ⟨T, E, G, edge, low⟩ t

theorem rejected_law : ¬ arena.{u, v}.Law rejected.{u, v} := by
  intro h
  let G : SimpleGraph (ULift.{u} Unit) := ⊥
  let edge : ULift.{u} Unit → Fin 6 → ULift.{v} Unit := fun _ _ => ⟨()⟩
  let low : ULift.{v} Unit → Bool := fun _ => true
  have hg : faceGluingCompatible G edge := by
    intro s t adj
    simp [G] at adj
  have bad := h G edge low hg
    (s := ⟨()⟩) (t := ⟨()⟩) (SimpleGraph.Reachable.refl _)
  change (3 : ℕ) = 0 at bad
  omega

theorem dependence : ObservationalDependence signature.{u, v} actual.{u, v} := by
  intro i
  let G : SimpleGraph (ULift.{u} Bool) := ⊥
  let edge : ULift.{u} Bool → Fin 6 → ULift.{v} Bool := fun t _ => ⟨t.down⟩
  let low : ULift.{v} Bool → Bool := fun e => e.down
  let p : signature.{u, v}.Params := ⟨ULift.{u} Bool, ULift.{v} Bool, G, edge, low⟩
  refine ⟨p, ⟨false⟩, ⟨true⟩, ?_⟩
  intro h
  have hzero : actual.readout i p ⟨false⟩ = 0 := by
    change (0 : ℕ) = 0
    rfl
  have hone : actual.readout i p ⟨true⟩ = 3 := by
    change (3 : ℕ) = 3
    rfl
  rw [hzero, hone] at h
  exact (by decide : (0 : ℕ) ≠ 3) h

def registration : Registration arena.{u, v} (arena.{u, v}.Law actual.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lowPairCount_eq_of_reachable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem lowPairCount_eq_of_reachable in arena
  readout via (realize signature.{u, v}
    (fun _ p t => lowPairCount p.2.2.2.1 p.2.2.2.2 t)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.Hyperideal.FaceSignaturePropagation.lowPairCount_eq_of_reachable
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Face-propagation registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "Face-propagation registration lacks validated source-bound evidence"
  | .declaredUnresolved diagnostic =>
      throwError "Face-propagation registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Face-propagation registration is undeclared"

#print axioms registration

end Reg.D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
