import D5.S3.Quantum.Foundation.UnitPreservingLiftImage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact full source reconstruction for the original unit-preserving cone image.
The enrolled dependent-family template is available; whole-family variation,
sensitivity, actual observational dependence and lawful source selection are
not supplied. This mirror declares no validated four-slot registration. -/

noncomputable section
universe v w
namespace Reg.D5.S3.Quantum.Foundation.UnitPreservingLiftImage

open Set
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.UnitPreservingLiftImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  W : Type w
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [addW : NormedAddCommGroup W]
  [spaceW : NormedSpace ℝ W]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  mass : V →ₗ[ℝ] ℝ
  readout : V →ₗ[ℝ] W

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.addW Inputs.spaceW

abbrev signature : Signature where
  Params := Inputs.{v,w}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def outcome (P : Inputs.{v,w}) (p : P.V) : Prop :=
    IsClosed (liftMap P.unit P.mass P.readout '' (P.cone : Set P.V)) ∧
    Convex ℝ (liftMap P.unit P.mass P.readout '' (P.cone : Set P.V)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ w ∈ liftMap P.unit P.mass P.readout '' (P.cone : Set P.V),
      t • w ∈ liftMap P.unit P.mass P.readout '' (P.cone : Set P.V)) ∧
    (∀ t s z, (t, s, z) ∈ liftMap P.unit P.mass P.readout '' (P.cone : Set P.V) ↔
      (0 ≤ t ∧ s = 0 ∧ z = 0) ∨
      (0 < s ∧ s⁻¹ • z ∈ domain P.cone P.mass P.readout ∧
        s * leastUnit P.cone P.unit P.mass P.readout (s⁻¹ • z) ≤ t)) ∧
    IsCompact ((P.mass.prod P.readout) '' base P.cone P.unit) ∧ Convex ℝ ((P.mass.prod P.readout) '' base P.cone P.unit) ∧
    (∀ s z, (s, z) ∈ (P.mass.prod P.readout) '' base P.cone P.unit ↔
      (s = 0 ∧ z = 0) ∨
      (0 < s ∧ s⁻¹ • z ∈ domain P.cone P.mass P.readout ∧
        s * leastUnit P.cone P.unit P.mass P.readout (s⁻¹ • z) ≤ 1)) ∧
    domain P.cone P.mass P.readout = {z | ∃ x ∈ base P.cone P.unit, x ≠ p ∧ (P.mass x)⁻¹ • P.readout x = z} ∧
    (∀ z ∈ domain P.cone P.mass P.readout, ∃ y ∈ fiber P.cone P.mass P.readout z,
      unitCost P.cone P.unit P.mass P.readout z = (P.unit y : EReal) ∧
      P.unit y = leastUnit P.cone P.unit P.mass P.readout z ∧ ∀ x ∈ fiber P.cone P.mass P.readout z, P.unit y ≤ P.unit x) ∧
    (∀ L : Submodule ℝ P.V, p ∈ L →
      ¬ ∃ v : (P.V ⧸ L) →ₗ[ℝ] ℝ, v.comp L.mkQ = P.unit)

def actual : Realization signature.{v,w} :=
  realize signature (fun _ P p => outcome P p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v,w}
  Law O := ∀ P : Inputs.{v,w}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    ∀ p : P.V, p ∈ base P.cone P.unit →
    (∀ x ∈ P.cone, 0 ≤ P.mass x) → P.mass p = 0 → P.readout p = 0 →
    (∀ x ∈ P.cone, P.mass x = 0 → ∃ t : ℝ, 0 ≤ t ∧ x = t • p) →
    O.readout () P p

abbrev source : Prop := type_of% (@unit_preserving_lift_image.{v,w})

theorem source_bridge : source.{v,w} ↔ arena.{v,w}.Law actual.{v,w} := by
  constructor
  · intro h P
    exact @h P.V P.W P.add P.space P.finite P.addW P.spaceW P.cone P.unit P.mass P.readout
  · intro h V W add space finite addW spaceW C u g H
    exact h (@Inputs.mk V W add space finite addW spaceW C u g H)

theorem actual_positive : arena.{v,w}.Law actual.{v,w} :=
  source_bridge.mp (@unit_preserving_lift_image.{v,w})

/-- A typed four-slot attempt, conditional on the still-missing whole-family
certificate. No such certificate or actual registration is claimed. -/
noncomputable def registrationAttempt
    (family : Registration arena.{v,w} source.{v,w}) :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@unit_preserving_lift_image.{v,w}) (Realization signature.{v,w}) Unit Unit := {
  unitName := `D5.S3.Quantum.Foundation.UnitPreservingLiftImage.unit_preserving_lift_image.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.UnitPreservingLiftImage.actual
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v,w}⟩
  objectArena := .source ⟨arena.{v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v,w} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v,w} (fun _ P p => outcome P p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.UnitPreservingLiftImage
