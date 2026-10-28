import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.SphereWedgePositiveNormalization

/-! Full-family source-bound observation of the pointed normalization map. -/

noncomputable section
open Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.SphereWedgePositiveNormalization
open _root_.D5.S3.Geometry.CompactWedgeFiniteFactor (FamilyWedge base)
open _root_.D5.S3.Geometry.EuclideanSphereJoin (StdSphere coordinatePoint)

namespace Reg.D5.S3.Geometry.SphereWedgePositiveNormalization

universe u

structure Parameters where
  J : Type u
  n : J → ℕ
  b : ∀ j, StdSphere (n j)

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := FamilyWedge p.b
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PositiveWedge p.n ⊕ ZeroIndex p.n
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => normalizationHomeomorph p.n p.b x) (fun e => nomatch e)

def rejected : Realization signature.{u} := by
  classical
  exact realize signature (fun _ p _ => if h : Nonempty (ZeroIndex p.n) then
    Sum.inr (Classical.choice h) else
    Sum.inl (base (fun j : PositiveIndex p.n => coordinatePoint (p.n j.val))))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, R.readout () p (base p.b) =
    Sum.inl (base (fun j : PositiveIndex p.n => coordinatePoint (p.n j.val)))

private theorem bridge : (type_of% (@normalization_base.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p
    exact h p.n p.b
  · intro h J n b
    exact h ⟨J, n, b⟩

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, fun _ => 0, fun _ => coordinatePoint 0⟩

private def testZero : ZeroIndex testParameters.{u}.n := ⟨⟨()⟩, rfl⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  have hh := h testParameters
  change (if h : Nonempty (ZeroIndex testParameters.n) then Sum.inr (Classical.choice h)
    else Sum.inl (base _)) = Sum.inl (base _) at hh
  rw [dif_pos ⟨testZero⟩] at hh
  cases hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let e := normalizationHomeomorph testParameters.{u}.n testParameters.b
  let x := e.symm (Sum.inl (base _))
  let y := e.symm (Sum.inr testZero)
  refine ⟨testParameters, x, y, ?_⟩
  change e x ≠ e y
  dsimp [x, y]
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact Sum.noConfusion

def family : Registration arena.{u} (type_of% (@normalization_base.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@normalization_base.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalization_base.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.SphereWedgePositiveNormalization.__information_unit
  realizationName := `Reg.D5.S3.Geometry.SphereWedgePositiveNormalization.family
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
    (fun _ p x => normalizationHomeomorph p.n p.b x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.SphereWedgePositiveNormalization
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.SphereWedgePositiveNormalization
