import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW
import Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open _root_.D5.S3.Geometry.Gluing.ActualLinkAffineFan (TruncatedPoint TruncatedTetrahedron)
open _root_.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
open _root_.D5.S3.Geometry.Gluing.TruncatedTetrahedronCellGeometry (cell_geometry)
open _root_.D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW
open Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
  (PairingData signature actual rejected barycenter)
open private test a a_interior dependence
  from Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
open private halfParameter twoCoords twoCoords_first
  from D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW

namespace Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW
noncomputable section
universe u

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {T : Type u} [finiteT : Fintype T]
    [topologyT : TopologicalSpace T] [discreteT : @DiscreteTopology T topologyT]
    (P : RawFacePairing T),
    @LowerGeometry T finiteT topologyT discreteT P (R.readout () ⟨T,P⟩)

theorem bridge : (type_of% (@lower_geometry.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h T finiteT topologyT discreteT P
    exact @h T finiteT topologyT discreteT P
  · intro h T finiteT topologyT discreteT P
    exact @h T finiteT topologyT discreteT P

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let h : HalfOccurrence test.1 := (⟨()⟩,⟨(0,1),by decide⟩)
  let v : OldVertex test.2 := Quotient.mk (oldSetoid test.2) h
  let x : Disk 1 := ⟨0,by simp⟩
  let b := halfPoint v.out (halfParameter x)
  have hchart := (@hh test.1 inferInstance inferInstance inferInstance test.2).half_characteristic v x
  have hb : barycenter test b = a := by
    apply Prod.ext (Subsingleton.elim _ _)
    apply Subtype.ext
    funext i
    rfl
  have hqa : q test.2 b = q test.2 a := by
    calc
      q test.2 b = halfCell test.2 v x.val :=
        ((lower_geometry test.2).half_characteristic v x).symm
      _ = q test.2 (barycenter test b) := hchart
      _ = q test.2 a := congrArg (q test.2) hb
  have he := ((cell_geometry test.2).interior_fibers a b a_interior).mp hqa.symm
  have hc := congrArg (fun z : TruncatedPoint test.1 => z.2.val v.out.2.val.1) he
  change _ = (1/4 : ℝ) at hc
  change twoCoords v.out.2
    (halfParameter x).val v.out.2.val.1 = 1/4 at hc
  rw [twoCoords_first] at hc
  norm_num [halfParameter,x] at hc

def familyRegistration : Registration arena.{u} (type_of% (@lower_geometry.{u})) where
  actual := realize signature.{u} (fun _ p => q p.2) actual.anchor
  bridge := bridge
  variation := ⟨bridge.mp @lower_geometry,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

/-- The lower-cell construction observed through the full original quotient projection. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lower_geometry.{u})
    (type_of% (realize signature.{u} (fun _ p => q p.2) actual.anchor))
    Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW.lower_geometry.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p => q p.2) actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW,
    definition := none,
    coordinates := #[0,4],
    readouts := #[{
      path := #["body","body","body","body","body","arg"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW
