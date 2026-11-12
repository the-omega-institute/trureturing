import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathTriangleFibre
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the complete original triangle radical family. -/
namespace Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre
open _root_.D5.S3.Quantum.Recovery.FourPathTriangleFibre
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ × ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p Y => F p.1 p.2 Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0,0),0,1,?_⟩
  norm_num [actual,realize,F,Z]

namespace Geometry
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (L X Y : ℝ), 1 < L → L^2 ≤ 2 → Triangle L X Y →
    0 < X ∧ 0 < Y ∧ 0 < X+Y ∧
      (Y-X)^2 < (X+Y)^2 ∧ (Y-X)^2 ≤ B (X+Y) ∧
      (Y-X)^2 ≤ D (L^2) (X+Y) ∧ Z L X Y^2 ≤ 1 ∧
      4*(A.readout () (L,X) Y)^2*((X+Y)^2-(Y-X)^2) =
        (B (X+Y)-(Y-X)^2)*(D (L^2) (X+Y)-(Y-X)^2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro hv
  have hv' := hv (6/5) 1 (1/4) (by norm_num) (by norm_num) (by norm_num [Triangle])
  obtain ⟨_,_,_,_,_,_,_,he⟩ := hv'
  norm_num [B,D,rejected,realize] at he

def source_registration : Registration arena
    (∀ (L X Y : ℝ), 1 < L → L^2 ≤ 2 → Triangle L X Y →
    0 < X ∧ 0 < Y ∧ 0 < X+Y ∧
      (Y-X)^2 < (X+Y)^2 ∧ (Y-X)^2 ≤ B (X+Y) ∧
      (Y-X)^2 ≤ D (L^2) (X+Y) ∧ Z L X Y^2 ≤ 1 ∧
      4*(F L X Y)^2*((X+Y)^2-(Y-X)^2) =
        (B (X+Y)-(Y-X)^2)*(D (L^2) (X+Y)-(Y-X)^2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨triangle_geometry,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Recovery.FourPathTriangleFibre.triangle_geometry)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre.Geometry.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre.Geometry.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Y => F p.1 p.2 Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathTriangleFibre
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","arg","arg","arg","arg","arg","arg","fn","arg","fn","arg","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end Geometry

namespace Ball
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (L X Y : ℝ), 1 < L → L^2 ≤ 2 → Triangle L X Y →
    (Y-X)^2+(2*A.readout () (L,X) Y)^2 ≤ T (L^2) (X+Y)

theorem rejected_law : ¬ arena.Law rejected := by
  intro hv
  have hv' := hv (6/5) 1 (1/4) (by norm_num) (by norm_num) (by norm_num [Triangle])
  norm_num [T,W,B,D,rejected,realize] at hv' 

def source_registration : Registration arena
    (∀ (L X Y : ℝ), 1 < L → L^2 ≤ 2 → Triangle L X Y →
    (Y-X)^2+(2*F L X Y)^2 ≤ T (L^2) (X+Y)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨closed_triangle_ball,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Recovery.FourPathTriangleFibre.closed_triangle_ball)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre.Ball.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre.Ball.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Y => F p.1 p.2 Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathTriangleFibre
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","arg","fn","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end Ball

namespace Fibre
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (L X Y : ℝ), 1 < L → L^2 ≤ 2 → Triangle L X Y →
    let u := X+Y
    let a := L^2
    0 ≤ T a u ∧ 0 ≤ W a u ∧
      W a u*(Y-X)^2+T a u*(2*A.readout () (L,X) Y)^2 ≤ T a u*W a u

theorem rejected_law : ¬ arena.Law rejected := by
  intro hv
  have hv' := hv (6/5) 1 (1/4) (by norm_num) (by norm_num) (by norm_num [Triangle])
  norm_num [T,W,B,D,rejected,realize] at hv' 

def source_registration : Registration arena
    (∀ (L X Y : ℝ), 1 < L → L^2 ≤ 2 → Triangle L X Y →
    let u := X+Y
    let a := L^2
    0 ≤ T a u ∧ 0 ≤ W a u ∧
      W a u*(Y-X)^2+T a u*(2*F L X Y)^2 ≤ T a u*W a u) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨closed_triangle_fibre,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Recovery.FourPathTriangleFibre.closed_triangle_fibre)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre.Fibre.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre.Fibre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Y => F p.1 p.2 Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathTriangleFibre
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","arg","fn","arg","arg","arg","fn","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end Fibre

end
end Reg.D5.S3.Quantum.Recovery.FourPathTriangleFibre
