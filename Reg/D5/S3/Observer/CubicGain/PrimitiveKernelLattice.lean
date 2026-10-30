import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.PrimitiveKernelLattice
import Reg.D5.S3.Observer.CubicGain.PrefixKernelSigns
import Reg.Support.SingleDependentReadout

/-! The whole source telescope with its real generator as the observed state. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrefixKernelSigns
open _root_.D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.PrimitiveKernelLattice

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat) (fun _ => Mat)

def actual : Realization signature := realize signature (fun _ _ N => N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Mat)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (w : Fin 3 → List Bool) (N : Mat), OrientedKernelGenerator w N →
      ∃ (p : PrimitiveCoordinates) (scale : ℝ), 0 < scale ∧
        R.readout () () N = scale • p.matrix ∧
        (∀ X, prefixDifference w X = 0 ↔ ∃ v : ℝ, X = v • p.matrix) ∧
        ∃ m : Fin 4 → ℤ, m 0 = 0 ∧ ∀ i,
          prefixMatrix w i *ᵥ p.column = p.column + (m i:ℝ) • p.direction) ∧
    (∀ (w : Fin 3 → List Bool) (p : PrimitiveCoordinates) (m : Fin 4 → ℤ),
      m 0 = 0 →
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column + (m i:ℝ) • p.direction) →
      Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3 →
      OrientedKernelGenerator w p.matrix)

private theorem inhabited_class : ∃ (w : Fin 3 → List Bool) (N : Mat),
    OrientedKernelGenerator w N := by
  by_contra hn
  obtain ⟨bad,hbad⟩ :=
    _root_.Reg.D5.S3.Observer.CubicGain.PrefixKernelSigns.family.variation.2
  apply hbad
  intro w N h
  exact (hn ⟨w,N,h⟩).elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w,N,hN⟩ := inhabited_class
  obtain ⟨p,scale,hscale,heq,-,-⟩ := h.1 w N hN
  have hh := congrArg Matrix.trace heq
  have ht : (0:ℝ) < (p.a:ℝ)*p.c+(p.b:ℝ)*p.d := by exact_mod_cast p.trace_pos
  have ht' := mul_pos hscale ht
  simp [rejected,realize,PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,
    PrimitiveCoordinates.row,Matrix.vecMulVec,Matrix.trace,Matrix.diag,
    Fin.sum_univ_two] at hh
  nlinarith

def family : Registration arena (type_of% @whole_class_primitive_lattice) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_class_primitive_lattice,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    change (0 : Mat) ≠ 1
    exact zero_ne_one

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_class_primitive_lattice) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Observer.CubicGain.PrimitiveKernelLattice.whole_class_primitive_lattice.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PrimitiveKernelLattice.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PrimitiveKernelLattice
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.PrimitiveKernelLattice
