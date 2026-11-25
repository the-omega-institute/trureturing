import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST

/-! The square of the actual BRST charge as an endomorphism-valued observation. -/

open scoped TensorProduct
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock ket vacuum)

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST

private theorem pureTensor_nonzero {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    v ⊗ₜ[ℂ] w ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let read := (TensorProduct.lid ℂ W).toLinearMap.comp
    (TensorProduct.map f LinearMap.id)
  have hread : read (v ⊗ₜ[ℂ] w) = w := by simp [read, hf]
  intro h
  rw [h, map_zero] at hread
  exact hw hread.symm

private theorem endomorphism_one_ne_zero : (1 : Module.End ℂ ComplexState) ≠ 0 := by
  let orbifold := TwistedGround.Orbifold.OriginalOrbifoldField.vacuumState
    ActualLeechHyperbolic.leechData ActualLeechOrbifoldMatter.leechUnit
  have ho : orbifold ≠ 0 := by
    intro h
    exact LatticePositiveEnergy.vacuum_nonzero _ (congrArg (fun x => x.1.val) h)
  have hp := LatticePositiveEnergy.vacuum_nonzero ActualLeechOrbifoldCriticalMatter.hyperbolicPlane
  have hg : (vacuum : Fock) ≠ 0 := by simp [vacuum, ket]
  let plane := LatticeAllStateField.vacuum ActualLeechOrbifoldCriticalMatter.hyperbolicPlane
  let x : ComplexState := (orbifold ⊗ₜ[ℂ] plane) ⊗ₜ[ℂ] vacuum
  have hx : x ≠ 0 := pureTensor_nonzero (pureTensor_nonzero ho hp) hg
  intro h
  exact hx (LinearMap.congr_fun h x)

namespace Q_squared

open _root_.D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
  renaming Q_squared → square_zero

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Module.End ℂ ComplexState) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => Q ^ 2 = x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 0

private theorem rejected_law : ¬ arena.Law rejected := id

def family : Registration arena (type_of% square_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨square_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), Q ^ 2, 1, ?_⟩
    intro h
    exact endomorphism_one_ne_zero ((Eq.mp h rfl).symm.trans square_zero)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.Q_squared)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST.Q_squared.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST.Q_squared.family
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
  escapeFrom := some (Module.End ℂ ComplexState)
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Q_squared
end Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
