import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import Reg.Support.SingleDependentReadout

/-! Equality observations for the public Pauli zero and finite-sum identities. -/

namespace Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction

open _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev equalitySignature : Signature where
  Params := Unit
  State _ := Matrix (Fin 2) (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityActual : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

theorem equalityDependence : ObservationalDependence equalitySignature equalityActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun y : Matrix (Fin 2) (Fin 2) ℂ => 0 = y) = (fun y => 1 = y) at h
  have hfalse : (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := (congrFun h 0).mp rfl
  have hentry := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 0 0) hfalse
  norm_num at hentry

abbrev zeroArena : Arena where
  signature := equalitySignature
  Law r := r.readout () () (B (0 : EuclideanSpace ℝ (Fin 3))) 0

theorem zeroNegative : ¬ zeroArena.Law equalityRejected := by
  intro h
  exact h B_zero

def zeroEvidence : Registration zeroArena (type_of% @B_zero) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨B_zero, equalityRejected, zeroNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity zeroArena.Law equalityActual
    equalityRejected zeroNegative
  dependence := equalityDependence

end
end Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction
