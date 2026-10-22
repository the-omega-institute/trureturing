import D5.S3.VertexAlgebra.BcGhostNumber
import Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent

set_option autoImplicit false

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostStressCurrent
open _root_.D5.S3.VertexAlgebra.BcGhostNumber
open Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent

namespace Reg.D5.S3.VertexAlgebra.BcGhostNumber

universe scalarLevel
noncomputable section

namespace B

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law readout := ∀ {K : Type scalarLevel} [CommRing K] (mode : ℤ),
    J * readout.readout () ⟨K, inferInstance⟩ mode -
      readout.readout () ⟨K, inferInstance⟩ mode * J =
        -readout.readout () ⟨K, inferInstance⟩ mode

def sourceStatement : Prop := ∀ {K : Type scalarLevel} [CommRing K] (mode : ℤ),
  J (K := K) * b mode - b mode * J = -b (K := K) mode

theorem sourceBridge :
    sourceStatement.{scalarLevel} ↔ arena.{scalarLevel}.Law bActual.{scalarLevel} := by
  constructor
  · intro source K commRing mode
    simpa only [bActual, realize] using source (K := K) mode
  · intro law K commRing mode
    simpa only [bActual, realize] using law (K := K) mode

theorem rejected : ¬ arena.{scalarLevel}.Law oneReadout := by
  intro law
  have equation := law (K := ULift.{scalarLevel} ℤ) 0
  change J * 1 - 1 * J = -(1 : Module.End (ULift.{scalarLevel} ℤ)
    (Fock (ULift.{scalarLevel} ℤ))) at equation
  have negIdentity : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = -1 := by simpa using equation
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by
    simpa using congrArg Neg.neg negIdentity
  exact zero_ne_one contradiction

def evidence : Registration arena sourceStatement :=
  { evidenceFor arena.Law bActual oneReadout
      (fun mode => J_b_commutator mode) rejected bDependence with
    bridge := sourceBridge }

end B

namespace C

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law readout := ∀ {K : Type scalarLevel} [CommRing K] (mode : ℤ),
    J * readout.readout () ⟨K, inferInstance⟩ mode -
      readout.readout () ⟨K, inferInstance⟩ mode * J =
        readout.readout () ⟨K, inferInstance⟩ mode

def sourceStatement : Prop := ∀ {K : Type scalarLevel} [CommRing K] (mode : ℤ),
  J (K := K) * c mode - c mode * J = c mode

theorem sourceBridge :
    sourceStatement.{scalarLevel} ↔ arena.{scalarLevel}.Law cActual.{scalarLevel} := by
  constructor
  · intro source K commRing mode
    simpa only [cActual, realize] using source (K := K) mode
  · intro law K commRing mode
    simpa only [cActual, realize] using law (K := K) mode

theorem rejected : ¬ arena.{scalarLevel}.Law oneReadout := by
  intro law
  have equation := law (K := ULift.{scalarLevel} ℤ) 0
  change J * 1 - 1 * J = (1 : Module.End (ULift.{scalarLevel} ℤ)
    (Fock (ULift.{scalarLevel} ℤ))) at equation
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by simpa using equation
  exact zero_ne_one contradiction

def evidence : Registration arena sourceStatement :=
  { evidenceFor arena.Law cActual oneReadout
      (fun mode => J_c_commutator mode) rejected cDependence with
    bridge := sourceBridge }

end C

namespace Stress

def actual : Realization signature.{scalarLevel} :=
  realize signature (fun _ parameters mode => letI := parameters.2; L mode)
    (fun empty => nomatch empty)

def lowering : Realization signature.{scalarLevel} :=
  realize signature (fun _ parameters _ => letI := parameters.2; b (-2))
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law readout := ∀ {K : Type scalarLevel} [CommRing K] (mode : ℤ),
    J * readout.readout () ⟨K, inferInstance⟩ mode -
      readout.readout () ⟨K, inferInstance⟩ mode * J = 0

def sourceStatement : Prop := ∀ {K : Type scalarLevel} [CommRing K] (mode : ℤ),
  J (K := K) * L mode - L mode * J = 0

theorem sourceBridge :
    sourceStatement.{scalarLevel} ↔ arena.{scalarLevel}.Law actual.{scalarLevel} := by
  constructor
  · intro source K commRing mode
    simpa only [actual, realize] using source (K := K) mode
  · intro law K commRing mode
    simpa only [actual, realize] using law (K := K) mode

theorem rejected : ¬ arena.{scalarLevel}.Law lowering := by
  intro law
  have equation := law (K := ULift.{scalarLevel} ℤ) 0
  change J * b (-2) - b (-2) * J = (0 : Module.End (ULift.{scalarLevel} ℤ)
    (Fock (ULift.{scalarLevel} ℤ))) at equation
  have grading := J_b_commutator (K := ULift.{scalarLevel} ℤ) (-2)
  have vanishes : b (K := ULift.{scalarLevel} ℤ) (-2) = 0 :=
    neg_eq_zero.mp (grading.symm.trans equation)
  have identity := b_c (K := ULift.{scalarLevel} ℤ) (-2) 2
  rw [vanishes] at identity
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by simpa using identity
  exact zero_ne_one contradiction

theorem dependence : ObservationalDependence signature.{scalarLevel} actual := by
  intro role
  refine ⟨⟨ULift.{scalarLevel} ℤ, inferInstance⟩, 0, 1, ?_⟩
  change L (K := ULift.{scalarLevel} ℤ) 0 ≠ L 1
  intro equality
  have first := L_b_commutator (K := ULift.{scalarLevel} ℤ) 0 0
  have second := L_b_commutator (K := ULift.{scalarLevel} ℤ) 1 0
  rw [equality] at first
  have vanishes : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = b 1 := by
    simpa using first.symm.trans second
  have identity := b_c (K := ULift.{scalarLevel} ℤ) 1 (-1)
  rw [← vanishes] at identity
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by simpa using identity
  exact zero_ne_one contradiction

def evidence : Registration arena sourceStatement :=
  { evidenceFor arena.Law actual lowering
      (fun mode => J_L_commutator mode) rejected dependence with
    bridge := sourceBridge }

end Stress

#print axioms B.evidence
#print axioms C.evidence
#print axioms Stress.evidence

end

end Reg.D5.S3.VertexAlgebra.BcGhostNumber
