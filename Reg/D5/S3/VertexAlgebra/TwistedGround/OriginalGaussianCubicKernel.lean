import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ({z : ℂ // ‖z‖ < 1} × H) (fun _ => H) (fun _ => H × H)

def actual : Realization signature :=
  realize signature (fun _ w f =>
    (selfOperator w.1.1 w.2 + mixedOperator w.1.1 f,
      mixedOperator w.1.1 w.2 + selfOperator w.1.1 f)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {z : ℂ} (hz : ‖z‖ < 1) (e f p q : H),
    ((∀ n : ℕ, p n + (∑' m : ℕ,
      matrixEntry z (n + 1) (m + 1) * q m) = -f n) ∧
      (∀ n : ℕ, q n + (∑' m : ℕ,
      matrixEntry z (n + 1) (m + 1) * p m) = -e n)) ↔
    (p = (A.readout () (⟨z, hz⟩, e) f).1 ∧
      q = (A.readout () (⟨z, hz⟩, e) f).2)

private def testVector : H := lp.single 2 0 (1 : ℂ)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hz : ‖(0 : ℂ)‖ < 1 := by norm_num
  have hh := (h hz 0 testVector 0 0).2 (by simp [rejected, realize])
  have hh0 := hh.1 0
  norm_num [testVector] at hh0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hz : ‖(0 : ℂ)‖ < 1 := by norm_num
  refine ⟨(⟨0, hz⟩, 0), 0, testVector, ?_⟩
  intro h
  have hzero : actual.readout i (⟨0, hz⟩, 0) testVector = (0, 0) := by
    rw [← h]
    simp [actual, realize]
  have hpair :
      (0 : H) = selfOperator 0 0 + mixedOperator 0 testVector ∧
      (0 : H) = mixedOperator 0 0 + selfOperator 0 testVector := by
    constructor
    · simpa [actual, realize] using (congrArg Prod.fst hzero).symm
    · simpa [actual, realize] using (congrArg Prod.snd hzero).symm
  have hh := (original_coefficient_equations_iff hz 0 testVector 0 0).2 hpair
  have hh0 := hh.1 0
  norm_num [testVector] at hh0

def evidence : Registration arena (type_of% @original_coefficient_equations_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_coefficient_equations_iff, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

-- Source-coordinate selection is explicitly unfinished. This is a faithful
-- original-telescope attempt, not declared_validated source binding.
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_coefficient_equations_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w f =>
    (selfOperator w.1.1 w.2 + mixedOperator w.1.1 f,
      mixedOperator w.1.1 w.2 + selfOperator w.1.1 f)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some H
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
