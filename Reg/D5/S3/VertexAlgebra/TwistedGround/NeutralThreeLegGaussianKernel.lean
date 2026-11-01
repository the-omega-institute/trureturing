import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel
import Reg.Support.SingleDependentReadout

noncomputable section
open scoped BigOperators
open _root_.D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel
open _root_.D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel.Damping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => massBound N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (d : Damping N),
    Summable (fun p : Index N × Index N => ‖d.entry p.1 p.2‖^2) ∧
      (∑' p : Index N × Index N, ‖d.entry p.1 p.2‖^2) ≤ R.readout () () N

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨d, hd⟩ := damping_nonempty 0 (1 : ℂ) one_ne_zero
  have hb : (∑' p : Index 0 × Index 0, ‖d.entry p.1 p.2‖^2) ≤ (-1 : ℝ) := (h d).2
  have hn : 0 ≤ (∑' p : Index 0 × Index 0, ‖d.entry p.1 p.2‖^2) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, massBound, eta]

def evidence : Registration arena (type_of% @Damping.matrix_square_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Damping.matrix_square_mass, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Damping.matrix_square_mass) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel.massUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => massBound N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms audit
end Reg.D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel
