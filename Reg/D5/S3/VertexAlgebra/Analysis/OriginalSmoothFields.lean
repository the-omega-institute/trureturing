import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields

/-! The dependent realization observes the norm of each Sobolev output while
retaining the full original model, charge and smooth-test telescope. -/

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open _root_.D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.OriginalGram
open private embed_injective from
  D5.S3.VertexAlgebra.Analysis.OriginalSobolev

namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Model, ℕ)
    (fun p => p.1.Sobolev p.2) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Complete original telescope; only the displayed output norm is observed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (a : Charge M.D),
    ∃ C : ℝ, 0 < C ∧ ∀ f : Test,
      (∀ k : ℕ, Summable (fun m : ℤ => ‖M.operatorTerm a f k m‖)) ∧
      (∀ (k : ℕ) (x : M.Sobolev (M.order a+k)),
        R.readout () ⟨M,k⟩ (M.smear a f k x) ≤ C * f.W (M.order a+k) * ‖x‖) ∧
      Dense (M.smoothDomain : Set M.Hilbert) ∧
      (∀ u : M.smoothDomain, M.field a f u ∈ M.smoothDomain) ∧
      (M.field a f).IsFormalAdjoint (M.opposite a f) ∧
      M.field a f ≤ (M.opposite a f).adjoint ∧
      (M.field a f).IsClosable ∧ (M.opposite a f).IsClosable ∧
      (M.field a f).closure.IsClosed ∧
      (M.field a f).closure = (M.finiteField a f).closure ∧
      (M.field a f).closure.HasCore M.finiteDomain ∧
      (∀ (δ : Charge M.D) (u : M.smoothDomain),
        (u : M.Hilbert) ∈ M.chargeSector 0 δ →
          M.field a f u ∈ M.chargeSector 0 (a+δ)) ∧
      (∀ k : ℕ, ‖M.smear a f k‖ ≤ C *
        (f.jetNorm 0 + (2^(M.order a+k) * f.jetNorm (M.order a+k+2)) *
          (∑' m : ℤ, 1 / (m : ℝ)^2))) ∧
      M.eta a = epsilon M.D a (-a) ∧
      (∀ k : ℕ, M.inclusion k k le_rfl = ContinuousLinearMap.id ℂ (M.Sobolev k)) ∧
      (∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k),
        (M.inclusion i j hij).comp (M.inclusion j k hjk) =
          M.inclusion i k (hij.trans hjk))

private def testLattice : LatticeData where
  rank := 1
  G := Matrix.diagonal (fun _ => 2)
  symmetric := by intro i j; simp [Matrix.diagonal, eq_comm]
  even_diagonal := by intro i; norm_num [Matrix.diagonal]

private theorem test_positive : (gramReal testLattice).PosDef := by
  simpa [gramReal, testLattice] using
    (Matrix.PosDef.diagonal (fun _ : Fin 1 => (by norm_num : (0 : ℝ)<2)))

private def testModel : Model where
  D := testLattice
  positive := test_positive
  inverse := (complex_inverse_exists testLattice test_positive).choose
  inverse_left := (complex_inverse_exists testLattice test_positive).choose_spec.1
  inverse_right := (complex_inverse_exists testLattice test_positive).choose_spec.2

private def zeroTest : Test where
  lift _ := 0
  smooth := contDiff_const
  periodic _ := rfl

private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C,hC,hall⟩ := h testModel 0
  obtain ⟨habs,hbound,hrest⟩ := hall zeroTest
  have hh := hbound 0 0
  change (1 : ℝ) ≤ C * zeroTest.W (testModel.order 0+0) *
    ‖(0 : testModel.Sobolev (testModel.order 0+0))‖ at hh
  have hh0 : (1 : ℝ) ≤ 0 := by simpa only [norm_zero, mul_zero] using hh
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨testModel,0⟩, 0, testModel.embed 0 (vacuum testModel.D), ?_⟩
  change ‖(0 : testModel.Hilbert)‖ ≠ ‖testModel.embed 0 (vacuum testModel.D)‖
  have hn : testModel.embed 0 (vacuum testModel.D) ≠ 0 := by
    intro hz
    exact vacuum_nonzero testModel.D
      (embed_injective testModel 0 (hz.trans (map_zero _).symm))
  simpa only [norm_zero] using (norm_pos_iff.mpr hn).ne

def evidence : Registration arena (type_of% (@original_smooth_fields)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_smooth_fields, rejected, rejected_bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_bad
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_smooth_fields) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields
    definition := none
    coordinates := #[0,4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg",
        "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields
