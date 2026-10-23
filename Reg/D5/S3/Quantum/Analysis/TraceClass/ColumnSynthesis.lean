import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.Compact
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Classical lp
open Filter Topology HilbertSchmidt
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def sqrtActual := realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a)
def scalarActual := realize scalarSignature.{u} (fun _ _ x => x) (fun a => nomatch a)
def scalarRejected := realize scalarSignature.{u} (fun _ _ _ => -1) (fun a => nomatch a)

theorem sqrtDependence : ObservationalDependence scalarSignature.{u} sqrtActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [sqrtActual, realize]

theorem scalarDependence : ObservationalDependence scalarSignature.{u} scalarActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [scalarActual, realize]

def synthesisLaw (R : Realization scalarSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (v : w → H)
    (hv : Summable (fun i : w => ‖v i‖ ^ 2)),
    ∃ A : H →L[ℂ] H,
      (∀ i, A (b i) = v i) ∧ IsHilbertSchmidt A ∧
      (∑' i : w, ‖A (b i)‖ ^ 2) = ∑' i : w, ‖v i‖ ^ 2 ∧
      ‖A‖ ≤ R.readout ⟨()⟩ () (∑' i : w, ‖v i‖ ^ 2)

abbrev synthesisArena : Arena where
  signature := scalarSignature.{u}
  Law := synthesisLaw

theorem synthesisActual : synthesisArena.{u}.Law sqrtActual := by
  intro H _ _ _ w b v hv
  exact exists_hilbertSchmidt_of_square_summable_columns b v hv

theorem synthesisRejected : ¬ synthesisArena.{u}.Law scalarRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  obtain ⟨A, _, _, _, hn⟩ := h (H := K) b (fun _ => 0) (by simp)
  have : ‖A‖ ≤ (-1 : ℝ) := hn
  linarith [norm_nonneg A]

def synthesisFamily : Registration synthesisArena (synthesisArena.Law sqrtActual) where
  actual := realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨synthesisActual, scalarRejected, synthesisRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarRejected, ?_, rfl, synthesisRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := sqrtDependence

def synthesisRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns.{u}) (type_of% (realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis.synthesisUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis.synthesisFamily
  realizationSource := none
  generated := false
  arena := .source ⟨synthesisArena⟩
  objectArena := .source ⟨synthesisArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source synthesisArena ⟨synthesisFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms synthesisFamily
#print axioms synthesisRegistration
end Reg.D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
