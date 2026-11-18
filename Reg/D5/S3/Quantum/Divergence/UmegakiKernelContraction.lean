import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiKernelContraction

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open _root_.D5.S3.Quantum.Divergence.UmegakiKernelContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction

universe u

abbrev Q := ULift.{u} Unit

def identityChannel : QuantumChannel Q.{u} Q.{u} where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (StarAlgEquiv.refl ℂ (CStarMatrix Q Q ℂ))
  trace_preserving _ := rfl

theorem identity_endpoint : EndpointBound identityChannel.{u} 1 := by
  intro R _ _ Z V _ _
  have h (W : Matrix (R × Q) (R × Q) ℂ) : amp identityChannel W = W := by
    ext ⟨r,i⟩ ⟨s,j⟩
    rw [amp_entry]
    rfl
  rw [h Z, h V, one_mul]

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Nonempty a] [Nonempty b] {R : Type u} [Fintype R] [DecidableEq R]
      (N : QuantumChannel a b) (c : ℝ) (hN : (act N 1).PosDef)
      (hc : c ∈ Set.Icc (0 : ℝ) 1) (hEnd : EndpointBound N c)
      (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ) (hZ : Z.PosDef)
      (hV : partialTraceRight V = 0) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (q (amp N Z) (amp N V) t) (c * q Z V t)

theorem source_equivalence :
    (type_of% @kernel_contraction.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 1 Matrix.PosDef.one (by simp) identity_endpoint
    1 0 0 Matrix.PosDef.one (by ext i j; simp [partialTraceRight]) (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% @kernel_contraction.{u}) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@kernel_contraction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_contraction.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiKernelContraction.kernel_contraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction
