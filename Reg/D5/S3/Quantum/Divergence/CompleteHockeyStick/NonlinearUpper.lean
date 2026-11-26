import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper

/-! Source-bound readout of the uniform lift constant. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit Matrix
open scoped BigOperators
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState)
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (E amp ptr ptr_amp)
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearUpper

universe u v w

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y ∧ y < 1) (fun e => nomatch e)

def singletonChannel (A : Type u) (B : Type v)
    [Fintype A] [DecidableEq A] [Unique A] [Fintype B] [DecidableEq B] [Unique B] :
    QuantumChannel A B := by
  let e : A ≃ B := Equiv.ofUnique _ _
  let f := CStarMatrix.reindexₐ ℂ ℂ e
  exact {
    toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap f
    trace_preserving := fun X => by
      change (∑ i : B, X (e.symm i) (e.symm i)) = ∑ i : A, X i i
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl) }

theorem singleton_span {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Unique A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) :
    Submodule.span ℂ (Set.range fun p :
        (Fin (Fintype.card B) × Fin (Fintype.card A)) ×
          (Fin (Fintype.card B) × Fin (Fintype.card A)) =>
        ((actual_kraus_representation N).kraus p.1)ᴴ *
          (actual_kraus_representation N).kraus p.2) = ⊤ := by
  let K := (actual_kraus_representation N).kraus
  have hone : (1 : Matrix A A ℂ) ∈
      Submodule.span ℂ (Set.range fun p : _ × _ => (K p.1)ᴴ * K p.2) := by
    rw [← (actual_kraus_representation N).hkraus]
    exact Submodule.sum_mem _ fun p _ => Submodule.subset_span ⟨(p, p), rfl⟩
  apply top_unique
  intro X _
  have hX : X = X default default • (1 : Matrix A A ℂ) := by
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp
  rw [hX]
  exact Submodule.smul_mem _ _ hone

private def outputBound {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (C : ℝ) : Prop :=
  ∀ (R : Type w) [Fintype R] [DecidableEq R] (γ : ℝ) (_hγ : 1 ≤ γ)
    (ρ σ : DensityState (R × A)),
    let ρ₀ := (toMState ρ).m
    let σ₀ := (toMState σ).m
    ptr ρ₀ = ptr σ₀ →
    let x := E γ ρ₀ σ₀
    0 < x → E γ (amp N ρ₀) (amp N σ₀) ≤ x - x ^ 2 / (C ^ 2 * (2 * x + γ - 1))

private def upperLaw (R : Realization signature) : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B)
    (_hspan : Submodule.span ℂ (Set.range fun p :
        (Fin (Fintype.card B) × Fin (Fintype.card A)) ×
          (Fin (Fintype.card B) × Fin (Fintype.card A)) =>
        ((actual_kraus_representation N).kraus p.1)ᴴ *
          (actual_kraus_representation N).kraus p.2) = ⊤),
    ∃ C : ℝ, R.readout () () 1 C ∧ outputBound.{u, v, w} N C

abbrev arena : Arena where
  signature := signature
  Law := upperLaw.{u, v, w}

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  let M := singletonChannel (ULift.{u} Unit) (ULift.{v} Unit)
  obtain ⟨C, ⟨hC, hlt⟩, _⟩ := h M (singleton_span M)
  exact (not_lt_of_ge hC) hlt

private theorem sensitivity : Sensitivity arena.{u, v, w} actual :=
  _root_.Reg.Support.SingleDependentReadout.sensitivity arena.{u, v, w}.Law actual rejected rejected_law

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le.mpr zero_lt_one) he

def family : Registration arena.{u, v, w} (type_of% @exists_uniform_nonlinear_upper.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_uniform_nonlinear_upper.{u, v, w}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_uniform_nonlinear_upper.{u, v, w}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearUpper.exists_uniform_nonlinear_upper.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn",
        "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper
