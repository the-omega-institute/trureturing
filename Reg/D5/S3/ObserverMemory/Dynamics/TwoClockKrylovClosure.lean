import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure
import Reg.Support.DependentFamily
import Mathlib.LinearAlgebra.Pi

open _root_.D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure
universe u

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ b a => a / b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Real.sqrt 2) (fun e => nomatch e)

/-- Only the exact clock-ratio operand is replaced; the original space,
endomorphism, subspace, hypotheses and both spans remain in the law. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (W : Submodule ℝ V) (a b : ℝ),
    Irrational (R.readout () b a) →
    Submodule.span ℝ {x | ∃ (k l : ℕ) (w : V), w ∈ W ∧
      x = (exp (a • A) ^ k) ((exp (b • A) ^ l) w)} =
    Submodule.span ℝ {x | ∃ (k : ℕ) (w : V), w ∈ W ∧ x = (A ^ k) w}

theorem actual_law : arena.{u}.Law actual := by
  exact two_clock_span_eq_krylov

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2) → ℝ
  let e₀ : V := Pi.single ⟨0⟩ 1
  let e₁ : V := Pi.single ⟨1⟩ 1
  let N : V →L[ℝ] V :=
    ((LinearMap.proj (⟨0⟩ : ULift.{u} (Fin 2))).smulRight e₁).toContinuousLinearMap
  let W := Submodule.span ℝ {e₀}
  have he₀ : e₀ ∈ W := Submodule.subset_span (Set.mem_singleton _)
  have hN : N e₀ = e₁ := by
    change e₀ (⟨0⟩ : ULift.{u} (Fin 2)) • e₁ = e₁
    rw [show e₀ (⟨0⟩ : ULift.{u} (Fin 2)) = 1 from Pi.single_eq_same _ _]
    exact one_smul ℝ e₁
  have heq := h N W 0 0 irrational_sqrt_two
  have he₁ : e₁ ∈ Submodule.span ℝ
      {x | ∃ (k : ℕ) (w : V), w ∈ W ∧ x = (N ^ k) w} :=
    Submodule.subset_span ⟨1, e₀, he₀, by simpa using hN.symm⟩
  rw [← heq] at he₁
  have hle : Submodule.span ℝ
      {x | ∃ (k l : ℕ) (w : V), w ∈ W ∧
        x = (exp ((0 : ℝ) • N) ^ k) ((exp ((0 : ℝ) • N) ^ l) w)} ≤ W := by
    apply Submodule.span_le.2
    rintro x ⟨k, l, w, hw, rfl⟩
    simpa using hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle he₁)
  have hbad := congrFun hc (⟨1⟩ : ULift.{u} (Fin 2))
  have hn : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by decide
  change c * e₀ (⟨1⟩ : ULift.{u} (Fin 2)) = e₁ ⟨1⟩ at hbad
  rw [show e₀ (⟨1⟩ : ULift.{u} (Fin 2)) = 0 from Pi.single_eq_of_ne hn.symm _,
    show e₁ (⟨1⟩ : ULift.{u} (Fin 2)) = 1 from Pi.single_eq_same _ _] at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration_1.{u_1} : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@two_clock_span_eq_krylov.{u_1}) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure.two_clock_span_eq_krylov.__information_unit
  realizationName := `Reg.D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨registration.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b a => a / b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end Reg.D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure
