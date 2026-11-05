import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.CommutingEncodingReflectionClass
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the equality of the two commuting encoding classes. -/

namespace Reg.D5.S3.Quantum.Information.CommutingEncodingReflectionClass

open _root_.D5.S3.Quantum.Information.CommutingEncodingReflectionClass
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (tensorOp tensor_mul)
open _root_.D5.S3.Quantum.FiniteDimensional (qubitX qubit_weyl_star)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the reflection-encoding predicate as the state vector varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => (Fin n → Fin 2) → ℂ)
    (fun n => (Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ ψ U => IsCommutingReflectionEncoding ψ U)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n → ∀ ψ : (Fin n → Fin 2) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) →
      ((∃ U, IsCommutingProductEncoding ψ U) ↔ ∃ U, R.readout () n ψ U)

private theorem sum_one_qubit {α : Type*} [AddCommMonoid α]
    (f : (Fin 1 → Fin 2) → α) : ∑ x, f x = f (fun _ => 0) + f (fun _ => 1) := by
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) f
    (fun a => f (fun _ => a)) (by intro x; congr; funext i; fin_cases i; rfl)]
  exact Fin.sum_univ_two _

private def basisState : (Fin 1 → Fin 2) → ℂ :=
  fun x => if x 0 = 0 then 1 else 0

private theorem basisState_normalized : ∑ x, ‖basisState x‖ ^ 2 = 1 := by
  rw [sum_one_qubit]
  norm_num [basisState]

private theorem basisState_encoded : ∃ U, IsCommutingReflectionEncoding basisState U := by
  classical
  let U : Fin (2 ^ 1) → Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
    fun a _ => if a = 0 then 1 else qubitX
  have hXh : qubitXᴴ = qubitX := qubit_weyl_star.2.1
  have hXsq : qubitX * qubitX = 1 := by
    simpa only [pow_two] using qubit_weyl_star.2.2.2.1
  have hXunit : qubitX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    exact ⟨by change qubitXᴴ * qubitX = 1; rw [hXh, hXsq],
      by change qubitX * qubitXᴴ = 1; rw [hXh, hXsq]⟩
  refine ⟨U, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a j
    fin_cases a <;> simp only [U]
    · exact one_mem _
    · exact hXunit
  · intro a b
    rw [tensor_mul, tensor_mul]
    congr 1
    funext j
    fin_cases a <;> fin_cases b <;> simp [U]
  · intro a b
    fin_cases a <;> fin_cases b <;>
      simp [tensorOp, Matrix.mulVec, dotProduct, sum_one_qubit, U,
        basisState, qubitX, Matrix.one_apply]
  · intro a j
    fin_cases a <;> simp only [U]
    · exact ⟨Matrix.isHermitian_one, by simp⟩
    · exact ⟨hXh, hXsq⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, hU⟩ := basisState_encoded
  obtain ⟨_, hf⟩ := (h 1 (by decide) basisState basisState_normalized).mp ⟨U, hU.1⟩
  exact hf

private theorem zero_not_encoded :
    ¬ ∃ U, IsCommutingReflectionEncoding (n := 0) (fun _ => 0) U := by
  rintro ⟨U, hU⟩
  have he := hU.1.2.2 (0 : Fin (2 ^ 0)) 0
  simp [Matrix.mulVec, dotProduct] at he

private theorem empty_encoded :
    ∃ U, IsCommutingReflectionEncoding (n := 0) (fun _ => 1) U := by
  classical
  refine ⟨fun _ j => Fin.elim0 j, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a j
    exact Fin.elim0 j
  · intro a b
    rfl
  · intro a b
    have hab : a = b := by omega
    simp [tensorOp, Matrix.mulVec, dotProduct, hab]
  · intro a j
    exact Fin.elim0 j

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  obtain ⟨U, hU⟩ := empty_encoded
  exact zero_not_encoded ⟨U, (congrFun h U).mpr hU⟩

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.CommutingEncodingReflectionClass.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CommutingEncodingReflectionClass.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CommutingEncodingReflectionClass.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ ψ U => IsCommutingReflectionEncoding ψ U)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CommutingEncodingReflectionClass
    definition := some {
      owner := `D5.S3.Quantum.Information.CommutingEncodingReflectionClass
      name := `D5.S3.Quantum.Information.CommutingEncodingReflectionClass.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.CommutingEncodingReflectionClass
