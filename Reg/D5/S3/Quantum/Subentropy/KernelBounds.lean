import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.KernelBounds
import Reg.Support.DependentFamily

/-! Source registrations for the classical determinant-kernel bounds. -/

noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Quantum.Subentropy.KernelBounds
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.KernelBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
universe u

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t f => f t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ t f => f t + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (x : ι) (t : ℝ) (ht : 0 < t),
    0 ≤ subentropyKernel (diagonal (fun i => (p i : ℂ))) t ∧
      r.readout () t (subentropyKernel (diagonal (fun i => (p i : ℂ)))) ≤
        (1 - p x) / (1 + t)^2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 1)
    (fun _ => by norm_num) (by simp) ⟨()⟩ 1 (by norm_num)
  norm_num [rejected, realize, subentropyKernel, Matrix.det_unique,
    Matrix.ofNat_apply] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, subentropyKernel (1 : Matrix Unit Unit ℂ),
    subentropyKernel (diagonal (fun _ : Fin 2 => (1/2 : ℂ))), ?_⟩
  norm_num [actual, realize, subentropyKernel, Matrix.det_unique, Matrix.det_fin_two,
    Matrix.one_apply, Matrix.diagonal_apply, Matrix.ofNat_apply]

def source_registration : Registration arena.{u} (type_of% @classical_kernel_bounds.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@classical_kernel_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@classical_kernel_bounds.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.KernelBounds.classical_kernel_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.KernelBounds.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t f => f t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.KernelBounds
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Subentropy.KernelBounds
