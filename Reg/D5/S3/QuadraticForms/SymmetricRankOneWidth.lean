import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.SymmetricRankOneWidth
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the width and root comparisons. -/

namespace Reg.D5.S3.QuadraticForms.SymmetricRankOneWidth

open _root_.D5.S3.QuadraticForms.SymmetricRankOneKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped BigOperators

set_option autoImplicit false

universe u v
noncomputable section

abbrev widthSignature := signature Unit (fun _ => ℕ) (fun _ => ℕ)

def widthActual : Realization widthSignature :=
  realize widthSignature (fun _ _ w => max 1 w) (fun e => nomatch e)

def widthRejected : Realization widthSignature :=
  realize widthSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem widthDependence : ObservationalDependence widthSignature widthActual := by
  intro i
  exact ⟨(), 0, 2, by change max (1 : ℕ) 0 ≠ max 1 2; decide⟩

private abbrev ZeroSpace := EuclideanSpace ℝ (ULift.{v} Empty)

private theorem nullityZero {E : Type*} [AddCommGroup E] [Module ℝ E] [Subsingleton E]
    (B : E →ₗ[ℝ] E) : Module.finrank ℝ (LinearMap.ker B) = 0 := by
  have he : LinearMap.ker B = ⊥ := Subsingleton.elim _ _
  rw [he]
  exact Module.finrank_zero_of_subsingleton

/-- Observe the node width in the bound, the saturation flag and the equality test. -/
abbrev boundArena : Arena where
  signature := widthSignature
  Law R := ∀ {ι : Type u} [Fintype ι]
    {F : ι → Type v} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)]
    (A : ∀ i, F i →ₗ[ℝ] F i) (_hA : ∀ i, (A i).IsSymmetric)
    (u : PiLp 2 F) (nonleaves : Finset ι) (w : ι → ℕ) {t : ℝ} (_ht : t ≠ 0)
    (_hleaf : ∀ i ∉ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = 0)
    (_hbound : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) ≤ w i)
    (_hsat : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = w i →
      HasNonzeroPairing (A i) (u i)),
    let W := R.readout () () (∑ i ∈ nonleaves, w i)
    let B := update (blockDiagonal A) u t
    let k := Module.finrank ℝ (LinearMap.ker B)
    k ≤ W ∧ (k = W → HasNonzeroPairing B u) ∧
      (1 < W → (k = W ↔ ∃ i, nonleaves = {i} ∧
        Module.finrank ℝ (LinearMap.ker (A i)) + 1 = w i ∧
        ∃ g : ι → ℝ, (∀ j, ScalarResponse (A j) (u j) (g j)) ∧
          1 + t * (∑ j, g j) = 0))

private theorem boundRejected_law : ¬ boundArena.{u,v}.Law widthRejected := by
  intro law
  let I := ULift.{u} Unit
  let A : I → ZeroSpace.{v} →ₗ[ℝ] ZeroSpace.{v} := fun _ => 0
  have bad := law A (by intro i; simp [A, LinearMap.IsSymmetric]) 0 ∅
    (fun _ => 1) (t := 1) one_ne_zero (fun i _ => nullityZero (A i))
    (by simp) (by simp)
  obtain ⟨z, hz⟩ := bad.2.1 (nullityZero _)
  exact hz (by simp)

def boundSource : Registration boundArena.{u,v} (type_of% @update_block_width.{u,v}) where
  actual := widthActual
  bridge := Iff.rfl
  variation := ⟨@update_block_width.{u,v}, widthRejected, boundRejected_law.{u,v}⟩
  sensitivity := sensitivity boundArena.{u,v}.Law widthActual widthRejected boundRejected_law.{u,v}
  dependence := widthDependence

/-- Observe the comparison width in the conclusion of the root criterion. -/
abbrev rootArena : Arena where
  signature := widthSignature
  Law R := ∀ {ι : Type u} [Fintype ι]
    {F : ι → Type v} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)] [DecidableEq ι]
    (A : ∀ i, F i →ₗ[ℝ] F i) (_hA : ∀ i, (A i).IsSymmetric)
    (u : PiLp 2 F) (nonleaves : Finset ι) (w : ι → ℕ) (x : ℝ)
    (_hchildren : 2 ≤ Fintype.card ι) (_hwide : 1 < max 1 (∑ i ∈ nonleaves, w i))
    (_hleaf : ∀ i ∉ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = 0 ∧
      ScalarResponse (A i) (u i) (-1 / (x + 1)))
    (_hbound : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) ≤ w i)
    (_hsat : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = w i →
      HasNonzeroPairing (A i) (u i)),
    let ℓ := (Finset.univ \ nonleaves).card
    Module.finrank ℝ (LinearMap.ker (update (blockDiagonal A) u 1)) =
      R.readout () () (∑ i ∈ nonleaves, w i) ↔
      ∃ i, nonleaves = {i} ∧ 0 < ℓ ∧
        Module.finrank ℝ (LinearMap.ker (A i)) + 1 = w i ∧
        ∃ g, ScalarResponse (A i) (u i) g ∧ 1 + g - (ℓ : ℝ) / (x + 1) = 0

private theorem rootRejected_law : ¬ rootArena.{u,v}.Law widthRejected := by
  intro law
  let I := ULift.{u} Bool
  let A : I → ZeroSpace.{v} →ₗ[ℝ] ZeroSpace.{v} := fun _ => 0
  have children : 2 ≤ Fintype.card I := by simp [I]
  have wide : 1 < max 1 (∑ _i : I, (1 : ℕ)) := by simp [I]
  have bad := law A (by intro i; simp [A, LinearMap.IsSymmetric]) 0 Finset.univ
    (fun _ => 1) 0 children wide (by simp) (fun i _ => by simp [nullityZero])
    (fun i _ h => by simp [nullityZero] at h)
  obtain ⟨i, hi, _⟩ := bad.mp (nullityZero _)
  have hc := congrArg Finset.card hi
  simp [I] at hc

def rootSource : Registration rootArena.{u,v} (type_of% @update_block_root_iff.{u,v}) where
  actual := widthActual
  bridge := Iff.rfl
  variation := ⟨@update_block_root_iff.{u,v}, widthRejected, rootRejected_law.{u,v}⟩
  sensitivity := sensitivity rootArena.{u,v}.Law widthActual widthRejected rootRejected_law.{u,v}
  dependence := widthDependence

def boundAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_block_width.{u,v}) (Realization widthSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneWidth.boundUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneWidth.boundSource
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena.{u,v}⟩
  objectArena := .source ⟨boundArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena.{u,v} ⟨boundSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize widthSignature (fun _ _ w => max 1 w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneWidth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def rootAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_block_root_iff.{u,v}) (Realization widthSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneWidth.rootUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneWidth.rootSource
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena.{u,v}⟩
  objectArena := .source ⟨rootArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena.{u,v} ⟨rootSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize widthSignature (fun _ _ w => max 1 w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneWidth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.QuadraticForms.SymmetricRankOneWidth
