import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.DensityKernel
import Reg.Support.DependentFamily

/-! Faithful source observations for density-kernel bounds and integrability. -/

noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Quantum.Subentropy.DensityKernel
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.DensityKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder
universe u

namespace Bounds

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
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1)
    (t : ℝ) (ht : 0 < t),
    0 ≤ r.readout () t (subentropyKernel A) ∧
      r.readout () t (subentropyKernel A) ≤ 1 / (1 + t)^2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance 1
    Matrix.PosSemidef.one (by simp [Matrix.trace]) 1 (by norm_num)
  norm_num [rejected, realize, subentropyKernel, Matrix.det_unique, Matrix.ofNat_apply] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, subentropyKernel (1 : Matrix Unit Unit ℂ),
    subentropyKernel (diagonal (fun _ : Fin 2 => (1/2 : ℂ))), ?_⟩
  norm_num [actual, realize, subentropyKernel, Matrix.det_unique, Matrix.det_fin_two,
    Matrix.one_apply, Matrix.ofNat_apply, Matrix.diagonal_apply]

def source_registration : Registration arena.{u} (type_of% @density_kernel_bounds.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@density_kernel_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@density_kernel_bounds.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.DensityKernel.density_kernel_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.DensityKernel.Bounds.source_registration
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
    owner := `D5.S3.Quantum.Subentropy.DensityKernel
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Bounds

namespace Integrability

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f =>
    @decide (IntegrableOn f (Ioi 0)) (Classical.propDecidable _)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1),
    R.readout () () (subentropyKernel A) = true

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance 1
    Matrix.PosSemidef.one (by simp [Matrix.trace])
  simp [rejected, realize] at he

/-- The zero matrix supplies an actual source kernel outside the density domain.
Its divergent reciprocal tail distinguishes the original integrability observation. -/
private theorem zero_kernel_not_integrable :
    ¬ IntegrableOn (subentropyKernel (0 : Matrix Unit Unit ℂ)) (Ioi 0) := by
  intro h
  have hs : Ioi (1 : ℝ) ⊆ Ioi 0 := by
    intro t ht
    exact lt_trans (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < t from ht)
  have hk : IntegrableOn
      (fun t => 2 * ‖subentropyKernel (0 : Matrix Unit Unit ℂ) t‖) (Ioi 1) :=
    ((h.mono_set hs).norm).const_mul 2
  apply (not_integrableOn_Ioi_inv (a := 1))
  refine hk.mono' measurable_inv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (1 : ℝ) < t at ht
  have ht0 : 0 < t := lt_trans (show (0 : ℝ) < 1 by norm_num) ht
  have ht1 : 0 < 1 + t := by linarith
  have hkt : subentropyKernel (0 : Matrix Unit Unit ℂ) t = -(1 / (1 + t)) := by
    simp only [subentropyKernel, smul_zero, add_zero, Matrix.det_one,
      Complex.one_re, inv_one]
    field_simp [ht1.ne']
    <;> ring
  rw [hkt, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0), Real.norm_eq_abs,
    abs_neg, abs_of_pos (one_div_pos.mpr ht1)]
  calc
    t⁻¹ = 1 / t := (one_div t).symm
    _ ≤ 2 / (1 + t) := (div_le_div_iff₀ ht0 ht1).mpr (by linarith)
    _ = 2 * (1 / (1 + t)) := by ring

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), subentropyKernel (1 : Matrix Unit Unit ℂ),
    subentropyKernel (0 : Matrix Unit Unit ℂ), ?_⟩
  have hi := integrable_subentropy_kernel
    (Matrix.PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef)
    (by simp [Matrix.trace])
  simp [actual, realize, hi, zero_kernel_not_integrable]

def source_registration : Registration arena.{u}
    (type_of% @integrable_subentropy_kernel.{u}) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using @integrable_subentropy_kernel.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integrable_subentropy_kernel.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.DensityKernel.integrable_subentropy_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.DensityKernel.Integrability.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f =>
    @decide (IntegrableOn f (Ioi 0)) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.DensityKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Integrability

end Reg.D5.S3.Quantum.Subentropy.DensityKernel
