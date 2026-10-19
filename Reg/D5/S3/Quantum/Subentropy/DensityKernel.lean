import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.DensityKernel
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

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
    0 ≤ subentropyKernel A t ∧
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
  Output _ _ := Set ℝ → Measure ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f s μ => IntegrableOn f s μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1),
    R.readout () () (subentropyKernel A) (Ioi 0) volume

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
  intro heq
  have hprop := congrArg (fun f => f (Ioi 0) volume) heq
  change IntegrableOn (subentropyKernel (1 : Matrix Unit Unit ℂ)) (Ioi 0) =
    IntegrableOn (subentropyKernel (0 : Matrix Unit Unit ℂ)) (Ioi 0) at hprop
  exact zero_kernel_not_integrable (hprop ▸ hi)

def source_registration : Registration arena.{u}
    (type_of% @integrable_subentropy_kernel.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integrable_subentropy_kernel, rejected, rejected_law⟩
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
  readout := some (realize signature (fun _ _ f s μ => IntegrableOn f s μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.DensityKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Integrability

namespace Continuity

abbrev signature : Signature where
  Params := Type u
  State ι := Matrix ι ι ℂ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := Set (Matrix ι ι ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : ∀ (e : signature.{u}.Anchor) (p : signature.{u}.Params),
    signature.{u}.State p := fun e => nomatch e

def observation : ∀ (i : signature.{u}.Role) (p : signature.{u}.Params),
    signature.{u}.State p → signature.{u}.Output i p :=
  fun _ _ f => ContinuousOn f

def actual : Realization signature.{u} :=
  realize signature.{u} observation.{u} emptyAnchor.{u}

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ _ => False) emptyAnchor.{u}

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    R.readout () ι (@matrixSubentropy ι _ _) {A | A.PosSemidef ∧ A.trace = 1}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance
  exact he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let c : ULift.{u} Unit := ⟨()⟩
  let fbad : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ → ℝ :=
    fun A => (Real.log (A c c).re)⁻¹
  refine ⟨ULift.{u} Unit, (fun _ => 0), fbad, ?_⟩
  intro heq
  have hprop := congrArg (fun F => F Set.univ) heq
  change ContinuousOn (fun _ : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    (0 : ℝ)) Set.univ = ContinuousOn fbad Set.univ at hprop
  have hgood : ContinuousOn (fun _ : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    (0 : ℝ)) Set.univ := continuous_const.continuousOn
  have hbad : ContinuousOn fbad Set.univ := hprop ▸ hgood
  have hc : Continuous (fun x : ℝ => (Real.log x)⁻¹) := by
    have hcomp := (continuousOn_univ.mp hbad).comp
      (show Continuous (fun x : ℝ => (fun _ _ : ULift.{u} Unit => (x : ℂ))) by
        fun_prop)
    change Continuous (fun x : ℝ => (Real.log x)⁻¹) at hcomp
    exact hcomp
  exact Real.not_continuousAt_inv_log_one hc.continuousAt

def source_registration : Registration arena.{u}
    (type_of% @continuousOn_matrixSubentropy.{u}) where
  actual := realize signature.{u} (fun _ _ f => ContinuousOn f) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@continuousOn_matrixSubentropy, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuousOn_matrixSubentropy.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.DensityKernel.continuousOn_matrixSubentropy.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.DensityKernel.Continuity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ f => ContinuousOn f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.DensityKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Continuity

namespace SpectralProbability

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (htr : A.trace = 1),
    (∀ i, R.readout () () 0 (hA.isHermitian.eigenvalues i)) ∧
      ∑ i, hA.isHermitian.eigenvalues i = 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance 1
    Matrix.PosSemidef.one (by simp [Matrix.trace])
  exact he.1 ⟨()⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht

def source_registration : Registration arena.{u} (type_of% @spectral_prob.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_prob, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spectral_prob.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.DensityKernel.spectral_prob.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.DensityKernel.SpectralProbability.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.DensityKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralProbability

end Reg.D5.S3.Quantum.Subentropy.DensityKernel
