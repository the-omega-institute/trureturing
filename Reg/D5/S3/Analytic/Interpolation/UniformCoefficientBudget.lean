import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.UniformCoefficientBudget
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget
open LeanInformationAudit Polynomial Set Finset

noncomputable section
namespace Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget

abbrev normSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Polynomial ℝ) (fun _ => ℝ)

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)

def normRejected (v : ℝ) : Realization normSignature :=
  realize normSignature (fun _ _ _ => v) (fun e => nomatch e)

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), 0, X - C 0, ?_⟩
  change coeffL1 0 ≠ coeffL1 (X - C 0)
  rw [coeffL1_X_sub_C]
  simp [coeffL1]

def coeffL1_add_leArena : Arena where
  signature := normSignature
  Law R := ∀ (p q : Polynomial ℝ), R.readout () () (p+q) ≤ coeffL1 p + coeffL1 q

private theorem coeffL1_add_le_rejected : ¬ coeffL1_add_leArena.Law (normRejected 1) := by
  intro h
  have hh := h 0 0
  change (1 : ℝ) ≤ _ at hh
  norm_num [coeffL1] at hh

def coeffL1_add_leEvidence : Registration coeffL1_add_leArena (coeffL1_add_leArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨coeffL1_add_le, normRejected 1, coeffL1_add_le_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coeffL1_add_leArena.Law normActual (normRejected 1) coeffL1_add_le_rejected
  dependence := normDependence

noncomputable def coeffL1_add_leRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_add_le)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_add_le_norm_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_add_leEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coeffL1_add_leArena⟩
  objectArena := .source ⟨coeffL1_add_leArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coeffL1_add_leArena ⟨coeffL1_add_leEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def coeffL1_mul_leArena : Arena where
  signature := normSignature
  Law R := ∀ (p q : Polynomial ℝ), R.readout () () (p*q) ≤ coeffL1 p * coeffL1 q

private theorem coeffL1_mul_le_rejected : ¬ coeffL1_mul_leArena.Law (normRejected 1) := by
  intro h
  have hh := h 0 0
  change (1 : ℝ) ≤ _ at hh
  norm_num [coeffL1] at hh

def coeffL1_mul_leEvidence : Registration coeffL1_mul_leArena (coeffL1_mul_leArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨coeffL1_mul_le, normRejected 1, coeffL1_mul_le_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coeffL1_mul_leArena.Law normActual (normRejected 1) coeffL1_mul_le_rejected
  dependence := normDependence

noncomputable def coeffL1_mul_leRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_mul_le)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_mul_le_norm_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_mul_leEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coeffL1_mul_leArena⟩
  objectArena := .source ⟨coeffL1_mul_leArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coeffL1_mul_leArena ⟨coeffL1_mul_leEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def coeffL1_C_mulArena : Arena where
  signature := normSignature
  Law R := ∀ (c : ℝ) (p : Polynomial ℝ), R.readout () () (C c*p) = |c| * coeffL1 p

private theorem coeffL1_C_mul_rejected : ¬ coeffL1_C_mulArena.Law (normRejected 1) := by
  intro h
  have hh := h 0 0
  norm_num [normRejected, realize, coeffL1] at hh

def coeffL1_C_mulEvidence : Registration coeffL1_C_mulArena (coeffL1_C_mulArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨coeffL1_C_mul, normRejected 1, coeffL1_C_mul_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coeffL1_C_mulArena.Law normActual (normRejected 1) coeffL1_C_mul_rejected
  dependence := normDependence

noncomputable def coeffL1_C_mulRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_C_mul)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_C_mul_norm_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_C_mulEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coeffL1_C_mulArena⟩
  objectArena := .source ⟨coeffL1_C_mulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coeffL1_C_mulArena ⟨coeffL1_C_mulEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def coeffL1_X_sub_CArena : Arena where
  signature := normSignature
  Law R := ∀ x : ℝ, R.readout () () (X-C x) = 1+|x|

private theorem coeffL1_X_sub_C_rejected : ¬ coeffL1_X_sub_CArena.Law (normRejected 0) := by
  intro h
  have hh := h 0
  norm_num [normRejected, realize] at hh

def coeffL1_X_sub_CEvidence : Registration coeffL1_X_sub_CArena (coeffL1_X_sub_CArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨coeffL1_X_sub_C, normRejected 0, coeffL1_X_sub_C_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coeffL1_X_sub_CArena.Law normActual (normRejected 0) coeffL1_X_sub_C_rejected
  dependence := normDependence

noncomputable def coeffL1_X_sub_CRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_X_sub_C)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_X_sub_C_norm_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.coeffL1_X_sub_CEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coeffL1_X_sub_CArena⟩
  objectArena := .source ⟨coeffL1_X_sub_CArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coeffL1_X_sub_CArena ⟨coeffL1_X_sub_CEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def interpolate_coeffL1_leArena : Arena where
  signature := normSignature
  Law R := ∀ (s : Finset ℝ) (a b : ℝ) (f : ℝ → ℝ) (B : ℕ → ℝ)
      (_hs : ∀ x ∈ s, x ∈ Icc a b) (_hsunit : ∀ x ∈ s, |x| ≤ 1)
      (_hf : ∀ x ∈ Icc a b, ContDiffAt ℝ (s.card - 1 : ℕ) f x)
      (_hB : ∀ j < s.card, 0 ≤ B j)
      (_hderiv : ∀ j < s.card, ∀ x ∈ Icc a b,
        |iteratedDeriv j f x| ≤ (j.factorial : ℝ) * B j),
      R.readout () () (Lagrange.interpolate s id f) ≤
        ∑ j ∈ range s.card, (2 : ℝ)^j * B j

private theorem interpolate_coeffL1_le_rejected : ¬ interpolate_coeffL1_leArena.Law (normRejected 1) := by
  intro h
  have hh := h ∅ 0 0 (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) (by intro x _; exact contDiffAt_const)
    (by simp) (by simp)
  change (1 : ℝ) ≤ _ at hh
  norm_num at hh

def interpolate_coeffL1_leEvidence : Registration interpolate_coeffL1_leArena (interpolate_coeffL1_leArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨interpolate_coeffL1_le, normRejected 1, interpolate_coeffL1_le_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    interpolate_coeffL1_leArena.Law normActual (normRejected 1) interpolate_coeffL1_le_rejected
  dependence := normDependence

noncomputable def interpolate_coeffL1_leRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.interpolate_coeffL1_le)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.interpolate_coeffL1_le_norm_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.interpolate_coeffL1_leEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨interpolate_coeffL1_leArena⟩
  objectArena := .source ⟨interpolate_coeffL1_leArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source interpolate_coeffL1_leArena ⟨interpolate_coeffL1_leEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def atomic_endpoint_certificateArena : Arena where
  signature := normSignature
  Law R := ∀ (α β : ℝ →₀ ℝ) (η b y : ℝ)
      (_hη : 0 < η) (_hby : b < y) (_hy : y ≤ 1)
      (_hα : ∀ x, 0 ≤ α x) (_hβ : ∀ x, 0 ≤ β x)
      (_hβtotal : β.sum (fun _ w => w) = 1)
      (_hαsupport : ∀ x ∈ α.support, x ∈ Icc 0 y)
      (_hβsupport : ∀ x ∈ β.support, x ∈ Icc 0 b)
      (_hmass : η ≤ α y),
      ∃ P : ℝ[X], P.natDegree < (α.support ∪ β.support).card ∧
        1 ≤ α.sum (fun x w => w * P.eval x) - β.sum (fun x w => w * P.eval x) ∧
        R.readout () () P ≤ (2 / η) * ∑ j ∈ range (α.support ∪ β.support).card,
          (16 / (η * (y - b))) ^ j / (2 * j).factorial

private theorem atomic_endpoint_certificate_rejected : ¬ atomic_endpoint_certificateArena.Law (normRejected 19) := by
  classical
  intro h
  obtain ⟨P, _, _, hh⟩ := h (Finsupp.single 1 1) (Finsupp.single 0 1) 1 0 1
    (by norm_num) (by norm_num) (by norm_num)
    (by intro x; simp [Finsupp.single_apply]; split_ifs <;> norm_num)
    (by intro x; simp [Finsupp.single_apply]; split_ifs <;> norm_num)
    (by simp)
    (by intro x hx; simp at hx; subst x; norm_num)
    (by intro x hx; simp at hx; subst x; norm_num)
    (by simp)
  change (19 : ℝ) ≤ _ at hh
  norm_num [Finset.sum_range_succ] at hh

def atomic_endpoint_certificateEvidence : Registration atomic_endpoint_certificateArena (atomic_endpoint_certificateArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨atomic_endpoint_certificate, normRejected 19, atomic_endpoint_certificate_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    atomic_endpoint_certificateArena.Law normActual (normRejected 19) atomic_endpoint_certificate_rejected
  dependence := normDependence

noncomputable def atomic_endpoint_certificateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.atomic_endpoint_certificate)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.atomic_endpoint_certificate_norm_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.atomic_endpoint_certificateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨atomic_endpoint_certificateArena⟩
  objectArena := .source ⟨atomic_endpoint_certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source atomic_endpoint_certificateArena ⟨atomic_endpoint_certificateEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev laplaceSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ →₀ ℝ, ℝ →₀ ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def laplaceActual : Realization laplaceSignature :=
  realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e)

def laplaceRejected : Realization laplaceSignature :=
  realize laplaceSignature (fun _ p t => atomicLaplace p.2 t) (fun e => nomatch e)

private theorem laplaceDependence : ObservationalDependence laplaceSignature laplaceActual := by
  intro i
  refine ⟨⟨Finsupp.single 1 1, 0⟩, 0, 1, ?_⟩
  change atomicLaplace (Finsupp.single 1 1) 0 ≠ atomicLaplace (Finsupp.single 1 1) 1
  have hn : (1 : ℝ) ≠ Real.exp (-1) :=
    ne_of_gt (Real.exp_lt_one_iff.mpr (by norm_num))
  simpa [atomicLaplace] using hn

private theorem single_nonneg (g x : ℝ) :
    0 ≤ (Finsupp.single g 1 : ℝ →₀ ℝ) x := by
  classical
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

private theorem single_support (g x : ℝ)
    (hx : x ∈ (Finsupp.single g 1 : ℝ →₀ ℝ).support) : x = g := by
  simpa using hx

def sparse_endpoint_coefficient_certificateArena : Arena where
  signature := normSignature
  Law R := ∀ (α β : ℝ →₀ ℝ) (η b y : ℝ)
    (q : ℕ) (hq : 0 < q) (hN : (α.support ∪ β.support).card ≤ q + 1)
    (hη : 0 < η) (hby : b < y) (hy : y ≤ 1)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hβtotal : β.sum (fun _ w => w) = 1)
    (hαsupport : ∀ x ∈ α.support, x ∈ Icc 0 y)
    (hβsupport : ∀ x ∈ β.support, x ∈ Icc 0 b)
    (hmass : η ≤ α y),
    ∃ P : ℝ[X], P.natDegree ≤ q ∧
      1 ≤ α.sum (fun x w => w * P.eval x) - β.sum (fun x w => w * P.eval x) ∧
      R.readout () () P ≤ (2 / η) *
        (Real.exp 1 * max 1 ((16 / (η * (y - b))) / (q : ℝ)^2)) ^ q

private theorem sparse_endpoint_coefficient_certificate_rejected : ¬ sparse_endpoint_coefficient_certificateArena.Law (normRejected 100) := by
  classical
  intro h
  obtain ⟨P, _, _, hh⟩ := h (Finsupp.single 1 1) (Finsupp.single 0 1) 1 0 1 1
    (by norm_num) (by simp) (by norm_num) (by norm_num) (by norm_num)
    (single_nonneg 1) (single_nonneg 0) (by simp)
    (by intro x hx; rw [single_support 1 x hx]; norm_num)
    (by intro x hx; rw [single_support 0 x hx]; norm_num) (by simp)
  change (100 : ℝ) ≤ _ at hh
  norm_num at hh
  have he := Real.exp_one_lt_three
  linarith

def sparse_endpoint_coefficient_certificateEvidence : Registration sparse_endpoint_coefficient_certificateArena (sparse_endpoint_coefficient_certificateArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨sparse_endpoint_coefficient_certificate, normRejected 100, sparse_endpoint_coefficient_certificate_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sparse_endpoint_coefficient_certificateArena.Law normActual (normRejected 100) sparse_endpoint_coefficient_certificate_rejected
  dependence := normDependence

noncomputable def sparse_endpoint_coefficient_certificateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_endpoint_coefficient_certificate)
    (type_of% (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_endpoint_coefficient_certificate_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_endpoint_coefficient_certificateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sparse_endpoint_coefficient_certificateArena⟩
  objectArena := .source ⟨sparse_endpoint_coefficient_certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sparse_endpoint_coefficient_certificateArena ⟨sparse_endpoint_coefficient_certificateEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ p => coeffL1 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def sparse_laplace_grid_certificateArena : Arena where
  signature := laplaceSignature
  Law R := ∀ (μ ν : ℝ →₀ ℝ) (η gμ gν h : ℝ)
    (q : ℕ) (hq : 0 < q) (hN : μ.support.card + ν.support.card ≤ q + 1)
    (hη : 0 < η) (hh : 0 < h) (hg : gμ < gν) (hgμ : 0 ≤ gμ)
    (hμ : ∀ E, 0 ≤ μ E) (hν : ∀ E, 0 ≤ ν E)
    (hνtotal : ν.sum (fun _ w => w) = 1)
    (hμsupport : ∀ E ∈ μ.support, gμ ≤ E)
    (hνsupport : ∀ E ∈ ν.support, gν ≤ E)
    (hmass : η ≤ μ gμ),
    ∃ a : ℕ → ℝ,
      1 ≤ ∑ k ∈ range (q + 1), a k *
        (R.readout () ⟨μ, ν⟩ ((k : ℝ) * h) - atomicLaplace ν ((k : ℝ) * h)) ∧
      (∑ k ∈ range (q + 1), |a k|) ≤ (2 / η) *
        (Real.exp 1 * max 1
          ((16 / (η * (Real.exp (-h * gμ) - Real.exp (-h * gν)))) / (q : ℝ)^2))^q

private theorem sparse_laplace_grid_certificate_rejected : ¬ sparse_laplace_grid_certificateArena.Law (laplaceRejected) := by
  classical
  intro h
  obtain ⟨a, hh, _⟩ := h (Finsupp.single 0 1) (Finsupp.single 1 1) 1 0 1 1 1
    (by norm_num) (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (single_nonneg 0) (single_nonneg 1) (by simp)
    (by intro x hx; rw [single_support 0 x hx])
    (by intro x hx; rw [single_support 1 x hx]) (by simp)
  norm_num [laplaceRejected, realize] at hh

def sparse_laplace_grid_certificateEvidence : Registration sparse_laplace_grid_certificateArena (sparse_laplace_grid_certificateArena.Law laplaceActual) where
  actual := laplaceActual
  bridge := Iff.rfl
  variation := ⟨sparse_laplace_grid_certificate, laplaceRejected, sparse_laplace_grid_certificate_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sparse_laplace_grid_certificateArena.Law laplaceActual (laplaceRejected) sparse_laplace_grid_certificate_rejected
  dependence := laplaceDependence

noncomputable def sparse_laplace_grid_certificateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_laplace_grid_certificate)
    (type_of% (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_laplace_grid_certificate_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_laplace_grid_certificateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sparse_laplace_grid_certificateArena⟩
  objectArena := .source ⟨sparse_laplace_grid_certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sparse_laplace_grid_certificateArena ⟨sparse_laplace_grid_certificateEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def sparse_laplace_window_certificateArena : Arena where
  signature := laplaceSignature
  Law R := ∀ (μ ν : ℝ →₀ ℝ) (η E gμ gν U : ℝ)
    (m : ℕ) (hm : 0 < m) (hU : 0 < U) (hE : 0 < E)
    (hη : 0 < η) (hη1 : η ≤ 1) (hgμ : 0 ≤ gμ) (hg : gμ < gν) (hgν : gν ≤ E)
    (hμ : ∀ t, 0 ≤ μ t) (hν : ∀ t, 0 ≤ ν t)
    (hνtotal : ν.sum (fun _ w => w) = 1)
    (hμsupport : ∀ t ∈ μ.support, gμ ≤ t)
    (hνsupport : ∀ t ∈ ν.support, gν ≤ t)
    (hmass : η ≤ μ gμ) (hμcard : μ.support.card ≤ m) (hνcard : ν.support.card ≤ m)
    (hmcap : m ≤ ⌈3 / Real.sqrt (η * ((gν - gμ) / E))⌉₊),
    let q := 2 * m - 1
    let M := max 1 ((q : ℝ) / U)
    let h := 1 / (M * E)
    ∃ a : ℕ → ℝ,
      (∀ k ≤ q, (k : ℝ) * h ∈ Icc 0 (U / E)) ∧
      1 ≤ ∑ k ∈ range (q + 1), a k *
        (R.readout () ⟨μ, ν⟩ ((k : ℝ) * h) - atomicLaplace ν ((k : ℝ) * h)) ∧
      (∑ k ∈ range (q + 1), |a k|) ≤
        (288 * M / (η^2 * (m : ℝ)^2 * ((gν - gμ) / E)))^q

private theorem sparse_laplace_window_certificate_rejected : ¬ sparse_laplace_window_certificateArena.Law (laplaceRejected) := by
  classical
  intro h
  obtain ⟨a, _, hh, _⟩ := h (Finsupp.single 0 1) (Finsupp.single 1 1) 1 1 0 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (single_nonneg 0) (single_nonneg 1) (by simp)
    (by intro x hx; rw [single_support 0 x hx])
    (by intro x hx; rw [single_support 1 x hx])
    (by simp) (by simp) (by simp) (by norm_num)
  norm_num [laplaceRejected, realize] at hh

def sparse_laplace_window_certificateEvidence : Registration sparse_laplace_window_certificateArena (sparse_laplace_window_certificateArena.Law laplaceActual) where
  actual := laplaceActual
  bridge := Iff.rfl
  variation := ⟨sparse_laplace_window_certificate, laplaceRejected, sparse_laplace_window_certificate_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sparse_laplace_window_certificateArena.Law laplaceActual (laplaceRejected) sparse_laplace_window_certificate_rejected
  dependence := laplaceDependence

noncomputable def sparse_laplace_window_certificateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_laplace_window_certificate)
    (type_of% (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_laplace_window_certificate_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.sparse_laplace_window_certificateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sparse_laplace_window_certificateArena⟩
  objectArena := .source ⟨sparse_laplace_window_certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sparse_laplace_window_certificateArena ⟨sparse_laplace_window_certificateEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def ordered_laplace_joint_certificateArena : Arena where
  signature := laplaceSignature
  Law R := ∀ (μ ν : ℝ →₀ ℝ) (η E gμ gν U : ℝ)
    (d : ℕ) (hd : 0 < d) (hU : 0 < U) (hE : 0 < E)
    (hη : 0 < η) (hη1 : η ≤ 1) (hgμ : 0 ≤ gμ) (hg : gμ < gν) (hgν : gν ≤ E)
    (hμ : ∀ t, 0 ≤ μ t) (hν : ∀ t, 0 ≤ ν t)
    (hμtotal : μ.sum (fun _ w => w) = 1) (hνtotal : ν.sum (fun _ w => w) = 1)
    (hμsupport : ∀ t ∈ μ.support, t ∈ Icc gμ E)
    (hνsupport : ∀ t ∈ ν.support, t ∈ Icc gν E)
    (hmass : η ≤ μ gμ) (hμcard : μ.support.card ≤ d) (hνcard : ν.support.card ≤ d),
    let Δ := (gν - gμ) / E
    let m := min d ⌈3 / Real.sqrt (η * Δ)⌉₊
    let q := 2 * m - 1
    let M := max 1 ((q : ℝ) / U)
    let h := 1 / (M * E)
    0 < m ∧ m ≤ d ∧ (m : ℝ)^2 * Δ ≤ 16 / η ∧
      ∃ c : ℕ → ℝ, (∀ k ≤ q, (k : ℝ) * h ∈ Icc 0 (U / E)) ∧
        1 ≤ ∑ k ∈ range (q + 1), c k *
          (R.readout () ⟨μ, ν⟩ ((k : ℝ) * h) - atomicLaplace ν ((k : ℝ) * h)) ∧
        (∑ k ∈ range (q + 1), |c k|) ≤ (1024 * M / (η^2 * (m : ℝ)^2 * Δ))^q

private theorem ordered_laplace_joint_certificate_rejected : ¬ ordered_laplace_joint_certificateArena.Law (laplaceRejected) := by
  classical
  intro h
  obtain ⟨_, _, _, a, _, hh, _⟩ := h (Finsupp.single 0 1) (Finsupp.single 1 1) 1 1 0 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (single_nonneg 0) (single_nonneg 1) (by simp) (by simp)
    (by intro x hx; rw [single_support 0 x hx]; norm_num)
    (by intro x hx; rw [single_support 1 x hx]; norm_num)
    (by simp) (by simp) (by simp)
  norm_num [laplaceRejected, realize] at hh

def ordered_laplace_joint_certificateEvidence : Registration ordered_laplace_joint_certificateArena (ordered_laplace_joint_certificateArena.Law laplaceActual) where
  actual := laplaceActual
  bridge := Iff.rfl
  variation := ⟨ordered_laplace_joint_certificate, laplaceRejected, ordered_laplace_joint_certificate_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    ordered_laplace_joint_certificateArena.Law laplaceActual (laplaceRejected) ordered_laplace_joint_certificate_rejected
  dependence := laplaceDependence

noncomputable def ordered_laplace_joint_certificateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.ordered_laplace_joint_certificate)
    (type_of% (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.ordered_laplace_joint_certificate_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.ordered_laplace_joint_certificateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨ordered_laplace_joint_certificateArena⟩
  objectArena := .source ⟨ordered_laplace_joint_certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ordered_laplace_joint_certificateArena ⟨ordered_laplace_joint_certificateEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def laplace_joint_certificatesArena : Arena where
  signature := laplaceSignature
  Law R := ∀ (μ ν : ℝ →₀ ℝ) (η E gμ gν : ℝ)
    (d : ℕ) (hd : 0 < d) (hE : 0 < E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hgμ : gμ ∈ Icc 0 E) (hgν : gν ∈ Icc 0 E) (hne : gμ ≠ gν)
    (hμ : ∀ t, 0 ≤ μ t) (hν : ∀ t, 0 ≤ ν t)
    (hμtotal : μ.sum (fun _ w => w) = 1) (hνtotal : ν.sum (fun _ w => w) = 1)
    (hμsupport : ∀ t ∈ μ.support, t ∈ Icc gμ E)
    (hνsupport : ∀ t ∈ ν.support, t ∈ Icc gν E)
    (hμmass : η ≤ μ gμ) (hνmass : η ≤ ν gν)
    (hμcard : μ.support.card ≤ d) (hνcard : ν.support.card ≤ d),
    let Δ := |gμ - gν| / E
    let m := min d ⌈3 / Real.sqrt (η * Δ)⌉₊
    let q := 2 * m - 1
    0 < m ∧ m ≤ d ∧ (m : ℝ)^2 * Δ ≤ 16 / η ∧
      (∃ c : ℕ → ℝ,
        1 ≤ ∑ k ∈ range (q + 1), c k * (R.readout () ⟨μ, ν⟩ ((k : ℝ) / E) -
          atomicLaplace ν ((k : ℝ) / E)) ∧
        (∑ k ∈ range (q + 1), |c k|) ≤ (1024 / (η^2 * (m : ℝ)^2 * Δ))^q) ∧
      (∀ U : ℝ, 0 < U →
        let M := max 1 ((q : ℝ) / U)
        let h := 1 / (M * E)
        ∃ c : ℕ → ℝ, (∀ k ≤ q, (k : ℝ) * h ∈ Icc 0 (U / E)) ∧
          1 ≤ ∑ k ∈ range (q + 1), c k *
            (atomicLaplace μ ((k : ℝ) * h) - atomicLaplace ν ((k : ℝ) * h)) ∧
          (∑ k ∈ range (q + 1), |c k|) ≤ (1024 * M / (η^2 * (m : ℝ)^2 * Δ))^q)

private theorem laplace_joint_certificates_rejected : ¬ laplace_joint_certificatesArena.Law (laplaceRejected) := by
  classical
  intro h
  obtain ⟨_, _, _, ⟨a, hh, _⟩, _⟩ := h (Finsupp.single 0 1) (Finsupp.single 1 1) 1 1 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (single_nonneg 0) (single_nonneg 1) (by simp) (by simp)
    (by intro x hx; rw [single_support 0 x hx]; norm_num)
    (by intro x hx; rw [single_support 1 x hx]; norm_num)
    (by simp) (by simp) (by simp) (by simp)
  norm_num [laplaceRejected, realize] at hh

def laplace_joint_certificatesEvidence : Registration laplace_joint_certificatesArena (laplace_joint_certificatesArena.Law laplaceActual) where
  actual := laplaceActual
  bridge := Iff.rfl
  variation := ⟨laplace_joint_certificates, laplaceRejected, laplace_joint_certificates_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    laplace_joint_certificatesArena.Law laplaceActual (laplaceRejected) laplace_joint_certificates_rejected
  dependence := laplaceDependence

noncomputable def laplace_joint_certificatesRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.laplace_joint_certificates)
    (type_of% (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.laplace_joint_certificates_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget.laplace_joint_certificatesEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨laplace_joint_certificatesArena⟩
  objectArena := .source ⟨laplace_joint_certificatesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source laplace_joint_certificatesArena ⟨laplace_joint_certificatesEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize laplaceSignature (fun _ p t => atomicLaplace p.1 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.UniformCoefficientBudget
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Interpolation.UniformCoefficientBudget
