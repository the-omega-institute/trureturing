import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.CdsoAllocationGerms
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! The source audit observes the actual removable extension in its first analytic clause. -/

open Filter
open scoped Topology
open CdsoPeriodic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Analytic.PowerSeries.CdsoAllocationGerms

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (ℕ × ℕ) (fun P => AllocationData P.1 P.2) (fun _ => ℝ → ℝ)

def actual : Realization signature := realize signature
  (fun _ _ b => b.extension) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => abs) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a h : ℕ} (ha : 2 ≤ a) (b c : AllocationData a h),
    AnalyticAt ℝ (R.readout () (a,h) b) 0 ∧ AnalyticAt ℝ c.extension 0 ∧
    b.actual =ᶠ[𝓝[>] 0] b.extension ∧ c.actual =ᶠ[𝓝[>] 0] c.extension ∧
    (b.actual =ᶠ[𝓝[>] 0] c.actual ↔
      ∀ k ≤ 3*(6*(a+1+h)+5)^2,
        iteratedDeriv k b.extension 0 / k.factorial =
          iteratedDeriv k c.extension 0 / k.factorial)

private def admissibleDatum (a h : ℕ) (hh : 0 < h) :
    {b : AllocationData a h // b.Admissible} := by
  let b : AllocationData a h :=
    ⟨1, by decide, hh, 0, by omega, 0, by omega,
      fun i => if i = 0 then (h : ℤ) else 0⟩
  refine ⟨b, ?_⟩
  simp [AllocationData.Admissible, AllocationData.n, b,
    max_eq_left (Nat.cast_nonneg h : (0 : ℤ) ≤ h),
    max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg h : (0 : ℤ) ≤ h))]

def b0 : AllocationData 2 2 := (admissibleDatum 2 2 (by decide)).val

def b1 : AllocationData 2 2 :=
  ⟨2, by decide, by decide, 0, by decide, 0, by decide,
    fun i => if i = 0 then 1 else 0⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hA : AnalyticAt ℝ (abs : ℝ → ℝ) 0 := (h (by decide) b0 b0).1
  exact not_differentiableAt_abs_zero hA.differentiableAt

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(2,2), b0, b1, ?_⟩
  intro he
  have he0 := congrFun he 0
  norm_num [actual, realize, AllocationData.extension, AllocationData.combination,
    radicalExtension, AllocationData.alpha, AllocationData.beta, AllocationData.r,
    AllocationData.m, AllocationData.n, b0, b1, admissibleDatum, Fin.sum_univ_succ] at he0

def family : Registration arena (type_of% @allocation_germ_iff_taylor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@allocation_germ_iff_taylor, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration (@allocation_germ_iff_taylor)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.CdsoAllocationGerms.allocation_unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.CdsoAllocationGerms.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b.extension) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.CdsoAllocationGerms
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Analytic.PowerSeries.CdsoAllocationGerms
