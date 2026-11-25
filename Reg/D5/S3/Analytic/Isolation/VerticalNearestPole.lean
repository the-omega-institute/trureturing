import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Isolation.VerticalNearestPole
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

open _root_.D5.S3.Analytic.Isolation.VerticalNearestPole
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter Metric
open scoped Topology BigOperators

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Analytic.Isolation.VerticalNearestPole

private theorem singleton_discrete (z₀ : ℂ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ ({z₀} : Set ℂ) := by
  exact disjoint_principal_right.mp
    (isClosed_and_discrete_iff.mp
      ⟨isClosed_singleton, (finite_singleton z₀).isDiscrete⟩ z)

namespace Perturbation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _σ : ℝ, ℝ)
    (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p z => dist (verticalCenter p.1 p.2) z) (fun e => nomatch e)

def rejected (d : ℝ) : Realization signature :=
  realize signature (fun _ _ _ => d) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  change dist (verticalCenter 0 0) 0 ≠ dist (verticalCenter 0 0) 1
  have hz : verticalCenter 0 0 = (0 : ℂ) := by apply Complex.ext <;> rfl
  rw [hz]
  simp


def arena : Arena where
  signature := signature
  Law V := ∀ {Z : Set ℂ},
    (∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) →
    ∀ {σ D ε : ℝ}, (∀ z ∈ Z, z.re < σ) → D < σ → 0 < ε →
    ∀ {z₀ : ℂ}, z₀ ∈ Z → σ - z₀.re < D →
    ∃ t : ℝ, |t - z₀.im| < ε ∧ ∃ z ∈ Z, ∃ R : ℝ,
      V.readout () ⟨σ, t⟩ z < R ∧ R ≤ D ∧
        ∀ w ∈ Z, w ∈ ball (verticalCenter σ t) R → w = z

private theorem rejected_fails : ¬ arena.Law (rejected 2) := by
  intro H
  obtain ⟨t, ht, z, hz, R, hnear, hR, hunique⟩ :=
    @H ({((3 : ℝ) / 2 : ℂ)} : Set ℂ)
      (fun z _ => singleton_discrete _ z) 2 1 1
      (by intro z hz; rcases mem_singleton_iff.mp hz with rfl; norm_num)
      (by norm_num) (by norm_num) ((3 : ℝ) / 2 : ℂ) (mem_singleton _)
      (by norm_num)
  change (2 : ℝ) < R at hnear
  linarith

def family : Registration arena (type_of% @isolated_nearest_of_vertical_perturbation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isolated_nearest_of_vertical_perturbation, rejected 2, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual (rejected 2) rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isolated_nearest_of_vertical_perturbation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Isolation.VerticalNearestPole.perturbationUnit
  realizationName := `Reg.D5.S3.Analytic.Isolation.VerticalNearestPole.Perturbation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z => dist (verticalCenter p.1 p.2) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Isolation.VerticalNearestPole
    definition := none
    coordinates := #[2, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg",
        "arg", "body", "arg", "arg", "body", "fn", "arg",
        "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Perturbation

namespace Dichotomy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ σ z => dist (σ : ℂ) z) (fun e => nomatch e)

def rejected (d : ℝ) : Realization signature :=
  realize signature (fun _ _ _ => d) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change dist (0 : ℂ) 0 ≠ dist (0 : ℂ) 1
  simp


def arena : Arena where
  signature := signature
  Law V := ∀ {Z : Set ℂ},
    (∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) →
    ∀ {σ θ : ℝ}, (∀ z ∈ Z, z.re < σ) → 0 < θ →
    ∀ {z₀ : ℂ}, z₀ ∈ Z → θ < z₀.re →
    (∃ D : ℝ, 0 < D ∧ D ≤ σ - θ ∧
      (∀ w ∈ Z, D ≤ V.readout () σ w) ∧
        ∃ z ∈ Z, σ - z.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ R : ℝ,
      σ - β < R ∧ R ≤ σ - θ ∧ ∀ w ∈ Z,
        w ∈ ball (σ : ℂ) R → w = (β : ℂ))

private theorem rejected_fails : ¬ arena.Law (rejected 0) := by
  intro H
  have h := @H ({(1 + Complex.I)} : Set ℂ)
    (fun z _ => singleton_discrete _ z) 2 ((1 : ℝ) / 2)
    (by intro z hz; rcases mem_singleton_iff.mp hz with rfl; norm_num)
    (by norm_num) (1 + Complex.I) (mem_singleton _) (by norm_num)
  rcases h with ⟨D, hD, hDbound, hfree, z, hz, haccessible⟩ |
    ⟨β, hβ, hβthreshold, R, hR, hRbound, hunique⟩
  · have hzero := hfree (1 + Complex.I) (mem_singleton _)
    change D ≤ (0 : ℝ) at hzero
    linarith
  · have hcomplex : (β : ℂ) = 1 + Complex.I := mem_singleton_iff.mp hβ
    have him := congrArg Complex.im hcomplex
    norm_num at him

def family : Registration arena (type_of% @real_center_spectral_dichotomy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@real_center_spectral_dichotomy, rejected 0, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual (rejected 0) rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@real_center_spectral_dichotomy) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Isolation.VerticalNearestPole.dichotomyUnit
  realizationName := `Reg.D5.S3.Analytic.Isolation.VerticalNearestPole.Dichotomy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ σ z => dist (σ : ℂ) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Isolation.VerticalNearestPole
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg", "body", "arg",
        "arg", "fn", "arg", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dichotomy

namespace Regularized

abbrev parameters := Σ ι : Type u, Σ _ : Fintype ι, ℂ
abbrev signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature parameters.{u}
    (fun _ => ℂ → ℂ) (fun _ => WithTop ℤ)
def actual : Realization signature :=
  realize signature (fun _ p F => meromorphicOrderAt F p.2.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [index : Fintype ι] (f : ι → ℂ → ℂ)
    (a : ι → ℝ) (K : ℂ),
    (∀ i, Differentiable ℂ (f i)) → (∀ i, f i 1 ≠ 0) → (∀ i, 0 < a i) →
    (∀ s : ℂ, s ≠ 1 → regularizedLogFamily f a K s =
      -((∑ i, (a i : ℂ) * logDeriv (f i) s) -
        s * (∑ i, (a i : ℂ) * logDeriv (f i) 1) + K * (1 - s)) / (s * (s - 1))) ∧
    (∀ r : ℂ, r ≠ 0 → (∀ i, f i r ≠ 0) →
      AnalyticAt ℂ (regularizedLogFamily f a K) r) ∧
    (∀ r : ℂ, r ≠ 0 → (∃ i, f i r = 0) →
      let c : ℝ := ∑ i, a i * analyticOrderNatAt (f i) r
      0 < c ∧ (-1 / (r * (r - 1))) * (c : ℂ) ≠ 0 ∧
        (∃ J : ℂ → ℂ, AnalyticAt ℂ J r ∧
          regularizedLogFamily f a K =ᶠ[𝓝[≠] r]
            fun z => ((-1 / (r * (r - 1))) * (c : ℂ)) / (z - r) + J z) ∧
        R.readout () ⟨ι, index, r⟩ (regularizedLogFamily f a K) = -1)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Unit) inferInstance (fun _ z => z - 2) (fun _ => 1) 0
    (by intro i; fun_prop) (by intro i; norm_num) (by intro i; norm_num)
  have heq : (0 : WithTop ℤ) = -1 :=
    (h0.2.2 2 (by norm_num) ⟨⟨()⟩, by norm_num⟩).2.2.2
  norm_num at heq

def family : Registration arena.{u} (type_of% @regularized_positive_log_family.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@regularized_positive_log_family.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := by
    change ObservationalDependence signature.{u} actual.{u}
    intro i
    refine ⟨⟨ULift.{u} Unit, inferInstance, 0⟩, id, fun _ => 1, ?_⟩
    change meromorphicOrderAt id (0 : ℂ) ≠ meromorphicOrderAt (fun _ : ℂ => 1) 0
    rw [meromorphicOrderAt_id, meromorphicOrderAt_const]
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@regularized_positive_log_family.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Analytic.Isolation.VerticalNearestPole.regularizedUnit
  realizationName := `Reg.D5.S3.Analytic.Isolation.VerticalNearestPole.Regularized.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p F => meromorphicOrderAt F p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Isolation.VerticalNearestPole
    definition := none
    coordinates := #[0, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg",
      "arg", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Regularized

end Reg.D5.S3.Analytic.Isolation.VerticalNearestPole
