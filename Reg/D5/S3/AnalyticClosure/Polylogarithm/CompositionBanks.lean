import D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks

open _root_.D5.S3.AnalyticClosure.Polylogarithm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex Filter Set LeanInformationAudit
open scoped ComplexConjugate
noncomputable section

abbrev signature : Signature where
  Params := ℕ+ × List ℕ+ × ℕ+
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z ↦ CompositionContinuation.continued (p.1 :: p.2.1) z) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+),
    let A : ℂ → ℂ := fun z ↦
      (z ^ CompositionDisk.depth tail / R.readout () (head, tail, ell) z) ^ (ell : ℕ)
    let endpoint : ℂ := if 1 < (head : ℕ) then
      ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0
    ∃ rho : ℝ, 0 < rho ∧ rho < 1 ∧
      (∀ z ∈ CompositionContinuation.omega, ‖z - 1‖ ≤ rho →
        R.readout () (head, tail, ell) z ≠ 0) ∧
      Tendsto A (nhdsWithin 1 CompositionContinuation.omega) (nhds endpoint) ∧
      ∃ upper lower : ℂ → ℂ,
        ContinuousOn upper {z | ‖z - 1‖ ≤ rho ∧ 0 ≤ z.im} ∧
        ContinuousOn lower {z | ‖z - 1‖ ≤ rho ∧ z.im ≤ 0} ∧
        (∀ z, ‖z - 1‖ ≤ rho → 0 ≤ z.im → z ∈ CompositionContinuation.omega → upper z = A z) ∧
        (∀ z, ‖z - 1‖ ≤ rho → z.im ≤ 0 → z ∈ CompositionContinuation.omega → lower z = A z) ∧
        upper 1 = endpoint ∧ lower 1 = endpoint ∧
        (∀ z, ‖z - 1‖ ≤ rho → z.im ≤ 0 → lower z = conj (upper (conj z))) ∧
        ∀ t : ℝ, 0 < t → t ≤ rho → (upper (1 + (t : ℂ))).im < 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, hrho, _, hn, _⟩ := h 1 [] 1
  have ho : ((1 - rho / 2 : ℝ) : ℂ) ∈ CompositionContinuation.omega := by
    change 1 - ((1 - rho / 2 : ℝ) : ℂ) ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [sub_re, one_re, ofReal_re]
    linarith
  have hd : ‖((1 - rho / 2 : ℝ) : ℂ) - 1‖ ≤ rho := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    rw [abs_of_neg (by linarith : 1 - rho / 2 - 1 < 0)]
    linarith
  exact (hn _ ho hd) rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hz := (CompositionSlit.result.2.2.1 1 []).1
  obtain ⟨_, _, R0, hR0, hn⟩ := CompositionZeroFreeCollar.result 1 []
  have ho : (1 / 2 : ℂ) ∈ CompositionContinuation.omega := by
    norm_num [CompositionContinuation.omega, Complex.mem_slitPlane_iff]
  have hne := hn (1 / 2) ho (by norm_num; linarith)
  have hc : CompositionContinuation.continued [1] (1 / 2) ≠ 0 := by
    intro he
    apply hne
    rw [CompositionZeroFreeCollar.normalizedContinuation,
      ite_eq_right (by norm_num : (1 / 2 : ℂ) ≠ 0), he, zero_div]
  refine ⟨(1, [], 1), 0, (1 / 2), ?_⟩
  change CompositionContinuation.continued [1] 0 ≠
    CompositionContinuation.continued [1] (1 / 2)
  rw [hz]
  exact hc.symm

def sourceEvidence : Registration arena (type_of% (@CompositionBanks.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨CompositionBanks.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def result_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@CompositionBanks.result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks.resultUnit
  realizationName := `Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z ↦ CompositionContinuation.continued (p.1 :: p.2.1) z) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "value", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks
