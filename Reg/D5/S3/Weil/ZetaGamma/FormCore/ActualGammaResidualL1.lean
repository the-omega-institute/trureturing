/- One public theorem, complete a>0 telescope and all five conclusions.
The selected source occurrence is only the exact norm-series RHS in clause 4. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
import Reg.Support.DependentFamily
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => ∑' n : ℕ, Real.pi /
    (((n : ℝ) + 1 / 4) * (a + ((n : ℝ) + 1 / 4))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a : ℝ) (_ha : 0 < a),
    Integrable (fun x : ℝ => ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
      (Complex.digamma (1 / 4)).re) / (x ^ 2 + a ^ 2)) volume ∧
      Summable (fun n : ℕ => Real.pi /
        (((n : ℝ) + 1 / 4) * (a + ((n : ℝ) + 1 / 4)))) ∧
      (∀ n : ℕ,
        Integrable (fun x : ℝ => x ^ 2 /
          (((n : ℝ) + 1 / 4) * (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2) *
            (x ^ 2 + a ^ 2))) volume ∧
        (∫ x : ℝ, ‖x ^ 2 /
          (((n : ℝ) + 1 / 4) * (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2) *
            (x ^ 2 + a ^ 2))‖) =
          Real.pi / (((n : ℝ) + 1 / 4) *
            (a + ((n : ℝ) + 1 / 4)))) ∧
      ((∫ x : ℝ, ‖((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
      (Complex.digamma (1 / 4)).re) / (x ^ 2 + a ^ 2)‖) =
        r.readout () () a) ∧
      (∀ x : ℝ,
        HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) -
          ((n : ℝ) + 1 / 4) / (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2))
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
            (Complex.digamma (1 / 4)).re))

private theorem source_reconstruction :
    (type_of% (@actual_digamma_quarter_resolvent_l1_domain_and_series)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall 1 (by norm_num)).2.2.2.1
  change (∫ x : ℝ, ‖((Complex.digamma ((1 / 4 : ℂ) +
      Complex.I * (x : ℂ))).re - (Complex.digamma (1 / 4)).re) /
        (x ^ 2 + (1 : ℝ) ^ 2)‖) = (-1 : ℝ) at hbad
  have hnonneg : 0 ≤ ∫ x : ℝ, ‖((Complex.digamma ((1 / 4 : ℂ) +
      Complex.I * (x : ℂ))).re - (Complex.digamma (1 / 4)).re) /
        (x ^ 2 + (1 : ℝ) ^ 2)‖ :=
    integral_nonneg fun x => norm_nonneg _
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
  change (∑' n : ℕ, Real.pi /
    (((n : ℝ) + 1 / 4) * ((1 : ℝ) + ((n : ℝ) + 1 / 4)))) ≠
      ∑' n : ℕ, Real.pi /
        (((n : ℝ) + 1 / 4) * ((2 : ℝ) + ((n : ℝ) + 1 / 4)))
  have hs1 :=
    (actual_digamma_quarter_resolvent_l1_domain_and_series 1 (by norm_num)).2.1
  have hs2 :=
    (actual_digamma_quarter_resolvent_l1_domain_and_series 2 (by norm_num)).2.1
  have hle (n : ℕ) : Real.pi /
      (((n : ℝ) + 1 / 4) * ((2 : ℝ) + ((n : ℝ) + 1 / 4))) ≤
        Real.pi /
          (((n : ℝ) + 1 / 4) * ((1 : ℝ) + ((n : ℝ) + 1 / 4))) := by
    have hc : 0 < (n : ℝ) + 1 / 4 := by positivity
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    nlinarith
  have hstrict0 : Real.pi /
      ((((0 : ℕ) : ℝ) + 1 / 4) * ((2 : ℝ) + (((0 : ℕ) : ℝ) + 1 / 4))) <
        Real.pi /
          ((((0 : ℕ) : ℝ) + 1 / 4) * ((1 : ℝ) + (((0 : ℕ) : ℝ) + 1 / 4))) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    norm_num
  have hlt := Summable.tsum_lt_tsum hle hstrict0 hs2 hs1
  exact ne_of_gt hlt

def familyRegistration : Registration arena
    (type_of% (@actual_digamma_quarter_resolvent_l1_domain_and_series)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_digamma_quarter_resolvent_l1_domain_and_series,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The two original binders are a,ha. Keep all five original conclusions.
The selected scalar is the right side of the equality in clause 4 only:
body/body, then three right And arguments, then left And argument, Eq RHS.
Original binder 0 is the genuine scalar state. No unrelated input is added. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_digamma_quarter_resolvent_l1_domain_and_series)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ a => ∑' n : ℕ, Real.pi /
      (((n : ℝ) + 1 / 4) * (a + ((n : ℝ) + 1 / 4))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
