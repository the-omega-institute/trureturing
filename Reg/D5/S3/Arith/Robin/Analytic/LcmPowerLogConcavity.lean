import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
import Reg.Support.DependentFamily

/-! The whole logarithmic concavity law with its actual real function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ κ t => logPowerDifference κ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 1 < κ →
    StrictConcaveOn ℝ (Ioi 0) (R.readout () κ) ∧
      ConcaveOn ℝ (Ici 0) (logPowerDifference κ) ∧ logPowerDifference κ 0 = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h (κ := 2) (by norm_num)).1
  have hb := hs.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) ≠ 2)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [rejected, realize] at hb

def family : Registration arena (type_of% @logPowerDifference_concavity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logPowerDifference_concavity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change logPowerDifference 2 0 ≠ logPowerDifference 2 1
    norm_num [logPowerDifference, powerDifference, Real.rpow_ofNat]
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@logPowerDifference_concavity) (Realization signature) Type Unit where
  unitName := `LcmPowerLogConcavity.logPowerDifference_concavity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ t => logPowerDifference κ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      functionOperand := true
      stateBinder := 0
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Curvature

def actual : Realization signature :=
  realize signature (fun _ κ t => powerDifference κ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ t : ℝ}, 0 < t →
    (deriv (R.readout () κ) t) ^ (2 : ℝ) -
        powerDifference κ t * deriv (deriv (powerDifference κ)) t =
      κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) ^ (2 : ℝ) +
        κ * (κ - 1) * (t * (1 + t)) ^ (κ - 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (t := 1) (by norm_num)
  have hc : powerDifference 2 = fun t : ℝ => 1 + 2 * t := by
    funext t
    norm_num [powerDifference, Real.rpow_ofNat]
    ring
  norm_num [rejected, realize, hc, Real.rpow_ofNat, deriv_const_add, deriv_const_mul] at hb

def family : Registration arena (type_of% @powerDifference_curvature) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@powerDifference_curvature, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, powerDifference, Real.rpow_ofNat]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@powerDifference_curvature) (Realization signature) Type Unit where
  unitName := `LcmPowerLogConcavity.powerDifference_curvature.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity.Curvature.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ t => powerDifference κ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Curvature
namespace Positive

def actual : Realization signature :=
  realize signature (fun _ κ t => powerDifference κ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ κ t => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ t : ℝ}, 1 < κ → 0 ≤ t → 0 < R.readout () κ t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (t := 0) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hb

def family : Registration arena (type_of% @difference_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@difference_pos, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, powerDifference, Real.rpow_ofNat]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@difference_pos) (Realization signature) Type Unit where
  unitName := `LcmPowerLogConcavity.difference_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ t => powerDifference κ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positive
namespace Derivative

def actual : Realization signature :=
  realize signature (fun _ κ t => logPowerDifference κ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ κ t => logPowerDifference κ t + t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ t : ℝ}, 1 < κ → 0 < t → HasDerivAt (R.readout () κ)
    (κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) / powerDifference κ t) t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (t := 1) (by norm_num) (by norm_num)
  have hd := (log_derivative (κ := 2) (t := 1) (by norm_num) (by norm_num)).add
    (hasDerivAt_id (1 : ℝ))
  have he := hb.unique hd
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @log_derivative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_derivative, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change logPowerDifference 2 0 ≠ logPowerDifference 2 1
    have hz : logPowerDifference 2 0 = 0 := by norm_num [logPowerDifference, powerDifference]
    have hp : 0 < logPowerDifference 2 1 := by
      norm_num [logPowerDifference, powerDifference, Real.rpow_ofNat]
      exact Real.log_pos (by norm_num)
    rw [hz]
    exact hp.ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_derivative) (Realization signature) Type Unit where
  unitName := `LcmPowerLogConcavity.log_derivative.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ t => logPowerDifference κ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivative
end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
