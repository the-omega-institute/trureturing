import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-!
# Information-Escape Registrations for Two-Node Schur-Ratio Regions

Faithful four-slot dependent-family registrations for all six public theorems of
`D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

noncomputable section
universe u

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
  (selfConjugate e h schurHook Q)
open _root_.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion

/-! ## 1. `alternating_choose_twoH_eq` -/

abbrev degSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def degActual : Realization degSignature :=
  realize degSignature (fun _ _ t => t - 1) (fun e => nomatch e)

def degRejected : Realization degSignature :=
  realize degSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem degDependence : ObservationalDependence degSignature degActual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change (1 - 1 : ℕ) ≠ 2 - 1
  decide

def alternatingArena : Arena where
  signature := degSignature
  Law R := ∀ {R₀ : Type u} [CommRing R₀] (t : ℕ) (x y : R₀) (_ht : 2 ≤ t),
    (∑ d ∈ Finset.range (t - 1),
      (-1 : R₀) ^ d * (t.choose (d + 2) : R₀) * twoH (d + 1) x y) =
      (t : R₀) - twoH (R.readout () () t) (1 - x) (1 - y)

private theorem alternating_rejected : ¬ alternatingArena.{u}.Law degRejected := by
  intro hlaw
  have hh := @hlaw (ULift.{u} ℝ) inferInstance 2 (0 : ULift.{u} ℝ) (0 : ULift.{u} ℝ) (by decide)
  have hread : degRejected.readout () () 2 = 0 := rfl
  rw [hread] at hh
  have hval := congrArg ULift.down hh
  norm_num [twoH] at hval

def alternatingEvidence :
    Registration alternatingArena.{u} (type_of% @alternating_choose_twoH_eq.{u}) where
  actual := degActual
  bridge := Iff.rfl
  variation := ⟨@alternating_choose_twoH_eq.{u}, degRejected, alternating_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    alternatingArena.{u}.Law degActual degRejected alternating_rejected
  dependence := degDependence

def alternatingRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@alternating_choose_twoH_eq.{u}) (Realization degSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.alternating_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.alternatingEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨alternatingArena⟩
  objectArena := .source ⟨alternatingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source alternatingArena ⟨alternatingEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize degSignature (fun _ _ t => t - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-! ## 2. `Q_two_node_closed_form` -/

abbrev q2Signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 2 → ℂ) (fun _ => ℂ)

def q2Actual : Realization q2Signature :=
  realize q2Signature (fun _ _ ζ => Q 2 2 1 ζ) (fun e => nomatch e)

def q2Rejected : Realization q2Signature :=
  realize q2Signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem q_zero_at_zero (t : ℕ) : Q t 2 1 (0 : Fin 2 → ℂ) = 0 := by
  have he0 : e 1 (0 : Fin 2 → ℂ) = 0 := by
    simp [e, Finset.powersetCard_one]
  unfold Q
  simp [he0]

private theorem q2Dependence : ObservationalDependence q2Signature q2Actual := by
  intro _
  refine ⟨(), 0, negConjPair 0 0 + 1, ?_⟩
  change Q 2 2 1 0 ≠ Q 2 2 1 (negConjPair 0 0 + 1)
  rw [q_zero_at_zero 2,
    (Q_two_node_closed_form 2 0 0 (by decide) (by norm_num) (by norm_num)).2]
  exact zero_ne_one

def qClosedFormArena : Arena where
  signature := q2Signature
  Law R := ∀ (t : ℕ) (a b : ℝ) (_ht : 2 ≤ t)
    (_hab : a ^ 2 + b ^ 2 ≤ 1) (_hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1),
    Q t 2 1 (negConjPair a b + 1) =
      ((t : ℂ) - h (t - 1) (conjPair a b)) / ((t : ℂ) * ((t : ℂ) - 1) * (1 - (a : ℂ))) ∧
    R.readout () () (negConjPair a b + 1) = 1

private theorem qClosedForm_rejected : ¬ qClosedFormArena.Law q2Rejected := by
  intro hlaw
  have hh := (hlaw 2 0 0 (by decide) (by norm_num) (by norm_num)).2
  norm_num [q2Rejected, realize] at hh

def qClosedFormEvidence :
    Registration qClosedFormArena (qClosedFormArena.Law q2Actual) where
  actual := q2Actual
  bridge := Iff.rfl
  variation := ⟨Q_two_node_closed_form, q2Rejected, qClosedForm_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    qClosedFormArena.Law q2Actual q2Rejected qClosedForm_rejected
  dependence := q2Dependence

def qClosedFormRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Q_two_node_closed_form) (Realization q2Signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.qClosedForm_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.qClosedFormEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨qClosedFormArena⟩
  objectArena := .source ⟨qClosedFormArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source qClosedFormArena ⟨qClosedFormEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize q2Signature (fun _ _ ζ => Q 2 2 1 ζ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-! ## 3. `first_inequality_iff_F_nonneg` and 5. `largest_admissible_disk` -/

abbrev qParamSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun _ => Fin 2 → ℂ) (fun _ => ℂ)

def qParamActual : Realization qParamSignature :=
  realize qParamSignature (fun _ t ζ => Q t 2 1 ζ) (fun e => nomatch e)

def qParamRejected : Realization qParamSignature :=
  realize qParamSignature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem qParamDependence : ObservationalDependence qParamSignature qParamActual := by
  intro _
  refine ⟨2, 0, negConjPair 0 0 + 1, ?_⟩
  change Q 2 2 1 0 ≠ Q 2 2 1 (negConjPair 0 0 + 1)
  rw [q_zero_at_zero 2,
    (Q_two_node_closed_form 2 0 0 (by decide) (by norm_num) (by norm_num)).2]
  exact zero_ne_one

def firstIffFArena : Arena where
  signature := qParamSignature
  Law R := ∀ (t : ℕ) (a b : ℝ) (_ht : 2 ≤ t)
    (_hab : a ^ 2 + b ^ 2 ≤ 1) (_hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1),
    ‖R.readout () t (negConjPair a b + 1)‖ ≤ 1 ↔ 0 ≤ F t a b

private theorem firstIffF_rejected : ¬ firstIffFArena.Law qParamRejected := by
  intro hlaw
  have hQ2 : ‖Q 2 2 1 (negConjPair 0 0 + 1)‖ ≤ 1 := by
    rw [(Q_two_node_closed_form 2 0 0 (by decide) (by norm_num) (by norm_num)).2]
    simp
  have hF : 0 ≤ F 2 0 0 :=
    (first_inequality_iff_F_nonneg 2 0 0 (by decide) (by norm_num) (by norm_num)).mp hQ2
  have hh := (hlaw 2 0 0 (by decide) (by norm_num) (by norm_num)).mpr hF
  norm_num [qParamRejected, realize] at hh

def firstIffFEvidence :
    Registration firstIffFArena (firstIffFArena.Law qParamActual) where
  actual := qParamActual
  bridge := Iff.rfl
  variation := ⟨first_inequality_iff_F_nonneg, qParamRejected, firstIffF_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    firstIffFArena.Law qParamActual qParamRejected firstIffF_rejected
  dependence := qParamDependence

def firstIffFRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@first_inequality_iff_F_nonneg) (Realization qParamSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.firstIffF_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.firstIffFEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨firstIffFArena⟩
  objectArena := .source ⟨firstIffFArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source firstIffFArena ⟨firstIffFEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize qParamSignature (fun _ t ζ => Q t 2 1 ζ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-! ## 4. `first_inequality_region` -/

abbrev q3Signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 2 → ℂ) (fun _ => ℂ)

def q3Actual : Realization q3Signature :=
  realize q3Signature (fun _ _ ζ => Q 3 2 1 ζ) (fun e => nomatch e)

def q3Rejected : Realization q3Signature :=
  realize q3Signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem q3Dependence : ObservationalDependence q3Signature q3Actual := by
  intro _
  refine ⟨(), negConjPair 0 0 + 1, negConjPair (9 / 10) (2 / 5) + 1, ?_⟩
  change Q 3 2 1 (negConjPair 0 0 + 1) ≠ Q 3 2 1 (negConjPair (9 / 10) (2 / 5) + 1)
  have hle : ‖Q 3 2 1 (negConjPair 0 0 + 1)‖ ≤ 1 :=
    (first_inequality_region 0 0 (by norm_num) (by norm_num)).2.2.1.mpr (by norm_num)
  have hw : ((9 / 10 : ℝ) : ℂ) + ((2 / 5 : ℝ) : ℂ) * Complex.I ≠ 1 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp at hre
    norm_num at hre
  have hnot : ¬ (‖Q 3 2 1 (negConjPair (9 / 10) (2 / 5) + 1)‖ ≤ 1) := by
    rw [(first_inequality_region (9 / 10) (2 / 5) (by norm_num) hw).2.2.1]
    norm_num
  intro heq
  rw [heq] at hle
  exact hnot hle

def firstRegionArena : Arena where
  signature := q3Signature
  Law R := ∀ (a b : ℝ)
    (_hab : a ^ 2 + b ^ 2 ≤ 1) (_hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1),
    (charPolyNegConj a b).map (algebraMap ℝ ℂ) =
      (∏ i : Fin 2, (Polynomial.X - Polynomial.C (negConjPair a b i))) ∧
    ((∀ t : ℕ, 2 ≤ t → ‖Q t 2 1 (negConjPair a b + 1)‖ ≤ 1) ↔
      ‖Q 3 2 1 (negConjPair a b + 1)‖ ≤ 1) ∧
    (‖R.readout () () (negConjPair a b + 1)‖ ≤ 1 ↔ b ^ 2 ≤ 3 * (1 - a) ^ 2) ∧
    (b ^ 2 ≤ 3 * (1 - a) ^ 2 ↔ inFirstSector (negConjPair a b)) ∧
    (b ^ 2 ≤ 3 * (1 - a) ^ 2 ↔
      (charPolyNegConj a b).eval (-1) ≤ ((charPolyNegConj a b).derivative.eval (-1)) ^ 2)

private theorem firstRegion_rejected : ¬ firstRegionArena.Law q3Rejected := by
  intro hlaw
  have hh := (hlaw 0 0 (by norm_num) (by norm_num)).2.2.1.mpr (by norm_num)
  norm_num [q3Rejected, realize] at hh

def firstRegionEvidence :
    Registration firstRegionArena (firstRegionArena.Law q3Actual) where
  actual := q3Actual
  bridge := Iff.rfl
  variation := ⟨first_inequality_region, q3Rejected, firstRegion_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    firstRegionArena.Law q3Actual q3Rejected firstRegion_rejected
  dependence := q3Dependence

def firstRegionRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@first_inequality_region) (Realization q3Signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.firstRegion_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.firstRegionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨firstRegionArena⟩
  objectArena := .source ⟨firstRegionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source firstRegionArena ⟨firstRegionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize q3Signature (fun _ _ ζ => Q 3 2 1 ζ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-! ## 5. `largest_admissible_disk` -/

def largestDiskArena : Arena where
  signature := qParamSignature
  Law R := ∀ (ρ : ℝ) (_hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1),
    (∀ (t : ℕ) (z : Fin 2 → ℂ),
      2 ≤ t → selfConjugate z → (∀ i, ‖z i‖ ≤ ρ) → z ≠ ![(-1 : ℂ), -1] →
        ‖R.readout () t (z + 1)‖ ≤ 1) ↔
      ρ ≤ Real.sqrt 3 / 2

private theorem largestDisk_rejected : ¬ largestDiskArena.Law qParamRejected := by
  classical
  intro hlaw
  have hρ_le : (1 / 2 : ℝ) ≤ Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hsc : selfConjugate (0 : Fin 2 → ℂ) := by
    refine ⟨fun i him => ?_, fun x => ?_⟩
    · simp at him
    · by_cases hx : (0 : ℂ) = x
      · exact ⟨1, by simp [hx]⟩
      · exact ⟨0, by simp [hx]⟩
  have hdisk : ∀ i : Fin 2, ‖(0 : Fin 2 → ℂ) i‖ ≤ 1 / 2 := fun _ => by simp
  have hzne : (0 : Fin 2 → ℂ) ≠ ![(-1 : ℂ), -1] := by
    intro heq
    have h0 := congrFun heq 0
    simp at h0
  have hh := (hlaw (1 / 2) (by norm_num) (by norm_num)).mpr hρ_le 2 0 (by decide) hsc hdisk hzne
  norm_num [qParamRejected, realize] at hh

def largestDiskEvidence :
    Registration largestDiskArena (largestDiskArena.Law qParamActual) where
  actual := qParamActual
  bridge := Iff.rfl
  variation := ⟨largest_admissible_disk, qParamRejected, largestDisk_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    largestDiskArena.Law qParamActual qParamRejected largestDisk_rejected
  dependence := qParamDependence

def largestDiskRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@largest_admissible_disk) (Realization qParamSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.largestDisk_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.largestDiskEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨largestDiskArena⟩
  objectArena := .source ⟨largestDiskArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source largestDiskArena ⟨largestDiskEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize qParamSignature (fun _ t ζ => Q t 2 1 ζ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-! ## 6. `second_inequality_region` -/

abbrev h1Signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 2 → ℂ) (fun _ => ℂ)

def h1Actual : Realization h1Signature :=
  realize h1Signature (fun _ _ z => h 1 z) (fun e => nomatch e)

def h1Rejected : Realization h1Signature :=
  realize h1Signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem h1Dependence : ObservationalDependence h1Signature h1Actual := by
  intro _
  refine ⟨(), conjPair 0 0, conjPair (1 / 2) 0, ?_⟩
  change h 1 (conjPair 0 0) ≠ h 1 (conjPair (1 / 2) 0)
  have h0 : ‖h 1 (conjPair 0 0)‖ = 2 * (0 : ℝ) :=
    (second_inequality_region 0 0 le_rfl (by norm_num)).2.2.2.1
  have h1 : ‖h 1 (conjPair (1 / 2) 0)‖ = 2 * (1 / 2 : ℝ) :=
    (second_inequality_region (1 / 2) 0 (by norm_num) (by norm_num)).2.2.2.1
  intro heq
  rw [heq, h1] at h0
  norm_num at h0

def secondRegionArena : Arena where
  signature := h1Signature
  Law R := ∀ (a b : ℝ) (_ha : 0 ≤ a) (_hab : a ^ 2 + b ^ 2 ≤ 1),
    (charPolyConj a b).map (algebraMap ℝ ℂ) =
      (∏ i : Fin 2, (Polynomial.X - Polynomial.C (conjPair a b i))) ∧
    (∀ t : ℕ, 2 ≤ t →
      (‖schurHook (t - 2) 0 (conjPair a b)‖ ≤ (Nat.choose t 2 : ℝ) * ‖e 1 (conjPair a b)‖ ↔
        ‖h (t - 1) (conjPair a b)‖ ≤ (t : ℝ) * ((t : ℝ) - 1) * a)) ∧
    ‖schurHook 0 0 (conjPair a b)‖ = (Nat.choose 2 2 : ℝ) * ‖e 1 (conjPair a b)‖ ∧
    ‖R.readout () () (conjPair a b)‖ = 2 * a ∧
    ((∀ t : ℕ, 2 ≤ t →
        ‖schurHook (t - 2) 0 (conjPair a b)‖ ≤ (Nat.choose t 2 : ℝ) * ‖e 1 (conjPair a b)‖) ↔
      ‖schurHook 1 0 (conjPair a b)‖ ≤ (Nat.choose 3 2 : ℝ) * ‖e 1 (conjPair a b)‖) ∧
    (‖schurHook 1 0 (conjPair a b)‖ ≤ (Nat.choose 3 2 : ℝ) * ‖e 1 (conjPair a b)‖ ↔
      b ^ 2 ≤ 3 * a ^ 2 + 6 * a) ∧
    (b ^ 2 ≤ 3 * a ^ 2 + 6 * a ↔
      (charPolyConj a b).eval 0 ≤
        ((charPolyConj a b).derivative.eval 0) ^ 2 -
          3 * ((charPolyConj a b).derivative.eval 0))

private theorem secondRegion_rejected : ¬ secondRegionArena.Law h1Rejected := by
  intro hlaw
  have hh := (hlaw 0 0 le_rfl (by norm_num)).2.2.2.1
  norm_num [h1Rejected, realize] at hh

def secondRegionEvidence :
    Registration secondRegionArena (secondRegionArena.Law h1Actual) where
  actual := h1Actual
  bridge := Iff.rfl
  variation := ⟨second_inequality_region, h1Rejected, secondRegion_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    secondRegionArena.Law h1Actual h1Rejected secondRegion_rejected
  dependence := h1Dependence

def secondRegionRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@second_inequality_region) (Realization h1Signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.secondRegion_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion.secondRegionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨secondRegionArena⟩
  objectArena := .source ⟨secondRegionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source secondRegionArena ⟨secondRegionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize h1Signature (fun _ _ z => h 1 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
end
