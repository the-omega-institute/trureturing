import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
open LeanInformationAudit

set_option quotPrecheck false
noncomputable section
namespace Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
universe u

abbrev traceSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e)
def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => -1) (fun e => nomatch e)

variable {n : Type u} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)

def traceEntropy (R : Realization traceSignature) (Y : S) : ℝ :=
  R.readout () () (Y.val * CFC.log Y.val).trace

def defect (B A : S) : ℝ :=
  (B.val * (CFC.log B.val - CFC.log A.val)).trace.re

def bkmForm (A H : S) : ℝ :=
  (H.val * _root_.D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val).trace.re

def normalizedDirection (A H : S) (t : ℝ) : M :=
  CFC.conjSqrt (Ring.inverse (A.val + t • (1 : M))) H.val

local notation "entropy" => traceEntropy traceActual
local notation "D" => defect
local notation "BKM" => bkmForm
local notation "K" => normalizedDirection

/-- The base trace readout in the symmetric gap varies; the BKM integral is fixed. -/
def bkmArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hA : A.val.PosDef) (_hr : ‖K A H 0‖ < 1),
    entropy (A + H) / 2 + entropy (A - H) / 2 - traceEntropy R A =
      (∫ v in (0 : ℝ)..1, (1 - v) *
        (BKM (A + v • H) H + BKM (A + v • (-H)) H)) / 2

/-- Only the equality's base trace readout varies; half-line integrability is retained. -/
def logArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hA : A.val.PosDef) (_hr : ‖K A H 0‖ < 1),
    (entropy (A + H) / 2 + entropy (A - H) / 2 - traceEntropy R A =
      -(∫ t in Ioi (0 : ℝ), (CFC.log (1 - (K A H t) ^ 2)).trace.re) / 2) ∧
      IntegrableOn (fun t => (CFC.log (1 - (K A H t) ^ 2)).trace.re) (Ioi (0 : ℝ))

/-- Only the upper bound's base trace varies; the lower bound and coefficient stay fixed. -/
def boundsArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hA : A.val.PosDef) (_hr : ‖K A H 0‖ < 1),
    BKM A H / 2 ≤ entropy (A + H) / 2 + entropy (A - H) / 2 - entropy A ∧
      entropy (A + H) / 2 + entropy (A - H) / 2 - traceEntropy R A ≤
        (if ‖K A H 0‖ = 0 then 1 else
          -Real.log (1 - ‖K A H 0‖ ^ 2) / ‖K A H 0‖ ^ 2) * BKM A H / 2

/-- The contracted gap's base trace varies, with all positivity and scale hypotheses retained. -/
def squareArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hA : A.val.PosDef) (_hp : (A + H).val.PosDef) (_hm : (A - H).val.PosDef)
    (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1),
    entropy (A + s • H) / 2 + entropy (A - s • H) / 2 - traceEntropy R A ≤
      s ^ 2 * (entropy (A + H) / 2 + entropy (A - H) / 2 - entropy A)

/-- The semidefinite theorem has the same varying readout and its original weaker hypotheses. -/
def psdArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hA : 0 ≤ A.val) (_hp : 0 ≤ (A + H).val) (_hm : 0 ≤ (A - H).val)
    (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1),
    entropy (A + s • H) / 2 + entropy (A - s • H) / 2 - traceEntropy R A ≤
      s ^ 2 * (entropy (A + H) / 2 + entropy (A - H) / 2 - entropy A)

theorem trace_dependence : ObservationalDependence traceSignature traceActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [traceActual, realize]

theorem actual_bkm_law : bkmArena.{u}.Law traceActual := @symmetric_entropy_gap_eq_integral_bkm.{u}

theorem rejected_bkm_law : ¬ bkmArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hr : ‖K A (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) 0‖ < 1 := by
    simp [normalizedDirection]
  have hh := h A 0 Matrix.PosDef.one hr
  norm_num [traceEntropy, bkmForm, normalizedDirection, traceActual, traceRejected, realize, A, CFC.log_one,
    _root_.D5.S3.Divergence.LogDerivTrace.logDeriv] at hh

def bkmEvidence : Registration bkmArena.{u} (type_of% @symmetric_entropy_gap_eq_integral_bkm.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_bkm_law, traceRejected, rejected_bkm_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    bkmArena.Law traceActual traceRejected rejected_bkm_law
  dependence := trace_dependence

theorem actual_log_law : logArena.{u}.Law traceActual := @symmetric_entropy_gap_eq_integral_log.{u}

theorem rejected_log_law : ¬ logArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hr : ‖K A (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) 0‖ < 1 := by
    simp [normalizedDirection]
  have hh := h A 0 Matrix.PosDef.one hr
  norm_num [traceEntropy, bkmForm, normalizedDirection, traceActual, traceRejected, realize, A, CFC.log_one,
    _root_.D5.S3.Divergence.LogDerivTrace.logDeriv] at hh

def logEvidence : Registration logArena.{u} (type_of% @symmetric_entropy_gap_eq_integral_log.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_log_law, traceRejected, rejected_log_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    logArena.Law traceActual traceRejected rejected_log_law
  dependence := trace_dependence

theorem actual_bounds_law : boundsArena.{u}.Law traceActual := @symmetric_entropy_gap_bkm_bounds.{u}

theorem rejected_bounds_law : ¬ boundsArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hr : ‖K A (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) 0‖ < 1 := by
    simp [normalizedDirection]
  have hh := h A 0 Matrix.PosDef.one hr
  norm_num [traceEntropy, bkmForm, normalizedDirection, traceActual, traceRejected, realize, A, CFC.log_one,
    _root_.D5.S3.Divergence.LogDerivTrace.logDeriv] at hh

def boundsEvidence : Registration boundsArena.{u} (type_of% @symmetric_entropy_gap_bkm_bounds.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_bounds_law, traceRejected, rejected_bounds_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    boundsArena.Law traceActual traceRejected rejected_bounds_law
  dependence := trace_dependence

theorem actual_square_law : squareArena.{u}.Law traceActual := @symmetric_entropy_gap_square_contraction.{u}

theorem rejected_square_law : ¬ squareArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hr : ‖K A (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) 0‖ < 1 := by
    simp [normalizedDirection]
  have hp : (A + 0).val.PosDef := by simpa using (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef)
  have hm : (A - 0).val.PosDef := by simpa using hp
  have hh := h A 0 Matrix.PosDef.one hp hm 0 (by norm_num)
  norm_num [traceEntropy, bkmForm, normalizedDirection, traceActual, traceRejected, realize, A, CFC.log_one,
    _root_.D5.S3.Divergence.LogDerivTrace.logDeriv] at hh

def squareEvidence : Registration squareArena.{u} (type_of% @symmetric_entropy_gap_square_contraction.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_square_law, traceRejected, rejected_square_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    squareArena.Law traceActual traceRejected rejected_square_law
  dependence := trace_dependence

theorem actual_psd_law : psdArena.{u}.Law traceActual := @symmetric_entropy_gap_square_contraction_psd.{u}

theorem rejected_psd_law : ¬ psdArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hr : ‖K A (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) 0‖ < 1 := by
    simp [normalizedDirection]
  have hA : (0 : Matrix n n ℂ) ≤ A.val := Matrix.PosDef.one.posSemidef.nonneg
  have hp : 0 ≤ (A + 0).val := by simpa using hA
  have hm : 0 ≤ (A - 0).val := by simpa using hA
  have hh := h A 0 hA hp hm 0 (by norm_num)
  norm_num [traceEntropy, bkmForm, normalizedDirection, traceActual, traceRejected, realize, A, CFC.log_one,
    _root_.D5.S3.Divergence.LogDerivTrace.logDeriv] at hh

def psdEvidence : Registration psdArena.{u} (type_of% @symmetric_entropy_gap_square_contraction_psd.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_psd_law, traceRejected, rejected_psd_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    psdArena.Law traceActual traceRejected rejected_psd_law
  dependence := trace_dependence

/-- Four-slot source evidence with the original theorem telescope. -/
def bkmRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_eq_integral_bkm.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_eq_integral_bkm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.bkmEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨bkmArena.{u}⟩
  objectArena := .source ⟨bkmArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bkmArena.{u} ⟨bkmEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "fn", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Four-slot source evidence with the original theorem telescope. -/
def logRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_eq_integral_log.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_eq_integral_log.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.logEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨logArena.{u}⟩
  objectArena := .source ⟨logArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logArena.{u} ⟨logEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "fn", "arg", "arg", "fn", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Four-slot source evidence with the original theorem telescope. -/
def boundsRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_bkm_bounds.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_bkm_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.boundsEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨boundsArena.{u}⟩
  objectArena := .source ⟨boundsArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundsArena.{u} ⟨boundsEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "arg", "arg", "fn", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Four-slot source evidence with the original theorem telescope. -/
def squareRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_square_contraction.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_square_contraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.squareEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena.{u}⟩
  objectArena := .source ⟨squareArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena.{u} ⟨squareEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg", "fn", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Four-slot source evidence with the original theorem telescope. -/
def psdRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_square_contraction_psd.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.symmetric_entropy_gap_square_contraction_psd.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder.psdEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨psdArena.{u}⟩
  objectArena := .source ⟨psdArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source psdArena.{u} ⟨psdEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg", "fn", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Quantum.Divergence.FiniteAmplitudeBKMRemainder
