import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.CothBernoulliDegree.Kernel
import Reg.Support.DependentFamily
import Mathlib.Analysis.PSeries
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel
open scoped BigOperators
open _root_.D5.S3.Analytic.CothBernoulliDegree.Kernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev phaseSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def phaseActual : Realization phaseSignature :=
  realize phaseSignature (fun _ _ M => M) (fun e => nomatch e)

def phaseRejected : Realization phaseSignature :=
  realize phaseSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev phaseArena : Arena where
  signature := phaseSignature
  Law Q := ∀ (M : ℝ), 5 ≤ M →
    (1 + (5 / M)^2 : ℝ)^(-M / 2 : ℝ) *
      Real.sin (Q.readout () () M * Real.arctan (5 / M)) ≤ -(1:ℝ)/8

private theorem phaseArenaRejected : ¬ phaseArena.Law phaseRejected := by
  intro h
  have he := h 5 (by norm_num)
  norm_num [phaseRejected, realize] at he

private theorem phaseArenaDependence : ObservationalDependence phaseSignature phaseActual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [phaseActual, realize]⟩

def phaseArenaSource : Registration phaseArena (type_of% @phase_bound) where
  actual := phaseActual
  bridge := Iff.rfl
  variation := ⟨phase_bound, phaseRejected, phaseArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨phaseRejected, ?_, rfl, phaseArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := phaseArenaDependence

def phaseAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@phase_bound) (Realization phaseSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.phaseAuditUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.phaseArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨phaseArena⟩
  objectArena := .source ⟨phaseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source phaseArena ⟨phaseArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phaseSignature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.Kernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]



abbrev tailSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ _ n => n) (fun e => nomatch e)

def tailRejected : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev tailArena : Arena where
  signature := tailSignature
  Law Q := ∀ (n : ℕ), 2 ≤ n →
    (∑' k : ℕ, 1 / ((k : ℝ) + 2)^(2 * Q.readout () () n + 1)) ≤ 1/16

private theorem tailArenaRejected : ¬ tailArena.Law tailRejected := by
  intro h
  have he := h 2 (by norm_num)
  change (∑' k : ℕ, 1 / ((k : ℝ) + 2)^3) ≤ 1/16 at he
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2)^3) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3:ℕ)))
  have ht := hs.le_tsum 0 (fun k hk => by positivity)
  have ht' : (1:ℝ)/8 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 2)^3 := by
    convert ht using 1 <;> norm_num
  linarith

private theorem tailArenaDependence : ObservationalDependence tailSignature tailActual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [tailActual, realize]⟩

def tailArenaSource : Registration tailArena (type_of% @tail_bound) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨tail_bound, tailRejected, tailArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tailRejected, ?_, rfl, tailArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := tailArenaDependence

def tailAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tail_bound) (Realization tailSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.tailAuditUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.tailArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tailSignature (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.Kernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel

namespace Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel
open _root_.D5.S3.Analytic.CothBernoulliDegree.Kernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex
noncomputable section

abbrev derivativeSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def derivativeActual : Realization derivativeSignature :=
  realize derivativeSignature
    (fun _ p t => iteratedDeriv p.1 (fun s : ℝ => s^(p.1+2)/(s^2+p.2^2)) t)
    (fun e => nomatch e)

def derivativeRejected : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem derivativeDependence : ObservationalDependence derivativeSignature derivativeActual := by
  intro i
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  norm_num [derivativeActual, realize]

abbrev certificateArena : Arena where
  signature := derivativeSignature
  Law Q := ∀ (N : ℕ) (a t : ℝ), 0 < a →
    Q.readout () ⟨N, a⟩ t =
      (N.factorial : ℝ) * (1 - ((1 + I*(t:ℂ)/(a:ℂ))^(-((N+1 : ℕ) : ℤ))).re)

private theorem certificateRejected : ¬ certificateArena.Law derivativeRejected := by
  intro h
  have he := h 0 1 1 (by norm_num)
  change (0:ℝ) = _ at he
  rw [← kernel_deriv_N 0 1 1 (by norm_num)] at he
  norm_num at he

def certificateSource : Registration certificateArena (type_of% @kernel_deriv_N) where
  actual := derivativeActual
  bridge := Iff.rfl
  variation := ⟨kernel_deriv_N, derivativeRejected, certificateRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    certificateArena.Law derivativeActual derivativeRejected certificateRejected
  dependence := derivativeDependence

abbrev positivityArena : Arena where
  signature := derivativeSignature
  Law Q := ∀ (N : ℕ) (a t : ℝ), 0 < a → 0 < t → 0 < Q.readout () ⟨N, a⟩ t

private theorem positivityRejected : ¬ positivityArena.Law derivativeRejected := by
  intro h
  have he := h 0 1 1 (by norm_num) (by norm_num)
  exact (lt_irrefl (0:ℝ)) he

def positivitySource : Registration positivityArena (type_of% @kernel_deriv_N_pos) where
  actual := derivativeActual
  bridge := Iff.rfl
  variation := ⟨kernel_deriv_N_pos, derivativeRejected, positivityRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    positivityArena.Law derivativeActual derivativeRejected positivityRejected
  dependence := derivativeDependence

def succActual : Realization derivativeSignature :=
  realize derivativeSignature
    (fun _ p t => iteratedDeriv (p.1+1) (fun s : ℝ => s^(p.1+2)/(s^2+p.2^2)) t)
    (fun e => nomatch e)

abbrev succArena : Arena where
  signature := derivativeSignature
  Law Q := ∀ (N : ℕ) (a t : ℝ), 0 < a →
    Q.readout () ⟨N, a⟩ t =
      (N+1).factorial / a * (1+(t/a)^2 : ℝ)^(-((N+2:ℕ):ℝ)/2) *
        Real.sin (((N+2:ℕ):ℝ)*Real.arctan (t/a))

private theorem succRejected : ¬ succArena.Law derivativeRejected := by
  intro h
  have he := h 0 1 1 (by norm_num)
  change (0:ℝ) = _ at he
  norm_num [Real.arctan_one,
    show (2:ℝ)*(Real.pi/4)=Real.pi/2 by ring, Real.rpow_neg_one] at he

private theorem succDependence : ObservationalDependence derivativeSignature succActual := by
  intro i
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  intro he
  change iteratedDeriv (0+1) (fun s : ℝ => s^(0+2)/(s^2+1^2)) 0 =
    iteratedDeriv (0+1) (fun s : ℝ => s^(0+2)/(s^2+1^2)) 1 at he
  rw [kernel_deriv_succ 0 1 0 (by norm_num), kernel_deriv_succ 0 1 1 (by norm_num)] at he
  norm_num [Real.arctan_one,
    show (2:ℝ)*(Real.pi/4)=Real.pi/2 by ring, Real.rpow_neg_one] at he

def succSource : Registration succArena (type_of% @kernel_deriv_succ) where
  actual := succActual
  bridge := Iff.rfl
  variation := ⟨kernel_deriv_succ, derivativeRejected, succRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    succArena.Law succActual derivativeRejected succRejected
  dependence := succDependence


def certificateAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_deriv_N) (Realization derivativeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.certificateAuditUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.certificateSource
  realizationSource := none
  generated := false
  arena := .source ⟨certificateArena⟩
  objectArena := .source ⟨certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source certificateArena ⟨certificateSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature
    (fun _ p t => iteratedDeriv (p.1) (fun s : ℝ => s^(p.1+2)/(s^2+p.2^2)) t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.Kernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]



def positivityAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_deriv_N_pos) (Realization derivativeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.positivityAuditUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.positivitySource
  realizationSource := none
  generated := false
  arena := .source ⟨positivityArena⟩
  objectArena := .source ⟨positivityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positivityArena ⟨positivitySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature
    (fun _ p t => iteratedDeriv (p.1) (fun s : ℝ => s^(p.1+2)/(s^2+p.2^2)) t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.Kernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]



def succAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_deriv_succ) (Realization derivativeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.succAuditUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel.succSource
  realizationSource := none
  generated := false
  arena := .source ⟨succArena⟩
  objectArena := .source ⟨succArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source succArena ⟨succSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature
    (fun _ p t => iteratedDeriv (p.1+1) (fun s : ℝ => s^(p.1+2)/(s^2+p.2^2)) t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.Kernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Analytic.CothBernoulliDegree.Kernel
