import D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Observe the deficit, factorial identity and residual factor as the cutoff varies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection

open _root_.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd (EStar)
open _root_.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev natSignature (P : Type) : Signature where
  Params := P
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev signature := natSignature Unit
abbrev deficitSignature := natSignature (Σ _ : ℕ, ℕ)

private theorem sensitive (arena : Arena) (hrole : Subsingleton arena.signature.Role)
    (actual bad : Realization arena.signature)
    (hAnchor : actual.anchor = bad.anchor) (hBad : ¬ arena.Law bad)
    (hempty : IsEmpty arena.signature.Anchor) : Sensitivity arena actual := by
  constructor
  · intro i
    exact ⟨bad, fun j hj => (hj (hrole.elim j i)).elim, hAnchor, hBad⟩
  · intro i
    exact (hempty.false i).elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev deficitArena : Arena where
  signature := deficitSignature
  Law R := ∀ (N : ℕ) {p t : ℕ}, p.Prime → 1 ≤ t →
    R.readout () ⟨p, t⟩ N =
      (if p ^ t = 2 then N else 0) +
        (if p = 2 then 0 else N / p ^ t) + levelIndicator N (p ^ t)

def deficitActual : Realization deficitSignature :=
  realize deficitSignature (fun _ q N => levelDeficit N (q.1 ^ q.2)) (fun e => nomatch e)

def deficitBad : Realization deficitSignature :=
  realize deficitSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem deficitRejected : ¬ deficitArena.Law deficitBad := by
  intro h
  have hbad := h 1 (p := 2) (t := 1) (by decide) (by decide)
  exact (by decide : ¬ (0 = (1 : ℕ))) hbad

def deficitFamily : Registration deficitArena (type_of% @levelDeficit_prime_pow) where
  actual := deficitActual
  bridge := Iff.rfl
  variation := ⟨levelDeficit_prime_pow, deficitBad, deficitRejected⟩
  sensitivity := sensitive deficitArena (by infer_instance) deficitActual deficitBad rfl
    deficitRejected (by infer_instance)
  dependence := by
    intro role
    refine ⟨⟨2, 1⟩, 0, 1, ?_⟩
    change levelDeficit 0 2 ≠ levelDeficit 1 2
    decide

def deficitAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@levelDeficit_prime_pow) (Realization deficitSignature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.levelDeficit_prime_pow.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.deficitFamily
  realizationSource := none
  generated := false
  arena := .source ⟨deficitArena⟩
  objectArena := .source ⟨deficitArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source deficitArena ⟨deficitFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deficitSignature (fun _ q N => levelDeficit N (q.1 ^ q.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
    definition := none
    coordinates := #[1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn", "arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev exactArena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, R.readout () () N = 2 ^ (Nat.digits 2 N).sum * N.factorial * RStar N

def exactActual : Realization signature :=
  realize signature (fun _ _ N => EStar N) (fun e => nomatch e)

private theorem exactRejected : ¬ exactArena.Law rejected := by
  intro h
  exact (by decide : ¬ (0 = (1 : ℕ))) (h 0)

def exactFamily : Registration exactArena (type_of% @EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar) where
  actual := exactActual
  bridge := Iff.rfl
  variation := ⟨EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar, rejected, exactRejected⟩
  sensitivity := sensitive exactArena (by infer_instance) exactActual rejected rfl
    exactRejected (by infer_instance)
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change EStar 0 ≠ EStar 1
    decide

def exactAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.exactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena⟩
  objectArena := .source ⟨exactArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source exactArena ⟨exactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => EStar N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev divisibilityArena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, R.readout () () N ∣ correctionMultinomial N

def divisibilityActual : Realization signature :=
  realize signature (fun _ _ N => RStar N) (fun e => nomatch e)

private theorem divisibilityRejected : ¬ divisibilityArena.Law rejected := by
  intro h
  exact (by decide : ¬ ((0 : ℕ) ∣ 1)) (h 0)

def divisibilityFamily : Registration divisibilityArena (type_of% @RStar_dvd_correctionMultinomial) where
  actual := divisibilityActual
  bridge := Iff.rfl
  variation := ⟨RStar_dvd_correctionMultinomial, rejected, divisibilityRejected⟩
  sensitivity := sensitive divisibilityArena (by infer_instance) divisibilityActual rejected rfl
    divisibilityRejected (by infer_instance)
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change RStar 0 ≠ RStar 1
    decide

def divisibilityAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@RStar_dvd_correctionMultinomial) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.RStar_dvd_correctionMultinomial.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.divisibilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨divisibilityArena⟩
  objectArena := .source ⟨divisibilityArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source divisibilityArena ⟨divisibilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => RStar N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev logArena : Arena where
  signature := signature
  Law R := ∀ N : ℕ,
    0 ≤ Real.log (RStar N) ∧
    Real.log (R.readout () () N) ≤ (4 * (N : ℝ) + 1) * Real.log 4

def logActual : Realization signature :=
  realize signature (fun _ _ N => RStar N) (fun e => nomatch e)

def logBad : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

private theorem logRejected : ¬ logArena.Law logBad := by
  intro h
  have hu : Real.log 5 ≤ Real.log 4 := by simpa [logBad, realize] using (h 0).2
  exact (not_le_of_gt (Real.log_lt_log (by norm_num) (by norm_num))) hu

def logFamily : Registration logArena (type_of% @log_RStar_bounds) where
  actual := logActual
  bridge := Iff.rfl
  variation := ⟨log_RStar_bounds, logBad, logRejected⟩
  sensitivity := sensitive logArena (by infer_instance) logActual logBad rfl
    logRejected (by infer_instance)
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change RStar 0 ≠ RStar 1
    decide

def logAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_RStar_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.log_RStar_bounds.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection.logFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logArena⟩
  objectArena := .source ⟨logArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source logArena ⟨logFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => RStar N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
