import D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Observe the accumulated LCM and the exceptional factor as the cutoff varies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd

open _root_.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd (lcmProduct rowProduct HStar EStar lcmProduct_eq EStar_dvd
    log_HStar_sub_sampled_chebyshev_le)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem sensitivity (arena : Arena) (hSignature : arena.signature = signature)
    (actual bad : Realization arena.signature)
    (hAnchor : actual.anchor = bad.anchor) (hBad : ¬ arena.Law bad) :
    Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, hAnchor, hBad⟩
    intro j hj
    have h : Subsingleton arena.signature.Role := hSignature ▸ (inferInstance : Subsingleton Unit)
    exact (hj (h.elim j i)).elim
  · intro i
    have h : IsEmpty arena.signature.Anchor := hSignature ▸ (inferInstance : IsEmpty Empty)
    exact (h.false i).elim

abbrev identityArena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, R.readout () () N = rowProduct N * HStar N * EStar N

def identityActual : Realization signature :=
  realize signature (fun _ _ N => lcmProduct N) (fun e => nomatch e)

private theorem identityRejected : ¬ identityArena.Law rejected := by
  intro h
  have hzero := h 0
  change 0 = rowProduct 0 * HStar 0 * EStar 0 at hzero
  exact (by decide : ¬ (0 = rowProduct 0 * HStar 0 * EStar 0)) hzero

def identityFamily : Registration identityArena (type_of% @lcmProduct_eq) where
  actual := identityActual
  bridge := Iff.rfl
  variation := ⟨lcmProduct_eq, rejected, identityRejected⟩
  sensitivity := sensitivity identityArena rfl identityActual rejected rfl identityRejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change lcmProduct 0 ≠ lcmProduct 1
    decide

def identityAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lcmProduct_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd.lcmProduct_eq.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd.identityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨identityArena⟩
  objectArena := .source ⟨identityArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source identityArena ⟨identityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => lcmProduct N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
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

abbrev boundArena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, R.readout () () N ∣ 2 ^ N * Nat.lcmUpto (4 * N + 1) *
      ∏ j ∈ range N, (j + 1) * (4 * (j + 1) + 1)

def boundActual : Realization signature :=
  realize signature (fun _ _ N => EStar N) (fun e => nomatch e)

private theorem boundRejected : ¬ boundArena.Law rejected := by
  intro h
  have hzero := h 0
  change (0 : ℕ) ∣ 2 ^ 0 * Nat.lcmUpto (4 * 0 + 1) *
      ∏ j ∈ range 0, (j + 1) * (4 * (j + 1) + 1) at hzero
  exact (by decide : ¬ ((0 : ℕ) ∣ 2 ^ 0 * Nat.lcmUpto (4 * 0 + 1) *
      ∏ j ∈ range 0, (j + 1) * (4 * (j + 1) + 1))) hzero

def boundFamily : Registration boundArena (type_of% @EStar_dvd) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨EStar_dvd, rejected, boundRejected⟩
  sensitivity := sensitivity boundArena rfl boundActual rejected rfl boundRejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change EStar 0 ≠ EStar 1
    decide

def boundAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@EStar_dvd) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd.EStar_dvd.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd.boundFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source boundArena ⟨boundFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => EStar N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
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

abbrev comparisonArena : Arena where
  signature := signature
  Law R := ∀ N : ℕ,
    |Real.log (R.readout () () N) -
      ((∑ i ∈ range (N + 1), Chebyshev.psi ((4 * i + 1 : ℕ) : ℝ)) -
        2 * Real.log 2 * (N : ℝ) * ((N : ℝ) + 1))| ≤
      14 * (N : ℝ) * Real.log ((N : ℝ) + 2)

def comparisonActual : Realization signature :=
  realize signature (fun _ _ N => HStar N) (fun e => nomatch e)

def comparisonBad : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem comparisonRejected : ¬ comparisonArena.Law comparisonBad := by
  intro h
  have hpsi : Chebyshev.psi 1 = 0 := Chebyshev.psi_eq_zero_of_le_one le_rfl
  have hzero : |Real.log 2| ≤ 0 := by
    simpa [comparisonBad, realize, hpsi] using h 0
  have hpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact (not_le_of_gt (hpos.trans_le (le_abs_self _))) hzero

def comparisonFamily :
    Registration comparisonArena (type_of% @log_HStar_sub_sampled_chebyshev_le) where
  actual := comparisonActual
  bridge := Iff.rfl
  variation := ⟨log_HStar_sub_sampled_chebyshev_le, comparisonBad, comparisonRejected⟩
  sensitivity :=
    sensitivity comparisonArena rfl comparisonActual comparisonBad rfl comparisonRejected
  dependence := by
    intro role
    refine ⟨(), 0, 2, ?_⟩
    change HStar 0 ≠ HStar 2
    decide

def comparisonAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_HStar_sub_sampled_chebyshev_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd.log_HStar_sub_sampled_chebyshev_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd.comparisonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨comparisonArena⟩
  objectArena := .source ⟨comparisonArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source comparisonArena ⟨comparisonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => HStar N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
