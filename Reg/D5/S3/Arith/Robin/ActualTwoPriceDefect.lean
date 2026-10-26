import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualGlobalBracketing
import Reg.Support.DependentFamily

/- Candidate only: not compiled or declared_validated. The whole pressure
integral statement is varied through its actual pressure function, without
putting an integral identity or a desired conclusion into a hypothesis. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.ActualTwoPriceDefect

open MeasureTheory
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.ActualGlobalBracketing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace PressureIntegral

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
  realize signature (fun _ _ q => pressure q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ q => pressure q + 1) (fun e => nomatch e)

/-- Only the pressure occurrence at price b is selected. The integral,
the pressure at a, both real endpoints and both domain hypotheses stay
exactly in the full law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, 1 < a → 1 < b →
    (∫ u in a..b, clock u * weight u) =
      R.readout () () (price b) - pressure (price a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 2) (b := 2) (by norm_num) (by norm_num)
  change (∫ u in (2 : ℝ)..2, clock u * weight u) =
    pressure (price 2) + 1 - pressure (price 2) at hbad
  rw [intervalIntegral.integral_same] at hbad
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let d : ℝ := goldenLayerMarginal 2 1
  have hd : 0 < d :=
    _root_.D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval.marginal_pos
      Nat.prime_two (by omega)
  let q := d / 2
  have hq : 0 < q := half_pos hd
  let N := strictInteger q
  have hN : 1 ≤ N := strictInteger_pos hq
  have hN0 : N ≠ 0 := by omega
  have hgain : q < goldenLayerMarginal 2 1 := by
    change d / 2 < d
    linarith
  have hfac : 1 ≤ N.factorization 2 :=
    (strict_layer_iff hq Nat.prime_two (by omega)).mpr hgain
  have hdiv : 2 ∣ N := (Nat.prime_two.dvd_iff_one_le_factorization hN0).mpr hfac
  have htwo : 2 ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdiv
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hpressure : pressure q = goldenResourceObjective q N :=
    pressure_eq_of_optimal hN (strict_is_optimal hq)
  have hother : goldenResourceObjective (q / 2) N ≤ pressure (q / 2) := by
    rw [pressure_eq_of_optimal (strictInteger_pos (half_pos hq))
      (strict_is_optimal (half_pos hq))]
    exact strict_is_optimal (half_pos hq) N hN
  have hstrict : pressure q < pressure (q / 2) := by
    dsimp only [goldenResourceObjective] at hpressure hother
    nlinarith [mul_pos hq hlog]
  refine ⟨(), q, q / 2, ?_⟩
  change pressure q ≠ pressure (q / 2)
  exact ne_of_lt hstrict

def family : Registration arena (type_of% (@pressure_integral)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pressure_integral, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pressure_integral)
    (type_of% (realize signature (fun _ _ q => pressure q) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualTwoPriceDefect.pressure_integral.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualTwoPriceDefect.PressureIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => pressure q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  -- Exact source state carrier, present in the original telescope/readout.
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualTwoPriceDefect
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end PressureIntegral
end Reg.D5.S3.Arith.Robin.ActualTwoPriceDefect
