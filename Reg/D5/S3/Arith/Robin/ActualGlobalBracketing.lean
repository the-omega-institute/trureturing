import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualGlobalBracketing
import Reg.Support.DependentFamily

/- Candidate only: not compiled, assessed, deposited, or declared_validated.
The raw source selector below is a hand-derived candidate for the exact
strictInteger occurrence in the existential bracket. Producer verification
is still required; this source grants no binding evidence on its own. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.ActualGlobalBracketing

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.ActualGlobalBracketing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace AllIntegerBracketing

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => strictInteger q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

/-- The whole original theorem is reconstructed, including positive price,
both natural-order bounds, the unrestricted integer and its lower bound.
Only the actual strict-inventory function occurrence is varied. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℝ, 0 < q ∧ R.readout () () q ≤ n ∧ n ≤ maximalInteger q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hlow, hhigh⟩ := h 2 (by omega)
  change (3 : ℕ) ≤ 2 at hlow
  exact (by norm_num : ¬ (3 : ℕ) ≤ 2) hlow

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨qHigh, hHigh, hsmall, _⟩ := all_integer_bracketing 2 (by omega)
  let d : ℝ := goldenLayerMarginal 2 2
  have hd : 0 < d :=
    _root_.D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval.marginal_pos
      Nat.prime_two (by omega)
  let qLow := d / 2
  have hLow : 0 < qLow := half_pos hd
  have hgain : qLow < goldenLayerMarginal 2 2 := by
    change d / 2 < d
    linarith
  have hfac : 2 ≤ (strictInteger qLow).factorization 2 :=
    (strict_layer_iff hLow Nat.prime_two (by omega)).mpr hgain
  have hn0 : strictInteger qLow ≠ 0 := by
    have hn := strictInteger_pos hLow
    omega
  have hdiv : 2 ^ 2 ∣ strictInteger qLow :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr hfac
  have hlarge := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv
  norm_num only [show (2 : ℕ) ^ 2 = 4 by norm_num] at hlarge
  refine ⟨(), qHigh, qLow, ?_⟩
  change strictInteger qHigh ≠ strictInteger qLow
  omega

def family : Registration arena (type_of% (@all_integer_bracketing)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@all_integer_bracketing, rejected, rejected_law⟩
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
    (@all_integer_bracketing)
    (type_of% (realize signature (fun _ _ q => strictInteger q) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualGlobalBracketing.all_integer_bracketing.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualGlobalBracketing.AllIntegerBracketing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => strictInteger q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  -- Exact source state carrier, present in the original telescope/readout.
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualGlobalBracketing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end AllIntegerBracketing
end Reg.D5.S3.Arith.Robin.ActualGlobalBracketing
