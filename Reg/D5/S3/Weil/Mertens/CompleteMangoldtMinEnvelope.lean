import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope
import Reg.Support.SingleDependentReadout

/- Select the exact sequence-valued observation mangoldtMinTerm L in the
   original Summable clause. Its original real L remains the state; no
   theorem telescope or quantitative conclusion is weakened. The rejected
   observation is the nonsummable constant-one sequence. The source
   path addresses And's first argument, then Summable's sequence argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope
open LeanInformationAudit Real Filter
open scoped Topology

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ) (fun _ => ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ L => mangoldtMinTerm L) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℕ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {L : ℝ}, 1 ≤ L →
    Summable (R.readout () () L) ∧
      (∑' n : ℕ, mangoldtMinTerm L n) ≤
        (5/2 : ℝ)*(Real.log 4 + 4)*L^(-4/5 : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) :=
    (h (L := (1 : ℝ)) (by norm_num)).1
  have hz : (1 : ℝ) = 0 := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    hs.tendsto_atTop_zero
  norm_num at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change mangoldtMinTerm 0 ≠ mangoldtMinTerm 1
  intro heq
  have hv := congrFun heq 2
  have hz : mangoldtMinTerm 0 2 = 0 := by
    unfold mangoldtMinTerm
    norm_num only [Nat.cast_ofNat, inv_zero]
    rw [min_eq_left (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    ring
  have hp : 0 < mangoldtMinTerm 1 2 := by
    unfold mangoldtMinTerm
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, inv_one]
    exact mul_pos
      (div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
        (Real.sqrt_pos.2 (by norm_num)))
      (lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
  rw [hz] at hv
  exact hp.ne hv

def evidence : Registration arena (type_of% @complete_mangoldt_min_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_mangoldt_min_envelope, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@complete_mangoldt_min_envelope) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope.complete_mangoldt_min_envelope.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ L => mangoldtMinTerm L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope
