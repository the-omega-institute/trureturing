import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale
import Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand

/- A complete-Law source-bound registration attempt, not a claim of
producer validation. The price, original endpoint disjunction, largest-prime
threshold and entire tail remain in the Law. Only the tail readout varies.
-/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale
open Finset
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.ActualGlobalBracketing
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Observation
abbrev signature :=
  _root_.Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.TailObservation.signature ℝ

def actual : Realization signature :=
  realize signature (fun _ _ N => tail N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ N =>
    (9 * Real.log 4) /
      (Real.sqrt (largestPrime N : ℝ) * Real.log (largestPrime N : ℝ)) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℝ}, 0 < q → ∀ {N : ℕ},
    (N = strictInteger q ∨ N = maximalInteger q) →
    4 ≤ largestPrime N → R.readout () q N ≤
      (9 * Real.log 4) /
        (Real.sqrt (largestPrime N : ℝ) * Real.log (largestPrime N : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Nat.Prime 5 := by norm_num
  have hm : 0 < goldenLayerMarginal 5 1 :=
    _root_.D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval.marginal_pos hp (by omega)
  let q : ℝ := goldenLayerMarginal 5 1 / 2
  have hq : 0 < q := half_pos hm
  have hselected : q < goldenLayerMarginal 5 1 := by
    dsimp only [q]
    linarith
  have ha : 1 ≤ (strictInteger q).factorization 5 :=
    (strict_layer_iff hq hp (by omega : 1 ≤ (1 : ℕ))).mpr hselected
  have hmem : 5 ∈ (strictInteger q).primeFactors :=
    hp.mem_primeFactors (Nat.dvd_of_factorization_pos (by omega))
      (by have hpos := strictInteger_pos hq; omega)
  have hu : 4 ≤ largestPrime (strictInteger q) := by
    have hh : 5 ≤ largestPrime (strictInteger q) := Finset.le_sup (f := id) hmem
    omega
  have hbad := h (q := q) hq (N := strictInteger q) (Or.inl rfl) hu
  change (9 * Real.log 4) /
      (Real.sqrt (largestPrime (strictInteger q) : ℝ) *
        Real.log (largestPrime (strictInteger q) : ℝ)) + 1 ≤
    (9 * Real.log 4) /
      (Real.sqrt (largestPrime (strictInteger q) : ℝ) *
        Real.log (largestPrime (strictInteger q) : ℝ)) at hbad
  linarith

def family : Registration arena
    (type_of% (@endpoint_tail_le_nine_log4_sqrt_log)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_tail_le_nine_log4_sqrt_log, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, (by funext e; exact nomatch e), rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    obtain ⟨q, x, y, hxy⟩ :=
      _root_.Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.family.dependence ()
    refine ⟨1, x, y, ?_⟩
    change tail x ≠ tail y
    change tail x ≠ tail y at hxy
    exact hxy
end Observation

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_tail_le_nine_log4_sqrt_log)
    (type_of% (realize Observation.signature
      (fun _ _ N => tail N) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale.endpoint_tail_le_nine_log4_sqrt_log.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale.Observation.family
  realizationSource := none
  generated := false
  arena := .source ⟨Observation.arena⟩
  objectArena := .source ⟨Observation.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Observation.arena ⟨Observation.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Observation.signature
    (fun _ _ N => tail N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale
