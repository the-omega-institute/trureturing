import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin
import Reg.Support.DependentFamily

/- SOURCE-ONLY original source/law/readout bridge attempt, UNCOMPILED.
   No Contract.Registration or declared_validated is asserted. No anchors
   have been added to manufacture an observational-dependence witness.
   The all-integer proof now uses the public same-correction second-order
   supplier through consumed private clock helpers; its complete headline
   and the law/readout telescope below are unchanged. This is source
   preparation, not native evidence or an accepted registration. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter

namespace Reg.D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger (goldenResourceObjective)
open _root_.D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin (K)
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin (F T all_integer_sharp_margin)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ n => if role then T n else F n) (fun e => nomatch e)

/-- Both actual integer margin sequences are readouts. RH and the original
real-price/full-positive-predecessor witness telescope are retained verbatim.
The law has no desired endpoint as an added premise. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀ _hRH : RiemannHypothesis,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K - ε < V.readout false () n ∧
      Real.exp Real.eulerMascheroniConstant * K - ε < V.readout true () n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m : ℕ, ∃ lambda : ℝ,
      N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |V.readout false () m - K| < ε ∧
      |V.readout true () m - Real.exp Real.eulerMascheroniConstant * K| < ε) ∧
    Filter.liminf (fun n : ℕ => V.readout false () n) atTop = K ∧
    Filter.liminf (fun n : ℕ => V.readout true () n) atTop =
      Real.exp Real.eulerMascheroniConstant * K

private theorem actual_law : arena.Law actual := by
  exact @all_integer_sharp_margin

private theorem source_bridge :
    (type_of% (@all_integer_sharp_margin)) ↔ arena.Law actual := Iff.rfl

/- Unfinished named audit obligations, with no substitute Contract:
   1. WholeFamilyIntervention: a concrete alternate family, with fixed
      nonintervened coordinates and a proved change in the FULL law.
   2. WholeFamilySensitivity: genuine sensitivity evidence for the two
      sequence readouts in this eventual/attainment/liminf telescope.
   3. ObservationalDependence: source-supported dependence on integer state
      and the distinct F/T observation role; a tautological anchor is invalid.
   4. SourceSelectionTemplate: an applicable template and exact source/readout
      selection evidence for these two readouts and the original objective.
   5. CurrentProducerBinding: native source binding and current accepted
      declaration/axiom closure for the complete uncompiled consumer theorem.
   The original-record endpoint supplier is public and delivered. The exact
   Law above is conditional on RH for EVERY family: under Not RH it holds
   vacuously. Consequently a rejected alternate family would imply RH.
   Empty anchors do not supply that rejection or observational dependence.
   Root owns the exact linked issue after native source finalization. No
   issue was filed, registration accepted, or judge/tool/Interface/Impl edited.
   actual_law/source_bridge are bridge drafts, not completed audit evidence. -/

end Reg.D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin
