/- Source-bound dependent-family registration for the original arithmetic owner.
Machine validation is supplied by the current scoped report, separately for each audit. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open _root_.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights (w)
open _root_.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
open _root_.D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N m => responseAdjointResidual N m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  rcases or6_response_adjoint_identity_and_signs (N := 3) (by norm_num) with
    ⟨_, _, _, _, ⟨p, hp, hpos⟩, ⟨n, hn, hneg⟩, _, _⟩
  refine ⟨3, p, n, ?_⟩
  change responseAdjointResidual 3 p ≠ responseAdjointResidual 3 n
  exact ne_of_gt (hneg.trans hpos)

namespace LowerBound

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 3 ≤ N →
    (1 - Real.log (2 : ℝ) / Real.log (N : ℝ)) ^ 2 / (24 * (N : ℝ) ^ 2 - 36 * (N : ℝ) + 14) ≤
      ∑ m ∈ Finset.Ico N (2 * N), w m * (R.readout () N m) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog23 : Real.log (2 : ℝ) < Real.log (3 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hgap : 0 < 1 - Real.log (2 : ℝ) / Real.log (3 : ℝ) :=
    sub_pos.mpr ((div_lt_one hlog3).mpr hlog23)
  have hpositive : 0 <
      (1 - Real.log (2 : ℝ) / Real.log (3 : ℝ)) ^ 2 / (24 * (3 : ℝ) ^ 2 - 36 * (3 : ℝ) + 14) := by
    exact div_pos (sq_pos_of_pos hgap) (by norm_num)
  have he := h (N := 3) (by norm_num)
  have hnonpos :
      (1 - Real.log (2 : ℝ) / Real.log (3 : ℝ)) ^ 2 / (24 * (3 : ℝ) ^ 2 - 36 * (3 : ℝ) + 14) ≤ 0 := by
    simpa [rejected, realize] using he
  exact (not_le_of_gt hpositive) hnonpos

def family : Registration arena (type_of% (@responseAdjoint_energy_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@responseAdjoint_energy_lower_bound, rejected, rejected_law⟩
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
    (@responseAdjoint_energy_lower_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy.responseAdjoint_energy_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy.LowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N m => responseAdjointResidual N m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- UNVERIFIED static occurrence candidates; see audit/source-audit.json.
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LowerBound

end Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy
