/- Source-bound dependent-family registration for the original arithmetic owner.
Machine validation is supplied by the current scoped report, separately for each audit. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open _root_.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights (w omega coeff)
open _root_.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint

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

namespace Identity

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 3 ≤ N → ∀ a b : ℝ,
    _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) =
      Real.log (N : ℝ) *
        ∑ m ∈ Finset.Ico N (2 * N), omega a b m * R.readout () N m

private theorem zero_family_rejected : ¬ arena.Law rejected := by
  intro h
  rcases or6_response_adjoint_identity_and_signs (N := 3) (by norm_num) with
    ⟨_, _, _, _, _, _, hstrict, _⟩
  obtain ⟨a, b, hNa, hab, hbN, hpositive⟩ := hstrict
  have hz := h (N := 3) (by norm_num) a b
  change _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual 3
      (coeff 3 a b) = Real.log (3 : ℝ) *
        ∑ m ∈ Finset.Ico 3 (2 * 3), omega a b m * (0 : ℝ) at hz
  simp only [mul_zero, Finset.sum_const_zero] at hz
  exact (ne_of_gt hpositive) hz


def family : Registration arena (type_of% (@responseAdjoint_actual_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@responseAdjoint_actual_identity, rejected, zero_family_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, zero_family_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@responseAdjoint_actual_identity) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalResidualResponseAdjoint.responseAdjoint_actual_identity.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint.Identity.family
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
    owner := `D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Identity

namespace IdentityAndSigns

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 3 ≤ N →
    (∑ m ∈ Finset.Ico N (2 * N), w m * R.readout () N m) = 0 ∧
    (∑ m ∈ Finset.Ico N (2 * N),
      (w m * ((m : ℝ) / N)) * R.readout () N m) = 0 ∧
    (∀ a b : ℝ,
      _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) =
        Real.log (N : ℝ) *
          ∑ m ∈ Finset.Ico N (2 * N), omega a b m * R.readout () N m) ∧
    (∃ m ∈ Finset.Ico N (2 * N), R.readout () N m ≠ 0) ∧
    (∃ m ∈ Finset.Ico N (2 * N), 0 < R.readout () N m) ∧
    (∃ m ∈ Finset.Ico N (2 * N), R.readout () N m < 0) ∧
    (∃ a b : ℝ, (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
      0 < _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b)) ∧
    (∃ a b : ℝ, (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
      _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) < 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, hm, hne⟩ := (h (N := 3) (by norm_num)).2.2.2.1
  change (0 : ℝ) ≠ 0 at hne
  exact hne rfl

def family : Registration arena (type_of% (@or6_response_adjoint_identity_and_signs)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@or6_response_adjoint_identity_and_signs, rejected, rejected_law⟩
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
    (@or6_response_adjoint_identity_and_signs) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalResidualResponseAdjoint.or6_response_adjoint_identity_and_signs.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint.IdentityAndSigns.family
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
  -- Enhanced whole-law source binding remains unfinished; no selector acceptance is claimed.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end IdentityAndSigns

end Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
