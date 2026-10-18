import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer (response)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

namespace Reg.D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace QuantitativeDefect

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ N =>
    (1 - Real.log (2 : ℝ) / Real.log (N : ℝ)) / 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ N =>
    (∑ m ∈ Ico N (2 * N), |response N m|) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 3 ≤ N → ∀ α β : ℝ, ∃ m ∈ Ico N (2 * N),
    R.readout () () N ≤ |response N m - α - β * ((m : ℝ) / N)|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, hm, hle⟩ := h (N := 3) (by norm_num) 0 0
  have hbad : (∑ k ∈ Ico 3 (2 * 3), |response 3 k|) + 1 ≤
      |response 3 m| := by
    simpa only [rejected, realize, sub_zero, zero_mul] using hle
  have hterm : |response 3 m| ≤ ∑ k ∈ Ico 3 (2 * 3), |response 3 k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (response 3 k)) hm
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlog34 : Real.log (3 : ℝ) < Real.log (4 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hratio : Real.log (2 : ℝ) / Real.log (4 : ℝ) <
      Real.log (2 : ℝ) / Real.log (3 : ℝ) := by
    apply (div_lt_div_iff₀ hlog4 hlog3).mpr
    exact mul_lt_mul_of_pos_left hlog34 hlog2
  change (1 - Real.log (2 : ℝ) / Real.log (3 : ℝ)) / 4 ≠
    (1 - Real.log (2 : ℝ) / Real.log (4 : ℝ)) / 4
  apply ne_of_lt
  linarith

def family : Registration arena (type_of% @response_affine_defect_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨response_affine_defect_lower_bound, rejected, rejected_law⟩
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
    (@response_affine_defect_lower_bound) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate.response_affine_defect_lower_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate.QuantitativeDefect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N =>
    (1 - Real.log (2 : ℝ) / Real.log (N : ℝ)) / 4) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Original source path: N,hN,alpha,beta; Exists predicate; right And clause;
  -- left operand of LE.le. N is lexical state binder 0; no parameter coordinate.
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end QuantitativeDefect

namespace Nonaffinity

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
  realize signature (fun _ N m => response N m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 3 ≤ N →
    ¬∃ α β : ℝ, ∀ m ∈ Ico N (2 * N),
      R.readout () N m = α + β * ((m : ℝ) / N)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h (N := 3) (by norm_num)
  refine ⟨0, 0, ?_⟩
  intro m hm
  simp only [rejected, realize, zero_mul, zero_add]

private theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro i
  have hdiff : ∃ m ∈ Ico 3 (2 * 3), response 3 m ≠ response 3 3 := by
    by_contra! hconstant
    apply response_not_affine_on_original_block (N := 3) (by norm_num)
    refine ⟨response 3 3, 0, ?_⟩
    intro m hm
    simpa only [zero_mul, add_zero] using hconstant m hm
  obtain ⟨m, hm, hne⟩ := hdiff
  refine ⟨3, m, 3, ?_⟩
  change response 3 m ≠ response 3 3
  exact hne

def family : Registration arena (type_of% @response_not_affine_on_original_block) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨response_not_affine_on_original_block, rejected, rejected_law⟩
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
    (@response_not_affine_on_original_block) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate.response_not_affine_on_original_block.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate.Nonaffinity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N m => response N m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Original source path: N,hN; Not; Exists alpha; Exists beta; forall m,hm;
  -- left operand of Eq. N is parameter coordinate 0 and m is lexical binder 4.
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Nonaffinity


namespace FourPoint

abbrev signature := QuantitativeDefect.signature

def actual : Realization signature :=
  realize signature (fun _ _ N => 1 - Real.log (2 : ℝ) / Real.log (N : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ N => 4 * (∑ m ∈ Ico N (2 * N), |response N m|) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 3 ≤ N →
    ∃ p c : ℕ, N < p ∧ p < 2 * N ∧ N < c ∧ c < 2 * N ∧ p ≠ c ∧
      ∀ α β : ℝ, R.readout () () N ≤
        ((response N c - α - β * ((c : ℝ) / N)) -
          (response N (c - 1) - α - β * (((c - 1 : ℕ) : ℝ) / N))) -
        ((response N p - α - β * ((p : ℝ) / N)) -
          (response N (p - 1) - α - β * (((p - 1 : ℕ) : ℝ) / N)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, c, hNp, hpN, hNc, hcN, _, hgap⟩ := h (N := 3) (by norm_num)
  have he := hgap 0 0
  simp only [rejected, realize, sub_zero, zero_mul] at he
  have hb (m : ℕ) (hm : m ∈ Ico 3 (2 * 3)) :
      |response 3 m| ≤ ∑ k ∈ Ico 3 (2 * 3), |response 3 k| :=
    single_le_sum (fun k _ => abs_nonneg (response 3 k)) hm
  have hp0 := hb p (mem_Ico.mpr ⟨by omega, hpN⟩)
  have hp1 := hb (p - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
  have hc0 := hb c (mem_Ico.mpr ⟨by omega, hcN⟩)
  have hc1 := hb (c - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
  linarith [le_abs_self (response 3 c), neg_abs_le (response 3 (c - 1)),
    neg_abs_le (response 3 p), le_abs_self (response 3 (p - 1))]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlog34 : Real.log (3 : ℝ) < Real.log (4 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hr : Real.log (2 : ℝ) / Real.log (4 : ℝ) <
      Real.log (2 : ℝ) / Real.log (3 : ℝ) :=
    (div_lt_div_iff₀ hlog4 hlog3).mpr (mul_lt_mul_of_pos_left hlog34 hlog2)
  change 1 - Real.log (2 : ℝ) / Real.log (3 : ℝ) ≠
    1 - Real.log (2 : ℝ) / Real.log (4 : ℝ)
  exact ne_of_lt (by linarith)

def family : Registration arena (type_of% @response_four_point_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨response_four_point_gap, rejected, rejected_law⟩
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
    (@response_four_point_gap) (Realization signature) Type Unit where
  unitName := `OriginalResidualResponseNonaffinityCandidate.response_four_point_gap.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate.FourPoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ N => 1 - Real.log (2 : ℝ) / Real.log (N : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Full-family proof is attempted; exact source binding still needs the native report.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end FourPoint

end
end Reg.D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
