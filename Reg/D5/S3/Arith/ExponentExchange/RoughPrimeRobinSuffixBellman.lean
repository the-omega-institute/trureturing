import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem loglog_three_pos : 0 < Real.log (Real.log (3 : ℝ)) := by
  apply Real.log_pos
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr
    Real.exp_one_lt_three

/-- The original telescope and all four clauses are retained. Only the first
maximum's budget is observed; the rest of the source fixes its comparison. -/
abbrev bellmanArena : Arena where
  signature := signature
  Law R := ∀ (C y i b h : ℕ) (_hb : 1 ≤ b),
    robinV C y i (R.readout () () b) h =
        (robinBranchValues C y i b h).max' (by
          classical
          exact ⟨_, Finset.mem_insert_self _ _⟩) ∧
      (∀ t : List ℕ, Feasible y i b h t → robinScore C y i t ≤ robinV C y i b h) ∧
      (∃ t : List ℕ, Feasible y i b h t ∧ robinScore C y i t = robinV C y i b h) ∧
      (∀ a : ℕ, 1 ≤ a → prime y i ^ a ≤ b → b / prime y i ^ a < b)

private theorem bellman_rejected_law : ¬ bellmanArena.Law rejected := by
  classical
  intro h
  have hh := (h 3 1 0 1 0 (by norm_num)).1
  have hterminal : 1 / Real.log (Real.log (3 : ℝ)) ∈
      robinBranchValues 3 1 0 1 0 := Finset.mem_insert_self _ _
  have hle := Finset.le_max' (s := robinBranchValues 3 1 0 1 0)
    (1 / Real.log (Real.log (3 : ℝ))) hterminal
  have hz : robinV 3 1 0 (rejected.readout () () 1) 0 = 0 := by
    simp [rejected, realize, robinV]
  rw [hz] at hh
  have hpos := one_div_pos.mpr loglog_three_pos
  linarith

def bellmanFamily : Registration bellmanArena (type_of% @robin_bellman_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_bellman_complete, rejected, bellman_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bellman_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

def bellmanAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@robin_bellman_complete) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman.robin_bellman_complete.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman.bellmanFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bellmanArena⟩
  objectArena := .source ⟨bellmanArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bellmanArena ⟨bellmanFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Only the budget in the conclusion's root maximum is observed. The actual
integer, denominator, roughness and every source hypothesis remain fixed. -/
abbrev roughArena : Arena where
  signature := signature
  Law R := ∀ {C y B n : ℕ}, 3 ≤ C → 1 ≤ y →
    1 ≤ n → n ≤ B → Rough y n →
      ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
          Real.log (Real.log ((C * n : ℕ) : ℝ)) ≤
        robinV C y 0 (R.readout () () B) (rootCap y B)

private theorem rough_rejected_law : ¬ roughArena.Law rejected := by
  intro h
  have hrough : Rough 1 1 := by
    intro p hp hpd
    exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim
  have hh := h (C := 3) (y := 1) (B := 1) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrough
  have hle : 1 / Real.log (Real.log (3 : ℝ)) ≤ 0 := by
    simpa [rejected, realize, robinV] using hh
  exact (not_le_of_gt (one_div_pos.mpr loglog_three_pos)) hle

def roughFamily : Registration roughArena (type_of% @rough_robin_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rough_robin_bound, rejected, rough_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rough_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

def roughAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@rough_robin_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman.rough_robin_bound.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman.roughFamily
  realizationSource := none
  generated := false
  arena := .source ⟨roughArena⟩
  objectArena := .source ⟨roughArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source roughArena ⟨roughFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms bellmanFamily
#print axioms roughFamily
#print axioms bellmanAudit
#print axioms roughAudit

end Reg.D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman
