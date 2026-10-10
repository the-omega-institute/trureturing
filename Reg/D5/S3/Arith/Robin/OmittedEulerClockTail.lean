import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OmittedEulerClockTail
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OmittedEulerClockTail

open _root_.D5.S3.Arith.Robin.OmittedEulerClockTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := ℕ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime → ∀ {u : ℝ}, 0 < u →
    Summable (R.readout () (p, u)) ∧
      (∑' q : ℕ, R.readout () (p, u) q) ≤
        (p : ℝ) ^ (-u) * (1 / (u * Real.log p) + anchorBudget p / Real.log p)

def actual : Realization signature :=
  realize signature (fun _ param q => primeTail param.1 param.2 q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (p := 2) (by decide) (u := 1) (by norm_num)).1
  have hn : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
    intro h
    have h10 : (1 : ℝ) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds h.tendsto_atTop_zero
    exact one_ne_zero h10
  exact hn hh

def primeRegistration : Registration arena
    (∀ {p : ℕ}, p.Prime → ∀ {u : ℝ}, 0 < u →
      Summable (primeTail p u) ∧ (∑' q : ℕ, primeTail p u q) ≤
        (p : ℝ) ^ (-u) * (1 / (u * Real.log p) + anchorBudget p / Real.log p)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(2, 1), 0, 2, ?_⟩
    norm_num [actual, realize, primeTail, Real.rpow_neg]

/-- The complete dependent-family law and its four kernel obligations are present.
Raw reconstruction and binding of the implicit series readout are still required;
this record is not a claim of declared_validated audit evidence. -/
def primeAudit : Contract.Registration (@prime_tail_bound)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.OmittedEulerClockTail.prime_tail_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OmittedEulerClockTail.primeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨primeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms primeRegistration

end

end Reg.D5.S3.Arith.Robin.OmittedEulerClockTail
