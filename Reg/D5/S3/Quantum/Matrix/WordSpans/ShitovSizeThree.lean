import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree

/-! Independent length observations in the premise and conclusion of the universal index law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree

open scoped Pointwise
open _root_.D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

local notation "M" => Matrix (Fin 3) (Fin 3) ℂ

abbrev signature : Signature where
  Params := Set M
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Submodule ℂ M
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ => exactWordSpan) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsLeast {k : ℕ | 0 < k ∧ ∀ S : Set M,
    (∃ m : ℕ, 0 < m ∧ R.readout false S m = ⊤) → R.readout true S k = ⊤} 7

private theorem span_eq_set_power (S : Set M) (n : ℕ) :
    exactWordSpan S n = Submodule.span ℂ (S ^ n) := by
  unfold exactWordSpan
  congr 1
  ext X
  exact Set.mem_pow.symm

private theorem empty_seventh : exactWordSpan (∅ : Set M) 7 = ⊥ := by
  rw [span_eq_set_power, Set.empty_pow (by decide), Submodule.span_empty]

private theorem univ_first : exactWordSpan (Set.univ : Set M) 1 = ⊤ := by
  rw [span_eq_set_power, pow_one, Submodule.span_univ]

def changed (i : Bool) : Realization signature :=
  realize signature (fun j S k =>
    if j = i then (if i = false then ⊤ else ⊥) else exactWordSpan S k) (fun e => nomatch e)

private theorem changed_law (i : Bool) : ¬ arena.Law (changed i) := by
  intro h
  have atSeven := h.1.2
  cases i
  · have hbad := atSeven ∅ ⟨1, by decide, by simp [changed, realize]⟩
    simp [changed, realize, empty_seventh] at hbad
  · have hbad := atSeven Set.univ ⟨1, by decide, by simpa [changed, realize] using univ_first⟩
    simp [changed, realize] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(∅ : Set M), 0, 7, ?_⟩
  change exactWordSpan (∅ : Set M) 0 ≠ exactWordSpan (∅ : Set M) 7
  rw [empty_seventh, span_eq_set_power, pow_zero]
  intro he
  have hone : (1 : M) ∈ Submodule.span ℂ (1 : Set M) := Submodule.subset_span (by simp)
  rw [he] at hone
  exact one_ne_zero (by simpa only [Submodule.mem_bot] using hone)

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, changed false, changed_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i, ?_, rfl, changed_law i⟩
      intro j hj
      funext S k
      simp [actual, changed, realize, hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["fn", "arg", "arg", "body", "arg", "body", "domain", "arg",
        "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["fn", "arg", "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree
