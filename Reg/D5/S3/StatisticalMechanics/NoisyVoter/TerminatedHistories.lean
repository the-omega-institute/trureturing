import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories
import Reg.Support.DependentFamily
import Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs

/-! # Source-bound audit of complete terminated graphical histories -/

namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories

noncomputable section

structure Query where
  V : Type
  Ω : Type
  G : SimpleGraph V
  ω : Ω

abbrev assignment (p : Query) := (c : Coord p.V) → p.Ω → Value p.G c

def signature : Signature where
  Params := Query
  State := assignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → p.V → List (ℕ × p.V)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x n v => history x n v p.ω) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V Ω : Type} {G : SimpleGraph V}
    (x : (c : Coord V) → Ω → Value G c) (ω : Ω) (n m : ℕ) (v w : V),
    let a := R.readout () ⟨V, Ω, G, ω⟩ x n v
    let b := R.readout () ⟨V, Ω, G, ω⟩ x m w
    a[0]? = some (n, v) ∧
    (∀ i p q, a[i]? = some p → a[i+1]? = some q → step x ω p = some q) ∧
    a.getLast? = some (labelVertex (source x n v ω)) ∧
    step x ω (labelVertex (source x n v ω)) = none ∧
    (∀ i j p, a[i]? = some p → b[j]? = some p →
      a.drop i = R.readout () ⟨V, Ω, G, ω⟩ x p.1 p.2 ∧
      b.drop j = R.readout () ⟨V, Ω, G, ω⟩ x p.1 p.2) ∧
    (source x n v ω = source x m w ω ↔ ∃ p, p ∈ a ∧ p ∈ b) ∧
    (source x n v ω = source x m w ω →
      labelVertex (source x n v ω) ∈ a ∧ labelVertex (source x n v ω) ∈ b ∧
      a.getLast? = b.getLast?)

private theorem bridge :
    (type_of% (@terminated_history_source_correspondence)) ↔ arena.Law actual := by
  constructor
  · intro h V Ω G x ω n m v w
    exact @h V Ω G x ω n m v w
  · intro h V Ω G x ω n m v w
    exact @h V Ω G x ω n m v w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (_root_.Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs.testAssignment false)
    () 0 0 false false).1
  cases hb

def history_family : Registration arena (type_of% (@terminated_history_source_correspondence)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @terminated_history_source_correspondence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i by cases i; cases j; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨⟨Bool, Unit, ⊤, ()⟩,
      _root_.Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs.testAssignment true,
      _root_.Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs.testAssignment false, ?_⟩
    intro h
    have he := congrArg (fun f => (f 1 false).length) h
    change 1 = 2 at he
    cases he

def history_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@terminated_history_source_correspondence) (Realization signature) (type_of% (@history)) Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories.terminated_history_source_correspondence.__information_unit
  realizationName := ``history_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨history_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x n v => history x n v p.ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories
