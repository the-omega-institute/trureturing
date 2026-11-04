import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
import Reg.Support.DependentFamily

/-! # Source-bound audit of the native opinion reconstruction -/

namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources

noncomputable section

structure Query where
  V : Type
  Ω : Type
  G : SimpleGraph V
  n : ℕ
  v : V
  ω : Ω

abbrev assignment (p : Query) := (c : Coord p.V) → p.Ω → Value p.G c

def signature : Signature where
  Params := Query
  State := assignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => nvm x p.n p.v p.ω) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (V Ω : Type) (G : SimpleGraph V) (x : (c : Coord V) → Ω → Value G c)
    (n : ℕ) (v : V) (ω : Ω),
    R.readout () ⟨V, Ω, G, n, v, ω⟩ x = coin x (source x n v ω) ω

def testAssignment (b : Bool) : (c : Coord Bool) → Unit → Value (⊤ : SimpleGraph Bool) c
  | .initial _, _ | .fresh _ _, _ | .refresh _ _, _ => b
  | .choice _ v, _ => ⟨!v, by cases v <;> decide⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h Bool Unit ⊤ (testAssignment true) 0 true ()
  change false = true at he
  exact Bool.false_ne_true he

def native_source_family : Registration arena (type_of% (@native_source)) where
  actual := actual
  bridge := by
    constructor
    · intro h V Ω G x n v ω
      exact h x n v ω
    · intro h V Ω G x n v ω
      exact h V Ω G x n v ω
  variation := ⟨@native_source, rejected, rejected_law⟩
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
    refine ⟨⟨Bool, Unit, ⊤, 0, true, ()⟩, testAssignment true, testAssignment false, ?_⟩
    change true ≠ false
    decide

def native_source_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_source) (Realization signature) (type_of% (@nvm)) Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources.native_source.__information_unit
  realizationName := ``native_source_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨native_source_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => nvm x p.n p.v p.ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@nvm)
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


/-- The original measurable-opinion telescope and its actual readout. -/
def measurableArena : Arena where
  signature := signature
  Law R := ∀ (V Ω : Type) (G : SimpleGraph V) [hG : G.LocallyFinite]
    [mΩ : MeasurableSpace Ω] (x : (c : Coord V) → Ω → Value G c),
    (∀ c, Measurable (x c)) → ∀ n v,
      Measurable (fun ω => R.readout () ⟨V, Ω, G, n, v, ω⟩ x)

theorem measurable_bridge : (type_of% (@nvm_measurable)) ↔ measurableArena.Law actual := by
  constructor
  · intro h V Ω G hG mΩ x hx n v
    exact @h V Ω G hG mΩ x hx n v
  · intro h V Ω G hG mΩ x hx n v
    exact @h V Ω G hG mΩ x hx n v

structure VarianceQuery where
  V : Type
  Ω : Type
  G : SimpleGraph V
  locallyFinite : G.LocallyFinite
  measurableΩ : MeasurableSpace Ω
  P : @MeasureTheory.Measure Ω measurableΩ
  u : V
  d : ℕ
  t : ℕ

abbrev varianceState (p : VarianceQuery) :=
  @Model p.V p.Ω p.G p.locallyFinite p.measurableΩ p.P

def varianceSignature : Signature where
  Params := VarianceQuery
  State := varianceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def varianceActual : Realization varianceSignature :=
  realize varianceSignature (fun _ p M => by
    letI := p.locallyFinite
    letI := p.measurableΩ
    exact ProbabilityTheory.variance (W M.coordinate p.u p.d p.t) p.P)
    (fun e => nomatch e)

def varianceArena : Arena where
  signature := varianceSignature
  Law R := ∀ (V Ω : Type) (G : SimpleGraph V) (hG : G.LocallyFinite)
    (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
    (M : @Model V Ω G hG mΩ P) (u : V) (d t : ℕ),
    (t : ℝ) / 4 * (1 - (1 - (M.ε : ℝ)) ^ d) ≤
      R.readout () ⟨V, Ω, G, hG, mΩ, P, u, d, t⟩ M

theorem uniform_variance_bridge : (type_of% (@uniform_variance_lower)) ↔
    varianceArena.Law varianceActual := by
  constructor
  · intro h V Ω G hG mΩ P M u d t
    exact @h V Ω G hG mΩ P M u d t
  · intro h V Ω G hG mΩ P M u d t
    exact h V Ω G hG mΩ P M u d t

/- The measurable and variance arenas preserve their complete original telescopes.
Their negative-law variation, whole-family sensitivity, actual observational dependence,
and source selections have no completed registration here. The native_source registration
is a separate target; its evidence supplies none of these missing slots. -/

#print axioms native_source_family
#print axioms native_source_registration
#print axioms measurable_bridge
#print axioms uniform_variance_bridge

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
