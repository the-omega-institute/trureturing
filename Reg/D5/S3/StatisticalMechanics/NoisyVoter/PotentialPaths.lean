import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
import Reg.Support.DependentFamily
import Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs

/-! # Source-bound audit of unstopped potential paths -/
namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
noncomputable section
structure Query where
  V : Type
  Ω : Type
  G : SimpleGraph V
  i : ℕ
  d : ℕ
  u : V
  ω : Ω
abbrev assignment (p : Query) := (c : Coord p.V) → p.Ω → Value p.G c

def signature : Signature where
  Params := Query
  State := assignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => path x (p.i+p.d) p.u p.ω) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p _ _ => p.u) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V Ω : Type} {G : SimpleGraph V}
    (x : (c : Coord V) → Ω → Value G c) (i d : ℕ) (u : V) (ω : Ω),
    R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x 0 = u ∧
    (∀ k < d, R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x (k+1) =
      (x (.choice (i+d-k) (R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x k)) ω).val) ∧
    (A x i d u ω ↔ survives x i d u ω = true) ∧
    (A x i d u ω ↔ birth (source x (i+d) u ω) ≤ i) ∧
    (A x i d u ω → source x (i+d) u ω = source x i (R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x d) ω) ∧
    (∀ k (hk : k < d),
      (∀ j < k, x (.refresh (i+d-j) (R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x j)) ω = false) →
      x (.refresh (i+d-k) (R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x k)) ω = true →
      source x (i+d) u ω = .inr (⟨i+d-k, by omega⟩, R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x k) ∧
      i < birth (source x (i+d) u ω)) ∧
    (¬ A x i d u ω → ∃ k < d,
      (∀ j < k, x (.refresh (i+d-j) (R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x j)) ω = false) ∧
      x (.refresh (i+d-k) (R.readout () ⟨V, Ω, G, i, d, u, ω⟩ x k)) ω = true) ∧
    (source x i u ω = source x (i+d) u ω → A x i d u ω)

private theorem bridge :
    (type_of% (@potential_path_source_correspondence)) ↔ arena.Law actual := by
  constructor
  · intro h V Ω G x i d u ω
    exact h x i d u ω
  · intro h V Ω G x i d u ω
    exact h x i d u ω

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (_root_.Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs.testAssignment false)
    0 1 false ()).2.1 0 (by decide)
  change false = true at he
  exact Bool.false_ne_true he

private def testChoice (b : Bool) (v : Fin 3) : (⊤ : SimpleGraph (Fin 3)).neighborSet v :=
  if h : v = 0 then
    ⟨if b then 1 else 2, by subst v; cases b <;> decide⟩
  else ⟨0, by change v ≠ 0; exact h⟩
private def testAssignment (b : Bool) :
    (c : Coord (Fin 3)) → Unit → Value (⊤ : SimpleGraph (Fin 3)) c
  | .initial _, _ | .fresh _ _, _ | .refresh _ _, _ => false
  | .choice _ v, _ => testChoice b v

def path_family : Registration arena (type_of% (@potential_path_source_correspondence)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @potential_path_source_correspondence, rejected, rejected_law⟩
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
    refine ⟨⟨Fin 3, Unit, ⊤, 0, 1, 0, ()⟩,
      testAssignment true, testAssignment false, ?_⟩
    intro h
    have he := congrArg (fun f => f 1) h
    change (1 : Fin 3) = 2 at he
    exact (by decide : (1 : Fin 3) ≠ 2) he

def path_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@potential_path_source_correspondence) (Realization signature) (type_of% (@path)) Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths.potential_path_source_correspondence.__information_unit
  realizationName := ``path_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨path_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => path x (p.i+p.d) p.u p.ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
