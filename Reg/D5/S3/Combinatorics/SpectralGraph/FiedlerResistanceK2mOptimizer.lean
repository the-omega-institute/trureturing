import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

/-! The observation retains the complete conductance function, with arbitrary nonedges. -/

noncomputable section
namespace Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation (lambda2 totalRes)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Weights (m : ℕ) := Sym2 (Fin (2+m)) → ℝ

abbrev signature : Signature where
  Params := ℕ
  State m := Weights m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Weights m
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => w) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Every occurrence of a conductance function is observed in the full source conjunction. -/
def observedClaim (m : ℕ) (R0 : ℝ) (observe : Weights m → Weights m) : Prop :=
  let t := maxValue m R0
  let a := plusConductance m R0
  let b := minusConductance m R0
  let p := uniformWeights m a b
  let q := uniformWeights m b a
  (∀ w : Weights m, (∀ e ∈ (K2m m).edgeSet, 0 < observe w e) →
    totalRes (K2m m) (observe w) = R0 → lambda2 (K2m m) (observe w) ≤ t) ∧
  ((∀ e ∈ (K2m m).edgeSet, 0 < observe p e) ∧ totalRes (K2m m) (observe p) = R0 ∧
    lambda2 (K2m m) (observe p) = t ∧ EdgeRestriction m a b (observe p)) ∧
  ((∀ e ∈ (K2m m).edgeSet, 0 < observe q e) ∧ totalRes (K2m m) (observe q) = R0 ∧
    lambda2 (K2m m) (observe q) = t ∧ EdgeRestriction m b a (observe q)) ∧
  (∀ w : Weights m, (∀ e ∈ (K2m m).edgeSet, 0 < observe w e) →
    totalRes (K2m m) (observe w) = R0 →
      (lambda2 (K2m m) (observe w) = t ↔
        EdgeRestriction m a b (observe w) ∨ EdgeRestriction m b a (observe w))) ∧
  (¬ ∃ w, EdgeRestriction m a b (observe w) ∧ EdgeRestriction m b a (observe w)) ∧
  (∀ w, EdgeRestriction m a b (observe w) →
    EdgeRestriction m b a (observe (exchangeWeights m w))) ∧
  (∀ w, EdgeRestriction m b a (observe w) →
    EdgeRestriction m a b (observe (exchangeWeights m w))) ∧
  (∀ w w', (∀ e ∈ (K2m m).edgeSet, observe w e = observe w' e) →
    lambda2 (K2m m) (observe w) = lambda2 (K2m m) (observe w') ∧
      totalRes (K2m m) (observe w) = totalRes (K2m m) (observe w'))

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 3 ≤ m → ∀ (R0 : ℝ), 0 < R0 → observedClaim m R0 (R.readout () m)

abbrev source := type_of% (@result)

theorem source_bridge : source ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h 3 (by norm_num) 1 (by norm_num)).2.1.1
  have he : s((0 : Fin (2+3)), (2 : Fin (2+3))) ∈ (K2m 3).edgeSet := by decide
  have hh := hp _ he
  change (0 : ℝ) < 0 at hh
  exact (lt_irrefl 0) hh

def family : Registration arena source where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨3, (0 : Weights 3), (1 : Weights 3), ?_⟩
    intro he
    have hh := congrFun he s((0 : Fin (2+3)), (2 : Fin (2+3)))
    norm_num [actual, realize] at hh

noncomputable def sourceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0} (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
      name := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.OptimizerClaim
      path := #[] }
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
