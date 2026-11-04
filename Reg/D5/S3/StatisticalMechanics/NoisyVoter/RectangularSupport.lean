import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport
import Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
import Reg.Support.DependentFamily

/-! # Original-domain registration of the rectangular support assertion -/

namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport

noncomputable section

structure Query where
  V : Type
  Ω : Type
  G : SimpleGraph V
  u : V
  N : ℕ
  ω : Ω

abbrev assignment (p : Query) := (c : Coord p.V) → p.Ω → Value p.G c

def signature : Signature where
  Params := Query
  State := assignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.N+1) → Bool × Label p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => history x p.u p.N p.ω) (fun e => nomatch e)

/-- A fresh time-one label cannot belong to the original zero-horizon label set. -/
def rejected : Realization signature :=
  realize signature
    (fun _ p x n => (nvm x n.val p.u p.ω, Sum.inr (⟨1, by decide⟩, p.u)))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V Ω : Type} {G : SimpleGraph V} [_hLF : G.LocallyFinite]
    (_hG : G.Connected) (_hNbr : ∀ v, ∃ w, G.Adj v w) (u : V) (N : ℕ),
    (∀ v, v ∈ K G u N ↔ G.dist u v ≤ N) ∧ Countable V ∧
    (∀ v, Sum.inl v ∈ L G u N ↔ v ∈ K G u N) ∧
    (∀ (n : ℕ+) v, Sum.inr (n, v) ∈ L G u N ↔ n.val ≤ N ∧ v ∈ K G u N) ∧
    (∀ c ∈ rectangle G u N, positive c) ∧
    ∃ f : RectangleState G u N → Fin (N+1) → Bool × Label V,
      Measurable f ∧
      ∀ (x : (c : Coord V) → Ω → Value G c) (ω : Ω),
        R.readout () ⟨V, Ω, G, u, N, ω⟩ x = f (restrictRectangle x u N ω) ∧
        ∀ s : Fin (N+1), (R.readout () ⟨V, Ω, G, u, N, ω⟩ x s).2 ∈ L G u N

private theorem bridge : (type_of% (@rectangular_history_support)) ↔ arena.Law actual := by
  constructor
  · intro h V Ω G hLF hG hNbr u N
    exact @h V Ω G hLF hG hNbr u N
  · intro h V Ω G hLF hG hNbr u N
    exact @h V Ω G hLF hG hNbr u N

private theorem test_neighbors (v : Bool) : ∃ w, (⊤ : SimpleGraph Bool).Adj v w :=
  ⟨!v, by cases v <;> decide⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hr := h (V := Bool) (Ω := Unit) (G := ⊤)
    SimpleGraph.connected_top test_neighbors true 0
  obtain ⟨f, _, hf⟩ := hr.2.2.2.2.2
  have hs := (hf (FiniteCausalInputs.testAssignment true) ()).2 (0 : Fin 1)
  change (Sum.inr (⟨1, by decide⟩, true) : Label Bool) ∈
    L (⊤ : SimpleGraph Bool) true 0 at hs
  have hactual := rectangular_history_support (Ω := Unit) (G := (⊤ : SimpleGraph Bool))
    SimpleGraph.connected_top test_neighbors true 0
  have hb := (hactual.2.2.2.1 ⟨1, by decide⟩ true).mp hs
  exact Nat.not_succ_le_zero 0 hb.1

def support_family : Registration arena (type_of% (@rectangular_history_support)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @rectangular_history_support, rejected, rejected_law⟩
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
    refine ⟨⟨Bool, Unit, ⊤, true, 0, ()⟩,
      FiniteCausalInputs.testAssignment true, FiniteCausalInputs.testAssignment false, ?_⟩
    intro h
    have he := congrArg (fun f => (f 0).1) h
    change true = false at he
    cases he

def support_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rectangular_history_support) (Realization signature) (type_of% (@history)) Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport.rectangular_history_support.__information_unit
  realizationName := ``support_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨support_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => history x p.u p.N p.ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport
    definition := none
    coordinates := #[0, 1, 2, 6, 7, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport
