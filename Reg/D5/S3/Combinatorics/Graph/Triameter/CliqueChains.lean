import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Triameter.CliqueChains

/-! The triameter observation and its source-bound equality law. -/

namespace Reg.D5.S3.Combinatorics.Graph.Triameter.CliqueChains

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Triameter
open _root_.D5.S3.Combinatorics.Graph.Triameter.EvenLegTriangle (Vertex)
open _root_.D5.S3.ConceptDynamics.InformationEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

abbrev signature : DependentFamily.Signature where
  Params := Σ V : Type u, Fintype V
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e)

def shifted : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V}, G.Connected →
    (R.readout () ⟨V, inst⟩ G = 4 * G.indepNum - 1 ↔
      ∃ (q : Fin 3 → ℕ) (f : V → Vertex q),
        _root_.D5.S3.Combinatorics.Graph.Triameter.CliqueChains G q f)

abbrev sourceScope := type_of% (@question1.{u})

private theorem shifted_breaks_law : ¬ arena.{u}.Law shifted.{u} := by
  let V := ULift.{u} Unit
  let G : SimpleGraph V := ⊤
  have hc : G.Connected := SimpleGraph.connected_top
  have hcard : Fintype.card V = 1 := by simp [V]
  obtain ⟨A, ha⟩ := G.exists_isNIndepSet_indepNum
  have hu : G.indepNum ≤ 1 := by
    rw [← ha.card_eq, ← hcard]
    exact Finset.card_le_univ A
  let x : V := ⟨()⟩
  have hi : G.IsIndepSet (({x} : Finset V) : Set V) := by
    intro a ha b hb hne
    exact (hne (Subsingleton.elim a b)).elim
  have hl := hi.card_le_indepNum (t := {x})
  simp only [Finset.card_singleton] at hl
  have hind : G.indepNum = 1 := Nat.le_antisymm hu hl
  intro h
  have he : shifted.readout () ⟨V, inferInstance⟩ G = 4 * G.indepNum - 1 := by
    rw [hind]
    rfl
  obtain ⟨q, f, hconstruction⟩ := (@h V _ G hc).mp he
  let a : Vertex q := ⟨0, 0⟩
  let b : Vertex q := ⟨1, 0⟩
  obtain ⟨v, hv⟩ := hconstruction.layers_nonempty a
  obtain ⟨w, hw⟩ := hconstruction.layers_nonempty b
  have hab : a = b := hv.symm.trans ((congrArg f (Subsingleton.elim v w)).trans hw)
  have h01 := congrArg Sigma.fst hab
  exact (by decide : (0 : Fin 3) ≠ 1) h01

private theorem actual_dependence :
    DependentFamily.ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let V := ULift.{u} (Fin 3)
  refine ⟨⟨V, inferInstance⟩, ⊥, ⊤, ?_⟩
  change triameter (⊥ : SimpleGraph V) ≠ triameter (⊤ : SimpleGraph V)
  have hz : triameter (⊥ : SimpleGraph V) = 0 := by
    simp [triameter, perimeter, SimpleGraph.dist_bot]
  let a (i : Fin 3) : V := ⟨i⟩
  have h01 : a 0 ≠ a 1 := by decide
  have h02 : a 0 ≠ a 2 := by decide
  have h12 : a 1 ≠ a 2 := by decide
  have hle : 3 ≤ triameter (⊤ : SimpleGraph V) := by
    have h := Finset.le_sup (f := perimeter (⊤ : SimpleGraph V)) (Finset.mem_univ a)
    simpa [triameter, perimeter, SimpleGraph.dist_top_of_ne h01,
      SimpleGraph.dist_top_of_ne h02, SimpleGraph.dist_top_of_ne h12] using h
  omega

def familyEvidence : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@question1.{u}, shifted, shifted_breaks_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shifted, ?_, rfl, shifted_breaks_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def contract : Contract.Registration.{_, _, _, 0, 0, 0, u+1, u, 0, 0, 0, 0}
    (@question1.{u})
    (type_of% (DependentFamily.realize signature
      (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e))) Type Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.Triameter.question1
    "Reg.D5.S3.Combinatorics.Graph.Triameter.CliqueChains/Reg.D5.S3.Combinatorics.Graph.Triameter.CliqueChains.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Triameter.CliqueChains.familyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ p G => @triameter p.1 p.2 G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Triameter.CliqueChains
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.Triameter.CliqueChains
