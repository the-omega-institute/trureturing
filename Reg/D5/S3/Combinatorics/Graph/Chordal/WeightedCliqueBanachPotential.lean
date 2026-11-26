import D5.S3.Combinatorics.Graph.Chordal.WeightedCliqueBanachPotential
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The reconstruction radius as a function of the triangle tolerance at each clique width. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedCliqueBanachPotential

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph

noncomputable section

universe u v

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ k ε => (4 - 4 / (k : ℝ) - 2 * ((k : ℝ) - 2)^2 / ((k : ℝ) * ((k : ℝ) - 1)^3)) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (k : ℕ) (_hk : 3 ≤ k)
    (_hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : V → E, ∀ i j, G.Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () k ε

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2)
  have hcard : Fintype.card V = 2 := by simp [V]
  have hG : (⊤ : SimpleGraph V).IsChordal := by
    intro x c hc hlen
    have hsize := hc.support_nodup.length_le_card
    rw [List.length_tail, c.length_support, hcard] at hsize
    omega
  have hclique (s : Finset V) (_ : (⊤ : SimpleGraph V).IsClique (s : Set V)) :
      s.card ≤ 3 + 1 := (Finset.card_le_univ s).trans (by rw [hcard]; decide)
  obtain ⟨φ, hφ⟩ := h hG 3 (by decide) hclique (E := ULift.{v} ℝ)
    (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  have hab : (⊤ : SimpleGraph V).Adj a b := by
    change a ≠ b
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  have herr := hφ a b hab
  change ‖(0 : ULift.{v} ℝ) - (φ b - φ a)‖ ≤ -1 at herr
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (φ b - φ a))]

def family : Registration arena.{u, v}
    (type_of% (@IsChordal.exists_biased_clique_banach_gain_potential.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_biased_clique_banach_gain_potential.{u, v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨4, 0, 1, ?_⟩
    norm_num [actual, realize]

example : (4 - 4 / (4 : ℝ) - 2 * (4 - 2)^2 / (4 * (4 - 1)^3)) = 79 / 27 ∧
    (79 / 27 : ℝ) < 3 := by norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_biased_clique_banach_gain_potential.{u, v})
    (Realization signature) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_biased_clique_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedCliqueBanachPotential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.WeightedCliqueBanachPotential
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedCliqueBanachPotential
