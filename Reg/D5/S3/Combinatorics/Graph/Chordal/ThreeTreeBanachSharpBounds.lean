import D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
import Mathlib.Analysis.Real.Sqrt
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Concrete radius comparisons and finite path-power obstructions. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds

open SimpleGraph

example : (72537 / 50000 : ℝ) < 3 / 2 ∧ 3 / 2 < (Real.sqrt 17 - 1) / 2 := by
  refine ⟨by norm_num, ?_⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hn := Real.sqrt_nonneg 17
  by_contra! h
  nlinarith [mul_nonneg (show 0 ≤ 4 - Real.sqrt 17 by linarith)
    (show 0 ≤ 4 + Real.sqrt 17 by linarith)]

example : (4 * 2 : ℝ) / (3 * 2 + 4) = 4 / 5 := by norm_num

example : ∃ g : Fin 9 → Fin 9 → pathHexagon,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j k, (pathPowerThree 9).Adj i j → (pathPowerThree 9).Adj j k →
      (pathPowerThree 9).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
    ∀ φ : Fin 9 → pathHexagon, ∃ i j, (pathPowerThree 9).Adj i j ∧
      (3 / 4 : ℝ) < ‖g i j - (φ j - φ i)‖ := by
  obtain ⟨g, hg, ht, h⟩ := pathPowerThree_banach_lower_four_thirds 2 (by decide)
  refine ⟨g, hg, ht, fun φ => ?_⟩
  obtain ⟨i,j,hij,hl⟩ := h φ
  exact ⟨i,j,hij, (show (3/4 : ℝ) < (4*2 : ℝ)/(3*2+4) by norm_num).trans_le hl⟩

example : ∃ g : Fin 18 → Fin 18 → pathHexagon,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j k, (pathPowerThree 18).Adj i j → (pathPowerThree 18).Adj j k →
      (pathPowerThree 18).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
    ∀ φ : Fin 18 → pathHexagon, ∃ i j, (pathPowerThree 18).Adj i j ∧
      (1 : ℝ) < ‖g i j - (φ j - φ i)‖ := by
  obtain ⟨g, hg, ht, h⟩ := pathPowerThree_banach_lower_four_thirds 5 (by decide)
  refine ⟨g, hg, ht, fun φ => ?_⟩
  obtain ⟨i,j,hij,hl⟩ := h φ
  exact ⟨i,j,hij, (show (1 : ℝ) < (4*5 : ℝ)/(3*5+4) by norm_num).trans_le hl⟩

example : ∃ g : Fin 303 → Fin 303 → pathHexagon,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j k, (pathPowerThree 303).Adj i j → (pathPowerThree 303).Adj j k →
      (pathPowerThree 303).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
    ∀ φ : Fin 303 → pathHexagon, ∃ i j, (pathPowerThree 303).Adj i j ∧
      (13 / 10 : ℝ) < ‖g i j - (φ j - φ i)‖ := by
  obtain ⟨g, hg, ht, h⟩ := pathPowerThree_banach_lower_four_thirds 100 (by decide)
  refine ⟨g, hg, ht, fun φ => ?_⟩
  obtain ⟨i,j,hij,hl⟩ := h φ
  exact ⟨i,j,hij, (show (13/10 : ℝ) < (4*100 : ℝ)/(3*100+4) by norm_num).trans_le hl⟩


open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit

noncomputable section

universe u v

namespace PathUpper

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => (4/3 : ℝ) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (g : Fin n → Fin n → E) (ε : ℝ) (_hε : 0 ≤ ε)
    (_hg : ∀ i j, g j i = -g i j)
    (_ht : ∀ i j k, (pathPowerThree n).Adj i j → (pathPowerThree n).Adj j k →
      (pathPowerThree n).Adj i k → ‖g i j + g j k - g i k‖ ≤ ε),
    ∃ φ : Fin n → E, ∀ i j, (pathPowerThree n).Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () () ε

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨φ, hφ⟩ := h (E := ULift.{u} ℝ) 2 (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have adj : (pathPowerThree 2).Adj (0 : Fin 2) 1 := by
    change (0 : Fin 2) ≠ 1 ∧ (0 : ℕ) ≤ 1 + 3 ∧ (1 : ℕ) ≤ 0 + 3
    decide
  have he := hφ 0 1 adj
  change ‖(0 : ULift.{u} ℝ) - (φ 1 - φ 0)‖ ≤ -1 at he
  linarith only [he, norm_nonneg ((0 : ULift.{u} ℝ) - (φ 1 - φ 0))]

def family : Registration arena.{u} (type_of% (@pathPowerThree_banach_upper_four_thirds.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPowerThree_banach_upper_four_thirds.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPowerThree_banach_upper_four_thirds.{u}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.pathPowerThree_banach_upper_four_thirds.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds.PathUpper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PathUpper

namespace ExplicitPathUpper

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => (4/3 : ℝ) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (g : Fin n → Fin n → E) (ε : ℝ) (_hε : 0 ≤ ε)
    (_hg : ∀ i j, g j i = -g i j)
    (_ht : ∀ i j k, (pathPowerThree n).Adj i j → (pathPowerThree n).Adj j k →
      (pathPowerThree n).Adj i k → ‖g i j + g j k - g i k‖ ≤ ε),
    ∀ i j, (pathPowerThree n).Adj i j →
      ‖g i j - (pathPowerThree_causal_potential n g j - pathPowerThree_causal_potential n g i)‖ ≤
        R.readout () () ε

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let g : Fin 2 → Fin 2 → ULift.{u} ℝ := fun _ _ => 0
  let φ := pathPowerThree_causal_potential 2 g
  have adj : (pathPowerThree 2).Adj (0 : Fin 2) 1 := by
    change (0 : Fin 2) ≠ 1 ∧ (0 : ℕ) ≤ 1 + 3 ∧ (1 : ℕ) ≤ 0 + 3
    decide
  have he := h 2 g 0 le_rfl (by simp [g]) (by simp [g]) 0 1 adj
  change ‖(0 : ULift.{u} ℝ) - (φ 1 - φ 0)‖ ≤ -1 at he
  linarith only [he, norm_nonneg ((0 : ULift.{u} ℝ) - (φ 1 - φ 0))]

def family : Registration arena.{u} (type_of% (@pathPowerThree_causal_potential_error.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPowerThree_causal_potential_error.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPowerThree_causal_potential_error.{u}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.pathPowerThree_causal_potential_error.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds.ExplicitPathUpper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExplicitPathUpper

namespace PathLower

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ m => (4*m : ℝ)/(3*m+4)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (_hm : 1 ≤ m),
    ∃ g : Fin (3*m+3) → Fin (3*m+3) → pathHexagon,
      (∀ i j, g j i = -g i j) ∧
      (∀ i j k, (pathPowerThree (3*m+3)).Adj i j → (pathPowerThree (3*m+3)).Adj j k →
        (pathPowerThree (3*m+3)).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
      ∀ φ : Fin (3*m+3) → pathHexagon, ∃ i j, (pathPowerThree (3*m+3)).Adj i j ∧
        R.readout () () m ≤ ‖g i j - (φ j - φ i)‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨g, hg, ht, hl⟩ := h 1 le_rfl
  obtain ⟨φ, hφ⟩ := pathPowerThree_banach_upper_four_thirds 6 g 1 zero_le_one hg ht
  obtain ⟨i, j, hij, he⟩ := hl φ
  change 2 ≤ ‖g i j - (φ j - φ i)‖ at he
  linarith only [he, hφ i j hij]

def family : Registration arena (type_of% (@pathPowerThree_banach_lower_four_thirds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pathPowerThree_banach_lower_four_thirds, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPowerThree_banach_lower_four_thirds) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.pathPowerThree_banach_lower_four_thirds.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds.PathLower.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "body", "arg",
        "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PathLower

namespace ChordalUpper

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => (72537/50000 : ℝ) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} {V : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (_hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 4)
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hg : ∀ i j, g j i = -g i j)
    (_ht : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k → ‖g i j + g j k - g i k‖ ≤ ε),
    ∃ φ : V → E, ∀ i j, G.Adj i j → ‖g i j - (φ j - φ i)‖ ≤ R.readout () () ε

private abbrev Pair := ULift.{v} (Fin 2)
private abbrev edgeGraph : SimpleGraph Pair.{v} := ⊤

private theorem edge_chordal : edgeGraph.{v}.IsChordal := by
  intro _ p hp hlen
  have h : p.support.tail.length ≤ 2 := hp.support_nodup.length_le_card.trans (by simp)
  rw [List.length_tail, p.length_support] at h
  omega

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hc (C : Set Pair.{v}) : C.ncard ≤ 4 := C.ncard_le_card.trans (by simp)
  obtain ⟨φ, hφ⟩ := h (E := ULift.{u} ℝ) (V := Pair.{v}) edge_chordal (fun C _ => hc C)
    (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  let i : Pair.{v} := ⟨0⟩
  let j : Pair.{v} := ⟨1⟩
  have adj : edgeGraph.Adj i j := by
    change i ≠ j
    intro e
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down e)
  have he := hφ i j adj
  change ‖(0 : ULift.{u} ℝ) - (φ j - φ i)‖ ≤ -1 at he
  linarith only [he, norm_nonneg ((0 : ULift.{u} ℝ) - (φ j - φ i))]

def family : Registration arena.{u,v}
    (type_of% (@IsChordal.exists_cliqueFour_banach_gain_potential_polygon.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_cliqueFour_banach_gain_potential_polygon.{u,v},
    rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_cliqueFour_banach_gain_potential_polygon.{u,v})
    (Realization signature) Unit Unit where
  unitName :=
    `SimpleGraph.IsChordal.exists_cliqueFour_banach_gain_potential_polygon.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds.ChordalUpper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "body",
        "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChordalUpper

end

end Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
