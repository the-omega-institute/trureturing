import D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Numerical tests and source-bound registrations for retained simplicial identities. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph

noncomputable section

universe u v

private abbrev Pair := ULift.{u} (Fin 2)
private def a : Pair.{u} := ⟨0⟩
private def b : Pair.{u} := ⟨1⟩
private abbrev pairGraph : SimpleGraph Pair.{u} := ⊤

private theorem pair_adj : pairGraph.Adj a b := by
  change a ≠ b
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)

private theorem pair_chordal : pairGraph.{u}.IsChordal := by
  have h : pairGraph.{u}.IsAcyclic := IsAcyclic.of_card_le_two (by simp)
  intro _ p hp _
  exact (h p hp).elim

private theorem pair_cliques (n : ℕ) (hn : 2 ≤ n) :
    ∀ C : Set Pair.{u}, pairGraph.IsClique C → C.ncard ≤ n := by
  intro C _
  exact C.ncard_le_card.trans (by simpa using hn)

private theorem impossible_pair (R : ℝ) (hR : R < 0)
    (h : ∃ p : Pair.{u} → ULift.{v} ℝ, ∀ x y, pairGraph.Adj x y →
      ‖(0 : ULift.{v} ℝ) - (p y - p x)‖ ≤ R) : False := by
  obtain ⟨p, h⟩ := h
  exact hR.not_ge ((norm_nonneg _).trans (h a b pair_adj))

private theorem sqrt17_lower : 3 ≤ Real.sqrt 17 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17), Real.sqrt_nonneg 17]

private theorem sqrt17_upper : Real.sqrt 17 ≤ 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17), Real.sqrt_nonneg 17]

example : (Real.sqrt 17 - 1) / 2 < (1 + Real.sqrt 5) / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hl : 2 < Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5]
  by_contra! h
  nlinarith [mul_nonneg (show 0 ≤ Real.sqrt 17 - (2 + Real.sqrt 5) by linarith)
    (show 0 ≤ Real.sqrt 17 + (2 + Real.sqrt 5) by linarith [sqrt17_lower])]

example : (2 : ℝ) < (3 + Real.sqrt 33) / 4 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 33), Real.sqrt_nonneg 33]

example : 2 * Real.sqrt 3 - 1 < 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

example : (3 + Real.sqrt 7) / 2 < 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7), Real.sqrt_nonneg 7]

section Instantiations

variable {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
  {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
  (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε)

example (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 4) :
    ∃ p : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (p y - p x)‖ ≤ ((Real.sqrt 17 - 1) / 2) * ε := by
  refine hG.exists_regrouped_simplicial_banach_gain_potential 3 (by decide) hclique
    ((Real.sqrt 17 - 1) / 2) ?_ ?_ ?_ g ε hε hskew htri
  · norm_num [max_eq_left (by norm_num : (3 : ℝ) - 2 ≤ 1)]
    linarith [sqrt17_lower]
  · norm_num
    linarith [sqrt17_upper]
  · norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)]

example (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 5) :
    ∃ p : V → E, ∀ x y, G.Adj x y → ‖g x y - (p y - p x)‖ ≤ 2 * ε :=
  hG.exists_regrouped_simplicial_banach_gain_potential 4 (by decide) hclique 2
    (by norm_num) (by norm_num) (by norm_num) g ε hε hskew htri

end Instantiations

namespace Regrouped

abbrev signature := SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ R ε => R * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (k : ℕ) (_hk : 2 ≤ k) (_hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ k+1)
    (R : ℝ) (_hmin : max 1 ((k : ℝ) - 2) ≤ R) (_hmax : R ≤ (k : ℝ) - 1)
    (_hquad : 2 * ((k : ℝ) - 1) ≤ R * (R + 1))
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hskew : ∀ x y, g y x = -g x y)
    (_htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε),
    ∃ φ : V → E, ∀ x y, G.Adj x y → ‖g x y - (φ y - φ x)‖ ≤ A.readout () R ε

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact impossible_pair (-1) (by norm_num)
    (h pair_chordal 2 le_rfl (pair_cliques 3 (by decide)) 1
      (by norm_num) (by norm_num) (by norm_num) (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp))

def family : Registration arena.{u,v} (type_of% (@IsChordal.exists_regrouped_simplicial_banach_gain_potential.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_regrouped_simplicial_banach_gain_potential.{u,v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_regrouped_simplicial_banach_gain_potential.{u,v}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_regrouped_simplicial_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach.Regrouped.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "body", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Regrouped

namespace CliqueSix

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => (2 * Real.sqrt 3 - 1) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (_hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 6)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hskew : ∀ x y, g y x = -g x y)
    (_htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε),
    ∃ φ : V → E, ∀ x y, G.Adj x y → ‖g x y - (φ y - φ x)‖ ≤ A.readout () () ε

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact impossible_pair (-1) (by norm_num)
    (h pair_chordal (pair_cliques 6 (by decide)) (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp))

def family : Registration arena.{u,v} (type_of% (@IsChordal.exists_multiIdentity_cliqueSix_banach_gain_potential.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_multiIdentity_cliqueSix_banach_gain_potential.{u,v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg 3]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_multiIdentity_cliqueSix_banach_gain_potential.{u,v}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_multiIdentity_cliqueSix_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach.CliqueSix.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CliqueSix

namespace CliqueSeven

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => ((3 + Real.sqrt 7) / 2) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (_hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 7)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hskew : ∀ x y, g y x = -g x y)
    (_htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε),
    ∃ φ : V → E, ∀ x y, G.Adj x y → ‖g x y - (φ y - φ x)‖ ≤ A.readout () () ε

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact impossible_pair (-1) (by norm_num)
    (h pair_chordal (pair_cliques 7 (by decide)) (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp))

def family : Registration arena.{u,v} (type_of% (@IsChordal.exists_multiIdentity_cliqueSeven_banach_gain_potential.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_multiIdentity_cliqueSeven_banach_gain_potential.{u,v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]
    linarith [Real.sqrt_nonneg 7]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_multiIdentity_cliqueSeven_banach_gain_potential.{u,v}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_multiIdentity_cliqueSeven_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach.CliqueSeven.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CliqueSeven

end Reg.D5.S3.Combinatorics.Graph.Chordal.MultiIdentitySimplicialBanach
