import D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound realizations of the finite averaging radius, the two-defect radii,
and the right endpoint of the path-power interval representation. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph SimpleGraph.BanachPathPower

noncomputable section
universe u v

namespace Banach

abbrev signature : Signature where
  Params := Σ _ : Type u, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p ε => (p.2 - 1 : ℝ) *
    (1 - (((p.2 - 1 : ℝ) / p.2) ^ (Nat.card p.1 - 1))) * ε) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (k : ℕ) (_hk : 2 ≤ k)
    (_hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : V → E, ∀ i j, G.Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () ⟨V, k⟩ ε

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
      s.card ≤ 2 + 1 := (Finset.card_le_univ s).trans (by rw [hcard]; decide)
  obtain ⟨φ, hφ⟩ := h hG 2 (by decide) hclique (E := ULift.{v} ℝ)
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
    (type_of% (@IsChordal.exists_simplicial_banach_gain_potential.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_simplicial_banach_gain_potential.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} (Fin 2), 2⟩, 0, 1, ?_⟩
    norm_num [actual, realize, Nat.card_eq_fintype_card]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_simplicial_banach_gain_potential.{u, v})
    (Realization signature.{u}) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_simplicial_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential.Banach.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
    definition := none
    coordinates := #[0, 4]
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

-- For every finite vertex count, the two low-width coefficients are strictly below one and two.
example (n : ℕ) : (2 - 1 : ℝ) * (1 - (((2 - 1 : ℝ) / 2) ^ (n - 1))) < 1 := by
  have h : 0 < (1 / 2 : ℝ) ^ (n - 1) := pow_pos (by norm_num) _
  norm_num

example (n : ℕ) : (3 - 1 : ℝ) * (1 - (((3 - 1 : ℝ) / 3) ^ (n - 1))) < 2 := by
  have h : 0 < (2 / 3 : ℝ) ^ (n - 1) := pow_pos (by norm_num) _
  norm_num

end Banach

abbrev groupSignature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def groupActual : Realization groupSignature :=
  realize groupSignature (fun _ _ ε => 2 * ε) (fun e => nomatch e)

def groupRejected : Realization groupSignature :=
  realize groupSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem groupDependence : ObservationalDependence groupSignature groupActual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [groupActual, realize]

namespace Interval

abbrev arena : Arena where
  signature := groupSignature
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {H : Type v} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] [Finite V]
    (ℓ r : V → ℝ) (_hI : ∀ v, ℓ v ≤ r v)
    (_hG : ∀ x y, G.Adj x y ↔ x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y))
    (g : V → V → H) (ε : ℝ) (_hε : 0 ≤ ε)
    (_hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (_htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε),
    G.IsChordal ∧ ∃ φ : V → H, ∀ x y, G.Adj x y →
      Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ R.readout () () ε

private theorem rejected_law : ¬ arena.{u, v}.Law groupRejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2)
  let H := Multiplicative (ULift.{v} ℝ)
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  have hab : (⊤ : SimpleGraph V).Adj a b := by
    change a ≠ b
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  obtain ⟨_, φ, hφ⟩ := h (G := (⊤ : SimpleGraph V)) (H := H)
    (fun _ => 0) (fun _ => 0) (by simp) (by simp) (fun _ _ => 1) 0 le_rfl
    (by simp) (by simp)
  have he := hφ a b hab
  change Dist.dist (1 : H) ((φ a)⁻¹ * φ b) ≤ -1 at he
  linarith [_root_.dist_nonneg (x := (1 : H)) (y := (φ a)⁻¹ * φ b)]

def family : Registration arena.{u, v}
    (type_of% (@intervalGraph_isChordal_and_two_approximate_gain_potential.{u, v})) where
  actual := groupActual
  bridge := Iff.rfl
  variation := ⟨@intervalGraph_isChordal_and_two_approximate_gain_potential.{u, v},
    groupRejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law groupActual groupRejected rejected_law
  dependence := groupDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@intervalGraph_isChordal_and_two_approximate_gain_potential.{u, v})
    (Realization groupSignature) Unit Unit where
  unitName := `SimpleGraph.intervalGraph_isChordal_and_two_approximate_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential.Interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize groupSignature groupActual.readout groupActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interval

namespace Split

abbrev arena : Arena where
  signature := groupSignature
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {H : Type v} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] [Finite V]
    (C : Set V) (_hC : G.IsClique C) (_hD : G.IsIndepSet Cᶜ)
    (g : V → V → H) (ε : ℝ) (_hε : 0 ≤ ε)
    (_hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (_htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε),
    G.IsChordal ∧ ∃ φ : V → H, ∀ x y, G.Adj x y →
      Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ R.readout () () ε

private theorem rejected_law : ¬ arena.{u, v}.Law groupRejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2)
  let H := Multiplicative (ULift.{v} ℝ)
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  have hab : (⊤ : SimpleGraph V).Adj a b := by
    change a ≠ b
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  obtain ⟨_, φ, hφ⟩ := h (G := (⊤ : SimpleGraph V)) (H := H)
    Set.univ (by simp) (by simp) (fun _ _ => 1) 0 le_rfl (by simp) (by simp)
  have he := hφ a b hab
  change Dist.dist (1 : H) ((φ a)⁻¹ * φ b) ≤ -1 at he
  linarith [_root_.dist_nonneg (x := (1 : H)) (y := (φ a)⁻¹ * φ b)]

def family : Registration arena.{u, v}
    (type_of% (@exists_two_approximate_gain_potential_of_split.{u, v})) where
  actual := groupActual
  bridge := Iff.rfl
  variation := ⟨@exists_two_approximate_gain_potential_of_split.{u, v}, groupRejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law groupActual groupRejected rejected_law
  dependence := groupDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_two_approximate_gain_potential_of_split.{u, v})
    (Realization groupSignature) Unit Unit where
  unitName := `SimpleGraph.exists_two_approximate_gain_potential_of_split.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential.Split.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize groupSignature groupActual.readout groupActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Split

namespace PathPower

abbrev signature := SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun p => Fin p.1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p i => (i.val : ℝ) + p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, ∃ ℓ r : Fin n → ℝ,
    (∀ i, ℓ i = (i.val : ℝ) ∧ r i = R.readout () ⟨n, k⟩ i) ∧
    (∀ i, ℓ i ≤ r i) ∧ ∀ x y, (pathPower n k).Adj x y ↔
      x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ℓ, r, hr, hI, _⟩ := h 1 1
  obtain ⟨h₁, h₂⟩ := hr 0
  norm_num at h₁
  change r 0 = -1 at h₂
  have he := hI 0
  rw [h₁, h₂] at he
  norm_num at he

def family : Registration arena (type_of% (@pathPower_isIntervalGraph)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pathPower_isIntervalGraph, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨2, 1⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPower_isIntervalGraph) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.BanachPathPower.pathPower_isIntervalGraph.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential.PathPower.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PathPower
end
end Reg.D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
