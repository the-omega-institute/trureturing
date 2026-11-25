import D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The three reconstruction radii as functions of the triangle tolerance. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph

noncomputable section

universe u v

private abbrev TwoVertices := ULift.{u} (Fin 2)

private def leftVertex : TwoVertices.{u} := ⟨0⟩
private def rightVertex : TwoVertices.{u} := ⟨1⟩

private theorem adjacentVertices :
    (⊤ : SimpleGraph TwoVertices.{u}).Adj leftVertex rightVertex := by
  change leftVertex ≠ rightVertex
  intro he
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)

private theorem impossibleNorm {E : Type v} [SeminormedAddCommGroup E] (x : E)
    (h : ‖x‖ ≤ -1) : False := by
  linarith [norm_nonneg x]

namespace MultiTier

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ k ε => (4 - 4 * ((k : ℝ) - 2) / ((k : ℝ)^2 - 3 * (k : ℝ) + 3)) * ε)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (k : ℕ) (_hk : 4 ≤ k)
    (_hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : V → E, ∀ i j, G.Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () k ε

private theorem twoVertexChordal : (⊤ : SimpleGraph TwoVertices.{u}).IsChordal := by
  intro x c hc hlen
  have hsize := hc.support_nodup.length_le_card
  have hcard : Fintype.card TwoVertices.{u} = 2 := by simp
  rw [List.length_tail, c.length_support, hcard] at hsize
  omega

private theorem twoVertexClique (s : Finset TwoVertices.{u}) : s.card ≤ 4 + 1 := by
  have hcard : Fintype.card TwoVertices.{u} = 2 := by simp
  exact (Finset.card_le_univ s).trans (by rw [hcard]; decide)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨φ, hφ⟩ := h twoVertexChordal 4 (by decide) (fun s _ => twoVertexClique s)
    (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hv := hφ leftVertex rightVertex adjacentVertices
  change ‖(0 : ULift.{v} ℝ) - (φ rightVertex - φ leftVertex)‖ ≤ -1 at hv
  exact impossibleNorm _ hv

example : ∃ φ : TwoVertices → ℝ, ‖(0 : ℝ) - (φ rightVertex - φ leftVertex)‖ ≤ 0 := by
  obtain ⟨φ, hφ⟩ := IsChordal.exists_multitier_clique_banach_gain_potential twoVertexChordal 4 (by decide)
    (fun s _ => twoVertexClique s) (fun _ _ => (0 : ℝ)) 0 le_rfl (by simp) (by simp)
  exact ⟨φ, by simpa using hφ leftVertex rightVertex adjacentVertices⟩

def family : Registration arena.{u, v} (type_of% (@IsChordal.exists_multitier_clique_banach_gain_potential.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_multitier_clique_banach_gain_potential.{u, v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨4, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_multitier_clique_banach_gain_potential.{u, v}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_multitier_clique_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach.MultiTier.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body",
        "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MultiTier

namespace UniversalCore

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m ε => (max 1 (2 - 2 / (m : ℝ))) * ε)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (H U : Set V)
    (_hUH : U ⊆ H) (_hU : U.Nonempty)
    (_huniv : ∀ u ∈ U, ∀ h ∈ H, u ≠ h → G.Adj u h)
    (_hind : G.IsIndepSet Hᶜ) (m : ℕ) (_hm : 1 ≤ m)
    (_hattach : ∀ o ∉ H, {a : V | G.Adj o a} ⊆ H ∧ G.IsClique {a : V | G.Adj o a} ∧
      {a : V | G.Adj o a}.ncard ≤ m)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : V → E, ∀ i j, G.Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () m ε

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨φ, hφ⟩ := h (⊤ : SimpleGraph TwoVertices.{u}) Set.univ Set.univ
    Set.Subset.rfl ⟨leftVertex, Set.mem_univ _⟩ (fun _ _ _ _ hne => hne) (by simp [Set.Pairwise])
    2 (by decide) (by simp) (E := ULift.{v} ℝ)
    (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hv := hφ leftVertex rightVertex adjacentVertices
  change ‖(0 : ULift.{v} ℝ) - (φ rightVertex - φ leftVertex)‖ ≤ -1 at hv
  exact impossibleNorm _ hv

example : ∃ φ : TwoVertices → ℝ, ‖(0 : ℝ) - (φ rightVertex - φ leftVertex)‖ ≤ 0 := by
  obtain ⟨φ, hφ⟩ := exists_universal_core_simplicial_banach_potential
    (⊤ : SimpleGraph TwoVertices) Set.univ Set.univ Set.Subset.rfl
    ⟨leftVertex, Set.mem_univ _⟩ (fun _ _ _ _ hne => hne) (by simp [Set.Pairwise]) 2 (by decide) (by simp)
    (fun _ _ => (0 : ℝ)) 0 le_rfl (by simp) (by simp)
  exact ⟨φ, by simpa using hφ leftVertex rightVertex adjacentVertices⟩

def family : Registration arena.{u, v} (type_of% (@exists_universal_core_simplicial_banach_potential.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_universal_core_simplicial_banach_potential.{u, v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, max_def]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_universal_core_simplicial_banach_potential.{u, v}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.exists_universal_core_simplicial_banach_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach.UniversalCore.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UniversalCore

namespace BridgedGadget

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m ε => (2 - 2 / (m : ℝ)) * ε)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m N : ℕ) (_hm : 2 ≤ m) (_hN : 1 ≤ N)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin N × GadgetVertex m) → (Fin N × GadgetVertex m) → E)
    (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, (bridgedGadget m N).Adj i j → (bridgedGadget m N).Adj j l →
      (bridgedGadget m N).Adj i l → ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : (Fin N × GadgetVertex m) → E, ∀ i j, (bridgedGadget m N).Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () m ε

private def rootVertex : Fin 2 × GadgetVertex 2 := (0, .root)
private def attachmentVertex : Fin 2 × GadgetVertex 2 := (0, .a 0)

private theorem rootAdjacent :
    (bridgedGadget 2 2).Adj rootVertex attachmentVertex :=
  Or.inl ⟨rfl, trivial⟩

private theorem rejected_law : ¬ arena.{v}.Law rejected := by
  intro h
  obtain ⟨φ, hφ⟩ := h 2 2 (by decide) (by decide) (E := ULift.{v} ℝ)
    (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hv := hφ rootVertex attachmentVertex rootAdjacent
  change ‖(0 : ULift.{v} ℝ) - (φ attachmentVertex - φ rootVertex)‖ ≤ -1 at hv
  exact impossibleNorm _ hv

example : ∃ φ : Fin 2 × GadgetVertex 2 → ℝ,
    ‖(0 : ℝ) - (φ attachmentVertex - φ rootVertex)‖ ≤ 0 := by
  obtain ⟨φ, hφ⟩ := bridgedGadget_banach_upper_bound 2 2 (by decide) (by decide)
    (fun _ _ => (0 : ℝ)) 0 le_rfl (by simp) (by simp)
  exact ⟨φ, by simpa using hφ rootVertex attachmentVertex rootAdjacent⟩

def family : Registration arena.{v} (type_of% (@bridgedGadget_banach_upper_bound.{v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bridgedGadget_banach_upper_bound.{v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bridgedGadget_banach_upper_bound.{v}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.bridgedGadget_banach_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach.BridgedGadget.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BridgedGadget

example (k : ℕ) (hk : 4 ≤ k) :
    4 - 4 * ((k : ℝ) - 2) / ((k : ℝ)^2 - 3 * (k : ℝ) + 3) <
      4 - 4 / (k : ℝ) - 2 * ((k : ℝ) - 2)^2 / ((k : ℝ) * ((k : ℝ) - 1)^3) := by
  let K : ℝ := k
  let D := K^2 - 3 * K + 3
  let t := K - 4
  have hK : 4 ≤ K := by exact_mod_cast hk
  have hKpos : 0 < K := by linarith
  have h₁ : 0 < K - 1 := by linarith
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg (K - 4)]
  have ht : 0 ≤ t := sub_nonneg.mpr hK
  have hnum : 0 < 2 * (K - 3) * (K - 1)^3 - (K - 2)^2 * D := by
    calc
      0 < 26 + 60 * t + 41 * t^2 + 11 * t^3 + t^4 := by positivity
      _ = _ := by dsimp [t, D]; ring
  have hquot := div_pos hnum (mul_pos (mul_pos hKpos hD) (pow_pos h₁ 3))
  have hdiff : 4 * (K - 2) / D - (4 / K + 2 * (K - 2)^2 / (K * (K - 1)^3)) =
      2 * ((2 * (K - 3) * (K - 1)^3 - (K - 2)^2 * D) / (K * D * (K - 1)^3)) := by
    field_simp [hD.ne', hKpos.ne', h₁.ne'] <;> dsimp [D] <;> ring
  change 4 - 4 * (K - 2) / D < 4 - 4 / K - 2 * (K - 2)^2 / (K * (K - 1)^3)
  linarith

example :
    4 - 4 * ((4 : ℝ) - 2) / ((4 : ℝ)^2 - 3 * (4 : ℝ) + 3) = 20 / 7 ∧
    4 - 4 / (4 : ℝ) - 2 * ((4 : ℝ) - 2)^2 / (4 * ((4 : ℝ) - 1)^3) = 79 / 27 ∧
    (20 / 7 : ℝ) < 79 / 27 ∧ (79 / 27 : ℝ) < 3 := by
  norm_num

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.MultiTierAndUniversalCliqueBanach
