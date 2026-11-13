import D5.S3.Quantum.Foundation.FixedZeroObstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound original whole-exclusion observations. A four-slot registration
also requires source selection, whole-family variation and sensitivity. -/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.FixedZeroObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => exclusion P.cone P.unit x) (fun e => nomatch e)

abbrev maximumArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ (t : pure C u) (g : P.V →ₗ[ℝ] ℝ), g ∈ zeroEffects C u t →
    ∃ v : pure C u, (v : P.V) ∈ O.readout () P t ∧
      ∀ x ∈ base C u, g x ≤ g v

abbrev maximumScope : Prop := type_of% (@zero_effect_maximizer.{u})

theorem maximum_source_bridge : maximumScope.{u} ↔ maximumArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem maximum_actual_positive : maximumArena.{u}.Law actual.{u} :=
  maximum_source_bridge.mp (@zero_effect_maximizer.{u})

abbrev facesArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    ∀ (s : pure C u) (h : P.V →ₗ[ℝ] ℝ), h ∈ fullZeroConfirmers C u s →
    ({x | x ∈ base C u ∧ h x = 0} = O.readout () P s) ∧
    ({x | x ∈ base C u ∧ h x = 1} = {(s : P.V)})

abbrev facesScope : Prop := type_of% (@full_zero_faces.{u})

theorem faces_source_bridge : facesScope.{u} ↔ facesArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem faces_actual_positive : facesArena.{u}.Law actual.{u} :=
  faces_source_bridge.mp (@full_zero_faces.{u})

abbrev distanceArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ (s t : pure C u) (h : P.V →ₗ[ℝ] ℝ), h ∈ fullZeroConfirmers C u s →
      (1 - sSup (h '' O.readout () P t)) / 2 ≤ zeroDistance hc hs t h

abbrev distanceScope : Prop := type_of% (@fixed_zero_distance_bound.{u})

theorem distance_source_bridge : distanceScope.{u} ↔ distanceArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem distance_actual_positive : distanceArena.{u}.Law actual.{u} :=
  distance_source_bridge.mp (@fixed_zero_distance_bound.{u})

abbrev edgesArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    stableZeroWitness hc hs →
    ∀ (p s : pure C u), (s : P.V) ∈ exclusion C u p →
    ∀ t : ℕ → pure C u,
      Filter.Tendsto (fun n => (t n : P.V)) Filter.atTop (nhds (p : P.V)) →
    ∃ v : ℕ → pure C u, (∀ n, (v n : P.V) ∈ O.readout () P (t n)) ∧
      Filter.Tendsto (fun n => (v n : P.V)) Filter.atTop (nhds (s : P.V))

abbrev edgesScope : Prop := type_of% (@stable_zero_implies_open_edges.{u})

theorem edges_source_bridge : edgesScope.{u} ↔ edgesArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem edges_actual_positive : edgesArena.{u}.Law actual.{u} :=
  edges_source_bridge.mp (@stable_zero_implies_open_edges.{u})

abbrev labelsArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ (pn : ℕ → pure C u) (x : P.V),
    Filter.Tendsto (fun n => (pn n : P.V)) Filter.atTop (nhds x) →
    ∀ G : TopologicalSpace.NonemptyCompacts P.V,
    Filter.Tendsto (fun n => Metric.hausdorffDist (O.readout () P (pn n)) G)
      Filter.atTop (nhds 0) →
    (Function.Injective (fun p : pure C u => O.readout () P p) →
      ((G : Set P.V).Nontrivial → x ∈ pure C u) ∧
      (∀ q : P.V, (G : Set P.V) = {q} → x ∉ pure C u →
        q ∈ pure C u ∧ x ∈ intrinsicInterior ℝ (O.readout () P q))) ∧
    (x ∈ pure C u → (G : Set P.V) ⊆ O.readout () P x)

abbrev labelsScope : Prop := type_of% (@exclusion_limit_labels.{u})

theorem labels_source_bridge : labelsScope.{u} ↔ labelsArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem labels_actual_positive : labelsArena.{u}.Law actual.{u} :=
  labels_source_bridge.mp (@exclusion_limit_labels.{u})

abbrev obstructionArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set P.V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x),
    Submodule.span ℝ (C : Set P.V) = ⊤ →
    (∀ p : pure C u, ∃ b : ExclusionChart C u p, b.dim = 3) →
    Function.Injective (fun p : pure C u => O.readout () P p) →
    ∀ (pn : ℕ → pure C u) (x q : P.V),
    Filter.Tendsto (fun n => (pn n : P.V)) Filter.atTop (nhds x) →
    Filter.Tendsto (fun n => Metric.hausdorffDist (O.readout () P (pn n)) {q})
      Filter.atTop (nhds 0) →
    ∃ s r : pure C u, (r : P.V) ∈ O.readout () P s ∧
      ∃ tn : ℕ → pure C u,
        Filter.Tendsto (fun n => (tn n : P.V)) Filter.atTop (nhds (r : P.V)) ∧
        ∀ h ∈ fullZeroConfirmers C u s,
          Filter.Tendsto (fun n => h (tn n)) Filter.atTop (nhds 0) ∧
          0 < Filter.liminf (fun n => zeroDistance hc hs (tn n) h) Filter.atTop

abbrev obstructionScope : Prop := type_of% (@fixed_zero_distance_obstruction.{u})

theorem obstruction_source_bridge : obstructionScope.{u} ↔ obstructionArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem obstruction_actual_positive : obstructionArena.{u}.Law actual.{u} :=
  obstruction_source_bridge.mp (@fixed_zero_distance_obstruction.{u})

namespace CompactMembership

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]

attribute [instance] Inputs.add

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := TopologicalSpace.NonemptyCompacts P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ F => (F : Set _)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u}, ∀ (F : ℕ → TopologicalSpace.NonemptyCompacts P.V)
    (G : TopologicalSpace.NonemptyCompacts P.V),
    Filter.Tendsto F Filter.atTop (nhds G) → ∀ {yn : ℕ → P.V} {y : P.V},
    (∀ n, yn n ∈ O.readout () P (F n)) →
    Filter.Tendsto yn Filter.atTop (nhds y) → y ∈ O.readout () P G

abbrev sourceScope : Prop := type_of% (@mem_compact_limit.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P F G hF yn y hyn hy
    exact @h P.V P.add F G hF yn y hyn hy
  · intro h V add F G hF yn y hyn hy
    exact h (@Inputs.mk V add) F G hF hyn hy

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@mem_compact_limit.{u})

end CompactMembership

end Reg.D5.S3.Quantum.Foundation.FixedZeroObstruction
