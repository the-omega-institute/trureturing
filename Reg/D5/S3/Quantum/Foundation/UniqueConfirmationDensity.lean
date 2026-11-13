import D5.S3.Quantum.Foundation.UniqueConfirmationDensity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source reconstruction for original label and contact sequences.
Whole-family sensitivity requires an inhabited full original model. -/

noncomputable section
universe v
open Set Filter
open scoped Topology

namespace Reg.D5.S3.Quantum.Foundation.UniqueConfirmationDensity

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.UniqueConfirmationDensity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output P _ := P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev labelArena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ z ∈ C, z ≠ 0 → 0 < u z) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    ∀ (p : pure C u) {x : P.V}, x ∈ intrinsicInterior ℝ (exclusion C u p) →
    ∀ (pn : ℕ → pure C u) (xn : ℕ → P.V),
    (∀ n, xn n ∈ exclusion C u (pn n)) → Tendsto xn atTop (𝓝 x) →
    Tendsto (fun n => O.readout () P (pn n)) atTop (𝓝 (p : P.V))

abbrev labelSourceScope : Prop := type_of% (@original_label_tendsto.{v})

theorem label_source_bridge : labelSourceScope.{v} ↔ labelArena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem label_actual_positive : labelArena.{v}.Law actual.{v} :=
  label_source_bridge.mp (@original_label_tendsto.{v})

abbrev densityArena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ z ∈ C, z ≠ 0 → 0 < u z) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    (∀ (p : pure C u) (x : P.V), x ∈ intrinsicInterior ℝ (exclusion C u p) →
      ∃ (pn : ℕ → pure C u) (xn : ℕ → P.V),
        (∀ n, UniqueConfirmer C u (pn n) ∧
          xn n ∈ intrinsicInterior ℝ (exclusion C u (pn n))) ∧
        Tendsto (fun n => O.readout () P (xn n)) atTop (𝓝 x) ∧
        Tendsto (fun n => O.readout () P (pn n)) atTop (𝓝 (p : P.V))) ∧
    closure {p : pure C u | UniqueConfirmer C u p} = Set.univ

abbrev densitySourceScope : Prop := type_of% (@original_unique_confirmer_density.{v})

theorem density_source_bridge : densitySourceScope.{v} ↔ densityArena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem density_actual_positive : densityArena.{v}.Law actual.{v} :=
  density_source_bridge.mp (@original_unique_confirmer_density.{v})

/-- Erasure fails at each actual full original model with an original pure label.
This conditional proof does not assert that such a model has been constructed. -/
theorem density_erased_negative_of_input (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ z ∈ P.cone, z ≠ 0 → 0 < P.unit z)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit)
    (hinj : Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p))
    (p : pure P.cone P.unit) : ¬ densityArena.{v}.Law erased.{v} := by
  intro h
  have hall := (exclusion_ball_faces hc hs hg hB).1 p
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hall.2.2.1 hall.1.nonempty
  obtain ⟨pn, xn, _, _, hlim⟩ := (h P hc hs hg hB hinj).1 p x hx
  have hp0 : (0 : P.V) = p := tendsto_nhds_unique tendsto_const_nhds hlim
  have hu := congrArg P.unit hp0
  exact zero_ne_one (by simpa only [map_zero, (pure_mem p).2] using hu)

theorem label_erased_negative_of_input (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ z ∈ P.cone, z ≠ 0 → 0 < P.unit z)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit)
    (hinj : Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p))
    (p : pure P.cone P.unit) : ¬ labelArena.{v}.Law erased.{v} := by
  intro h
  have hall := (exclusion_ball_faces hc hs hg hB).1 p
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hall.2.2.1 hall.1.nonempty
  have hlim := h P hc hs hg hB hinj p hx (fun _ => p) (fun _ => x)
    (fun _ => intrinsicInterior_subset hx) tendsto_const_nhds
  have hp0 : (0 : P.V) = p := tendsto_nhds_unique tendsto_const_nhds hlim
  have hu := congrArg P.unit hp0
  exact zero_ne_one (by simpa only [map_zero, (pure_mem p).2] using hu)

end Reg.D5.S3.Quantum.Foundation.UniqueConfirmationDensity
