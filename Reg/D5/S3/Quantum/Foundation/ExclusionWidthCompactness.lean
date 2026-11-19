import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Whole-effect width readouts with exact original telescopes.
The source bridges do not supply whole-family intervention, sensitivity,
observational dependence or occurrence-bound source selection. -/

noncomputable section
open Set Filter Topology
universe v

namespace Reg.D5.S3.Quantum.Foundation.ExclusionWidthCompactness

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.ContinuousFrameSum
open _root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

structure NonzeroInputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nonzero : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] NonzeroInputs.add NonzeroInputs.space NonzeroInputs.finite NonzeroInputs.nonzero

namespace width_upperSemicontinuous

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u),
    UpperSemicontinuous (fun p : pure C u => O.readout () P (exclusion C u p))

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.width_upperSemicontinuous.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.width_upperSemicontinuous.{v})

end width_upperSemicontinuous

namespace positive_width_layer_compact

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    {a : ℝ} (ha : 0 < a),
    IsCompact {x | x ∈ pure C u ∧ a ≤ O.readout () P (exclusion C u x)}

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.positive_width_layer_compact.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.positive_width_layer_compact.{v})

end positive_width_layer_compact

namespace original_exclusion_width

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u),
    let F := {x | x ∈ base C u ∧ comparison C u p x = 0}
    (0 < O.readout () P F ∧ O.readout () P F ≤ 1) ∧
    ∃ f ∈ effects C u, ∃ y ∈ F, ∃ z ∈ F, O.readout () P F = f y - f z

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.original_exclusion_width.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.original_exclusion_width.{v})

end original_exclusion_width

namespace saturated_labels_compact

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u),
    IsCompact {x | x ∈ pure C u ∧ O.readout () P (exclusion C u x) = 1}

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.saturated_labels_compact.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.saturated_labels_compact.{v})

end saturated_labels_compact

namespace width_tendsto_zero_of_mixed_limit

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : ℕ → pure C u) {x : V}
    (hpx : Tendsto (fun n => (p n : V)) atTop (𝓝 x)) (hx : x ∉ pure C u),
    Tendsto (fun n => O.readout () P (exclusion C u (p n))) atTop (𝓝 0)

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.width_tendsto_zero_of_mixed_limit.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.width_tendsto_zero_of_mixed_limit.{v})

end width_tendsto_zero_of_mixed_limit

namespace diameter_tendsto_zero_of_mixed_limit

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P x => exclusion P.cone P.unit x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : ℕ → pure C u) {x : V}
    (hpx : Tendsto (fun n => (p n : V)) atTop (𝓝 x)) (hx : x ∉ pure C u),
    Tendsto (fun n => Metric.diam (O.readout () P (p n))) atTop (𝓝 0)

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.diameter_tendsto_zero_of_mixed_limit.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.diameter_tendsto_zero_of_mixed_limit.{v})

end diameter_tendsto_zero_of_mixed_limit

namespace pure_eq_countable_width_layers

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u),
    pure C u = ⋃ n : ℕ, {x | x ∈ pure C u ∧
      1 / (n + 1 : ℝ) ≤ O.readout () P (exclusion C u x)}

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.pure_eq_countable_width_layers.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.pure_eq_countable_width_layers.{v})

end pure_eq_countable_width_layers

namespace width_global_maximum

abbrev signature : Signature where
  Params := NonzeroInputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : NonzeroInputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p)),
    ∃ p : pure C u, 0 < O.readout () P (exclusion C u p) ∧
      O.readout () P (exclusion C u p) ≤ 1 ∧
      (∀ q : pure C u, O.readout () P (exclusion C u q) ≤ O.readout () P (exclusion C u p)) ∧
      sSup ((fun q : pure C u => O.readout () P (exclusion C u q)) '' univ) =
        O.readout () P (exclusion C u p)

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.width_global_maximum.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.nonzero
  · intro h V add space finite C u nonzero
    exact h (@NonzeroInputs.mk V add space finite nonzero C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.width_global_maximum.{v})

end width_global_maximum

namespace near_saturation_subsequence

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : ℕ → pure C u)
    (hw : Tendsto (fun n => O.readout () P (exclusion C u (p n))) atTop (𝓝 1)),
    ∃ q : pure C u, O.readout () P (exclusion C u q) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => (p (φ n) : V)) atTop (𝓝 (q : V))

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.near_saturation_subsequence.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.near_saturation_subsequence.{v})

end near_saturation_subsequence

namespace no_saturation_uniform_gap

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P F => width P.cone P.unit F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hno : ∀ p : pure C u, O.readout () P (exclusion C u p) ≠ 1),
    sSup ((fun p : pure C u => O.readout () P (exclusion C u p)) '' univ) < 1

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.no_saturation_uniform_gap.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness.no_saturation_uniform_gap.{v})

end no_saturation_uniform_gap

end Reg.D5.S3.Quantum.Foundation.ExclusionWidthCompactness
