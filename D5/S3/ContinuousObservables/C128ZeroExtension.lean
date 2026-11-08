/- GID: D5/S3/ContinuousObservables/C128ZeroExtension
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/C128ZeroExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization, mathlib/module/Mathlib.Topology.ContinuousMap.Ideals]
   utility: none
   digest: Whole matrix fields vanishing at infinity identify isometrically with the closed star ideal of continuous fields on the unit interval vanishing off the punctured quarter interval. -/

import D5.S3.ContinuousObservables.C0Multipliers
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import Mathlib.Topology.ContinuousMap.Ideals
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # Zero extension on the punctured quarter interval

The full complex ideal and its inverse restriction use all fields vanishing at infinity.
-/

noncomputable section

open Set Filter
open scoped Topology ZeroAtInfty OnePoint ComplexOrder

namespace D5.S3.ContinuousObservables.C128ZeroExtension

open C0Multipliers

/-- The original compact base, with both endpoints. -/
abbrev Y := ↥(Icc (0 : ℝ) 1)

/-- The original inclusion of the entire punctured interval in the compact base. -/
def inclusion (t : sourceDomain) : Y :=
  ⟨t, t.property.1.1.le, t.property.1.2.le.trans (by norm_num)⟩

private def collapse (t : ℝ) : OnePoint sourceDomain := by
  classical
  exact if h : t ∈ sourceDomain then (⟨t, h⟩ : sourceDomain) else ∞

private theorem collapse_continuous : Continuous collapse := by
  classical
  apply continuous_def.mpr
  intro s hs
  by_cases hi : (∞ : OnePoint sourceDomain) ∈ s
  · have heq : collapse ⁻¹' s =
        (Subtype.val '' (((↑) : sourceDomain → OnePoint sourceDomain) ⁻¹' s)ᶜ)ᶜ := by
      ext t
      by_cases ht : t ∈ sourceDomain <;> simp [collapse, ht, hi]
    rw [heq]
    exact ((hs.1 hi).image continuous_subtype_val).isClosed.isOpen_compl
  · have heq : collapse ⁻¹' s =
        Subtype.val '' (((↑) : sourceDomain → OnePoint sourceDomain) ⁻¹' s) := by
      ext t
      by_cases ht : t ∈ sourceDomain <;> simp [collapse, ht, hi]
    rw [heq]
    exact sourceDomain_open.isOpenEmbedding_subtypeVal.isOpenMap _ hs.2

/-- Extension by zero on the whole compact base. -/
def zeroExtension (f : SourceAlgebra) : C(Y, MatrixFiber) :=
  f.toOnePoint.comp ⟨fun y => collapse y, collapse_continuous.comp continuous_subtype_val⟩

private theorem extension_on (f : SourceAlgebra) (t : sourceDomain) :
    zeroExtension f (inclusion t) = f t := by
  classical
  simp [zeroExtension, collapse, inclusion, t.property]

private theorem extension_off (f : SourceAlgebra) (y : Y)
    (hy : (y : ℝ) ∉ sourceDomain) : zeroExtension f y = 0 := by
  classical
  simp [zeroExtension, collapse, hy]

/-- The entire zero-off-domain ideal, defined independently of extension. -/
def wholeIdeal : Ideal C(Y, MatrixFiber) :=
  ContinuousMap.idealOfSet MatrixFiber {y | (y : ℝ) ∈ sourceDomain}

private theorem ideal_spec (g : C(Y, MatrixFiber)) :
    g ∈ wholeIdeal ↔ ∀ y : Y, (y : ℝ) ∉ sourceDomain → g y = 0 := Iff.rfl

private theorem inclusion_embedding : Topology.IsEmbedding inclusion := by
  exact Topology.IsEmbedding.of_comp (by unfold inclusion; fun_prop) continuous_subtype_val
    (show Topology.IsEmbedding ((Subtype.val : Y → ℝ) ∘ inclusion) from
      Topology.IsEmbedding.subtypeVal)

private theorem restriction_vanishes (g : C(Y, MatrixFiber)) (hg : g ∈ wholeIdeal) :
    Tendsto (fun t : sourceDomain => g (inclusion t)) (cocompact sourceDomain) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K : Set Y := {y | ε ≤ ‖g y‖}
  have hK : IsCompact K := (isClosed_le continuous_const g.continuous.norm).isCompact
  have hKU : K ⊆ range inclusion := by
    intro y hy
    have hu : (y : ℝ) ∈ sourceDomain := by
      by_contra hn
      have hz := (ideal_spec g).mp hg y hn
      have : ε ≤ 0 := by simpa [K, hz] using hy
      exact (not_le_of_gt hε) this
    exact ⟨⟨y, hu⟩, Subtype.ext rfl⟩
  have hpre : IsCompact (inclusion ⁻¹' K) :=
    inclusion_embedding.isInducing.isCompact_preimage' hK hKU
  apply mem_cocompact.mpr
  refine ⟨inclusion ⁻¹' K, hpre, ?_⟩
  intro t ht
  change dist (g (inclusion t)) 0 < ε
  rw [dist_zero_right]
  exact lt_of_not_ge ht

/-- Restriction of every zero-off-domain field belongs to the whole C0 algebra. -/
def restriction (g : wholeIdeal) : SourceAlgebra where
  toFun t := g.val (inclusion t)
  continuous_toFun := g.val.continuous.comp inclusion_embedding.continuous
  zero_at_infty' := restriction_vanishes g.val g.property

private theorem extension_restriction (g : wholeIdeal) : zeroExtension (restriction g) = g.val := by
  classical
  apply ContinuousMap.ext
  intro y
  by_cases hy : (y : ℝ) ∈ sourceDomain
  · exact extension_on (restriction g) ⟨y, hy⟩
  · rw [extension_off _ _ hy, (ideal_spec g.val).mp g.property y hy]

private theorem restriction_extension (f : SourceAlgebra) (t : sourceDomain) :
    zeroExtension f (inclusion t) = f t := extension_on f t

private theorem extension_norm (f : SourceAlgebra) : ‖zeroExtension f‖ = ‖f‖ := by
  classical
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    by_cases hy : (y : ℝ) ∈ sourceDomain
    · have he := extension_on f ⟨y, hy⟩
      exact he ▸ f.toBCF.norm_coe_le_norm ⟨y, hy⟩
    · simp [extension_off _ _ hy]
  · change ‖f.toBCF‖ ≤ ‖zeroExtension f‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro t
    change ‖f t‖ ≤ ‖zeroExtension f‖
    rw [← extension_on f t]
    exact (zeroExtension f).norm_coe_le_norm _

private theorem extension_mem (f : SourceAlgebra) : zeroExtension f ∈ wholeIdeal :=
  (ideal_spec _).mpr (extension_off f)

/-- The complex-linear zero extension preserves all products and star. -/
def extensionHom : SourceAlgebra →⋆ₙₐ[ℂ] C(Y, MatrixFiber) where
  toFun := zeroExtension
  map_zero' := by
    classical
    ext y
    simp [zeroExtension]
  map_add' f g := by
    ext y
    simp [zeroExtension]
  map_mul' f g := by
    ext y
    simp [zeroExtension]
  map_smul' c f := by
    ext y
    simp [zeroExtension]
  map_star' f := by
    ext y
    simp [zeroExtension]

/-- Zero extension identifies the entire closed two-sided star ideal, with inverse
restriction, exact operator norm, and no restriction on support. -/
theorem whole_zero_extension :
    Isometry extensionHom ∧
    range extensionHom = (wholeIdeal : Set C(Y, MatrixFiber)) ∧
    IsClosed (wholeIdeal : Set C(Y, MatrixFiber)) ∧
    (∀ (g : wholeIdeal), zeroExtension (restriction g) = g.val) ∧
    (∀ (f : SourceAlgebra) (t : sourceDomain), zeroExtension f (inclusion t) = f t) ∧
    (∀ (g : C(Y, MatrixFiber)), g ∈ wholeIdeal →
      ∀ h : C(Y, MatrixFiber), g * h ∈ wholeIdeal ∧ star g ∈ wholeIdeal) := by
  refine ⟨AddMonoidHomClass.isometry_of_norm extensionHom extension_norm, ?_,
    ContinuousMap.idealOfSet_closed _ _, extension_restriction, restriction_extension, ?_⟩
  · ext g
    constructor
    · rintro ⟨f, rfl⟩
      exact extension_mem f
    · intro hg
      exact ⟨restriction ⟨g, hg⟩, extension_restriction ⟨g, hg⟩⟩
  · intro g hg h
    constructor
    · exact (ideal_spec _).mpr fun y hy => by simp [((ideal_spec _).mp hg y hy)]
    · exact (ideal_spec _).mpr fun y hy => by simp [((ideal_spec _).mp hg y hy)]

end D5.S3.ContinuousObservables.C128ZeroExtension
