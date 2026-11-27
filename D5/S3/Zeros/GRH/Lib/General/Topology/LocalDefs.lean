/- GID: D5/S3/Zeros/GRH/Lib/General/Topology/LocalDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Topology/LocalDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Topology.LocalDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Topology/LocalDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.GaussSum.LocalHomUnit
import D5.S3.Zeros.GRH.Lib.Adelic.Witt.FrameAction
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of topology (textbook or folklore).

Part of: Gauss sums of a character of the determinant over matrix rings (known result; see
Lib.Weil.GaussSum.ShearInvariance).

Set-up used by: Gauss sums of a character of the determinant over matrix rings.

This file: Schwartz-Bruhat functions, products of local fields, tame and additive characters. -/

variable {X} [TopologicalSpace X] {s : Set X} {φ Γ Y Z} {F : Type} [TopologicalSpace Γ]
  [TopologicalSpace Y]

/-- The space of locally constant, compactly supported complex functions on X that vanish
outside s. -/
def schwartzBruhat s := Submodule.ofLinearComb {f : X → ℂ | IsLocallyConstant f ∧
  HasCompactSupport f ∧ f.support ⊆ s} ⟨0, .zero, .zero, nofun⟩ fun _ ⟨f, p, _⟩ _ ⟨g, q, _⟩ a b ↦
  ⟨f.comp₂ g (a * · + b * ·), p.mul_left.add q.mul_left, by simp_all; grind⟩

lemma schwartzBruhat.comp [T2Space X] {t : Set Y} (h : φ ∈ schwartzBruhat s) {f} g (hs :
  s.MapsTo g t) (hf : Continuous f := by fun_prop) (hg : Continuous g := by fun_prop)
  (hi : g.LeftInverse f := by intro; aesop) : φ ∘ f ∈ schwartzBruhat t := ⟨h.1.comp_continuous hf,
  h.2.1.comp_isClosedEmbedding (hi.isClosedEmbedding hg hf), (hi · ▸ h.2.2.trans hs ·)⟩

lemma schwartzBruhat.isLocallyConstant_curry (h : φ ∈ schwartzBruhat s) (f : Γ → Y → X) (g : Γ → X →
  Y) (hi : ∀ γ y, g γ (f γ y) = y := by
  simp) (hf : Continuous ↿f := by fun_prop) (hg : Continuous ↿g := by fun_prop) : IsLocallyConstant
  fun γ y ↦ φ (f γ y) := (IsLocallyConstant.iff_exists_open _).2 fun k ↦ let : UniformSpace ℂ := ⊥
  (exists_nhds_square (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
  ((ContinuousMap.comp ⟨_, h.1.continuous⟩ (.mk fun ((a, b), x) ↦ f a (g b x))).curry.2.tendsto (k,
  k)) _ h.2.1 _ .rfl)).imp (by simp [Set.subset_def]; grind [subset_tsupport φ, Function.support])

open MeasureTheory

lemma integral_mem_of_isLocallyConstant [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (μ :
  Measure Y) [IsFiniteMeasure μ] {f : Y → Z → ℂ} (l : IsLocallyConstant f) {P : Submodule ℂ _}
  (h : ∀ g, f g ∈ P) : (∫ g, f g · ∂μ) ∈ P := by
  convert P.sum_smul_mem (μ.real <| f ⁻¹' {·}) (t := l.range_finite.toFinset) (f := id) (by simpa)
  simp [← integral_indicator_const, (l _).measurableSet]
  rw [← integral_finsetSum] <;> simp [Set.indicator, Integrable.indicator, (l _).measurableSet]

/-- Axioms met by a finite product of non-archimedean local fields: a locally compact ring with
Haar measure, compact open subring O of volume one, and a topologically nilpotent invertible
ϖ in O. -/
class SemilocalField F extends CommRing F, TopologicalSpace F, MeasureSpace F, IsTopologicalRing F,
    PolishSpace F, LocallyCompactSpace F, BorelSpace F, volume.IsAddHaarMeasure where
  O : Subring F
  ϖ : Fˣ
  ϖ_mem : ↑ϖ ∈ O
  isCompact_O : @IsCompact F _ O
  volume_O : volume O = 1
  isOpen_O : _root_.IsOpen O.carrier
  unif_nilpotent : IsTopologicallyNilpotent ϖ.1
  valPair : IsValuationPair O

variable [V : SemilocalField F] (χ : MulChar F ℂ)

/-- x is a unit of the subring O. -/
@[simp] abbrev IsIntegralUnit (x : F) := x ∈ SemilocalField.O ∧ ∃ s ∈ SemilocalField.O, s * x = 1

/-- `χ⁻¹` on the units of `O`, zero elsewhere. -/
noncomputable def invOnUnits x := ite (IsIntegralUnit x) (χ x)⁻¹ 0

/-- A finite ring R, a surjection π: O → R with kernel ϖO, and a primitive character η
(`IsPrimitiveMulChar`) with η∘π equal to χ⁻¹ on units, 0 on non-units. -/
class TameLocalChar where
  (ResidueRing) [commRing : CommRing ResidueRing] [finite : Finite ResidueRing] (reduction :
    V.O →+* ResidueRing) (resChar) reduction_spec : (⇑reduction).Surjective ∧ ∀ x, reduction x = 0 ↔
    SemilocalField.ϖ⁻¹.1 * x.1 ∈ SemilocalField.O
  resChar_spec : IsPrimitiveMulChar resChar ∧ ∀ x, invOnUnits χ x.1 = resChar (reduction x)

attribute [instance_reducible, instance] TameLocalChar.commRing
attribute [instance] TameLocalChar.finite

lemma isIntegralUnit_iff_isUnit {u : V.O} : IsIntegralUnit u.1 ↔
  IsUnit u := by simp [isUnit_iff_exists_inv', Subtype.ext_iff]

/-- The additive character ψ has conductor O: ψ is trivial on tO exactly when t lies in O. -/
def HasIntegralConductor (ψ : AddChar F ℂ) := Continuous ψ ∧ ∀ t,
  (∀ s ∈ SemilocalField.O, ψ (t * s) = 1) ↔ t ∈ SemilocalField.O
