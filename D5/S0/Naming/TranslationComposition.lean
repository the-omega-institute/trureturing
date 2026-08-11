/- GID: D5/S0/Naming/TranslationComposition
   generality: G
   mirror-B: D5/B/S0/Naming/TranslationComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Approximate translations compose with additive error and composed resource modulus. -/

/- Library-search audit trail (2026-08-11):
   * Repository searches for approximate translations, semantic error, resource moduli, and
     translation composition found no existing abstraction or theorem. The existing
     `Naming.NamingSystem` is reused as the unique source for partial assignments and heights.
   * Pinned-mathlib searches found the exact reusable primitives `Isometry.comp`,
     `Isometry.dist_eq`, `Monotone.comp`, and `dist_triangle`; no approximate- or
     quasi-isometry abstraction matched the partial semantic and resource-controlled statement.
   * Authenticated GitHub Lean code searches for `ApproxTranslation`, `approximate translation`,
     and `Isometry.comp resource` each returned zero results. This declaration is therefore a
     repo-derived formalization rather than an attribution to a third-party Lean theorem.
-/

import D5.S0.Naming.NamingSystem
import Mathlib.Topology.MetricSpace.Isometry

namespace D5.S0.Naming.TranslationComposition

open MeasureTheory

universe u v w

/-- A partial translation between naming systems, with conditional semantic control and a
monotone resource modulus. The semantic clause follows the partial assignments exactly: it is
required only when both endpoint meanings exist. -/
structure Translation
    {X : Type u} [PseudoMetricSpace X] [MeasureSpace X]
    {Y : Type v} [PseudoMetricSpace Y] [MeasureSpace Y]
    (source : NamingSystem X) (target : NamingSystem Y)
    (epsilon : ℝ) (modulus : ℕ → ℕ) where
  domain : Set source.Name
  toFun : source.Name → target.Name
  embedding : X → Y
  isometry_embedding : Isometry embedding
  monotone_modulus : Monotone modulus
  semantic_bound :
    ∀ a ∈ domain, ∀ {x y},
      source.assignment a = some x →
      target.assignment (toFun a) = some y →
      dist y (embedding x) ≤ epsilon
  resource_bound :
    ∀ a ∈ domain, target.height (toFun a) ≤ modulus (source.height a)

/-- The partial semantic assignments needed by the two error estimates meet at every point where
the composite endpoints have meanings. This is the precise semantic content of saying that the
composition is defined. -/
def SemanticallyComposable
    {X : Type u} [PseudoMetricSpace X] [MeasureSpace X]
    {Y : Type v} [PseudoMetricSpace Y] [MeasureSpace Y]
    {Z : Type w} [PseudoMetricSpace Z] [MeasureSpace Z]
    {source : NamingSystem X} {middle : NamingSystem Y} {target : NamingSystem Z}
    {epsilon₁ epsilon₂ : ℝ} {modulus₁ modulus₂ : ℕ → ℕ}
    (translation₁ : Translation source middle epsilon₁ modulus₁)
    (translation₂ : Translation middle target epsilon₂ modulus₂) : Prop :=
  ∀ a ∈ translation₁.domain,
    translation₁.toFun a ∈ translation₂.domain →
    ∀ {x z},
      source.assignment a = some x →
      target.assignment (translation₂.toFun (translation₁.toFun a)) = some z →
      ∃ y, middle.assignment (translation₁.toFun a) = some y

/-- Composing two translations adds their semantic tolerances, composes their monotone resource
moduli, and composes their isometric embeddings. -/
theorem translation_composition
    {X : Type u} [PseudoMetricSpace X] [MeasureSpace X]
    {Y : Type v} [PseudoMetricSpace Y] [MeasureSpace Y]
    {Z : Type w} [PseudoMetricSpace Z] [MeasureSpace Z]
    {source : NamingSystem X} {middle : NamingSystem Y} {target : NamingSystem Z}
    {epsilon₁ epsilon₂ : ℝ} {modulus₁ modulus₂ : ℕ → ℕ}
    (translation₁ : Translation source middle epsilon₁ modulus₁)
    (translation₂ : Translation middle target epsilon₂ modulus₂)
    (hsemantic : SemanticallyComposable translation₁ translation₂) :
    ∃ translation :
        Translation source target (epsilon₁ + epsilon₂) (modulus₂ ∘ modulus₁),
      translation.domain =
          {a | a ∈ translation₁.domain ∧ translation₁.toFun a ∈ translation₂.domain} ∧
      translation.toFun = translation₂.toFun ∘ translation₁.toFun ∧
      translation.embedding = translation₂.embedding ∘ translation₁.embedding := by
  refine ⟨{
    domain := {a | a ∈ translation₁.domain ∧ translation₁.toFun a ∈ translation₂.domain}
    toFun := translation₂.toFun ∘ translation₁.toFun
    embedding := translation₂.embedding ∘ translation₁.embedding
    isometry_embedding :=
      translation₂.isometry_embedding.comp translation₁.isometry_embedding
    monotone_modulus :=
      translation₂.monotone_modulus.comp translation₁.monotone_modulus
    semantic_bound := by
      intro a ha x z hx hz
      obtain ⟨y, hy⟩ := hsemantic a ha.1 ha.2 hx hz
      calc
        dist z ((translation₂.embedding ∘ translation₁.embedding) x) ≤
            dist z (translation₂.embedding y) +
              dist (translation₂.embedding y)
                ((translation₂.embedding ∘ translation₁.embedding) x) :=
          dist_triangle z (translation₂.embedding y)
            ((translation₂.embedding ∘ translation₁.embedding) x)
        _ = dist z (translation₂.embedding y) + dist y (translation₁.embedding x) := by
          simp only [Function.comp_apply, translation₂.isometry_embedding.dist_eq]
        _ ≤ epsilon₂ + epsilon₁ :=
          add_le_add
            (translation₂.semantic_bound (translation₁.toFun a) ha.2 hy hz)
            (translation₁.semantic_bound a ha.1 hx hy)
        _ = epsilon₁ + epsilon₂ := add_comm epsilon₂ epsilon₁
    resource_bound := by
      intro a ha
      calc
        target.height (translation₂.toFun (translation₁.toFun a)) ≤
            modulus₂ (middle.height (translation₁.toFun a)) :=
          translation₂.resource_bound (translation₁.toFun a) ha.2
        _ ≤ modulus₂ (modulus₁ (source.height a)) :=
          translation₂.monotone_modulus (translation₁.resource_bound a ha.1)
        _ = (modulus₂ ∘ modulus₁) (source.height a) := rfl
  }, rfl, rfl, rfl⟩

end D5.S0.Naming.TranslationComposition
