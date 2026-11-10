/- GID: D5/S3/Analytic/Entire/TranslationFinite
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/TranslationFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise closed finite translation spaces and their actual derivative endomorphisms. -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

/-!
This module works in the product topology on all scalar functions, not in a
Fock norm domain for an unbounded differentiation operator. Finite dimension
makes a translation-invariant function space closed in the product topology;
the pointwise limits of its difference quotients therefore stay in the space.
The intended consumer is the finite separation classification of entire
Hankel kernels. The subsequent constant-coefficient ODE classification is a
separate obligation and is not assumed here.
-/

noncomputable section
open Filter Topology

namespace D5.S3.Analytic.Entire

/-- Translation acts on all complex-valued functions without a regularity premise. -/
def translate (t : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun z => f (z + t)

def translateLinear (t : ℂ) : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun := translate t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem translate_zero (f : ℂ → ℂ) : translate 0 f = f := by
  funext z
  simp [translate]

theorem translate_add (s t : ℂ) (f : ℂ → ℂ) :
    translate s (translate t f) = translate (s + t) f := by
  funext z
  simp only [translate, add_assoc]

/-- The complete algebraic span of every complex translate. -/
def translationSpace (f : ℂ → ℂ) : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ (Set.range (fun t => translate t f))

theorem mem_translation_space (f : ℂ → ℂ) : f ∈ translationSpace f := by
  have h : translate 0 f ∈ translationSpace f := Submodule.subset_span ⟨0, rfl⟩
  rwa [translate_zero] at h

theorem translation_space_invariant (f : ℂ → ℂ) (t : ℂ) :
    translationSpace f ≤ (translationSpace f).comap (translateLinear t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change translate t (translate s f) ∈ translationSpace f
  rw [translate_add]
  exact Submodule.subset_span ⟨t + s, rfl⟩

/-- Entire functions form a genuine complex submodule of the pointwise function space. -/
def entireSubmodule : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f}
  zero_mem' := differentiable_const 0
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change Differentiable ℂ (fun z => c * f z)
    exact hf.const_mul c

theorem translation_space_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    translationSpace f ≤ entireSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact hf.comp (differentiable_id.add_const t)

/-- The derivative is a pointwise limit of actual members of the finite space.
No differentiability operator on a completed Hilbert space is postulated. -/
theorem deriv_mem_of_finite_translation_invariant
    (W : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ W]
    (htranslate : ∀ t, W ≤ W.comap (translateLinear t))
    {f : ℂ → ℂ} (hf : f ∈ W) (hentire : Differentiable ℂ f) :
    deriv f ∈ W := by
  let q : ℂ → (ℂ → ℂ) := fun t => t⁻¹ • (translate t f - f)
  have hq (t : ℂ) : q t ∈ W :=
    W.smul_mem _ (W.sub_mem (htranslate t hf) hf)
  have hlim : Tendsto q (𝓝[≠] (0 : ℂ)) (𝓝 (deriv f)) := by
    apply tendsto_pi_nhds.mpr
    intro z
    exact (hentire z).hasDerivAt.tendsto_slope_zero
  exact W.closed_of_finiteDimensional.mem_of_tendsto hlim
    (Filter.Eventually.of_forall hq)

/-- Differentiation restricted to the finite-dimensional entire translation space. -/
def derivativeEnd (W : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ W]
    (hentire : W ≤ entireSubmodule)
    (htranslate : ∀ t, W ≤ W.comap (translateLinear t)) : Module.End ℂ W where
  toFun f := ⟨deriv (f : ℂ → ℂ),
    deriv_mem_of_finite_translation_invariant W htranslate f.property
      (hentire f.property)⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact deriv_add (hentire f.property z) (hentire g.property z)
  map_smul' c f := by
    apply Subtype.ext
    funext z
    exact deriv_const_mul c (hentire f.property z)

#print axioms deriv_mem_of_finite_translation_invariant

end D5.S3.Analytic.Entire
