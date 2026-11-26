import OmegaMath.NumberTheory.GRH.Lib.Weil.MixedModel.ZeroTerm
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: The mixed Schrödinger model function of a vector is continuous and integrable. -/

open MeasureTheory Equiv

namespace Space.Splitting

variable {E} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s n₀ p} [Fintype n₀] [Fintype p]
  {s₀} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p)

@[fun_prop] lemma continuous_mixedTerm f :
  Continuous (D.mixedTerm · f) := by simp [mixedTerm]; fun_prop

/-- For a splitting of V over V₀ with p hyperbolic planes and f in 𝒮(V), the 𝒮(V₀)-valued
function x ↦ f[x] of the mixed model is integrable on 𝔸^p. -/
@[fun_prop] lemma integrable_mixedTerm f : Integrable (D.mixedTerm · f) := ⟨by fun_prop,
  (lintegral_addOrbitMeasure_lintegral (H :=
  _root_.ratVectors E p) (continuous_mixedTerm ..).enorm.measurable).ge.trans_lt
  (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨_, fun x ↦ by
  erw [lintegral_count, ← (ofInjective _ (@toAdele E ..).injective.comp_left).tsum_eq]
  simpa [← ofReal_norm] using! D.tsum_enorm_mixedTerm_le.choose_spec (ϱ _ (D.lAdelic.mulVec x) f)⟩)⟩
