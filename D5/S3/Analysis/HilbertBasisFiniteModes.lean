/- GID: D5/S3/Analysis/HilbertBasisFiniteModes
   generality: G
   mirror-B: none(waiver:covered-by-ccrfock-factor-disjointness-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert-basis synthesis from a finite tuple and its exact coordinate and inner-product formulas. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-! Omega original.
Hilbert-basis synthesis from a finite tuple and its exact coordinate and inner-product formulas. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Complex

namespace Omega.HilbertBasisFiniteModes

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Embed a finite complex tuple as a displacement in the indicated modes. -/
def modeEmbed (b : HilbertBasis I ℂ H) (F : Finset I) (z : F → ℂ) : H :=
  ∑ i : F, z i • b i

theorem repr_modeEmbed (b : HilbertBasis I ℂ H) (F : Finset I) (z : F → ℂ) (i : I) :
    b.repr (modeEmbed b F z) i =
      @dite ℂ (i ∈ F) (Classical.propDecidable _) (fun h => z ⟨i, h⟩) (fun _ => 0) := by
  classical
  simp only [modeEmbed, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, b.repr_self, lp.single_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  split_ifs with hi
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : F)]
    · simp
    · intro j _ hj
      exact ite_eq_right (fun h : i = (j : I) => hj (Subtype.ext h.symm))
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (fun h : i = (j : I) => hi (h.symm ▸ j.property))

theorem inner_modeEmbed (b : HilbertBasis I ℂ H) (F : Finset I) (z : F → ℂ) (v : H) :
    ⟪v, modeEmbed b F z⟫_ℂ = ∑ i : F, conj (b.repr v i) * z i := by
  simp only [modeEmbed, inner_sum, inner_smul_right, HilbertBasis.repr_apply_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [inner_conj_symm, mul_comm])

theorem modeEmbed_norm_sq (b : HilbertBasis I ℂ H) (F : Finset I) (z : F → ℂ) :
    ‖modeEmbed b F z‖ ^ 2 = ∑ i : F, ‖z i‖ ^ 2 := by
  have h := inner_modeEmbed b F z (modeEmbed b F z)
  simp only [repr_modeEmbed, Subtype.property, dite_true, inner_self_eq_norm_sq_to_K] at h
  have he : ∀ x : ℂ, conj x * x = (‖x‖ : ℂ) ^ 2 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp only [he, ← Complex.ofReal_pow, ← Complex.ofReal_sum] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact h

/-- A range containing every finite coordinate synthesis is dense. -/
theorem dense_range_of_modeEmbed {S : Type*} (b : HilbertBasis I ℂ H) {z : S → H}
    (hz : ∀ (F : Finset I) (w : F → ℂ), ∃ s, z s = modeEmbed b F w) : Dense (Set.range z) := by
  intro x
  apply mem_closure_of_tendsto (b.hasSum_repr x)
  refine Filter.Eventually.of_forall (fun F => ?_)
  obtain ⟨s, hs⟩ := hz F (fun i => b.repr x i)
  refine ⟨s, hs.trans ?_⟩
  unfold modeEmbed
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach F (fun i => b.repr x i • b i)

end Omega.HilbertBasisFiniteModes
