/- GID: D5/S3/Topology/Measures/WeakStarPerturbation
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/WeakStarPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dense norm control extends to every weak-star point and preserves injection. -/

import D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Analysis.Normed.Module.WeakDual

/-! # Full-domain weak-star norm estimates and normalization -/

open Set Filter Topology Function

noncomputable section

namespace D5.S3.Topology.Measures.WeakStarPerturbation

universe u v w

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A uniform operator-norm estimate on a dense set holds at every point
for weak-star continuous maps. The norm itself need not be continuous. -/
theorem norm_sub_le_of_denseRange {A : Type v} {T : Type w}
    [TopologicalSpace T] (i : A → T) (hi : DenseRange i)
    (f g : T → WeakDual ℝ X) (hf : Continuous f) (hg : Continuous g)
    (ε : ℝ) (hε : ∀ a, ‖WeakDual.toStrongDual (f (i a) - g (i a))‖ ≤ ε) :
    ∀ p, ‖WeakDual.toStrongDual (f p - g p)‖ ≤ ε := by
  have hc : IsClosed {p | ‖WeakDual.toStrongDual (f p - g p)‖ ≤ ε} := by
    simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right, Pi.sub_apply,
      Set.mem_setOf_eq] using
      (WeakDual.isClosed_closedBall (0 : StrongDual ℝ X) ε).preimage (hf.sub hg)
  intro p
  exact (closure_minimal (Set.range_subset_iff.mpr hε) hc) (hi p)

/-- An operator-norm gap survives approximation with `2 * ε < c`, including
at points outside the dense set. -/
theorem injective_of_approximation {A : Type v} {T : Type w}
    [TopologicalSpace T]
    (i : A → T) (hi : DenseRange i)
    (f g : T → WeakDual ℝ X) (hf : Continuous f) (hg : Continuous g)
    (c ε : ℝ) (hgap : ∀ p q, p ≠ q → c ≤ ‖WeakDual.toStrongDual (f p - f q)‖)
    (hε : 2 * ε < c)
    (hsmall : ∀ a, ‖WeakDual.toStrongDual (f (i a) - g (i a))‖ ≤ ε) :
    Injective g := by
  intro p q hpq
  by_contra hne
  have hbound := norm_sub_le_of_denseRange i hi f g hf hg ε hsmall
  have hid : WeakDual.toStrongDual (f p - f q) =
      WeakDual.toStrongDual (f p - g p) - WeakDual.toStrongDual (f q - g q) := by
    rw [hpq]
    simp only [map_sub]
    abel
  have hnorm : ‖WeakDual.toStrongDual (f p - f q)‖ ≤ ε + ε := by
    rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add (hbound p) (hbound q))
  linarith [hgap p q hne]

/-- Banach–Alaoglu gives the full Stone–Čech extension of every bounded
dual sequence, with the same bound at every point. -/
theorem exists_bounded_extension (a : ℕ → StrongDual ℝ X) (R : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ R) :
    ∃ f : Ultrafilter ℕ → WeakDual ℝ X, Continuous f ∧
      (∀ n, f (pure n) = StrongDual.toWeakDual (a n)) ∧
      ∀ p, ‖WeakDual.toStrongDual (f p)‖ ≤ R := by
  let B : Set (WeakDual ℝ X) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
  have hB : IsCompact B := WeakDual.isCompact_closedBall 0 R
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let b : ℕ → B := fun n => ⟨StrongDual.toWeakDual (a n), by
    simpa only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual] using ha n⟩
  refine ⟨fun p => (Ultrafilter.extend b p).val,
    continuous_subtype_val.comp (continuous_ultrafilter_extend b), ?_, ?_⟩
  · intro n
    simp only [ultrafilter_extend_pure]
    rfl
  · intro p
    have h := (Ultrafilter.extend b p).property
    simpa only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right] using h

/-- The correction from normalization by the actual varying norms to
normalization by their positive limit is norm null. -/
theorem normalize_sub_tendsto_zero {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ℕ → E) (B r : ℝ)
    (hb : ∀ n, ‖a n‖ ≤ B) (hr : 0 < r)
    (ha : Tendsto (fun n => ‖a n‖) atTop (𝓝 r)) :
    Tendsto (fun n => ‖a n‖⁻¹ • a n - r⁻¹ • a n) atTop (𝓝 0) := by
  have hcoeff : Tendsto (fun n => ‖‖a n‖⁻¹ - r⁻¹‖) atTop (𝓝 0) := by
    simpa using ((ha.inv₀ hr.ne').sub_const r⁻¹).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (by simpa using hcoeff.mul_const B)
  rw [← sub_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)

#print axioms injective_of_approximation
#print axioms normalize_sub_tendsto_zero

end D5.S3.Topology.Measures.WeakStarPerturbation
