/- GID: D5/S3/Topology/Measures/L1WeakExtraction
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1WeakExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded Hilbert approximations give weak subsequences in Banach spaces. -/

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Weak extraction through countably many bounded Hilbert approximations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology TopologicalSpace
open scoped InnerProductSpace

namespace D5.S3.Topology.Measures.L1WeakExtraction

universe u v

private theorem common_weak_subsequence_separable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SeparableSpace H]
    (t : ℕ → ℕ → H) (R : ℕ → ℝ) (hb : ∀ m n, ‖t m n‖ ≤ R m) :
    ∃ (j : ℕ → ℕ) (q : ℕ → H), StrictMono j ∧
      ∀ m (φ : H →L[ℝ] ℝ),
        Tendsto (fun n => φ (t m (j n))) atTop (𝓝 (φ (q m))) := by
  let B (m : ℕ) :=
    (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) (R m))
  have hB (m : ℕ) : IsCompact (B m) := WeakDual.isCompact_closedBall _ _
  letI (m : ℕ) : CompactSpace (B m) := isCompact_iff_compactSpace.mp (hB m)
  letI (m : ℕ) : TopologicalSpace.MetrizableSpace (B m) :=
    WeakDual.metrizable_of_isCompact ℝ H (B m) (hB m)
  let z (n : ℕ) : ∀ m, B m := fun m =>
    ⟨(InnerProductSpace.toDual ℝ H (t m n)).toWeakDual, by
      change dist (InnerProductSpace.toDual ℝ H (t m n)) 0 ≤ R m
      simpa using hb m n⟩
  obtain ⟨p, j, hj, hz⟩ := CompactSpace.tendsto_subseq z
  let q (m : ℕ) : H :=
    (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual (p m).val)
  refine ⟨j, q, hj, fun m φ => ?_⟩
  have hm : Tendsto (fun n => ((z (j n) m).val)) atTop (𝓝 (p m).val) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      ((continuous_apply m).continuousAt.tendsto.comp hz)
  let a : H := (InnerProductSpace.toDual ℝ H).symm φ
  have he := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hm) a
  have ht (x : H) : InnerProductSpace.toDual ℝ H x a = φ x := by
    rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hq : (p m).val a = φ (q m) := by
    calc
      (p m).val a = ⟪q m, a⟫_ℝ := (InnerProductSpace.toDual_symm_apply).symm
      _ = ⟪a, q m⟫_ℝ := real_inner_comm _ _
      _ = φ (q m) := InnerProductSpace.toDual_symm_apply
  change Tendsto (fun n => InnerProductSpace.toDual ℝ H (t m (j n)) a)
    atTop (𝓝 ((p m).val a)) at he
  simpa only [ht, hq] using he

/-- Countably many bounded Hilbert sequences have one common weak subsequence.
The ambient Hilbert space need not be separable. -/
theorem exists_common_weak_subsequence
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (t : ℕ → ℕ → H) (R : ℕ → ℝ) (hb : ∀ m n, ‖t m n‖ ≤ R m) :
    ∃ (j : ℕ → ℕ) (q : ℕ → H), StrictMono j ∧
      ∀ m (φ : H →L[ℝ] ℝ),
        Tendsto (fun n => φ (t m (j n))) atTop (𝓝 (φ (q m))) := by
  let S : Submodule ℝ H := Submodule.span ℝ (range (fun p : ℕ × ℕ => t p.1 p.2))
  let V : Submodule ℝ H := S.topologicalClosure
  have hs : IsSeparable (V : Set H) := by
    change IsSeparable (closure (S : Set H))
    exact ((countable_range (fun p : ℕ × ℕ => t p.1 p.2)).isSeparable.span).closure
  letI : SeparableSpace V := hs.separableSpace
  let a (m n : ℕ) : V :=
    ⟨t m n, S.le_topologicalClosure (Submodule.subset_span (mem_range.mpr ⟨(m, n), rfl⟩))⟩
  obtain ⟨j, q, hj, hq⟩ := common_weak_subsequence_separable a R (fun m n => hb m n)
  refine ⟨j, fun m => (q m).val, hj, fun m φ => ?_⟩
  exact hq m (φ.comp V.subtypeL)

/-- Uniform norm approximation by images of bounded Hilbert sequences gives a
subsequence converging against every continuous real linear functional. -/
theorem exists_weak_subsequence_of_hilbert_approximation
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] X) (f : ℕ → X) (t : ℕ → ℕ → H) (R δ : ℕ → ℝ)
    (hb : ∀ m n, ‖t m n‖ ≤ R m)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (herr : ∀ m n, ‖f n - T (t m n)‖ ≤ δ m) :
    ∃ (j : ℕ → ℕ) (v : X), StrictMono j ∧
      ∀ φ : X →L[ℝ] ℝ, Tendsto (fun n => φ (f (j n))) atTop (𝓝 (φ v)) := by
  obtain ⟨j, q, hj, hq⟩ := exists_common_weak_subsequence t R hb
  let z (m : ℕ) := T (q m)
  have hz (m : ℕ) (φ : X →L[ℝ] ℝ) :
      Tendsto (fun n => φ (T (t m (j n)))) atTop (𝓝 (φ (z m))) :=
    hq m (φ.comp T)
  have hdist (m k : ℕ) : ‖z m - z k‖ ≤ δ m + δ k := by
    obtain ⟨φ, hφ, hnorm⟩ := exists_dual_vector'' ℝ (z m - z k)
    have hlim := (hz m φ).sub (hz k φ)
    have hle (n : ℕ) : φ (T (t m (j n))) - φ (T (t k (j n))) ≤ δ m + δ k := by
      have ht : ‖T (t m (j n)) - T (t k (j n))‖ ≤ δ m + δ k := by
        calc
          _ ≤ ‖T (t m (j n)) - f (j n)‖ + ‖f (j n) - T (t k (j n))‖ :=
            by simpa only [dist_eq_norm] using
              dist_triangle (T (t m (j n))) (f (j n)) (T (t k (j n)))
          _ ≤ δ m + δ k := by
            rw [norm_sub_rev (T (t m (j n))) (f (j n))]
            exact add_le_add (herr m (j n)) (herr k (j n))
      calc
        _ = φ (T (t m (j n)) - T (t k (j n))) := (map_sub _ _ _).symm
        _ ≤ ‖φ (T (t m (j n)) - T (t k (j n)))‖ := le_abs_self _
        _ ≤ ‖φ‖ * ‖T (t m (j n)) - T (t k (j n))‖ := φ.le_opNorm _
        _ ≤ 1 * (δ m + δ k) := mul_le_mul hφ ht (norm_nonneg _) (by positivity)
        _ = _ := one_mul _
    have := le_of_tendsto' hlim hle
    rwa [← map_sub, hnorm] at this
  have hc : CauchySeq z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hev := (tendsto_order.1 hδlim).2 (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun m hm k hk => ?_⟩
    rw [dist_eq_norm]
    exact (hdist m k).trans_lt (by linarith [hN m hm, hN k hk])
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨j, v, hj, fun φ => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsmall : Tendsto (fun m => ‖φ‖ * δ m + ‖φ‖ * ‖z m - v‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hδlim).add
      (tendsto_const_nhds.mul ((tendsto_iff_norm_sub_tendsto_zero.1 hv)))
  obtain ⟨m, hm⟩ := ((tendsto_order.1 hsmall).2 (ε / 2) (by linarith)).exists
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hz m φ)) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  calc
    dist (φ (f (j n))) (φ v) ≤
        dist (φ (f (j n))) (φ (T (t m (j n)))) +
          dist (φ (T (t m (j n)))) (φ (z m)) + dist (φ (z m)) (φ v) :=
      dist_triangle4 _ _ _ _
    _ ≤ ‖φ‖ * δ m + dist (φ (T (t m (j n)))) (φ (z m)) + ‖φ‖ * ‖z m - v‖ := by
      have hfirst : dist (φ (f (j n))) (φ (T (t m (j n)))) ≤ ‖φ‖ * δ m := by
        rw [dist_eq_norm, ← map_sub]
        exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (herr m (j n)) (norm_nonneg _))
      have hlast : dist (φ (z m)) (φ v) ≤ ‖φ‖ * ‖z m - v‖ := by
        rw [dist_eq_norm, ← map_sub]
        exact φ.le_opNorm _
      exact add_le_add (add_le_add hfirst le_rfl) hlast
    _ < ε := by linarith [hN n hn]

end D5.S3.Topology.Measures.L1WeakExtraction
