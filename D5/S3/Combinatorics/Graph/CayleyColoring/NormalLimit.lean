/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/NormalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weak Gaussian limit uses the expectation and variance of the sequential colored-tree move count. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.FiniteProbability

open scoped BigOperators ENNReal ProbabilityTheory Topology
open Filter MeasureTheory ProbabilityTheory

namespace CayleyTreeProbability

noncomputable section

open CayleyColors CayleyExactAudit CayleyFiniteLaw CayleyNativeLaw CayleyParent CayleyProbe CayleyReduction
  CayleyScheduler DiscardedOccupancy

universe u

/-- Standardization by the source expectation and source standard deviation. -/
def sourceStandardized {n k : ℕ} [NeZero k] {K : Type u} (embed : ZMod k ↪ K)
    (s : SourceSample n k) : ℝ :=
  let T : SourceSample n k → ℝ := fun t => sourceCount embed t
  (T s - ∫ t, T t ∂sourceMeasure n k) / Real.sqrt (Var[T; sourceMeasure n k])

def sourceStandardizedLaw {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) [NeZero k] {K : Type u}
    (embed : ZMod k ↪ K) : ProbabilityMeasure ℝ := by
  letI : Nonempty (SourceSample n k) :=
    (Nat.card_ne_zero.mp (sample_spaces_positive hk (⟨0, hn⟩ : Fin n)).1.ne').1
  exact ⟨(sourceMeasure n k).map (sourceStandardized embed),
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2
      (show IsProbabilityMeasure (uniform (SourceSample n k)) from inferInstance)⟩

theorem source_moments {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) [NeZero k]
    {K : Type u} (embed : ZMod k ↪ K)
    (policy : (s : Colored (Fin n) (ZMod k)) → FreePolicy (K := K) s.1.2.val) :
    (∫ s : SourceSample n k, (sourceCount embed s : ℝ) ∂sourceMeasure n k) =
      ∫ w, literalCount n (n - 1) w ∂literalMeasure hn hk (n - 1) ∧
    Var[(fun s : SourceSample n k => (sourceCount embed s : ℝ)); sourceMeasure n k] =
      Var[literalCount n (n - 1); literalMeasure hn hk (n - 1)] := by
  have h := source_occupancy_law hn hk embed policy
  exact ⟨h.integral_eq, h.variance_eq⟩

private theorem source_standardized_law {k N : ℕ} (hk : 2 ≤ k) [NeZero k] {K : Type u}
    (embed : ZMod k ↪ K)
    (policy : (s : Colored (Fin (N + 1)) (ZMod k)) → FreePolicy (K := K) s.1.2.val) :
    sourceStandardizedLaw (Nat.succ_pos N) hk embed = literalLaw k hk N := by
  have idist := source_occupancy_law (Nat.succ_pos N) hk embed policy
  have hm := source_moments (Nat.succ_pos N) hk embed policy
  have he := idist.comp (u := fun x =>
    (x - ∫ s : SourceSample (N + 1) k, (sourceCount embed s : ℝ) ∂sourceMeasure (N + 1) k) /
      Real.sqrt (Var[(fun s : SourceSample (N + 1) k => (sourceCount embed s : ℝ));
        sourceMeasure (N + 1) k])) (by fun_prop)
  apply Subtype.ext
  change (sourceMeasure (N + 1) k).map (sourceStandardized embed) =
    (literalMeasure (Nat.succ_pos N) hk N).map (literalStandardized (Nat.succ_pos N) hk N)
  refine he.map_eq.trans ?_
  congr 1
  funext w
  simp only [Function.comp_apply, literalStandardized, hm.1, hm.2]
  rfl

/-- For the native random central daemon on an independently uniformly colored Cayley tree,
the actual source variance is eventually positive and the exactly standardized laws converge
weakly to the standard normal. A row's policy may depend on the entire past and coloring. -/
theorem colored_cayley_tree_clt (k : ℕ) (hk : 2 ≤ k) (Palette : ℕ → Type u)
    (embed : ∀ N, ZMod k ↪ Palette N)
    (policy : ∀ (N : ℕ) (s : Colored (Fin (N + 1)) (ZMod k)),
      FreePolicy (K := Palette N) s.1.2.val) :
    letI : NeZero k := ⟨by omega⟩
    (∀ᶠ N : ℕ in atTop,
      0 < Var[(fun s : SourceSample (N + 1) k => (sourceCount (embed N) s : ℝ));
        sourceMeasure (N + 1) k]) ∧
    Tendsto (fun N => sourceStandardizedLaw (Nat.succ_pos N) hk (embed N)) atTop
      (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let : NeZero k := ⟨by omega⟩
  refine ⟨?_, (exact_occupancy_normal_limit k hk).congr
    (fun N => (source_standardized_law hk (embed N) (policy N)).symm)⟩
  filter_upwards [literal_variance_eventually_positive k hk] with N hp
  rw [(source_moments (Nat.succ_pos N) hk (embed N) (policy N)).2]
  exact hp

end
end CayleyTreeProbability
