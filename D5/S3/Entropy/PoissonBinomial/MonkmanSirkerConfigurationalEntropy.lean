/- GID: D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Majorization monotonicity of Poisson-binomial configurational entropy. -/

import D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep

/-! Majorization monotonicity on the closed unit cube. -/

namespace D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy

open scoped BigOperators Topology
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (moreMixed desc prefixSum)

private lemma desc_affine {M : ℕ} (a b : ℝ) (hb : 0 < b) (c : Fin M → ℝ) :
    desc (fun i => a + b * c i) = (desc c).map (fun x => a + b * x) := by
  apply List.Perm.eq_of_pairwise' (r := fun x y : ℝ => y ≤ x)
  · exact List.pairwise_mergeSort' (fun x y : ℝ => y ≤ x) _
  · apply List.Pairwise.map
    · intro x y hxy
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hb.le)
    · exact List.pairwise_mergeSort' (fun x y : ℝ => y ≤ x) _
  · exact (List.mergeSort_perm _ _).trans
      (by simpa [List.map_ofFn, desc, Function.comp_def] using
        ((List.mergeSort_perm (List.ofFn c) (fun x y : ℝ => decide (y ≤ x))).symm.map
          (fun x => a + b * x)))

private lemma prefix_affine (xs : List ℝ) (a b : ℝ) (k : ℕ) :
    prefixSum (xs.map (fun x => a + b * x)) k =
      ((xs.take k).length : ℝ) * a + b * prefixSum xs k := by
  have hs (ys : List ℝ) : (ys.map (fun x => a + b * x)).sum =
      (ys.length : ℝ) * a + b * ys.sum := by
    induction ys with
    | nil => simp
    | cons y ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one, ih]; ring
  simpa only [prefixSum, ← List.map_take] using hs (xs.take k)

private lemma moreMixed_affine {M : ℕ} {c d : Fin M → ℝ} (hm : moreMixed d c)
    (a b : ℝ) (hb : 0 < b) :
    moreMixed (fun i => a + b * d i) (fun i => a + b * c i) := by
  have hlen (x : Fin M → ℝ) (k : ℕ) : (List.take k (desc x)).length = min k M := by
    simp [desc]
  constructor
  · intro k hk
    rw [desc_affine a b hb, desc_affine a b hb, prefix_affine, prefix_affine,
      hlen, hlen]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hm.1 k hk) hb.le)
  · rw [desc_affine a b hb, desc_affine a b hb, prefix_affine, prefix_affine,
      hlen, hlen, hm.2]

private lemma affine_interior {M : ℕ} (c : Fin M → ℝ)
    (hc : ∀ i, c i ∈ Set.Icc 0 1) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∀ i, ε + (1 - 2 * ε) * c i ∈ Set.Ioo 0 1 := by
  intro i
  have hb : 0 < 1 - 2 * ε := by linarith
  constructor
  · nlinarith [mul_nonneg hb.le (hc i).1]
  · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hc i).2)]


def claim : Prop :=
  ∀ (M : ℕ) (c d : Fin M → ℝ),
    (∀ i, c i ∈ Set.Icc 0 1) →
    (∀ i, d i ∈ Set.Icc 0 1) →
    moreMixed d c → F c ≤ F d

/-- Configurational entropy is nondecreasing under majorization of Bernoulli parameters. -/
theorem result : claim := by
  intro M c d hc hd hm
  have hlim (x : Fin M → ℝ) :
      Filter.Tendsto (fun ε : ℝ => F (fun i => ε + (1 - 2 * ε) * x i))
        (𝓝[>] 0) (𝓝 (F x)) := by
    have hh : Continuous (fun ε : ℝ => F (fun i => ε + (1 - 2 * ε) * x i)) :=
      continuous_F.comp (by fun_prop)
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto (hlim c) (hlim d)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 2 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε'
  exact le_of_interior_ttransform F F_le_interiorT _ _
    (affine_interior c hc hε hε') (affine_interior d hd hε hε')
    (moreMixed_affine hm ε (1 - 2 * ε) (by linarith))

end D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
