/- GID: D5/S3/Analytic/WeightedCapacity/InfiniteActiveNonIsolation
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/InfiniteActiveNonIsolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Infinite active capacities make every finite state non-isolated in the rational probe topology. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.InfiniteActiveNonIsolation

open DyadicTailFilling ProbeTopologySequences Set Filter TopologicalSpace
open scoped Topology BigOperators

/-- Finite coordinate constraints and rational character balls centered at a finite state. -/
def basicNhd (A : ℕ → ℕ) (u : B A) (I : Finset ℕ) {m : ℕ}
    (rs : Fin m → ℕ → ℚ) (eps : Fin m → ℚ) : Set (B A) :=
  {w | (∀ n ∈ I, w.val n = u.val n) ∧
    ∀ a, dist (chi (rs a) w) (chi (rs a) u) < (eps a : ℝ)}

/-- If infinitely many coordinates have positive capacity, every neighborhood of every finite
state in the rational probe topology contains a different finite state. -/
theorem not_isolated_of_infinite_active (A : ℕ → ℕ)
    (hA : Set.Infinite {n : ℕ | 0 < A n}) (u : B A)
    (U : Set (B A)) (hU : U ∈ @nhds _ (tauPlus A) u) :
    ∃ w ∈ U, w ≠ u := by
  classical
  let Y := (ℕ → AddCircle (1 : ℝ)) × ((ℕ → ℚ) → AddCircle (1 : ℝ))
  let E : B A → Y := fun w => (psi w, fun r => chi r w)
  have htop : tauPlus A = induced E inferInstance := by
    simp only [tauPlus, E, instTopologicalSpaceProd, Pi.topologicalSpace,
      induced_inf, induced_iInf, induced_compose, Function.comp_def]
  rw [htop, nhds_induced, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  let v (w : B A) : ℕ →₀ ℤ := Finsupp.ofSupportFinite
    (fun n => ((w.val n : ℕ) : ℤ)) (by
      apply w.property.subset
      intro n hn
      change ((w.val n : ℕ) : ℤ) ≠ 0 at hn
      change (w.val n : ℕ) ≠ 0
      exact fun h => hn (by rw [h]; rfl))
  have hv (w : B A) (n : ℕ) : v w n = ((w.val n : ℕ) : ℤ) := rfl
  have hvs (w : B A) : (v w).support = w.property.toFinset := by
    ext n
    simp [Finsupp.mem_support_iff, hv]
  let F : (ℕ →₀ ℤ) →+ Y := {
    toFun := fun d =>
      (fun n => ((Real.goldenRatio * (d n : ℝ) : ℝ) : AddCircle (1 : ℝ)),
       fun r => (((d.sum fun n a => r n * (a : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)))
    map_zero' := by
      apply Prod.ext <;> funext n <;> simp
    map_add' := by
      intro d e
      apply Prod.ext
      · funext n
        change ((Real.goldenRatio * ((d + e) n : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
          ((Real.goldenRatio * (d n : ℝ) : ℝ) : AddCircle (1 : ℝ)) +
          ((Real.goldenRatio * (e n : ℝ) : ℝ) : AddCircle (1 : ℝ))
        simp [mul_add]
      · funext r
        dsimp
        rw [Finsupp.sum_add_index (by intros; simp) (by intros; push_cast; ring)]
        push_cast
        rfl }
  have hFE (w : B A) : F (v w) = E w := by
    apply Prod.ext
    · funext n
      simp [F, E, psi, hv]
    · funext r
      change ((((v w).sum (fun n a => r n * (a : ℚ)) : ℚ) : ℝ) :
        AddCircle (1 : ℝ)) = chi r w
      simp only [Finsupp.sum, hvs, chi, hv, Int.cast_natCast]
  let S : Set ℕ := {n : ℕ | 0 < A n} \ Function.support (fun n => (u.val n : ℕ))
  have hS : S.Infinite := hA.sdiff u.property
  let a : ℕ ↪ S := Set.Infinite.natEmbedding S hS
  let n : ℕ → ℕ := fun k => (a k).val
  have hninj : Function.Injective n := Subtype.val_injective.comp a.injective
  have hn (k : ℕ) : 0 < A (n k) ∧ (u.val (n k) : ℕ) = 0 := by
    have h := (a k).property
    simpa [S, n, Function.support] using h
  let t (k : ℕ) : Finset ℕ := (Finset.range k).image n
  have htm {i j : ℕ} (hij : i ≤ j) : t i ⊆ t j :=
    Finset.image_subset_image (Finset.range_mono hij)
  let d (s : Finset ℕ) : ℕ →₀ ℤ := ∑ k ∈ s, Finsupp.single k 1
  have hd (s : Finset ℕ) (k : ℕ) : d s k = if k ∈ s then 1 else 0 := by
    simp [d, Finsupp.single_apply]
  let p (k : ℕ) : Y := F (d (t k))
  obtain ⟨c, hc⟩ := exists_clusterPt_of_compactSpace (Filter.map p atTop)
  have hcont : Continuous (fun z : Y × Y => E u + (z.1 - z.2)) :=
    continuous_const.add (continuous_fst.sub continuous_snd)
  have hnear : {z : Y × Y | E u + (z.1 - z.2) ∈ V} ∈ 𝓝 (c, c) := by
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨V₁, hV₁, V₂, hV₂, hpair⟩ := mem_nhds_prod_iff.mp hnear
  have hfreq : ∃ᶠ k in atTop, p k ∈ V₁ ∩ V₂ :=
    mapClusterPt_iff_frequently.mp hc _ (inter_mem hV₁ hV₂)
  obtain ⟨i, _, hi⟩ := frequently_atTop.mp hfreq 0
  obtain ⟨j, hij, hj⟩ := frequently_atTop'.mp hfreq i
  let s := t j \ t i
  have hs (k : ℕ) (hk : k ∈ s) : 0 < A k ∧ (u.val k : ℕ) = 0 := by
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hk).1
    exact hn l
  have hni : n i ∈ s := by
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩
    · rintro h
      obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
      have := hninj he
      have := Finset.mem_range.mp hl
      omega
  let w : B A := ⟨fun k => if hk : k ∈ s then ⟨1, by have := (hs k hk).1; omega⟩
      else u.val k, by
    apply (s.finite_toSet.union u.property).subset
    intro k hk
    by_cases hks : k ∈ s
    · exact Or.inl hks
    · exact Or.inr (by simpa [Function.support, hks] using hk)⟩
  have hw (k : ℕ) : (w.val k : ℕ) = if k ∈ s then 1 else (u.val k : ℕ) := by
    by_cases hk : k ∈ s <;> simp [w, hk]
  have hvw : v w = v u + d s := by
    ext k
    rw [Finsupp.add_apply, hv, hv, hd, hw]
    by_cases hk : k ∈ s
    · simp [hk, (hs k hk).2]
    · simp [hk]
  have hds : d s = d (t j) - d (t i) := by
    ext k
    rw [Finsupp.sub_apply, hd, hd, hd]
    by_cases hki : k ∈ t i
    · have hkj := htm hij.le hki
      simp [s, hki, hkj]
    · by_cases hkj : k ∈ t j <;> simp [s, hki, hkj]
  have hEw : E w = E u + (p j - p i) := by
    rw [← hFE, hvw, map_add, hFE, hds, map_sub]
  refine ⟨w, hVU ?_, ?_⟩
  · change E w ∈ V
    rw [hEw]
    exact hpair (show (p j, p i) ∈ V₁ ×ˢ V₂ from ⟨hj.1, hi.2⟩)
  · intro heq
    have he := congrArg (fun x : B A => (x.val (n i) : ℕ)) heq
    rw [hw] at he
    simp [hni, (hn i).2] at he

#print axioms not_isolated_of_infinite_active

end D5.S3.Analytic.WeightedCapacity.InfiniteActiveNonIsolation
