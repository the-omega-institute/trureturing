/- GID: D5/S3/Geometry/ColourfulCaratheodory
   generality: G
   mirror-B: D5/B/S3/Geometry/ColourfulCaratheodory
   mirror-E: none(waiver:classical-colourful-selection)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Caratheodory, mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.Minimal]
   utility: none
   digest: Colour-preserving convex hull selection for arbitrary subsets of real Euclidean space. -/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped BigOperators

namespace D5.S3.Geometry.ColourfulCaratheodory

private theorem nearest_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : Set E} (hc : Convex ℝ A) {q : E} (hq : q ∈ A)
    (hm : ∀ r ∈ A, ‖q‖ ≤ ‖r‖) : ∀ r ∈ A, inner ℝ q q ≤ inner ℝ q r := by
  have he : ‖(0 : E) - q‖ = ⨅ r : A, ‖(0 : E) - r‖ := by
    simp only [zero_sub, norm_neg]
    apply le_antisymm
    · exact le_ciInf (fun r => hm r r.property)
    · exact ciInf_le ⟨0, by simp only [mem_range, forall_exists_index]; exact fun _ _ => norm_nonneg _⟩ ⟨q, hq⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hq).mp he
  intro r hr
  have h := hi r hr
  simpa only [zero_sub, inner_neg_left, inner_sub_right, neg_nonpos, sub_nonneg] using h

private theorem colourful_exchange {d : ℕ}
    (S : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (S i))
    (f : Fin (d + 1) → EuclideanSpace ℝ (Fin d)) (hf : ∀ i, f i ∈ S i)
    (q : EuclideanSpace ℝ (Fin d)) (hq : q ∈ convexHull ℝ (range f))
    (hm : ∀ r ∈ convexHull ℝ (range f), ‖q‖ ≤ ‖r‖) (hne : q ≠ 0) :
    ∃ (g : Fin (d + 1) → EuclideanSpace ℝ (Fin d)) (r : EuclideanSpace ℝ (Fin d)),
      (∀ i, g i ∈ S i) ∧ r ∈ convexHull ℝ (range g) ∧ ‖r‖ < ‖q‖ := by
  classical
  obtain ⟨ι, hι, z, w, hz, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hq
  letI := hι
  have hc : 0 < inner ℝ q q := real_inner_self_pos.mpr hne
  have hs := nearest_inner (convex_convexHull ℝ (range f)) hq hm
  have hzi (i : ι) : inner ℝ q q ≤ inner ℝ q (z i) :=
    hs (z i) (subset_convexHull ℝ (range f) (hz (mem_range_self i)))
  have heq (i : ι) : inner ℝ q (z i) = inner ℝ q q := by
    have hsum : ∑ j, w j * (inner ℝ q (z j) - inner ℝ q q) = 0 := by
      simp only [mul_sub, sum_sub_distrib, ← inner_smul_right, ← inner_sum, ← sum_mul, hw1, one_mul, hwz, sub_self]
    have hzsum := (sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hw j).le (sub_nonneg.mpr (hzi j)))).mp hsum i (mem_univ i)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzsum).resolve_left (hw i).ne')
  have hlin : LinearIndependent ℝ z := by
    rw [linearIndependent_iff']
    intro t a ha i hi
    have hsum : (∑ j ∈ t, a j) * inner ℝ q q = 0 := by
      have h := congrArg (fun x => inner ℝ q x) ha
      simpa only [inner_sum, inner_smul_right, heq, ← sum_mul, inner_zero_right] using h
    have hzero : ∑ j ∈ t, a j = 0 := (mul_eq_zero.mp hsum).resolve_right hc.ne'
    exact hai.eq_zero_of_sum_eq_zero hzero ha i hi
  have hcard : Fintype.card ι ≤ d := by
    simpa using hlin.fintype_card_le_finrank
  choose c hc using (fun j => hz (mem_range_self j))
  have hmiss : ¬ Function.Surjective c := by
    intro h
    have hle := Fintype.card_le_of_surjective c h
    simp only [Fintype.card_fin] at hle
    omega
  obtain ⟨k, hk⟩ := not_forall.mp hmiss
  have hck (j : ι) : c j ≠ k := fun h => hk ⟨j, h⟩
  have hx : ∃ x ∈ S k, inner ℝ q x < inner ℝ q q := by
    by_contra! h
    have hconv : Convex ℝ {x | inner ℝ q q ≤ inner ℝ q x} := by
      intro x hx y hy a b ha hb hab
      simp only [mem_setOf_eq, inner_add_right, inner_smul_right]
      nlinarith
    have h0 := convexHull_min h hconv (hS k)
    simp only [mem_setOf_eq, inner_zero_right] at h0
    linarith
  obtain ⟨x, hx, hlt⟩ := hx
  let g := Function.update f k x
  have hg (i) : g i ∈ S i := by
    by_cases h : i = k
    · subst i; simpa [g] using hx
    · simpa [g, h] using hf i
  have hzg (j : ι) : z j ∈ range g := by
    refine ⟨c j, ?_⟩
    simpa [g, hck j] using hc j
  have hqg : q ∈ convexHull ℝ (range g) :=
    mem_convexHull_of_exists_fintype w z (fun j => (hw j).le) hw1 hzg hwz
  have hxg : x ∈ convexHull ℝ (range g) :=
    subset_convexHull ℝ _ ⟨k, by simp [g]⟩
  refine ⟨g, ?_⟩
  by_contra! h
  have hmin : ∀ r ∈ convexHull ℝ (range g), ‖q‖ ≤ ‖r‖ := by
    intro r hr
    exact h r (hg) hr
  have hle := nearest_inner (convex_convexHull ℝ (range g)) hqg hmin x hxg
  exact (not_lt_of_ge hle) hlt

end D5.S3.Geometry.ColourfulCaratheodory
