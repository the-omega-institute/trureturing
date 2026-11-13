/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeBoundaryEquation
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeBoundaryEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cone boundary equations have exact homogeneous chart lifts and squarefree minima. -/

import D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

noncomputable section

open Set Filter
open scoped Topology Pointwise

namespace D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

open private exists_full_compact_base base_chart_geometry
  from D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase

open private linePolynomial eval_linePolynomial affineLinearPolynomial eval_affineLinearPolynomial homogeneous_eval_smul
  from D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

variable {ι : Type*} [Fintype ι]

private theorem cone_frontier_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ProperCone ℝ E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : y ∈ frontier (C : Set E)) : r • y ∈ frontier (C : Set E) := by
  have hscale : ∀ r : ℝ, 0 < r → r • (C : Set E) = (C : Set E) := by
    intro r hr
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact C.smul_mem hy hr.le
    · intro y hy
      refine ⟨r⁻¹ • y, C.smul_mem hy (inv_nonneg.mpr hr.le), ?_⟩
      simp [smul_smul, hr.ne']
  have hfront : ∀ r : ℝ, 0 < r → ∀ y ∈ frontier (C : Set E),
      r • y ∈ frontier (C : Set E) := by
    intro r hr y hy
    have hf := (Homeomorph.smulOfNeZero r hr.ne' : E ≃ₜ E).image_frontier (C : Set E)
    have heq : r • frontier (C : Set E) = frontier (C : Set E) := by
      simpa [hscale r hr] using hf
    rw [← heq]
    exact ⟨y, hy, rfl⟩
  exact hfront r hr y hy

private theorem cone_vertex_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) : (0 : E) ∈ frontier (C : Set E) := by
  rw [C.isClosed.frontier_eq]
  refine ⟨C.toPointedCone.zero_mem, ?_⟩
  intro hzero
  obtain ⟨z, hz⟩ := exists_ne (0 : E)
  obtain ⟨y, hy⟩ : ∃ y : E, y ∉ C := by
    by_cases hzc : z ∈ C
    · exact ⟨-z, hs z hzc hz⟩
    · exact ⟨z, hzc⟩
  have htend : Tendsto (fun t : ℝ => t⁻¹ • y) atTop (𝓝 (0 : E)) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul_const y
  have hm := htend.eventually (mem_interior_iff_mem_nhds.mp hzero)
  obtain ⟨t, ht, hty⟩ := ((eventually_gt_atTop (0 : ℝ)).and hm).exists
  apply hy
  simpa [smul_smul, ht.ne'] using C.smul_mem hty ht.le

private theorem cone_boundary_component {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (p : MvPolynomial ι ℝ)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∀ d : ℕ, ∀ y ∈ frontier (C : Set E),
      MvPolynomial.eval (c y) (MvPolynomial.homogeneousComponent d p) = 0 := by
  classical
  intro d y hy
  by_cases hd : p.totalDegree < d
  · rw [MvPolynomial.homogeneousComponent_eq_zero d p hd, map_zero]
  let Q : Polynomial ℝ := ∑ k ∈ Finset.range (p.totalDegree + 1),
    Polynomial.monomial k (MvPolynomial.eval (c y) (MvPolynomial.homogeneousComponent k p))
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioi_infinite (0 : ℝ)).mono
    intro r hr
    change Q.eval r = 0
    have hh := hvan (r • y) (cone_frontier_smul C hr hy)
    rw [← MvPolynomial.sum_homogeneousComponent p, map_sum] at hh
    simpa only [Q, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
      map_smul, homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _),
      mul_comm] using hh
  have hc := congrArg (fun f : Polynomial ℝ => f.coeff d) hQ
  simpa [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_of_le (le_of_not_gt hd)] using hc

private theorem cone_boundary_homogeneous_equation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧
      ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0 := by
  classical
  have hcomp := cone_boundary_component c C p hvan
  obtain ⟨d, hd, hq⟩ : ∃ d ∈ Finset.range (p.totalDegree + 1),
      MvPolynomial.homogeneousComponent d p ≠ 0 := by
    by_contra! h
    apply hp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    exact Finset.sum_eq_zero h
  have hz := cone_vertex_frontier C hs
  have hdpos : 0 < d := by
    by_contra! hd0
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd0
    subst d
    have hc := hcomp 0 0 hz
    simp only [map_zero, MvPolynomial.homogeneousComponent_zero, MvPolynomial.eval_C] at hc
    exact hq (by simp [hc])
  exact ⟨d, MvPolynomial.homogeneousComponent d p, hdpos,
    Nat.le_of_lt_succ (Finset.mem_range.mp hd), hq,
    MvPolynomial.homogeneousComponent_isHomogeneous d p, hcomp d⟩

private theorem substitution_degree {κ : Type*} (p : MvPolynomial κ ℝ)
    (f : κ → MvPolynomial ι ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (p.eval₂ MvPolynomial.C f).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ d.support, (f i ^ d i).totalDegree) ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private def affinePullback {κ : Type*} (p : MvPolynomial κ ℝ) (a : κ → ℝ)
    (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) : MvPolynomial ι ℝ :=
  p.eval₂ MvPolynomial.C (fun j => MvPolynomial.C (a j) +
    affineLinearPolynomial 0 ((ContinuousLinearMap.proj j).comp A))

private theorem eval_affinePullback {κ : Type*} (p : MvPolynomial κ ℝ)
    (a : κ → ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : ι → ℝ) :
    MvPolynomial.eval x (affinePullback p a A) = MvPolynomial.eval (a + A x) p := by
  rw [affinePullback, MvPolynomial.eval_eval₂]
  congr 1
  · ext r
    simp
  · funext j
    simp [eval_affineLinearPolynomial]

private theorem affinePullback_degree {κ : Type*} (p : MvPolynomial κ ℝ)
    (a : κ → ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) :
    (affinePullback p a A).totalDegree ≤ p.totalDegree := by
  apply substitution_degree
  intro j
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp

/-- Homogenization uses a linear normalization and a linear kernel chart.
The formula is polynomial on the whole carrier, including normalization zero. -/
private def chartHomogenize {κ : Type*} (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) : MvPolynomial ι ℝ :=
  ∑ k ∈ Finset.range (p.totalDegree + 1),
    affineLinearPolynomial 0 u ^ (p.totalDegree - k) *
      affinePullback (MvPolynomial.homogeneousComponent k p) 0 A

private theorem chartHomogenize_homogeneous {κ : Type*} (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) :
    (chartHomogenize p u A).IsHomogeneous p.totalDegree := by
  classical
  have hlin : ∀ L : (ι → ℝ) →L[ℝ] ℝ,
      (affineLinearPolynomial 0 L).IsHomogeneous 1 := by
    intro L
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa using MvPolynomial.isHomogeneous_C_mul_X (L (Pi.single i 1)) i
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hk : k ≤ p.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hcomp : (affinePullback (MvPolynomial.homogeneousComponent k p) 0 A).IsHomogeneous k := by
    simpa [affinePullback] using
      (MvPolynomial.homogeneousComponent_isHomogeneous k p).eval₂ MvPolynomial.C
        (fun j => affineLinearPolynomial 0 ((ContinuousLinearMap.proj j).comp A))
        (fun r => MvPolynomial.isHomogeneous_C ι r)
        (fun j => hlin _)
  simpa [Nat.sub_add_cancel hk] using ((hlin u).pow (p.totalDegree - k)).mul hcomp

private theorem eval_chartHomogenize {κ : Type*} [Fintype κ] (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (x : ι → ℝ) (hx : u x ≠ 0) :
    MvPolynomial.eval x (chartHomogenize p u A) =
      u x ^ p.totalDegree * MvPolynomial.eval ((u x)⁻¹ • A x) p := by
  classical
  have hsum : MvPolynomial.eval ((u x)⁻¹ • A x) p =
      ∑ k ∈ Finset.range (p.totalDegree + 1),
        MvPolynomial.eval ((u x)⁻¹ • A x) (MvPolynomial.homogeneousComponent k p) := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  rw [chartHomogenize, map_sum, hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : k ≤ p.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, eval_affineLinearPolynomial, sub_zero, eval_affinePullback,
    zero_add, homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous k p)]
  rw [← mul_assoc]
  congr 1
  rw [inv_pow, pow_sub₀ _ hx hk]

private theorem homogeneous_restriction_ne_zero {κ : Type*} [Fintype κ]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) {d : ℕ} (hhom : p.IsHomogeneous d)
    (u : (ι → ℝ) →L[ℝ] ℝ) (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hdecomp : ∀ x, J (A x) = x - u x • b) :
    affinePullback p b J ≠ 0 := by
  intro hf
  have hnon : ∀ x : ι → ℝ, u x ≠ 0 → MvPolynomial.eval x p = 0 := by
    intro x hx
    have heval := eval_affinePullback p b J ((u x)⁻¹ • A x)
    have heq : b + J ((u x)⁻¹ • A x) = (u x)⁻¹ • x := by
      rw [map_smul, hdecomp, smul_sub, smul_smul, inv_mul_cancel₀ hx, one_smul]
      module
    rw [hf, map_zero, heq, homogeneous_eval_smul p hhom] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left (pow_ne_zero _ (inv_ne_zero hx))
  apply hp
  apply MvPolynomial.funext
  intro x
  by_cases hx : u x ≠ 0
  · simpa using hnon x hx
  · have hx : u x = 0 := not_ne_iff.mp hx
    have hline : linePolynomial p x b = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Ioi_infinite (0 : ℝ)).mono
      intro t ht
      change (linePolynomial p x b).eval t = 0
      rw [eval_linePolynomial]
      apply hnon
      simpa [map_add, map_smul, hx, hb] using ht.ne'
    have hh := congrArg (fun q : Polynomial ℝ => q.eval 0) hline
    simpa [eval_linePolynomial] using hh

private theorem chartHomogenize_section {κ : Type*} [Fintype κ] (p : MvPolynomial κ ℝ)
    (u : (ι → ℝ) →L[ℝ] ℝ) (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hJ : ∀ v, u (J v) = 0) (hAb : A b = 0) (hAJ : ∀ v, A (J v) = v)
    (v : κ → ℝ) :
    MvPolynomial.eval (b + J v) (chartHomogenize p u A) = MvPolynomial.eval v p := by
  have hu : u (b + J v) = 1 := by simp [hb, hJ]
  rw [eval_chartHomogenize p u A _ (by rw [hu]; norm_num)]
  simp [hu, map_add, hAb, hAJ]

private theorem chartHomogenize_ne_zero {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (hp : p ≠ 0)
    (u : (ι → ℝ) →L[ℝ] ℝ) (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hJ : ∀ v, u (J v) = 0) (hAb : A b = 0) (hAJ : ∀ v, A (J v) = v) :
    chartHomogenize p u A ≠ 0 := by
  intro h
  apply hp
  apply MvPolynomial.funext
  intro v
  have hh := chartHomogenize_section p u b hb J A hJ hAb hAJ v
  simpa [h] using hh.symm

private theorem chart_boundary_lift {κ : Type*} [Fintype κ]
    (C : ProperCone ℝ (ι → ℝ))
    (u : (ι → ℝ) →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hdecomp : ∀ x, J (A x) = x - u x • b)
    (hfront : ∀ v, v ∈ frontier {v : κ → ℝ | b + J v ∈ C} ↔
      b + J v ∈ frontier (C : Set (ι → ℝ)))
    (g : MvPolynomial κ ℝ) (hd : 0 < g.totalDegree)
    (hgv : ∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v g = 0) :
    ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y (chartHomogenize g u A) = 0 := by
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    have hh := homogeneous_eval_smul (chartHomogenize g u A)
      (chartHomogenize_homogeneous g u A) 0 b
    simpa [hd.ne'] using hh
  · have huy : 0 < u y := hu y ((C.isClosed.frontier_eq ▸ hy).1) hy0
    have hnorm : (u y)⁻¹ • y ∈ frontier (C : Set (ι → ℝ)) :=
      cone_frontier_smul C (inv_pos.mpr huy) hy
    have heq : b + J ((u y)⁻¹ • A y) = (u y)⁻¹ • y := by
      rw [map_smul, hdecomp, smul_sub, smul_smul, inv_mul_cancel₀ huy.ne', one_smul]
      module
    have hv := hgv ((u y)⁻¹ • A y) ((hfront _).mpr (heq.symm ▸ hnorm))
    rw [eval_chartHomogenize g u A y huy.ne', hv, mul_zero]

private theorem chart_minimum_correspondence {κ : Type*} [Fintype κ]
    (C : ProperCone ℝ (ι → ℝ))
    (u : (ι → ℝ) →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (b : ι → ℝ) (hb : u b = 1)
    (J : (κ → ℝ) →L[ℝ] (ι → ℝ)) (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hJ : ∀ v, u (J v) = 0) (hAb : A b = 0) (hAJ : ∀ v, A (J v) = v)
    (hdecomp : ∀ x, J (A x) = x - u x • b)
    (hfront : ∀ v, v ∈ frontier {v : κ → ℝ | b + J v ∈ C} ↔
      b + J v ∈ frontier (C : Set (ι → ℝ)))
    (hne : (frontier {v : κ → ℝ | b + J v ∈ C}).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) {d : ℕ} (hhom : p.IsHomogeneous d)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    let f := affinePullback p b J
    f ≠ 0 ∧ f.totalDegree = p.totalDegree ∧
      (∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v f = 0) ∧
      ∀ g : MvPolynomial κ ℝ, g ≠ 0 →
        (∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v g = 0) →
          f.totalDegree ≤ g.totalDegree := by
  dsimp only
  have hf : affinePullback p b J ≠ 0 :=
    homogeneous_restriction_ne_zero p hp hhom u b hb J A hdecomp
  have hfv : ∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C},
      MvPolynomial.eval v (affinePullback p b J) = 0 := by
    intro v hv
    rw [eval_affinePullback]
    exact hvan _ ((hfront v).mp hv)
  have hbound : ∀ g : MvPolynomial κ ℝ, g ≠ 0 →
      (∀ v ∈ frontier {v : κ → ℝ | b + J v ∈ C}, MvPolynomial.eval v g = 0) →
        p.totalDegree ≤ g.totalDegree := by
    intro g hg hgv
    have hgpos : 0 < g.totalDegree := by
      by_contra! h
      have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
      obtain ⟨v, hv⟩ := hne
      have hh := hgv v hv
      rw [heq, MvPolynomial.eval_C] at hh
      exact hg (heq.trans (by rw [hh, map_zero]))
    have hG := chartHomogenize_ne_zero g hg u b hb J A hJ hAb hAJ
    have hGd := (chartHomogenize_homogeneous g u A).totalDegree hG
    rw [← hGd]
    exact hmin _ hG (chart_boundary_lift C u hu b hb J A hdecomp hfront g hgpos hgv)
  have hdeg := (hbound _ hf hfv).antisymm (affinePullback_degree p b J)
  exact ⟨hf, hdeg.symm, hfv, fun g hg hgv => hdeg.symm.trans_le (hbound g hg hgv)⟩

private theorem minimum_equation_squarefree (S : Set (ι → ℝ))
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ S, MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ S, MvPolynomial.eval y q = 0) → p.totalDegree ≤ q.totalDegree) :
    Squarefree p := by
  intro a ha
  obtain ⟨r, hpr⟩ := ha
  have ha0 : a ≠ 0 := by
    intro h
    exact hp (by simp [h] at hpr ⊢; exact hpr)
  have hr0 : r ≠ 0 := by
    intro h
    exact hp (by simpa [h] using hpr)
  have hdeg : p.totalDegree = 2 * a.totalDegree + r.totalDegree := by
    rw [hpr, MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero ha0 ha0) hr0,
      MvPolynomial.totalDegree_mul_of_isDomain ha0 ha0]
    omega
  have har : ∀ y ∈ S, MvPolynomial.eval y (a * r) = 0 := by
    intro y hy
    have hh := hvan y hy
    rw [hpr, map_mul, map_mul] at hh
    rw [map_mul]
    rcases mul_eq_zero.mp hh with h | h
    · exact mul_eq_zero.mpr (Or.inl ((mul_self_eq_zero.mp h)))
    · exact mul_eq_zero.mpr (Or.inr h)
  have hm := hmin (a * r) (mul_ne_zero ha0 hr0) har
  rw [MvPolynomial.totalDegree_mul_of_isDomain ha0 hr0, hdeg] at hm
  have hda : a.totalDegree = 0 := by omega
  have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hda
  have hc : a.coeff 0 ≠ 0 := by
    intro h
    exact ha0 (heq.trans (by rw [h, map_zero]))
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

private theorem exists_homogeneous_minimum [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) ∧
      ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
          q.totalDegree ≤ r.totalDegree := by
  classical
  have hex : ∃ d : ℕ, ∃ f : MvPolynomial ι ℝ, f ≠ 0 ∧ f.totalDegree = d ∧
      ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y f = 0 :=
    ⟨p.totalDegree, p, hp, rfl, hvan⟩
  obtain ⟨f, hf, hfd, hfv⟩ := Nat.find_spec hex
  have hmin : ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
        f.totalDegree ≤ r.totalDegree := by
    intro r hr hrv
    rw [hfd]
    exact Nat.find_min' hex ⟨r, hr, rfl, hrv⟩
  obtain ⟨d, q, hd, hdf, hq, hhom, hqv⟩ := cone_boundary_homogeneous_equation
    (ContinuousLinearEquiv.refl ℝ (ι → ℝ)) C hs f hf hfv
  have hqd := hhom.totalDegree hq
  have hqmin : ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
        q.totalDegree ≤ r.totalDegree := by
    intro r hr hrv
    rw [hqd]
    exact hdf.trans (hmin r hr hrv)
  exact ⟨d, q, hd, hdf.trans (hmin p hp hvan), hq, hhom,
    minimum_equation_squarefree _ q hq hqv hqmin, hqv, hqmin⟩


end D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation
