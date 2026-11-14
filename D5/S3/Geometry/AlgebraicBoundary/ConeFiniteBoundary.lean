/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeFiniteBoundary
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeFiniteBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-degree entire-boundary minima retain the original principal ideal and scalar uniqueness. -/

import D5.S3.Geometry.AlgebraicBoundary.BoundarySemialgebraic
import D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal

noncomputable section
open Set
open scoped Topology
namespace D5.S3.Geometry.AlgebraicBoundary.ConeFiniteBoundary

open private original_cone_semialgebraic
  from D5.S3.Geometry.AlgebraicBoundary.BoundarySemialgebraic
open private exists_homogeneous_minimum
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation
open private minimum_boundary_ideal
  from D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal

variable {ι : Type*} [Fintype ι]

private theorem original_finite_boundary_ideal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (hfull : (interior (C : Set E)).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    (C : Set E) ∈ MeasureTheory.generateSetAlgebra
      (range (fun r : MvPolynomial ι ℝ => {x : E | MvPolynomial.eval (c x) r = 0}) ∪
        range (fun r : MvPolynomial ι ℝ => {x : E | 0 < MvPolynomial.eval (c x) r})) ∧
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧ q.totalDegree = d ∧
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      (∀ r : MvPolynomial ι ℝ,
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ q ∣ r) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 → r.totalDegree ≤ d →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * q) := by
  classical
  letI : Nontrivial (ι → ℝ) := c.toEquiv.symm.nontrivial
  let D := C.comap c.symm.toContinuousLinearMap
  have hi : interior (D : Set (ι → ℝ)) = c.symm ⁻¹' interior (C : Set E) :=
    (c.symm.toHomeomorph.preimage_interior (C : Set E)).symm
  have hf : frontier (D : Set (ι → ℝ)) = c.symm ⁻¹' frontier (C : Set E) :=
    (c.symm.toHomeomorph.preimage_frontier (C : Set E)).symm
  have hsD : (D : ConvexCone ℝ (ι → ℝ)).Salient := by
    intro x hx hx0 hneg
    apply hs (c.symm x) hx
    · intro h
      have hh := congrArg c h
      exact hx0 (by simpa using hh)
    · simpa [D] using hneg
  have hfullD : (interior (D : Set (ι → ℝ))).Nonempty := by
    obtain ⟨a, ha⟩ := hfull
    exact ⟨c a, by simpa [hi] using ha⟩
  have hboundary : ∀ r : MvPolynomial ι ℝ,
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔
        ∀ z ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval z r = 0 := by
    intro r
    constructor
    · intro h z hz
      simpa using h (c.symm z) (by simpa [hf] using hz)
    · intro h y hy
      exact h (c y) (by simpa [hf] using hy)
  obtain ⟨d, q, hd, hdp, hq, hhom, hsq, hqv, hmin⟩ :=
    exists_homogeneous_minimum D hsD p hp ((hboundary p).mp hvan)
  have hqd := hhom.totalDegree hq
  have hideal := minimum_boundary_ideal D hfullD q hq hd hhom hqv hmin
  refine ⟨(original_cone_semialgebraic c C hfull p hp hvan).1,
    d, q, hd, hdp, hq, hhom, hsq, hqd, (hboundary q).mpr hqv, ?_, ?_, ?_⟩
  · intro r hr hrv
    exact hmin r hr ((hboundary r).mp hrv)
  · intro r
    exact (hboundary r).trans (hideal r)
  · intro r hr hrd hrv
    obtain ⟨g, hrg⟩ := (hideal r).mp ((hboundary r).mp hrv)
    have hg : g ≠ 0 := by intro hz; exact hr (by simpa [hz] using hrg)
    have hdeg : r.totalDegree = q.totalDegree + g.totalDegree := by
      rw [hrg, MvPolynomial.totalDegree_mul_of_isDomain hq hg]
    have hgdeg : g.totalDegree = 0 := by omega
    have hgC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hgdeg
    refine ⟨g.coeff 0, ?_, ?_⟩
    · intro hz
      exact hg (by rw [hgC, hz, map_zero])
    · calc
        r = q * g := hrg
        _ = g * q := mul_comm _ _
        _ = MvPolynomial.C (g.coeff 0) * q := congrArg (fun z => z * q) hgC

end D5.S3.Geometry.AlgebraicBoundary.ConeFiniteBoundary
