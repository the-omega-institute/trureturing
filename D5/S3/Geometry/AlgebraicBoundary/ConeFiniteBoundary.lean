/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeFiniteBoundary
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeFiniteBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-degree entire-boundary minima retain the original principal ideal and scalar uniqueness. -/

import D5.S3.Geometry.AlgebraicBoundary.BoundarySemialgebraic
import D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal

/-! Entire-boundary generators retain all homogeneous factors in arbitrary degree. -/

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

private def degreeExpansion {σ R : Type*} [CommRing R] :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

private theorem degreeExpansion_monomial {σ R : Type*} [CommRing R]
    (s : σ →₀ ℕ) (r : R) :
    degreeExpansion (MvPolynomial.monomial s r) =
      Polynomial.monomial s.degree (MvPolynomial.monomial s r) := by
  classical
  change MvPolynomial.eval₂Hom _ _ _ = _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    ← Polynomial.C_mul_X_pow_eq_monomial, MvPolynomial.monomial_eq,
    Finsupp.degree_apply, Polynomial.C_mul, mul_assoc]

private theorem degreeExpansion_coeff {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (n : ℕ) :
    (degreeExpansion p).coeff n = MvPolynomial.homogeneousComponent n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s r =>
    rw [degreeExpansion_monomial, MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_monomial r rfl)]
    simp [Polynomial.coeff_monomial, eq_comm]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

private theorem degreeExpansion_homogeneous {σ R : Type*} [CommRing R]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    degreeExpansion p = Polynomial.monomial d p := by
  classical
  ext n
  rw [degreeExpansion_coeff, MvPolynomial.homogeneousComponent_of_mem hp]
  simp [Polynomial.coeff_monomial, eq_comm]

/-- Formal scaling retains each homogeneous component as a coefficient. The extreme
degrees of a product cannot cancel in a domain, including degree-zero factors. -/
private theorem homogeneous_factors {σ R : Type*} [CommRing R] [IsDomain R]
    {p f g : MvPolynomial σ R} {d : ℕ} (hp : p ≠ 0)
    (hhom : p.IsHomogeneous d) (hfg : p = f * g) :
    f ≠ 0 ∧ g ≠ 0 ∧ f.IsHomogeneous f.totalDegree ∧
      g.IsHomogeneous g.totalDegree ∧ f.totalDegree + g.totalDegree = d := by
  classical
  have hf : f ≠ 0 := by intro h; exact hp (by simp [hfg, h])
  have hg : g ≠ 0 := by intro h; exact hp (by simp [hfg, h])
  have hinj : ∀ q : MvPolynomial σ R, degreeExpansion q = 0 → q = 0 := by
    intro q hq
    rw [← MvPolynomial.sum_homogeneousComponent q]
    apply Finset.sum_eq_zero
    intro k hk
    simpa [degreeExpansion_coeff] using congrArg (fun P => Polynomial.coeff P k) hq
  have hF : degreeExpansion f ≠ 0 := fun h => hf (hinj f h)
  have hG : degreeExpansion g ≠ 0 := fun h => hg (hinj g h)
  have hprod : degreeExpansion f * degreeExpansion g = Polynomial.monomial d p := by
    rw [← map_mul, ← hfg, degreeExpansion_homogeneous hhom]
  have htop := congrArg Polynomial.natDegree hprod
  have hbot := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul hF hG, Polynomial.natDegree_monomial,
    ite_eq_right hp] at htop
  rw [Polynomial.natTrailingDegree_mul hF hG, Polynomial.natTrailingDegree_monomial hp] at hbot
  have hFle := Polynomial.natTrailingDegree_le_natDegree (degreeExpansion f)
  have hGle := Polynomial.natTrailingDegree_le_natDegree (degreeExpansion g)
  have hsingle : ∀ q : MvPolynomial σ R,
      (degreeExpansion q).natTrailingDegree = (degreeExpansion q).natDegree →
      q.IsHomogeneous (degreeExpansion q).natDegree := by
    intro q hq s hs
    have hsz : q.coeff s ≠ 0 := hs
    have hk : s.degree = (degreeExpansion q).natDegree := by
      by_contra hn
      have hz : (degreeExpansion q).coeff s.degree = 0 := by
        rcases lt_or_gt_of_ne hn with h | h
        · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt h
      rw [degreeExpansion_coeff] at hz
      have hh := congrArg (fun Q : MvPolynomial σ R => Q.coeff s) hz
      simp only [MvPolynomial.coeff_homogeneousComponent, ite_eq_left rfl,
        AddMonoidAlgebra.coeff_zero, Pi.zero_apply] at hh
      exact hsz hh
    simpa only [Finsupp.degree_eq_weight_one, ← Pi.one_def] using hk
  have hfh := hsingle f (by omega)
  have hgh := hsingle g (by omega)
  refine ⟨hf, hg, ?_, ?_, ?_⟩
  · simpa only [hfh.totalDegree hf] using hfh
  · simpa only [hgh.totalDegree hg] using hgh
  · rw [← hhom.totalDegree hp, hfg, MvPolynomial.totalDegree_mul_of_isDomain hf hg]

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
          ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * q) ∧
      (∀ f g : MvPolynomial ι ℝ, q = f * g →
        f ≠ 0 ∧ g ≠ 0 ∧ f.IsHomogeneous f.totalDegree ∧
          g.IsHomogeneous g.totalDegree ∧ f.totalDegree + g.totalDegree = d) := by
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
    d, q, hd, hdp, hq, hhom, hsq, hqd, (hboundary q).mpr hqv, ?_, ?_, ?_, ?_⟩
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
  · intro f g hfg
    exact homogeneous_factors hq hhom hfg

end D5.S3.Geometry.AlgebraicBoundary.ConeFiniteBoundary
