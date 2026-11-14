/- GID: D5/S3/Geometry/AlgebraicBoundary/BoundaryPrincipalIdeal
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/BoundaryPrincipalIdeal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous entire-boundary minima divide all finite-degree boundary equations. -/

import D5.S3.Geometry.AlgebraicBoundary.BoundaryCoordinates
import Mathlib.RingTheory.Radical.Basic

/-! Entire-boundary divisibility uses actual constructed transverse coordinates. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal

open private polynomialCoordinates eval_polynomialCoordinates exists_transverse_coordinates
  from D5.S3.Geometry.AlgebraicBoundary.BoundaryCoordinates
open private visible_irreducible_factor_dvd
  from D5.S3.Geometry.AlgebraicBoundary.BoundaryElimination
open private homogeneous_eval_smul linePolynomial eval_linePolynomial linePolynomial_top_coeff
  from D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor
open private minimum_equation_squarefree
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

universe u
variable {ι : Type u} [Fintype ι]

private theorem minimum_boundary_ideal
    (C : ProperCone ℝ (ι → ℝ)) (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (q : MvPolynomial ι ℝ) (hq : q ≠ 0) {d : ℕ} (hd : 0 < d)
    (hhom : q.IsHomogeneous d)
    (hqv : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0)
    (hmin : ∀ r : MvPolynomial ι ℝ, r ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
        q.totalDegree ≤ r.totalDegree) :
    ∀ r : MvPolynomial ι ℝ,
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) ↔ q ∣ r := by
  classical
  letI : StrongNormalizationMonoid (MvPolynomial ι ℝ) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨e, he, hqe⟩ : ∃ e ∈ interior (C : Set (ι → ℝ)), MvPolynomial.eval e q ≠ 0 := by
    by_contra! hn
    obtain ⟨a, ha⟩ := hfull
    obtain ⟨I, s, hs, hsU⟩ := isOpen_pi_iff.mp isOpen_interior a ha
    let T (i : ι) : Set ℝ := if i ∈ I then s i else univ
    have hT (i : ι) : (T i).Infinite := by
      by_cases hi : i ∈ I
      · exact infinite_of_mem_nhds (a i) (by simpa [T, hi] using
          ((hs i hi).1.mem_nhds (hs i hi).2))
      · simpa [T, hi] using infinite_univ (α := ℝ)
    have hTU : univ.pi T ⊆ interior (C : Set (ι → ℝ)) := by
      simpa only [T, ← Finset.mem_coe, univ_pi_ite] using hsU
    apply hq
    apply MvPolynomial.funext_set T hT
    intro x hx
    simpa using hn x (hTU hx)
  have he0 : e ≠ 0 := by
    intro h
    have hv := homogeneous_eval_smul q hhom 0 e
    have hz : MvPolynomial.eval (0 : ι → ℝ) q = 0 := by
      simpa [zero_pow (Nat.ne_of_gt hd)] using hv
    exact hqe (by simpa [h] using hz)
  obtain ⟨κ, instκ, c, u, π, J, hue, hπe, huJ, hπJ, hc, hcs⟩ :=
    exists_transverse_coordinates e he0
  letI := instκ
  let F : MvPolynomial ι ℝ ≃+* Polynomial (MvPolynomial κ ℝ) :=
    (polynomialCoordinates c).trans (MvPolynomial.optionEquivLeft ℝ κ).toRingEquiv
  have hFeval : ∀ (p : MvPolynomial ι ℝ) (x : ι → ℝ),
      (F p).eval₂ (MvPolynomial.eval (π x)) (u x) = MvPolynomial.eval x p := by
    intro p x
    rw [← Polynomial.eval_map]
    change Polynomial.eval (u x)
      (Polynomial.map (MvPolynomial.eval (π x))
        (MvPolynomial.optionEquivLeft ℝ κ (polynomialCoordinates c p))) = _
    rw [← MvPolynomial.optionEquivLeft_elim_eval, ← hcs,
      eval_polynomialCoordinates, c.apply_symm_apply]
  have hline : ∀ v : κ → ℝ,
      (F q).map (MvPolynomial.eval v) = linePolynomial q (J v) e := by
    intro v
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_map, eval_linePolynomial]
    simpa [map_add, map_smul, hπJ, hπe, huJ, hue] using hFeval q (J v + t • e)
  have hcoef : (F q).coeff d = MvPolynomial.C (MvPolynomial.eval e q) := by
    apply MvPolynomial.funext
    intro v
    have hv := congrArg (fun p : Polynomial ℝ => p.coeff d) (hline v)
    simpa [Polynomial.coeff_map, linePolynomial_top_coeff q hhom] using hv
  have hfactors : ∀ f : MvPolynomial ι ℝ, Irreducible f → f ∣ q →
      ∀ r : MvPolynomial ι ℝ,
        (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0) → f ∣ r := by
    intro f hf hfd r hrv
    obtain ⟨g, hqfg⟩ := hfd
    have hg : g ≠ 0 := by intro h; exact hq (by simpa [h] using hqfg)
    have hz : ∃ z ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval z g ≠ 0 := by
      by_contra! hn
      have hm := hmin g hg hn
      have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hf.ne_zero hg
      rw [← hqfg] at hdeg
      have hfd0 : f.totalDegree = 0 := by omega
      have hfc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hfd0
      have hf0 : f.coeff 0 ≠ 0 := by
        intro h
        exact hf.ne_zero (hfc.trans (by rw [h, map_zero]))
      apply hf.not_isUnit
      rw [hfc]
      exact (isUnit_iff_ne_zero.mpr hf0).map MvPolynomial.C
    obtain ⟨z, hzf, hgz⟩ := hz
    have hFi : Irreducible (F f) := (MulEquiv.irreducible_iff F).mpr hf
    have hFd : (F f).natDegree ≠ 0 := by
      intro hzero
      have hfc : F f = Polynomial.C ((F f).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hzero
      have hcf := congrArg (fun p : Polynomial (MvPolynomial κ ℝ) => p.coeff d)
        (congrArg F hqfg)
      rw [map_mul, hfc, Polynomial.coeff_C_mul, hcoef] at hcf
      have hunit : IsUnit ((F f).coeff 0 * (F g).coeff d) := by
        rw [← hcf]
        exact (isUnit_iff_ne_zero.mpr hqe).map MvPolynomial.C
      apply hFi.not_isUnit
      rw [hfc]
      exact Polynomial.isUnit_C.mpr (isUnit_of_mul_isUnit_left hunit)
    have hdiv := visible_irreducible_factor_dvd C he hzf π J hπe hπJ u (F f) (F r)
      hFi hFd (fun y => MvPolynomial.eval y g) (MvPolynomial.continuous_eval g) hgz
      (by intro y hy; rw [hFeval]; simpa [hqfg, map_mul] using hqv y hy)
      (by intro y hy; rw [hFeval]; exact hrv y hy)
    exact (map_dvd_iff F).mp hdiv
  intro r
  constructor
  · intro hrv
    by_cases hr : r = 0
    · simp [hr]
    have hsq := minimum_equation_squarefree _ q hq hqv hmin
    apply (hsq.isRadical.dvd_radical hq).trans
    apply (UniqueFactorizationMonoid.radical_dvd_iff_primeFactors_subset hr).mpr
    intro f hf
    have hff := (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hq).mp
      (UniqueFactorizationMonoid.mem_primeFactors.mp hf)
    apply UniqueFactorizationMonoid.mem_primeFactors.mpr
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hr).mpr
      ⟨hff.1, hff.2.1, hfactors f hff.1 hff.2.2 r hrv⟩
  · rintro ⟨g, rfl⟩ y hy
    simp [hqv y hy]

end D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal
