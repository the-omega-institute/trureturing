/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalTorusResultants
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalTorusResultants
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Nonzero Laurent resultants in the two different coordinates exclude a height-one torus prime. -/
import D5.S3.Quantum.TensorNetworks.UniformHorizontalTwoProjections
import Mathlib.Algebra.Polynomial.Laurent

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHorizontalTorusResultants

open Polynomial UniformHorizontalTwoProjections

noncomputable section

variable {K : Type*} [Field K]
variable {S : Type*} [CommRing S]

/-- A fixed-degree resultant lies in the ideal whenever the two polynomials
vanish modulo that ideal at a common element. -/
theorem resultant_mem_of_eval₂_mem {R : Type*} [CommRing R] (I : Ideal S)
    (f : R →+* S) (t : S) {p q : R[X]} {d e : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e) (hde : d ≠ 0 ∨ e ≠ 0)
    (h₁ : p.eval₂ f t ∈ I) (h₂ : q.eval₂ f t ∈ I) :
    f (p.resultant q d e) ∈ I := by
  obtain ⟨a, b, _, _, h⟩ := exists_mul_add_mul_eq_C_resultant p q hp hq hde
  have h' := congrArg (eval₂RingHom f t) h
  simp only [map_add, map_mul, coe_eval₂RingHom, eval₂_C] at h'
  rw [← h']
  exact I.add_mem (I.mul_mem_right _ h₁) (I.mul_mem_right _ h₂)

private def univariate (i : Fin 2) : K[X] →+* Bivariate K :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X i)

private abbrev Coeff (K : Type*) [Field K] := FractionRing (MvPolynomial (Fin 1) K)

private def coeffConst : K →+* Coeff K :=
  (algebraMap (MvPolynomial (Fin 1) K) _).comp MvPolynomial.C

private def coeffVar : Coeff K :=
  algebraMap (MvPolynomial (Fin 1) K) _ (MvPolynomial.X 0)

private theorem projection_univariate_hom (i j : Fin 2) :
    (projection (K := K) i).comp (univariate j) =
      if i = j then mapRingHom coeffConst else
        C.comp (eval₂RingHom coeffConst coeffVar) := by
  apply Polynomial.ringHom_ext
  · intro a
    fin_cases i <;> fin_cases j <;>
      simp [univariate, projection, coeffConst, MvPolynomial.finSuccEquiv_apply]
  · fin_cases i <;> fin_cases j <;>
      norm_num [univariate, projection, coeffVar, Equiv.swap_apply_def,
        MvPolynomial.finSuccEquiv_apply] <;>
      rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide, Fin.cases_succ, map_C]

private theorem coeff_eval₂_ne_zero {p : K[X]} (h : p ≠ 0) :
    p.eval₂ coeffConst coeffVar ≠ 0 := by
  let e := (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm
  have he : (eval₂RingHom coeffConst coeffVar : K[X] →+* Coeff K) =
      (algebraMap (MvPolynomial (Fin 1) K) _).comp e.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
      change coeffConst a = algebraMap (MvPolynomial (Fin 1) K) _ (e (C a))
      rw [show e (C a) = MvPolynomial.C a from e.commutes a]
      rfl
    · simp only [coe_eval₂RingHom, eval₂_X, RingHom.comp_apply]
      change coeffVar = algebraMap (MvPolynomial (Fin 1) K) _ (e X)
      unfold coeffVar
      apply congrArg (algebraMap (MvPolynomial (Fin 1) K) (Coeff K))
      apply (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective
      simp [e, MvPolynomial.uniqueAlgEquiv_apply]
  change eval₂RingHom coeffConst coeffVar p ≠ 0
  rw [he]
  change (algebraMap (MvPolynomial (Fin 1) K) (Coeff K)) (e p) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 1) K) (Coeff K))).mpr
    (fun hz => h (e.injective (hz.trans (map_zero e).symm)))

private theorem projectedResultants_univariate {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ProjectedResultants (univariate 0 p) (univariate 1 q) := by
  have h₀ (j : Fin 2) (r : K[X]) :
      projection j (univariate j r) = r.map coeffConst := by
    simpa only [ite_true, RingHom.comp_apply, coe_mapRingHom] using
      DFunLike.congr_fun (projection_univariate_hom j j) r
  have h₁ (i j : Fin 2) (h : i ≠ j) (r : K[X]) :
      projection i (univariate j r) = C (r.eval₂ coeffConst coeffVar) := by
    simpa only [ite_eq_right h, RingHom.comp_apply, coe_eval₂RingHom] using
      DFunLike.congr_fun (projection_univariate_hom i j) r
  intro i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
  rcases hi with rfl | rfl
  · refine ⟨p.map coeffConst, C (q.eval₂ coeffConst coeffVar), 0, 0, max 1 p.natDegree,
      0, natDegree_map_le.trans (le_max_right _ _), by simp, Or.inl (by simp), ?_, ?_, ?_⟩
    · simpa only [resultant_C_zero_right] using pow_ne_zero _ (coeff_eval₂_ne_zero hq)
    · simpa only [pow_zero, one_mul] using h₀ 0 p
    · simpa only [pow_zero, one_mul] using h₁ 0 1 (by decide) q
  · refine ⟨C (p.eval₂ coeffConst coeffVar), q.map coeffConst, 0, 0, 0,
      max 1 q.natDegree, by simp, natDegree_map_le.trans (le_max_right _ _),
      Or.inr (by simp), ?_, ?_, ?_⟩
    · simpa only [resultant_C_zero_left] using pow_ne_zero _ (coeff_eval₂_ne_zero hp)
    · simpa only [pow_zero, one_mul] using h₁ 1 0 (by decide) p
    · simpa only [pow_zero, one_mul] using h₀ 1 q

private theorem univariate_mem_of_laurent_mem [Algebra (Bivariate K) S]
    (c : K →+* S) (ts : Fin 2 → Sˣ)
    (hc : ∀ a, algebraMap (Bivariate K) S (MvPolynomial.C a) = c a)
    (ht : ∀ j, algebraMap (Bivariate K) S (MvPolynomial.X j) = (ts j : S))
    (I : Ideal S) (j : Fin 2) {r : LaurentPolynomial K} (hr : r ≠ 0)
    (hm : LaurentPolynomial.eval₂ c (ts j) r ∈ I) :
    ∃ q : K[X], q ≠ 0 ∧ algebraMap (Bivariate K) S (univariate j q) ∈ I := by
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow r
  refine ⟨q, ?_, ?_⟩
  · intro hzero
    rw [hzero, map_zero] at hq
    apply hr
    exact (LaurentPolynomial.isUnit_T (n : ℤ)).mul_right_cancel
      (by simpa only [zero_mul] using hq.symm)
  have he : (algebraMap (Bivariate K) S).comp (univariate j) =
      eval₂RingHom c (ts j : S) := by
    apply Polynomial.ringHom_ext
    · simp [univariate, hc]
    · simpa [univariate] using ht j
  change ((algebraMap (Bivariate K) S).comp (univariate j)) q ∈ I
  rw [he]
  change q.eval₂ c (ts j : S) ∈ I
  rw [← LaurentPolynomial.eval₂_toLaurent c (ts j) q, hq, map_mul]
  exact I.mul_mem_right _ hm

/-- A height-one torus prime cannot contain nonzero Laurent polynomials
in the two different coordinates. The original projected-resultant
exclusion applies after clearing their Laurent denominators. -/
theorem height_one_torus_prime_cannot_contain_axis_resultants
    [Algebra (Bivariate K) S]
    [IsLocalization.Away ((MvPolynomial.X 0 : Bivariate K) * MvPolynomial.X 1) S]
    (c : K →+* S) (ts : Fin 2 → Sˣ)
    (hc : ∀ a, algebraMap (Bivariate K) S (MvPolynomial.C a) = c a)
    (ht : ∀ j, algebraMap (Bivariate K) S (MvPolynomial.X j) = (ts j : S))
    (I : Ideal S) [I.IsPrime] (hh : I.height = 1)
    (r s : LaurentPolynomial K) (hr : r ≠ 0) (hs : s ≠ 0)
    (h₀ : LaurentPolynomial.eval₂ c (ts 0) r ∈ I)
    (h₁ : LaurentPolynomial.eval₂ c (ts 1) s ∈ I) : False := by
  obtain ⟨p, hp, hpI⟩ := univariate_mem_of_laurent_mem c ts hc ht I 0 hr h₀
  obtain ⟨q, hq, hqI⟩ := univariate_mem_of_laurent_mem c ts hc ht I 1 hs h₁
  exact height_one_torus_prime_cannot_contain_pair I hh hpI hqI
    (projectedResultants_univariate hp hq)

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHorizontalTorusResultants
