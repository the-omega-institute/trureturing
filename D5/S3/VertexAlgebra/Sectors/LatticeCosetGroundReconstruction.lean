/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetGroundReconstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetGroundReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native charged coefficients reconstruct from their longitudinal projection and transverse creation. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCreationSeparation

/-! The charged calculation retains the full native integral zero-mode power
and epsilon. The creation-factor split is applied to the finite native
annihilation polynomial. No positivity of the ambient block form is used.
The field convention is Bakalov--Kac, math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetGroundReconstruction

open LatticeGeneratingFieldLocality LatticeActualProductKernel LatticeActualGeneratorLocality
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeCosetCreationSeparation MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private creationCoeff_separation from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCreationSeparation
open private polynomialProjection_injection injection_single projection_single from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

open private mixedState_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private high_modes_finite map_finsum_linear from D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

private theorem convolution_cutoff (F : LatticeData) (α : Charge F)
    (q : Polynomial (Oscillator F)) (s : ℤ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → convolution F α (s-j) q = 0 := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    obtain ⟨N,hN⟩ := hq
    obtain ⟨M,hM⟩ := hr
    exact ⟨max N M, fun j hj => by rw [map_add, hN j (by omega), hM j (by omega), add_zero]⟩
  | monomial k z =>
    refine ⟨(s+k).toNat+1, fun j hj => ?_⟩
    rw [convolution_monomial]
    simp [creationCoeff, show s-(j : ℤ)+k < 0 by omega]

private theorem convolution_separation (b : Fin e → ℤ) (n : Charge D)
    (s : ℤ) (q : Polynomial (Oscillator (ambient D e B C hC hCe))) :
    convolution (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n) s
        (Polynomial.map (longitudinalPolynomial D B C hC hCe).toRingHom q) =
      ∑ᶠ j : ℕ, longitudinalPolynomial D B C hC hCe
          (convolution (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n) (s-j)
            (Polynomial.map (longitudinalPolynomial D B C hC hCe).toRingHom q)) *
        transversePolynomial D B C hC hCe
          (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) b)) := by
  classical
  let F := ambient D e B C hC hCe
  let β := liftCharge D B C hC hCe b n
  let L := longitudinalPolynomial D B C hC hCe
  let T := transversePolynomial D B C hC hCe
  let g := creationExponential (externalLattice C hC hCe) b
  have hL (z : Oscillator F) : L (L z) = L z := by
    dsimp only [L, longitudinalPolynomial, AlgHom.comp_apply]
    rw [polynomialProjection_injection]
  have finite (r : Polynomial (Oscillator F)) : Function.HasFiniteSupport (fun j : ℕ =>
      L (convolution F β (s-j) (Polynomial.map L.toRingHom r)) * T (PowerSeries.coeff j g)) := by
    obtain ⟨N,hN⟩ := convolution_cutoff F β (Polynomial.map L.toRingHom r) s
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    exact hj (by dsimp only; rw [hN j (by omega), map_zero, zero_mul])
  change convolution F β s (Polynomial.map L.toRingHom q) =
    ∑ᶠ j : ℕ, L (convolution F β (s-j) (Polynomial.map L.toRingHom q)) * T (PowerSeries.coeff j g)
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [Polynomial.map_add, map_add, add_mul]
    rw [hq, hr, finsum_add_distrib (finite q) (finite r)]
  | monomial k z =>
    simp only [Polynomial.map_monomial, convolution_monomial, map_mul, hL]
    have hc := creationCoeff_separation D B C hC hCe b n (s+k)
    change creationCoeff F β (s+k) =
      ∑ᶠ j : ℕ, L (creationCoeff F β (s+k-j)) * T (PowerSeries.coeff j g) at hc
    rw [hc]
    have hf : Function.HasFiniteSupport (fun j : ℕ =>
        L (creationCoeff F β (s+k-j)) * T (PowerSeries.coeff j g)) := by
      apply (Finset.finite_toSet (Finset.range ((s+k).toNat+1))).subset
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hn
      exact hj (by simp [creationCoeff, show s+k-(j : ℤ) < 0 by omega])
    change L z * (∑ᶠ j : ℕ, L (creationCoeff F β (s+k-j)) * T (PowerSeries.coeff j g)) =
      ∑ᶠ j : ℕ, L (L z) * L (creationCoeff F β (s-j+k)) * T (PowerSeries.coeff j g)
    rw [hL, ← LinearMap.mulLeft_apply ℂ (L z),
      map_finsum_linear (LinearMap.mulLeft ℂ (L z)) _ hf]
    apply finsum_congr
    intro j
    change L z * (L (creationCoeff F β (s+k-j)) * T (PowerSeries.coeff j g)) =
      (L z * L (creationCoeff F β (s-j+k))) * T (PowerSeries.coeff j g)
    rw [show s+k-(j : ℤ) = s-j+k by omega, mul_assoc]

private theorem translated_injection_longitudinal (a : Fin e → ℤ) (n : Charge D)
    (f : Oscillator D) :
    Polynomial.map (longitudinalPolynomial D B C hC hCe).toRingHom
        (translatedPolynomial (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
          (polynomialInjection D B C hC hCe f)) =
      translatedPolynomial (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (polynomialInjection D B C hC hCe f) := by
  let α := liftCharge D B C hC hCe a n
  let F := ambient D e B C hC hCe
  let L := longitudinalPolynomial D B C hC hCe
  let tr : Oscillator F →ₐ[ℂ] Polynomial (Oscillator F) :=
    aeval (fun x : Index F => translationVariable F α x.1 x.2)
  have he : ((Polynomial.mapAlgHom L).comp tr).comp (polynomialInjection D B C hC hCe) =
      tr.comp (polynomialInjection D B C hC hCe) := by
    apply MvPolynomial.algHom_ext
    intro x
    change Polynomial.map L.toRingHom (tr (polynomialInjection D B C hC hCe (X x))) =
      tr (polynomialInjection D B C hC hCe (X x))
    rw [show polynomialInjection D B C hC hCe (X x) = X (x.1.castAdd e, x.2) by
      simp [polynomialInjection] ]
    simp only [tr, aeval_X]
    simp [L, translationVariable, longitudinalPolynomial, polynomialProjection,
      projectionVariable, polynomialInjection, MvPolynomial.smul_eq_C_mul]
    rw [Polynomial.map_C]
    congr 1
    change polynomialInjection D B C hC hCe
      (polynomialProjection D B C hC hCe (X (x.1.castAdd e, x.2))) = _
    simp [polynomialProjection, projectionVariable, polynomialInjection]
  exact DFunLike.congr_fun he f

private theorem projection_lift_single (d : Fin e → ℤ) (n : Charge D)
    (f : Oscillator (ambient D e B C hC hCe)) :
    projection D B C hC hCe d (Finsupp.single (liftCharge D B C hC hCe d n) f) =
      Finsupp.single n (polynomialProjection D B C hC hCe f) := by
  have he : externalCharge D B C hC hCe (liftCharge D B C hC hCe d n) = d := by
    funext i
    simp [externalCharge, liftCharge]
  have ho : oldCharge D B C hC hCe (liftCharge D B C hC hCe d n) = n := by
    funext i
    simp [oldCharge, liftCharge]
  simp [projection_single, he, ho]

/-- Every native charged ground field on an arbitrary injected target state
reconstructs from its actual projected coefficients and transverse creation.
This is the charged base of the all-source normal-product induction. -/
theorem ground_reconstruction (a d : Fin e → ℤ) (n : Charge D)
    (m : ℤ) (g : Carrier D) :
    ((actualField (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n))[[m]])
        (injection D B C hC hCe d g) =
      ∑ᶠ j : ℕ, mixedState D B C hC hCe (a+d)
        (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) a))
        (projection D B C hC hCe (a+d)
          (((actualField (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n))[[m+j]])
            (injection D B C hC hCe d g))) := by
  classical
  let F := ambient D e B C hC hCe
  let α := liftCharge D B C hC hCe a n
  let L := longitudinalPolynomial D B C hC hCe
  let T := transversePolynomial D B C hC hCe
  let h := creationExponential (externalLattice C hC hCe) a
  have finite (m : ℤ) (g : Carrier D) : Function.HasFiniteSupport (fun j : ℕ =>
      mixedState D B C hC hCe (a+d) (PowerSeries.coeff j h)
        (projection D B C hC hCe (a+d)
          (((actualField F α)[[m+j]]) (injection D B C hC hCe d g)))) :=
    high_modes_finite (actualField F α)
      (fun j => (mixedState D B C hC hCe (a+d) (PowerSeries.coeff j h)).comp
        (projection D B C hC hCe (a+d))) m (injection D B C hC hCe d g)
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' =>
    simp only [map_add]
    rw [hg, hg', finsum_add_distrib (finite m g) (finite m g')]
  | single r f =>
    let δ := liftCharge D B C hC hCe d r
    let q := translatedPolynomial F α (polynomialInjection D B C hC hCe f)
    let s := -m-1-bilinear F α δ
    have hcharge : α+δ = liftCharge D B C hC hCe (a+d) (n+r) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp [α, δ, liftCharge]
    have hraw (t : ℤ) : ((actualField F α)[[t]])
        (injection D B C hC hCe d (Finsupp.single r f)) =
        epsilon F α δ • Finsupp.single (liftCharge D B C hC hCe (a+d) (n+r))
          (convolution F α (-t-1-bilinear F α δ) q) := by
      rw [injection_single, actual_modes, raw_single_convolution, hcharge]
    have hc := convolution_separation D B C hC hCe a n s q
    rw [translated_injection_longitudinal D B C hC hCe a n f] at hc
    change convolution F α s q = ∑ᶠ j : ℕ,
      L (convolution F α (s-j) q) * T (PowerSeries.coeff j h) at hc
    have hs : Function.HasFiniteSupport (fun j : ℕ =>
        L (convolution F α (s-j) q) * T (PowerSeries.coeff j h)) := by
      obtain ⟨N,hN⟩ := convolution_cutoff F α q s
      apply (Finset.finite_toSet (Finset.range N)).subset
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hn
      exact hj (by dsimp only; rw [hN j (by omega), map_zero, zero_mul])
    change ((actualField F α)[[m]]) (injection D B C hC hCe d (Finsupp.single r f)) =
      ∑ᶠ j : ℕ, mixedState D B C hC hCe (a+d) (PowerSeries.coeff j h)
        (projection D B C hC hCe (a+d) (((actualField F α)[[m+j]])
          (injection D B C hC hCe d (Finsupp.single r f))))
    simp only [hraw, map_smul,
      projection_lift_single D B C hC hCe (a+d) (n+r),
      mixedState_single D B C hC hCe (a+d)]
    let S : Oscillator F →ₗ[ℂ] Carrier F :=
      epsilon F α δ • Finsupp.lsingle (liftCharge D B C hC hCe (a+d) (n+r))
    change S (convolution F α s q) = ∑ᶠ j : ℕ,
      S (L (convolution F α (-(m+j)-1-bilinear F α δ) q) * T (PowerSeries.coeff j h))
    have hm (j : ℕ) : -(m+(j : ℤ))-1-bilinear F α δ = s-j := by dsimp only [s]; omega
    simp_rw [hm]
    rw [hc, map_finsum_linear S _ hs]

end
end D5.S3.VertexAlgebra.LatticeCosetGroundReconstruction
