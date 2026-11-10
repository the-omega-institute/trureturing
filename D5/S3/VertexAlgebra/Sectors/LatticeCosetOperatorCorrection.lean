/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetOperatorCorrection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetOperatorCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state native inner creation expansion and transverse operator correction. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetReconstruction
import D5.S3.VertexAlgebra.Sectors.LatticeCosetGroundReconstruction

/-! All source descendants use the native multiplication recursion. The
outer source acts on arbitrary transverse target polynomials. Inner-first
coefficient extraction retains the original integral exponents and epsilon.
No positivity of the ambient form is assumed. Native field conventions
follow Bakalov--Kac, math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetOperatorCorrection

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeSugawaraCurrents FieldNormalProduct LatticeDiscriminantTheta
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeCosetCreationSeparation LatticeCosetInnerExpansion LatticeCosetGroundReconstruction
open LatticeCosetProjectedAction MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private native_normal_separation from D5.S3.VertexAlgebra.Sectors.LatticeCosetReconstruction
open private high_modes_finite map_finsum_linear from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation
open private injection_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private current current_negative derivative_injection compressedField_modes from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion
open private multiplication_recursion from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

private theorem reconstruction_finite (a d : Fin e → ℤ) (u g : Carrier D) (m : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      mixedState D B C hC hCe (a+d)
        (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) a))
        (compressed D B C hC hCe a d u (m+j) g)) := by
  obtain ⟨N,hN⟩ := compressed_high_modes D B C hC hCe a d u g m
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  exact hj (by dsimp only; rw [hN j (by omega), map_zero])

private theorem derivative_negative_mixed (hD : (gramReal D).PosDef)
    (d d' : Fin e → ℤ) (x : Index D) (i : ℕ)
    (h : MvPolynomial (Fin e × ℕ) ℂ) (g : Carrier D) :
    ((dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e)))
        [[-(i : ℤ)-1]]) (mixedState D B C hC hCe d' h g) =
      mixedState D B C hC hCe d' h
        (((dividedDerivative x.2 (current D B d x.1))[[-(i : ℤ)-1]]) g) := by
  rw [derivative_modes (ambient D e B C hC hCe) (x.1.castAdd e, x.2)]
  simp only [LinearMap.smul_apply, current_mixed D B C hC hCe hD]
  change _ = mixedState D B C hC hCe d' h
    (Ring.choose (-(-(i : ℤ)-1)-1+x.2) x.2 •
      HVertexOperator.coeff (current D B d x.1) (-(-(i : ℤ)-1)-1+x.2) g)
  rw [map_zsmul, VertexOperator.coeff_eq_ncoeff]
  rw [show -(-(-(i : ℤ)-1)-1+x.2)-1 = -(i : ℤ)-1-x.2 by omega]
  change ((Ring.choose (-(-(i : ℤ)-1)-1+x.2) x.2 : ℤ) : ℂ) •
      mixedState D B C hC hCe d' h (((current D B d' x.1)[[-(i : ℤ)-1-x.2]]) g) = _
  rw [current_negative D B d' d x.1 _ (by omega), Int.cast_smul_eq_zsmul]

/-- The complete native inner field on every original state is a finite
convolution of its actual compressed coefficients with transverse creation. -/
theorem inner_creation_expansion (hD : (gramReal D).PosDef)
    (a d : Fin e → ℤ) (u g : Carrier D) (m : ℤ) :
    ((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]])
        (injection D B C hC hCe d g) =
      ∑ᶠ j : ℕ, mixedState D B C hC hCe (a+d)
        (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) a))
        (compressed D B C hC hCe a d u (m+j) g) := by
  classical
  induction u using Finsupp.induction_linear generalizing m g with
  | zero => simp [compressed]
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    rw [hu, hv]
    change _ = ∑ᶠ j : ℕ, mixedState D B C hC hCe (a+d)
      (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) a))
      (compressed D B C hC hCe a d (u+v) (m+j) g)
    simp only [compressed, map_add, Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply]
    exact (finsum_add_distrib (reconstruction_finite D B C hC hCe a d u g m)
      (reconstruction_finite D B C hC hCe a d v g m)).symm
  | single n f =>
    induction f using MvPolynomial.induction_on generalizing m g with
    | C z =>
      have hz : MvPolynomial.C z = z • (1 : Oscillator D) := by
        simp [MvPolynomial.smul_eq_C_mul]
      rw [hz, ← Finsupp.smul_single]
      simp only [compressed, map_smul, Pi.smul_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, RingHom.id_apply]
      have hs : Function.HasFiniteSupport (fun j : ℕ =>
          mixedState D B C hC hCe (a+d)
            (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) a))
            (projection D B C hC hCe (a+d)
              (((Y (ambient D e B C hC hCe)
                (injection D B C hC hCe a (Finsupp.single n 1)))[[m+j]])
                  (injection D B C hC hCe d g)))) :=
        reconstruction_finite D B C hC hCe a d (Finsupp.single n 1) g m
      rw [← smul_finsum' z hs]
      congr 1
      simp only [injection_single, map_one, stateField_ground]
      exact ground_reconstruction D B C hC hCe a d n m g
    | add f f' hf hf' =>
      simp only [Finsupp.single_add, map_add, Pi.add_apply, LinearMap.add_apply]
      rw [hf, hf']
      simp only [compressed, Finsupp.single_add, map_add, Pi.add_apply,
        LinearMap.add_apply, LinearMap.comp_apply]
      exact (finsum_add_distrib
        (reconstruction_finite D B C hC hCe a d (Finsupp.single n f) g m)
        (reconstruction_finite D B C hC hCe a d (Finsupp.single n f') g m)).symm
    | mul_X f x hf =>
      have hrec : Y (ambient D e B C hC hCe)
          (injection D B C hC hCe a (Finsupp.single n (X x*f))) =
          (normalMinusOne
            (dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e)))
            (Y (ambient D e B C hC hCe)
              (injection D B C hC hCe a (Finsupp.single n f)))).1 := by
        have hx : polynomialInjection D B C hC hCe (X x) =
            X (x.1.castAdd e, x.2) := by simp [polynomialInjection]
        rw [injection_single, map_mul, hx, injection_single D B C hC hCe a n f]
        exact multiplication_recursion _ _ _ _
      rw [mul_comm f (X x)]
      change _ = ∑ᶠ j : ℕ, mixedState D B C hC hCe (a+d)
        (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) a))
        (compressed D B C hC hCe a d (Finsupp.single n (X x*f)) (m+j) g)
      simp_rw [← compressedField_modes]
      rw [hrec, compressed_multiplication_recursion D B C hC hCe hD]
      apply native_normal_separation
      · intro t v
        simpa only [compressedField_modes, compressed, LinearMap.comp_apply] using hf v t
      · intro i j v
        exact derivative_negative_mixed D B C hC hCe hD d (a+d) x i _ v
      · intro i v
        exact derivative_injection D B C hC hCe hD d x i v

open private mixedState_single multiply_single from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private polynomialMode_monomial from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetProjectedAction

private theorem mixed_injection (d : Fin e → ℤ)
    (h : MvPolynomial (Fin e × ℕ) ℂ) (g : Carrier D) :
    mixedState D B C hC hCe d h g =
      multiply _ (transversePolynomial D B C hC hCe h) (injection D B C hC hCe d g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n f =>
    rw [mixedState_single, injection_single, multiply_single, mul_comm]

/-- The full actual two-source composition differs from iterated compression
by precisely the Schur binomial correction, with finite summand support,
for every original state and integer mode. The ambient symmetric even block form need not be positive. -/
theorem intermediate_projection_correction (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D) (p q : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ => correction D B C a b j •
      compressed D B C hC hCe a (b+c) u (p-j)
        (compressed D B C hC hCe b c v (q+j) w)) ∧
    projection D B C hC hCe (a+b+c)
      (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[p]])
        (((Y (ambient D e B C hC hCe) (injection D B C hC hCe b v))[[q]])
          (injection D B C hC hCe c w))) =
      ∑ᶠ j : ℕ, correction D B C a b j •
        compressed D B C hC hCe a (b+c) u (p-j)
          (compressed D B C hC hCe b c v (q+j) w) := by
  refine ⟨correction_finite D B C hC hCe a b c u v w p q, ?_⟩
  rw [inner_creation_expansion D B C hC hCe hD b c v w q, add_assoc]
  let L := (projection D B C hC hCe (a+(b+c))).comp
    ((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[p]])
  change L (∑ᶠ j : ℕ, mixedState D B C hC hCe (b+c)
      (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) b))
      (compressed D B C hC hCe b c v (q+j) w)) = _
  rw [map_finsum_linear L _ (reconstruction_finite D B C hC hCe b c v w q)]
  apply finsum_congr
  intro j
  dsimp only [L, LinearMap.comp_apply]
  rw [mixed_injection D B C hC hCe,
    projected_transverse_polynomial D B C hC hCe hD,
    transverse_creation_coefficient D B C hC hCe hD]
  rw [map_smul, Polynomial.X_pow_eq_monomial, polynomialMode_monomial, one_smul]
  rfl

end
end D5.S3.VertexAlgebra.LatticeCosetOperatorCorrection
