/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cube-one monomial lifts fix the integral fixed charge lines. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround

/-! The cyclically ordered products of a charge orbit have the same cocycle sign.
The norm certificate then forces the lift to fix every fixed charged ground vector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeSectorIntertwiner
open LatticeActualGeneratorLocality (epsilon_add_left epsilon_skew paritySign_square)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open P48qFixedRankCertificate P48qGramCertificate
open scoped VertexOperator Matrix

noncomputable section

private abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

private theorem ground_ne_zero (D : LatticeData) (a : Charge D) :
    ground D a ≠ 0 := by
  classical
  simp

private theorem ground_mul (D : LatticeData) (a b : Charge D) :
    ((Y D (ground D a))[[-bilinear D a b - 1]]) (ground D b) =
      epsilon D a b • ground D (a + b) := by
  change ((Y D (inclusion D a 1))[[-bilinear D a b - 1]]) (inclusion D b 1) = _
  rw [← inclusion_canonical, canonical_ground_normalization, map_smul]
  rfl

private theorem epsilon_ne_zero (D : LatticeData) (a b : Charge D) :
    epsilon D a b ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> simp

theorem fixed_charge_phase_eq_one_of_cube_one_norm_image
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (lift : Carrier D ≃ₗ[ℂ] Carrier D) (phase : Charge D → ℂˣ)
    (hLift : ∀ a, lift (ground D a) = (phase a : ℂ) • ground D (g a))
    (hMode : ∀ (u v : Carrier D) (m : ℤ),
      lift (((Y D u)[[m]]) v) = ((Y D (lift u))[[m]]) (lift v))
    (hCube : lift ^ (3 : ℕ) = 1)
    (hGcube : ∀ a, g (g (g a)) = a)
    (hGisometry : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (hNormImage : ∀ v, g v = v →
      ∃ x, x + g x + g (g x) = v)
    (a : Charge D) (ha : g a = a) :
    phase a = 1 := by
  have hPhaseLaw (x y : Charge D) :
      epsilon D x y * (phase (x + y) : ℂ) =
        (phase x : ℂ) * (phase y : ℂ) * epsilon D (g x) (g y) := by
    have h := hMode (ground D x) (ground D y) (-bilinear D x y - 1)
    have hxy : g (x + y) = g x + g y := map_add g x y
    rw [ground_mul, map_smul, hLift, hxy, hLift x, hLift y, map_smul] at h
    simp only [VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply,
      map_smul, smul_smul] at h
    have hPair : bilinear D (g x) (g y) = bilinear D x y := hGisometry x y
    have hGround :
        ((Y D (ground D (g x)))[[-bilinear D x y - 1]])
            (ground D (g y)) =
          epsilon D (g x) (g y) • ground D (g x + g y) := by
      simpa only [hPair] using ground_mul D (g x) (g y)
    rw [← VertexOperator.ncoeff, hGround, smul_smul] at h
    exact (smul_left_injective ℂ (ground_ne_zero D (g x + g y)) h).trans (by ac_rfl)

  obtain ⟨x, hx⟩ := hNormImage a ha
  have hOrbitProduct :
      (phase x : ℂ) * (phase (g x) : ℂ) * (phase (g (g x)) : ℂ) = 1 := by
    have hNested :
        lift (lift (lift (ground D x))) =
          ((phase x : ℂ) * (phase (g x) : ℂ) *
            (phase (g (g x)) : ℂ)) • ground D x := by
      simp only [hLift, map_smul, smul_smul, hGcube, mul_assoc]
    have hCubeGround :
        (lift ^ (3 : ℕ)) (ground D x) = ground D x := by
      rw [hCube]
      simp
    have hNestedCube : lift (lift (lift (ground D x))) = ground D x := by
      calc
        lift (lift (lift (ground D x))) =
            (lift ^ (3 : ℕ)) (ground D x) := by
              simp [pow_succ', LinearEquiv.mul_apply]
        _ = ground D x := hCubeGround
    have hs :
        ((phase x : ℂ) * (phase (g x) : ℂ) *
          (phase (g (g x)) : ℂ)) • ground D x = ground D x :=
      hNested.symm.trans hNestedCube
    apply smul_left_injective ℂ (ground_ne_zero D x)
    simpa using hs

  have hPairOrbit :
      bilinear D (g x) x = bilinear D (g (g x)) x := by
    calc
      bilinear D (g x) x = bilinear D x (g x) := bilinear_symmetric D _ _
      _ = bilinear D (g x) (g (g x)) := (hGisometry x (g x)).symm
      _ = bilinear D (g (g x)) x := by
        have h := hGisometry (g x) (g (g x))
        rw [hGcube x] at h
        exact h.symm

  have hEpsilonOrbit :
      epsilon D (g x) (g (g x)) *
          epsilon D (g x + g (g x)) x =
        epsilon D x (g x) *
          epsilon D (x + g x) (g (g x)) := by
    calc
      epsilon D (g x) (g (g x)) *
          epsilon D (g x + g (g x)) x =
          epsilon D (g x) (g (g x)) *
            (epsilon D (g x) x * epsilon D (g (g x)) x) := by
              rw [epsilon_add_left]
      _ = epsilon D (g x) (g (g x)) *
          ((paritySign (bilinear D (g x) x) * epsilon D x (g x)) *
            (paritySign (bilinear D (g (g x)) x) *
              epsilon D x (g (g x)))) := by
              rw [epsilon_skew D (g x) x, epsilon_skew D (g (g x)) x]
      _ = epsilon D x (g x) *
          (epsilon D x (g (g x)) * epsilon D (g x) (g (g x))) := by
              rw [hPairOrbit]
              calc
                _ = (paritySign (bilinear D (g (g x)) x) *
                    paritySign (bilinear D (g (g x)) x)) *
                    (epsilon D x (g x) *
                      (epsilon D x (g (g x)) * epsilon D (g x) (g (g x)))) := by ring
                _ = _ := by rw [paritySign_square, one_mul]
      _ = epsilon D x (g x) *
          epsilon D (x + g x) (g (g x)) := by
              rw [epsilon_add_left]

  have hFirst := hPhaseLaw x (g x)
  have hSecond := hPhaseLaw (x + g x) (g (g x))
  have hSecond' :
      epsilon D (x + g x) (g (g x)) *
          (phase (x + g x + g (g x)) : ℂ) =
        (phase (x + g x) : ℂ) * (phase (g (g x)) : ℂ) *
          epsilon D (g x + g (g x)) x := by
    simpa only [map_add, hGcube x, add_assoc] using hSecond
  have hTotal :
      (epsilon D x (g x) * epsilon D (x + g x) (g (g x))) *
          (phase (x + g x + g (g x)) : ℂ) =
        epsilon D (g x) (g (g x)) *
          epsilon D (g x + g (g x)) x := by
    calc
      (epsilon D x (g x) * epsilon D (x + g x) (g (g x))) *
          (phase (x + g x + g (g x)) : ℂ) =
          epsilon D x (g x) *
            ((phase (x + g x) : ℂ) * (phase (g (g x)) : ℂ) *
              epsilon D (g x + g (g x)) x) := by
                rw [mul_assoc, hSecond']
      _ = (epsilon D x (g x) * (phase (x + g x) : ℂ)) *
            (phase (g (g x)) : ℂ) *
            epsilon D (g x + g (g x)) x := by ring
      _ = (((phase x : ℂ) * (phase (g x) : ℂ) *
            epsilon D (g x) (g (g x))) *
            (phase (g (g x)) : ℂ)) *
            epsilon D (g x + g (g x)) x := by rw [hFirst]
      _ = ((phase x : ℂ) * (phase (g x) : ℂ) *
            (phase (g (g x)) : ℂ)) *
          (epsilon D (g x) (g (g x)) *
            epsilon D (g x + g (g x)) x) := by ring
      _ = epsilon D (g x) (g (g x)) *
          epsilon D (g x + g (g x)) x := by rw [hOrbitProduct, one_mul]

  have hFixedPhaseComplex :
      (phase (x + g x + g (g x)) : ℂ) = 1 := by
    have hEps :
        epsilon D x (g x) * epsilon D (x + g x) (g (g x)) ≠ 0 :=
      mul_ne_zero (epsilon_ne_zero D x (g x))
        (epsilon_ne_zero D (x + g x) (g (g x)))
    apply mul_left_cancel₀ hEps
    simpa only [mul_one] using hTotal.trans hEpsilonOrbit
  apply Units.ext
  change (phase a : ℂ) = 1
  simpa [hx] using hFixedPhaseComplex

/- The normalized concrete row action. -/
local notation "A" => nebeOrderThree

private theorem transpose_cube : (Aᵀ) ^ 3 = 1 := by
  rw [← Matrix.transpose_pow, nebeOrderThree_cube, Matrix.transpose_one]

def p48qG : Charge nebeLatticeData ≃+ Charge nebeLatticeData :=
  (Matrix.toLin'OfInv (M := (Aᵀ) ^ 2) (M' := Aᵀ)
    (by rw [← pow_succ]; exact transpose_cube)
    (by rw [← pow_succ']; exact transpose_cube)).toAddEquiv

theorem p48qG_apply (a : Charge nebeLatticeData) : p48qG a = a ᵥ* A := by
  change Aᵀ *ᵥ a = a ᵥ* A
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]

theorem p48qG_cube (a : Charge nebeLatticeData) :
    p48qG (p48qG (p48qG a)) = a := by
  have h : (A * A) * A = 1 := by
    rw [← pow_two, ← pow_succ, nebeOrderThree_cube]
  simp only [p48qG_apply, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem p48qG_isometry (a b : Charge nebeLatticeData) :
    bilinear nebeLatticeData (p48qG a) (p48qG b) =
      bilinear nebeLatticeData a b := by
  have hForm := Matrix.toBilin'_comp nebeGram Aᵀ Aᵀ
  rw [Matrix.transpose_transpose, gram_isometry_certificate] at hForm
  have h := congrArg
    (fun f : LinearMap.BilinForm ℤ (Charge nebeLatticeData) => f a b) hForm
  change nebeGram.toBilin' (p48qG a) (p48qG b) = nebeGram.toBilin' a b at h
  simpa only [Matrix.toBilin'_apply, bilinear, nebeLatticeData] using h

theorem p48q_fixed_is_norm_image (v : Charge nebeLatticeData)
    (hv : p48qG v = v) :
    ∃ x, x + p48qG x + p48qG (p48qG x) = v := by
  have hv' : Matrix.vecMul v A = v := by
    simpa only [p48qG_apply] using hv
  obtain ⟨x, hx⟩ :=
    P48qNormImageCertificate.nebeOrderThree_fixed_is_norm_image v hv'
  refine ⟨x, ?_⟩
  simpa only [p48qG_apply, Matrix.vecMul_vecMul, pow_two, Matrix.vecMul_add,
    Matrix.vecMul_one, add_assoc] using hx

theorem p48q_order_three_lift_standard
    (lift : Carrier nebeLatticeData ≃ₗ[ℂ] Carrier nebeLatticeData)
    (phase : Charge nebeLatticeData → ℂˣ)
    (hLift : ∀ a, lift (ground nebeLatticeData a) =
      (phase a : ℂ) • ground nebeLatticeData (p48qG a))
    (hMode : ∀ (u v : Carrier nebeLatticeData) (m : ℤ),
      lift (((Y nebeLatticeData u)[[m]]) v) =
        ((Y nebeLatticeData (lift u))[[m]]) (lift v))
    (hCube : lift ^ (3 : ℕ) = 1)
    (a : Charge nebeLatticeData) (ha : p48qG a = a) :
    phase a = 1 := by
  exact fixed_charge_phase_eq_one_of_cube_one_norm_image
    nebeLatticeData p48qG lift phase hLift hMode hCube p48qG_cube
      p48qG_isometry p48q_fixed_is_norm_image a ha

#print axioms fixed_charge_phase_eq_one_of_cube_one_norm_image
#print axioms p48q_order_three_lift_standard

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeLiftRigidity
