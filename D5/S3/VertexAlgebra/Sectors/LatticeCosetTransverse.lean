/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetTransverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetTransverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native polynomial translation of transverse oscillator descendants. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

/-!
The creation and annihilation polynomials are those of the native lattice
field, Bakalov--Kac, math/0402315v1, section 4.1. The Schur complement is
computed by the original rational Gram inverse. No positive ambient lattice,
new vertex algebra, scalar cocycle replacement or contraction premise occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetTransverse

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators

noncomputable section

open private gram_longitudinal from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private bilinear_unit from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- A transverse oscillator is an actual ambient polynomial, not a new state. -/
def transverse (j : Fin e) (k : ℕ) : Oscillator (ambient D e B C hC hCe) :=
  X (j.natAdd D.rank, k) -
    ∑ i : Fin D.rank, (longitudinal D B i j : ℂ) • X (i.castAdd e, k)

/-- Contraction of the external charge with one transverse direction. -/
def transversePair (a : Fin e → ℤ) (j : Fin e) : ℚ :=
  ∑ k, (a k : ℚ) * ((C k j : ℚ) - ∑ i, (B i k : ℚ) * longitudinal D B i j)

/-- The actual native annihilation translation, followed by longitudinal
projection coefficient by coefficient. -/
def translatedProjection (A : Charge (ambient D e B C hC hCe)) :
    Oscillator (ambient D e B C hC hCe) →ₐ[ℂ] Polynomial (Oscillator D) :=
  (Polynomial.mapAlgHom (polynomialProjection D B C hC hCe)).comp
    (aeval (fun x : Index (ambient D e B C hC hCe) =>
      translationVariable (ambient D e B C hC hCe) A x.1 x.2))

private theorem translatedProjection_apply
    (A : Charge (ambient D e B C hC hCe))
    (p : Oscillator (ambient D e B C hC hCe)) :
    translatedProjection D B C hC hCe A p =
      Polynomial.map (polynomialProjection D B C hC hCe).toRingHom
        (translatedPolynomial (ambient D e B C hC hCe) A p) := rfl

private theorem bilinear_old (a : Fin e → ℤ) (n : Charge D) (i : Fin D.rank) :
    bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (unitCharge _ (i.castAdd e)) =
      (∑ k, n k * D.G k i) + ∑ k, a k * B i k := by
  classical
  rw [bilinear_symmetric, bilinear_unit]
  change (∑ k : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp [liftCharge, ambient, D.symmetric, mul_comm]

private theorem bilinear_external (a : Fin e → ℤ) (n : Charge D) (j : Fin e) :
    bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (unitCharge _ (j.natAdd D.rank)) =
      (∑ k, n k * B k j) + ∑ k, a k * C k j := by
  classical
  rw [bilinear_symmetric, bilinear_unit]
  change (∑ k : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp [liftCharge, ambient, hC, mul_comm]

private theorem transverse_pairing (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (j : Fin e) :
    (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (unitCharge _ (j.natAdd D.rank)) : ℚ) -
      ∑ i, longitudinal D B i j *
        (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
          (unitCharge _ (i.castAdd e)) : ℚ) = transversePair D B C a j := by
  rw [bilinear_external]
  simp_rw [bilinear_old, Int.cast_add, Int.cast_sum, Int.cast_mul]
  have old : (∑ i, longitudinal D B i j * ∑ k, (n k : ℚ) * (D.G k i : ℚ)) =
      ∑ k, (n k : ℚ) * (B k j : ℚ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (∑ i, longitudinal D B i j * ((n k : ℚ) * (D.G k i : ℚ))) =
          (n k : ℚ) * ∑ i, (D.G k i : ℚ) * longitudinal D B i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ = _ := by rw [gram_longitudinal D B hD]
  have ext : (∑ i, longitudinal D B i j * ∑ k, (a k : ℚ) * (B i k : ℚ)) =
      ∑ k, (a k : ℚ) * ∑ i, (B i k : ℚ) * longitudinal D B i j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros
    apply Finset.sum_congr rfl
    intros
    ring
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [old, ext]
  simp only [transversePair, mul_sub, Finset.sum_sub_distrib]
  ring

private theorem projection_transverse (j : Fin e) (k : ℕ) :
    polynomialProjection D B C hC hCe (transverse D B C hC hCe j k) = 0 := by
  simp [transverse, polynomialProjection, projectionVariable, map_smul]

private theorem translatedProjection_variable
    (A : Charge (ambient D e B C hC hCe))
    (x : Index (ambient D e B C hC hCe)) :
    translatedProjection D B C hC hCe A (X x) =
      Polynomial.C (projectionVariable D B C hC hCe x) -
        Polynomial.C ((bilinear (ambient D e B C hC hCe) A (unitCharge _ x.1) : ℂ) •
          (1 : Oscillator D)) * Polynomial.X^(x.2+1) := by
  simp [translatedProjection, translationVariable, polynomialProjection]

/-- The old charge cancels out of the transverse contraction. The minus sign
comes from the native translationVariable, at every oscillator frequency. -/
theorem transverse_translation (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (j : Fin e) (k : ℕ) :
    translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n)
        (transverse D B C hC hCe j k) =
      -Polynomial.C ((transversePair D B C a j : ℂ) • (1 : Oscillator D)) *
        Polynomial.X^(k+1) := by
  classical
  have pair :
      (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
          (unitCharge _ (j.natAdd D.rank)) : ℂ) -
        ∑ i, (longitudinal D B i j : ℂ) *
          (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
            (unitCharge _ (i.castAdd e)) : ℂ) = (transversePair D B C a j : ℂ) := by
    exact_mod_cast transverse_pairing D B C hC hCe hD a n j
  have hCsmul (z : ℂ) (p : Oscillator D) :
      Polynomial.C (z • p) = z • (Polynomial.C p : Polynomial (Oscillator D)) :=
    map_smul (Polynomial.CAlgHom : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D)) z p
  simp only [transverse, map_sub, map_sum, map_smul, translatedProjection_variable,
    projectionVariable, Fin.addCases_right, Fin.addCases_left]
  simp only [smul_sub, Finset.sum_sub_distrib, ← map_sum,
    ← hCsmul, smul_mul_assoc, ← Finset.sum_mul, ← Finset.sum_smul,
    smul_smul]
  have hscalar := congrArg (fun z : ℂ => Polynomial.C (z • (1 : Oscillator D))) pair
  simp only [sub_smul, map_sub, ← Finset.sum_smul, smul_smul, map_sum] at hscalar
  linear_combination -Polynomial.X^(k+1) * hscalar

/-- Every polynomial in transverse oscillators is contracted by the same
native substitution. No bound on the polynomial degree or frequency is used. -/
theorem transverse_polynomial_translation (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (p : MvPolynomial (Fin e × ℕ) ℂ) :
    translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n)
        (aeval (fun x : Fin e × ℕ => transverse D B C hC hCe x.1 x.2) p) =
      aeval (fun x : Fin e × ℕ =>
        -Polynomial.C ((transversePair D B C a x.1 : ℂ) • (1 : Oscillator D)) *
          Polynomial.X^(x.2+1)) p := by
  have h : (translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n)).comp
      (aeval (fun x : Fin e × ℕ => transverse D B C hC hCe x.1 x.2)) =
      aeval (fun x : Fin e × ℕ =>
        -Polynomial.C ((transversePair D B C a x.1 : ℂ) • (1 : Oscillator D)) *
          Polynomial.X^(x.2+1)) := by
    ext x
    simpa using transverse_translation D B C hC hCe hD a n x.1 x.2
  exact DFunLike.congr_fun h p

end
end D5.S3.VertexAlgebra.LatticeCosetTransverse
