/- GID: D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Type II physical null state and finite Fock coefficient obstruction. -/

import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOriginalTypeIINullState

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open SourceBPZ.OriginalMatterHermitian MvPolynomial
open scoped BigOperators

noncomputable section

private theorem coeff_linear_mul_X (D : LatticeData) (x y : Index D)
    (P : Oscillator D) :
    coeff (Finsupp.single x 1) (P * X y) = if x = y then coeff 0 P else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp [coeff_mul_X']
  · simp [coeff_mul_X', h, Ne.symm h]

private theorem coeff_zero_derivation (D : LatticeData) (P : Oscillator D) :
    coeff 0 (oscillatorDerivation D P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [oscillatorDerivation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    simp [Derivation.leibniz, oscillatorDerivation, MvPolynomial.mkDerivation_X,
      ← constantCoeff_eq, hP]

private theorem coeff_derivation_two (D : LatticeData) (i : Fin D.rank)
    (P : Oscillator D) :
    coeff (Finsupp.single (i, 1) 1) (oscillatorDerivation D P) =
      coeff (Finsupp.single (i, 0) 1) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [oscillatorDerivation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    rcases x with ⟨j,k⟩
    rw [Derivation.leibniz]
    simp only [oscillatorDerivation, MvPolynomial.mkDerivation_X]
    rw [smul_eq_mul, mul_comm (X (j,k))]
    simp only [coeff_add, mul_smul_comm, coeff_smul, coeff_linear_mul_X,
      coeff_zero_derivation]
    by_cases h : k = 0
    · subst k; simp
    · simp [h, show k + 1 ≠ 1 by omega]

private def ell (D : LatticeData) (p : Charge D) (x : Carrier D) : ℂ :=
  ∑ i : Fin D.rank, (∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ)) *
    coeff (Finsupp.single (i, 1) 1) (x p)

private theorem charge_scalar (D : LatticeData) (p : Charge D) (i : Fin D.rank) :
    chargeScalar D p i = ∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ) := by
  simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]

private theorem ell_translation_single (D : LatticeData) (p q : Charge D)
    (P : Oscillator D) :
    ell D p (translation D (Finsupp.single q P)) =
      if q = p then ∑ i : Fin D.rank, chargeScalar D p i *
        coeff (Finsupp.single (i,0) 1) P else 0 := by
  classical
  by_cases h : q = p
  · subst q
    simp only [translation_single, ell, Finsupp.single_eq_same, coeff_add]
    have hc (i : Fin D.rank) : coeff (Finsupp.single (i,1) 1)
        (chargePolynomial D p * P) = 0 := by
      simp [chargePolynomial, Finset.sum_mul, mul_comm _ P, coeff_linear_mul_X]
    simp_rw [hc, add_zero, coeff_derivation_two, ← charge_scalar]
    simp
  · simp [translation_single, ell, Finsupp.single_eq_of_ne h]

private theorem mode_mul_X (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (m : ℤ) (i : Fin D.rank) (k : ℕ) (P : Oscillator D) :
    sectorSugawaraMode D H p m (P * X (i,k)) =
      X (i,k) * sectorSugawaraMode D H p m P +
        ((k+1 : ℕ) : ℂ) • neutralPolynomialMode D i p (m - (k+1 : ℕ)) P := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) =>
      (A (Finsupp.single p P)) p)
    (sugawaraMode_current_commutator D H hHG hGH i m (-((k+1 : ℕ) : ℤ)))
  have hn : neutralPolynomialMode D i p (-((k+1 : ℕ) : ℤ)) =
      LinearMap.mulLeft ℂ (X (i,k)) := by
    simp [neutralPolynomialMode, show -((k+1 : ℕ) : ℤ) < 0 by omega]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
    sugawaraMode_single_sector, LinearMap.smul_apply, Finsupp.sub_apply,
    Finsupp.single_eq_same, Finsupp.smul_apply, hn, LinearMap.mulLeft_apply] at h
  rw [mul_comm P]
  apply sub_eq_iff_eq_add.mp at h
  convert h using 1 <;> push_cast <;> ring

private theorem coeff_mode_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : Oscillator D) :
    coeff 0 (sectorSugawaraMode D H p 1 P) =
      ∑ i : Fin D.rank, chargeScalar D p i * coeff (Finsupp.single (i,0) 1) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hg := sugawaraMode_ground_positive D H p 1 (by omega)
    have hc : Finsupp.single p (C c : Oscillator D) =
        c • Finsupp.single p (1 : Oscillator D) := by simp [← C_mul']
    have hz := congrArg (fun x : Carrier D => x p) (show
        sugawaraMode D H 1 (Finsupp.single p (C c)) = 0 by rw [hc, map_smul, hg, smul_zero])
    simpa [sugawaraMode_single_sector] using hz
  | add P Q hP hQ =>
    simp [hP, hQ, Finset.sum_add_distrib, mul_add]
  | mul_X P x hP =>
    rcases x with ⟨j,k⟩
    rw [mode_mul_X D H hHG hGH]
    simp only [coeff_add, ← constantCoeff_eq, map_mul, constantCoeff_X, zero_mul,
      zero_add, coeff_smul]
    cases k with
    | zero =>
      simp [neutralPolynomialMode, chargeScalar, coeff_linear_mul_X,
        constantCoeff_eq, eq_comm]
    | succ k =>
      have hn : (1 : ℤ) - ((k+1+1 : ℕ) : ℤ) < 0 := by omega
      simp [neutralPolynomialMode, hn, coeff_linear_mul_X, constantCoeff_eq]

end
end D5.S3.VertexAlgebra.LatticeOriginalTypeIINullState
