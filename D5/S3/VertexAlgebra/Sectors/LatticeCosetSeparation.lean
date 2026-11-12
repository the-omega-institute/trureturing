/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetSeparation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native old-current transport on arbitrary transverse target polynomials. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetTransverse
import D5.S3.VertexAlgebra.LatticeActualProductKernel

/-!
Orthogonal oscillator separation for the native lattice fields of
Bakalov--Kac, math/0402315v1, section 4.1. The original integral charges,
cocycle and half diagonal are unchanged. Only the old Gram matrix is
positive definite; no positivity or nondegeneracy of the ambient form is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetSeparation

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeCosetCompression LatticeCosetTransverse
open LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private gram_longitudinal_complex
  old_current_pairing injection_single projection_single polynomialProjection_injection
  from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private transverse_pairing from D5.S3.VertexAlgebra.Sectors.LatticeCosetTransverse
open private translated_mul from D5.S3.VertexAlgebra.LatticeSugawaraConformal

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- Embed an arbitrary transverse polynomial into the actual ambient ring. -/
def transversePolynomial : MvPolynomial (Fin e × ℕ) ℂ →ₐ[ℂ]
    Oscillator (ambient D e B C hC hCe) :=
  aeval (fun x : Fin e × ℕ => transverse D B C hC hCe x.1 x.2)

/-- The bilinear oscillator embedding with a fixed external charge. -/
def mixedState (d : Fin e → ℤ) (h : MvPolynomial (Fin e × ℕ) ℂ) :
    Carrier D →ₗ[ℂ] Carrier (ambient D e B C hC hCe) :=
  Finsupp.lsum ℂ (fun n =>
    (Finsupp.lsingle (liftCharge D B C hC hCe d n)).comp
      ((LinearMap.mulRight ℂ (transversePolynomial D B C hC hCe h)).comp
        (polynomialInjection D B C hC hCe).toLinearMap))

private theorem mixedState_single (d : Fin e → ℤ)
    (h : MvPolynomial (Fin e × ℕ) ℂ) (n : Charge D) (f : Oscillator D) :
    mixedState D B C hC hCe d h (Finsupp.single n f) =
      Finsupp.single (liftCharge D B C hC hCe d n)
        (polynomialInjection D B C hC hCe f * transversePolynomial D B C hC hCe h) := by
  simp [mixedState]

private theorem partial_transverse (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r : ℕ) (j : Fin e) (k : ℕ) :
    weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
      (transverse D B C hC hCe j k) = 0 := by
  classical
  simp only [transverse, map_sub, map_sum, map_smul]
  rw [LatticeActualAnnihilation.annihilate_X (ambient D e B C hC hCe) (i.castAdd e)
    (j.natAdd D.rank) r k]
  simp_rw [LatticeActualAnnihilation.annihilate_X (ambient D e B C hC hCe) (i.castAdd e)]
  by_cases hr : r = k
  · simp only [hr, ↓reduceIte, ambient, Fin.addCases_left, Fin.addCases_right]
    simp only [smul_smul, MvPolynomial.smul_eq_C_mul, mul_one, ← map_mul, ← map_sum]
    rw [show (∑ t, (longitudinal D B t j : ℂ) * (D.G i t : ℂ)) = (B i j : ℂ) by
      simpa only [mul_comm] using gram_longitudinal_complex D B hD i j]
    exact sub_self _
  · simp [hr]

private theorem partial_transversePolynomial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r : ℕ) (h : MvPolynomial (Fin e × ℕ) ℂ) :
    weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
      (transversePolynomial D B C hC hCe h) = 0 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C z => simp [transversePolynomial, weightedPartial]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p x hp =>
    rw [map_mul, LatticeActualAnnihilation.annihilate_mul, hp, zero_mul, zero_add]
    simp only [transversePolynomial, aeval_X]
    rw [partial_transverse D B C hC hCe hD, mul_zero]

private theorem partial_injection (i : Fin D.rank) (r : ℕ) (f : Oscillator D) :
    weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
        (polynomialInjection D B C hC hCe f) =
      polynomialInjection D B C hC hCe (weightedPartial D i r f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C z => simp [polynomialInjection, weightedPartial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    have hx : weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
        (polynomialInjection D B C hC hCe (X x)) =
        polynomialInjection D B C hC hCe (weightedPartial D i r (X x)) := by
      simp only [polynomialInjection, rename_X]
      rcases x with ⟨j,k⟩
      rw [LatticeActualAnnihilation.annihilate_X (ambient D e B C hC hCe) (i.castAdd e)
        (j.castAdd e) r k, LatticeActualAnnihilation.annihilate_X D i j r k]
      split_ifs <;> simp [ambient]
    simp only [map_mul, LatticeActualAnnihilation.annihilate_mul, map_add, hp, hx]

/-- Every actual old current acts only on the longitudinal target factor,
including arbitrary transverse polynomials and all integer modes. -/
theorem current_mixed_polynomial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (d : Fin e → ℤ) (n : Charge D) (m : ℤ)
    (f : Oscillator D) (h : MvPolynomial (Fin e × ℕ) ℂ) :
    neutralPolynomialMode (ambient D e B C hC hCe) (i.castAdd e)
        (liftCharge D B C hC hCe d n) m
        (polynomialInjection D B C hC hCe f * transversePolynomial D B C hC hCe h) =
      polynomialInjection D B C hC hCe
        (LatticeDualCosetModule.shiftedCurrentPolynomial D (Matrix.mulVec B d) 1 i n m f) *
          transversePolynomial D B C hC hCe h := by
  by_cases hm : m < 0
  · simp [neutralPolynomialMode, LatticeDualCosetModule.shiftedCurrentPolynomial,
      hm, polynomialInjection, mul_assoc]
  · by_cases hz : m = 0
    · have hp := old_current_pairing D B C hC hCe i (liftCharge D B C hC hCe d n)
      have ho : oldCharge D B C hC hCe (liftCharge D B C hC hCe d n) = n := by
        funext j
        simp [oldCharge, liftCharge]
      have he : externalCharge D B C hC hCe (liftCharge D B C hC hCe d n) = d := by
        funext j
        simp [externalCharge, liftCharge]
      rw [ho, he] at hp
      simp [neutralPolynomialMode, LatticeDualCosetModule.shiftedCurrentPolynomial,
        hm, hz, hp, map_smul, smul_mul_assoc]
    · simp only [neutralPolynomialMode, hm, hz, ↓reduceIte]
      change ((m : ℂ) • weightedPartial (ambient D e B C hC hCe) (i.castAdd e)
        (m-1).toNat) _ = _
      simp only [LinearMap.smul_apply, LatticeActualAnnihilation.annihilate_mul, partial_injection,
        partial_transversePolynomial D B C hC hCe hD, mul_zero, add_zero]
      simp [LatticeDualCosetModule.shiftedCurrentPolynomial, hm, hz, weightedPartial,
        map_smul, smul_mul_assoc]

/-- Native shifted currents already have statewise truncation. The full
ambient current intertwines their action on every transverse target factor. -/
theorem current_mixed (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (d : Fin e → ℤ) (m : ℤ) (g : Carrier D)
    (h : MvPolynomial (Fin e × ℕ) ℂ) :
    neutralMode (ambient D e B C hC hCe) (i.castAdd e) m
        (mixedState D B C hC hCe d h g) =
      mixedState D B C hC hCe d h
        (((LatticeDualCosetModule.action D (Matrix.mulVec B d)
          (Finsupp.single (0 : Charge D) (X (i,0))))[[m]]) g) := by
  have he : (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m).comp
      (mixedState D B C hC hCe d h) =
      (mixedState D B C hC hCe d h).comp
        ((LatticeDualCosetModule.action D (Matrix.mulVec B d)
          (Finsupp.single (0 : Charge D) (X (i,0))))[[m]]) := by
    apply Finsupp.lhom_ext
    intro n f
    simp only [LinearMap.comp_apply, mixedState_single,
      LatticeDualCosetModule.action_current_coefficients, neutralMode,
      Finsupp.lsum_single, Finsupp.lsingle_apply]
    rw [current_mixed_polynomial D B C hC hCe hD]
  exact DFunLike.congr_fun he g

/-- The unprojected native substitution, retaining every transverse variable. -/
def transverseTranslation (a : Fin e → ℤ) : MvPolynomial (Fin e × ℕ) ℂ →ₐ[ℂ]
    Polynomial (Oscillator (ambient D e B C hC hCe)) :=
  aeval (fun x : Fin e × ℕ =>
    Polynomial.C (transverse D B C hC hCe x.1 x.2) -
      Polynomial.C ((transversePair D B C a x.1 : ℂ) • 1) * Polynomial.X^(x.2+1))

private theorem translated_transverse (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (j : Fin e) (k : ℕ) :
    translatedPolynomial (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (transverse D B C hC hCe j k) =
      Polynomial.C (transverse D B C hC hCe j k) -
        Polynomial.C ((transversePair D B C a j : ℂ) • 1) * Polynomial.X^(k+1) := by
  classical
  let F := ambient D e B C hC hCe
  let A := liftCharge D B C hC hCe a n
  have pair : (bilinear F A (unitCharge F (j.natAdd D.rank)) : ℂ) -
      ∑ i, (longitudinal D B i j : ℂ) *
        (bilinear F A (unitCharge F (i.castAdd e)) : ℂ) =
        (transversePair D B C a j : ℂ) := by
    exact_mod_cast transverse_pairing D B C hC hCe hD a n j
  have hc (z : ℂ) (p : Oscillator F) :
      Polynomial.C (z • p) = z • (Polynomial.C p : Polynomial (Oscillator F)) :=
    map_smul (Polynomial.CAlgHom : Oscillator F →ₐ[ℂ] Polynomial (Oscillator F)) z p
  change aeval (fun x : Index F => translationVariable F A x.1 x.2)
      (transverse D B C hC hCe j k) = _
  simp only [transverse, map_sub, map_sum, map_smul, aeval_X,
    translationVariable, smul_sub, Finset.sum_sub_distrib, ← hc, ← smul_mul_assoc,
    smul_smul]
  rw [← map_sum, ← Finset.sum_mul, ← map_sum, ← Finset.sum_smul]
  have hs := congrArg (fun z : ℂ => Polynomial.C (z • (1 : Oscillator F))) pair
  simp only [sub_smul, map_sub] at hs
  linear_combination -Polynomial.X^(k+1) * hs

/-- Full translation of an arbitrary transverse target, before projection.
The old source charge cancels, but the transverse variables are retained. -/
theorem translated_mixed_polynomial (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (f : Oscillator D)
    (h : MvPolynomial (Fin e × ℕ) ℂ) :
    translatedPolynomial (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (polynomialInjection D B C hC hCe f * transversePolynomial D B C hC hCe h) =
      translatedPolynomial (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (polynomialInjection D B C hC hCe f) * transverseTranslation D B C hC hCe a h := by
  have ht : (aeval (fun x : Index (ambient D e B C hC hCe) =>
      translationVariable (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        x.1 x.2)).comp (transversePolynomial D B C hC hCe) =
      transverseTranslation D B C hC hCe a := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, transversePolynomial, aeval_X,
      transverseTranslation]
    change translatedPolynomial _ _ (transverse D B C hC hCe x.1 x.2) = _
    exact translated_transverse D B C hC hCe hD a n x.1 x.2
  change aeval _ (_ * _) = _
  rw [map_mul]
  exact congrArg (fun t => translatedPolynomial (ambient D e B C hC hCe)
    (liftCharge D B C hC hCe a n) (polynomialInjection D B C hC hCe f) * t)
      (DFunLike.congr_fun ht h)

/-- Multiplication in each actual charge sector. -/
def multiply (F : LatticeData) (t : Oscillator F) : Module.End ℂ (Carrier F) :=
  Finsupp.lsum ℂ (fun n => (Finsupp.lsingle n).comp (LinearMap.mulLeft ℂ t))

private theorem multiply_single (F : LatticeData) (t f : Oscillator F) (n : Charge F) :
    multiply F t (Finsupp.single n f) = Finsupp.single n (t*f) := by
  simp [multiply]

private theorem current_transverse_mul (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (j : Fin e) (k : ℕ) (m : ℤ)
    (v : Carrier (ambient D e B C hC hCe)) :
    neutralMode (ambient D e B C hC hCe) (i.castAdd e) m
        (multiply _ (transverse D B C hC hCe j k) v) =
      multiply _ (transverse D B C hC hCe j k)
        (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m v) := by
  have he : (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m).comp
      (multiply _ (transverse D B C hC hCe j k)) =
      (multiply _ (transverse D B C hC hCe j k)).comp
        (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m) := by
    apply Finsupp.lhom_ext
    intro n f
    simp only [LinearMap.comp_apply, multiply_single, neutralMode,
      Finsupp.lsum_single, Finsupp.lsingle_apply]
    congr 1
    by_cases hm : m < 0
    · simp [neutralPolynomialMode, hm, mul_left_comm]
    · by_cases hz : m = 0
      · simp [neutralPolynomialMode, hz, mul_smul_comm]
      · simp only [neutralPolynomialMode, hm, hz, ↓reduceIte]
        change (m : ℂ) • weightedPartial _ (i.castAdd e) (m-1).toNat
          (transverse D B C hC hCe j k * f) =
            transverse D B C hC hCe j k * ((m : ℂ) • weightedPartial _ _ _ f)
        rw [LatticeActualAnnihilation.annihilate_mul, partial_transverse D B C hC hCe hD]
        simp [mul_smul_comm]
  exact DFunLike.congr_fun he v

/-- The charged native field commutes past a transverse oscillator by the
Schur contraction, uniformly on every ambient target state. -/
theorem ground_transverse_commutator (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (j : Fin e) (k : ℕ) (m : ℤ)
    (v : Carrier (ambient D e B C hC hCe)) :
    ((actualField (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n))[[m]])
        (multiply _ (transverse D B C hC hCe j k) v) =
      multiply _ (transverse D B C hC hCe j k)
        (((actualField (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n))[[m]]) v) -
      (transversePair D B C a j : ℂ) •
        (((actualField (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n))
          [[m-(k+1 : ℕ)]]) v) := by
  let F := ambient D e B C hC hCe
  let A := liftCharge D B C hC hCe a n
  let T := transverse D B C hC hCe j k
  let s : ℂ := transversePair D B C a j
  have he : ((actualField F A)[[m]]).comp (multiply F T) =
      (multiply F T).comp ((actualField F A)[[m]]) -
        s • ((actualField F A)[[m-(k+1 : ℕ)]]) := by
    apply Finsupp.lhom_ext
    intro d f
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      multiply_single, LatticeActualGeneratorLocality.actual_modes,
      LatticeActualProductKernel.raw_single_convolution, map_smul]
    have ht : translatedPolynomial (ambient D e B C hC hCe)
        (liftCharge D B C hC hCe a n) (transverse D B C hC hCe j k) =
        Polynomial.C (transverse D B C hC hCe j k) -
          Polynomial.C ((transversePair D B C a j : ℂ) • 1) * Polynomial.X^(k+1) := by
      have hh := translated_mixed_polynomial D B C hC hCe hD a n 1 (X (j,k))
      have hone : translatedPolynomial (ambient D e B C hC hCe)
          (liftCharge D B C hC hCe a n) 1 = 1 := by simp [translatedPolynomial]
      simpa only [map_one, one_mul, transversePolynomial, transverseTranslation,
        aeval_X, hone] using hh
    change translatedPolynomial F A T = Polynomial.C T -
      Polynomial.C (s • 1) * Polynomial.X^(k+1) at ht
    rw [translated_mul, ht, sub_mul,
      map_sub, LatticeActualProductKernel.convolution_C_mul]
    rw [mul_assoc, LatticeActualProductKernel.convolution_C_mul,
      LatticeActualProductKernel.convolution_X_pow]
    rw [show -(m-(k+1 : ℕ))-1-bilinear F A d = -m-1-bilinear F A d+(k+1 : ℕ) by omega]
    simp only [smul_mul_assoc, one_mul, Finsupp.single_sub, Finsupp.smul_single,
      smul_sub, multiply_single, mul_smul_comm, smul_smul]
    simp [mul_comm]
  exact DFunLike.congr_fun he v

end
end D5.S3.VertexAlgebra.LatticeCosetSeparation
