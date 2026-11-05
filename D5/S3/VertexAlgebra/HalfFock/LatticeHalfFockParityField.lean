/- GID: D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual target-parity intertwining for corrected fields and its fixed-sector consumer. -/

/- No Jacobi, field equivariance, positive-definiteness, or output transport
   premise is added. Target parity is the already defined actualParity.

   New calculation: sigma intertwines the actual charged oscillator kernel;
   its propagation through actual normal words and finite Corr yields the
   target/source equivariance consumed by fixedParitySlice below.
   Classical order-two lattice orbifold mathematics; no novelty claim.
-/
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy
import D5.S3.VertexAlgebra.LatticeHalfFockParityT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedMonodromy
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockFiniteCorrection LatticeHalfFockParityT LatticeInvolution
open MvPolynomial

private theorem sigma_halfCreationSeries (D : LatticeData) (a : Charge D) :
    PowerSeries.map (sigma D) (halfCreationSeries D a) = halfCreationSeries D (-a) := by
  ext degree
  simp only [PowerSeries.coeff_map, halfCreationSeries, PowerSeries.coeff_mk]
  split_ifs <;>
    simp [map_sum, sigma_smul, Finset.sum_neg_distrib, smul_neg, neg_smul]

private theorem sigma_halfCreationExponential (D : LatticeData) (a : Charge D) :
    PowerSeries.map (sigma D) (halfCreationExponential D a) =
      halfCreationExponential D (-a) := by
  have h : PowerSeries.HasSubst (halfCreationSeries D a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have hm := PowerSeries.map_subst (h := sigma D) h (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (sigma D) (halfCreationExponential D a) =
    (PowerSeries.map (sigma D) (PowerSeries.exp (Oscillator D))).subst
      (PowerSeries.map (sigma D) (halfCreationSeries D a)) at hm
  rw [hm, PowerSeries.map_exp, sigma_halfCreationSeries]
  rfl

private theorem sigma_halfCreationCoeff (D : LatticeData) (a : Charge D) (e : ℤ) :
    sigma D (halfCreationCoeff D a e) = halfCreationCoeff D (-a) e := by
  unfold halfCreationCoeff
  split_ifs
  · exact map_zero _
  · rw [← PowerSeries.coeff_map, sigma_halfCreationExponential]

private theorem sigma_halfTranslatedPolynomial (D : LatticeData) (a : Charge D)
    (p : Oscillator D) :
    Polynomial.map (sigma D) (halfTranslatedPolynomial D a p) =
      halfTranslatedPolynomial D (-a) (sigma D p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [halfTranslatedPolynomial]
  | add p q hp hq =>
    simp only [halfTranslatedPolynomial, map_add, Polynomial.map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p x hp =>
    simp only [halfTranslatedPolynomial, map_mul, Polynomial.map_mul, sigma_X,
      map_neg, MvPolynomial.eval₂AlgHom_X] at hp ⊢
    rw [hp]
    congr 1
    simp [halfTranslationVariable, bilinear, sigma_smul, neg_smul, smul_neg]
    <;> ring

/-- New kernel intertwining, before any Jacobi or conformal consequence.
    Consumed by charged_parity and then correctedField_target_parity. -/
private theorem oscillator_sigma (D : LatticeData) (a : Charge D) (e : ℤ)
    (p : Oscillator D) :
    sigma D (oscillatorCoefficient D a e p) =
      oscillatorCoefficient D (-a) e (sigma D p) := by
  change sigmaLinear D (∑ᶠ r : ℕ, oscillatorTerm D a e p r) =
    ∑ᶠ r : ℕ, oscillatorTerm D (-a) e (sigma D p) r
  rw [map_finsum _ (charged_term_finite_support D a e p)]
  apply finsum_congr
  intro r
  change sigma D (oscillatorTerm D a e p r) = _
  simp only [oscillatorTerm, map_mul, sigma_halfCreationCoeff, norm_neg]
  rw [← Polynomial.coeff_map, sigma_halfTranslatedPolynomial]

private theorem charged_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu (chargedCoefficient D hu a e x) =
      chargedCoefficient D hu (-a) e (actualParity D hu x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    simp only [chargedCoefficient, actualParity, LinearMap.smul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, map_smul]
    change chargeScalar D a • (sigma D (oscillatorCoefficient D a e p) ⊗ₜ[ℂ]
      groundAction D hu a t) =
      chargeScalar D (-a) • (oscillatorCoefficient D (-a) e (sigma D p) ⊗ₜ[ℂ]
        groundAction D hu (-a) t)
    rw [oscillator_sigma, ground_neg]
    simp only [chargeScalar, norm_neg]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem sigma_current (D : LatticeData) (i : Fin D.rank) (j : ℤ)
    (p : Oscillator D) :
    sigma D (LatticeHalfFock.current D i j p) =
      -LatticeHalfFock.current D i j (sigma D p) := by
  unfold LatticeHalfFock.current
  split_ifs
  · simp [LinearMap.mulLeft_apply, map_mul]
  · change sigma D (LatticeHalfFock.frequency j •
      LatticeSugawaraCurrents.weightedPartial D i j.toNat p) =
      -(LatticeHalfFock.frequency j •
        LatticeSugawaraCurrents.weightedPartial D i j.toNat (sigma D p))
    have hw : sigma D (LatticeSugawaraCurrents.weightedPartial D i j.toNat p) =
        -LatticeSugawaraCurrents.weightedPartial D i j.toNat (sigma D p) := by
      simp only [LatticeSugawaraCurrents.weightedPartial, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, sigma_smul]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have hp := sigma_pderiv D (x, j.toNat) p
      change (D.G i x : ℂ) • sigma D ((pderiv (x, j.toNat)) p) =
        -((D.G i x : ℂ) • (pderiv (x, j.toNat)) (sigma D p))
      rw [hp]
      simp [smul_neg]
    rw [sigma_smul, hw, smul_neg]

private theorem parity_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Index D) (j : ℤ) (x : ActualTensor D hu) :
    actualParity D hu (jetCurrent D hu i j x) =
      -jetCurrent D hu i j (actualParity D hu x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    simp only [jetCurrent, actualParity, LatticeHalfFock.tensorCurrent,
      LatticeHalfFock.tensorEnd, LinearMap.smul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, map_smul]
    change jetScalar i.2 j • (sigma D (LatticeHalfFock.current D i.1 j p) ⊗ₜ[ℂ] t) =
      -(jetScalar i.2 j •
        (LatticeHalfFock.current D i.1 j (sigma D p) ⊗ₜ[ℂ] t))
    rw [sigma_current, TensorProduct.neg_tmul, smul_neg]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

private theorem flat_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (m : ModeTuple D w)
    (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu (flatCoefficient D hu (chargedField D hu a) w m e x) =
      ((-1 : ℂ)^w.length) •
        flatCoefficient D hu (chargedField D hu (-a)) w m e (actualParity D hu x) := by
  induction w generalizing e x with
  | nil =>
    simpa only [flatCoefficient, chargedField, HVertexOperator.coeff_of_coeff,
      List.length_nil, pow_zero, one_smul] using charged_parity D hu a e x
  | cons i w ih =>
    rcases m with ⟨j, m⟩
    by_cases hj : j < 0
    · simp only [flatCoefficient, if_pos hj, Module.End.mul_apply]
      rw [parity_jet, ih]
      simp [map_smul, List.length_cons, pow_succ, mul_comm, neg_smul]
    · simp only [flatCoefficient, if_neg hj, Module.End.mul_apply]
      rw [ih, parity_jet, map_neg]
      simp [List.length_cons, pow_succ, mul_comm, neg_smul]

private theorem word_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu ((wordField D hu (chargedField D hu a) w).coeff e x) =
      ((-1 : ℂ)^w.length) •
        (wordField D hu (chargedField D hu (-a)) w).coeff e (actualParity D hu x) := by
  rw [wordField_coefficient, wordField_coefficient,
    map_finsum _ (flatTerm_finite D hu (chargedField D hu a) w e x),
    smul_finsum' _ (flatTerm_finite D hu (chargedField D hu (-a)) w e (actualParity D hu x))]
  apply finsum_congr
  intro m
  exact flat_parity D hu a w m e x

private theorem polynomial_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu ((LatticeHalfFockFockNormalField.polynomialField D hu a p).coeff e x) =
      (LatticeHalfFockFockNormalField.polynomialField D hu (-a) (sigma D p)).coeff e
        (actualParity D hu x) := by
  let left : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    { toFun p := actualParity D hu
        ((LatticeHalfFockFockNormalField.polynomialField D hu a p).coeff e x)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let right : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    { toFun p :=
        (LatticeHalfFockFockNormalField.polynomialField D hu (-a) (sigma D p)).coeff e
          (actualParity D hu x)
      map_add' := by intros; simp
      map_smul' := by intros; simp [sigma_smul] }
  have maps : left = right := by
    apply (basisMonomials (Index D) ℂ).ext
    intro d
    change actualParity D hu
      ((LatticeHalfFockFockNormalField.polynomialField D hu a (monomial d 1)).coeff e x) =
      (LatticeHalfFockFockNormalField.polynomialField D hu (-a)
        (sigma D (monomial d 1))).coeff e (actualParity D hu x)
    rw [sigma_monomial, map_smul, polynomialField_monomial_public,
      polynomialField_monomial_public]
    have hocc : LatticeHalfFockFockNormalField.occurrences D d =
        LatticeAllStateField.occurrences D d := by
      simp [LatticeHalfFockFockNormalField.occurrences, LatticeAllStateField.occurrences]
    simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply, hocc] using
      word_parity D hu a (LatticeAllStateField.occurrences D d) e x
  exact LinearMap.congr_fun maps p

private theorem correctedSum_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (u : ℕ →₀ Oscillator D) (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu ((correctedSum D hu a u).coeff e x) =
      (correctedSum D hu (-a) (Finsupp.mapRange.linearMap (sigmaLinear D) u)).coeff e
        (actualParity D hu x) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hu, hv]
  | single s p =>
    simp only [correctedSum, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
    rw [shiftField_coefficient_public, shiftField_coefficient_public]
    exact polynomial_parity D hu a p (e + 2 * (s : ℤ)) x

private theorem correctedPolynomial_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu ((correctedPolynomial D hu a p).coeff e x) =
      (correctedPolynomial D hu (-a) (sigma D p)).coeff e (actualParity D hu x) := by
  simp only [correctedPolynomial, LinearMap.comp_apply]
  rw [Corr_sigma]
  exact correctedSum_parity D hu a (Corr D a p) e x

/-- Target/source equivariance on the original two different carriers.
    Consumed by fixed_parity_preserved and fixedParitySlice. -/
/- proof_shape: correctedField_target_parity: content
   admission_basis: escape-witness
   escape_witness: oscillator_sigma evaluates the actual charged oscillator
   kernel under sigma. Both normal-ordering branches consume its propagated
   signed-jet relation before finite word, correction and charge summation.
   Coordinate monodromy alone supplies no action on the target carrier. -/
theorem correctedField_target_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) :
    actualParity D hu ((correctedField D hu a).coeff e x) =
      (correctedField D hu (theta D a)).coeff e (actualParity D hu x) := by
  let left : Carrier D →ₗ[ℂ] ActualTensor D hu :=
    { toFun a := actualParity D hu ((correctedField D hu a).coeff e x)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let right : Carrier D →ₗ[ℂ] ActualTensor D hu :=
    { toFun a := (correctedField D hu (theta D a)).coeff e (actualParity D hu x)
      map_add' := by intros; simp
      map_smul' := by intros; simp [map_smul] }
  have h : left = right := by
    apply Finsupp.lhom_ext
    intro a p
    change actualParity D hu ((correctedField D hu (Finsupp.single a p)).coeff e x) =
      (correctedField D hu (thetaLinear D (Finsupp.single a p))).coeff e
        (actualParity D hu x)
    simp only [theta_single, correctedField, Finsupp.lsum_single]
    exact correctedPolynomial_parity D hu a p e x
  exact LinearMap.congr_fun h a

def paritySpace (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ) :
    Submodule ℂ (ActualTensor D hu) :=
  LinearMap.ker (actualParity D hu - s • LinearMap.id)

private theorem fixed_parity_preserved (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : FixedCarrier D) (e : ℤ) (x : ActualTensor D hu)
    (hx : x ∈ paritySpace D hu s) :
    (correctedField D hu a.val).coeff e x ∈ paritySpace D hu s := by
  have ha : theta D a.val = a.val := (mem_fixedSpace D a.val).mp a.property
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  rw [correctedField_target_parity, ha, hx, map_smul]

/-- Live consumer: the actual fixed-source field on each target parity space.
    No Jacobi axiom is stored as a new hypothesis. Its module Jacobi law is
    inherited only after native verification of the separate doubled-mode law.
    The choices s=1 and s=-1 give the two orbifold-sector actions. -/
def fixedParitySlice (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (a : FixedCarrier D) : VertexOperator ℂ (paritySpace D hu s) :=
  VertexOperator.of_coeff
    (fun e => ((correctedField D hu a.val).coeff (2*e)).restrict
      (fun x hx => fixed_parity_preserved D hu s a (2*e) x hx)) (by
      intro x
      refine ⟨(((HahnModule.of ℂ).symm ((correctedField D hu a.val) x.val)).order) / 2 - 1, ?_⟩
      intro e member
      by_contra outside
      apply member
      apply Subtype.ext
      change ((HahnModule.of ℂ).symm ((correctedField D hu a.val) x.val)).coeff (2*e) = 0
      apply HahnSeries.coeff_eq_zero_of_lt_order
      omega)

end D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
