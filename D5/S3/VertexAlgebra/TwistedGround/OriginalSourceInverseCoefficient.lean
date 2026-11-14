/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mode-dependent bilinear factorial transpose and original inverse row coefficients. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
import D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource

/-! Mode-dependent polynomial substitution and its ordinary transpose for the
factorial complex bilinear form. The original inverse covariance retains the
integer frequency k+1. Positive-energy support makes the source Taylor and
occupation contractions finite; the final application retains both charges,
all five occupation factorials and every integer Laurent selector.

proof_shape: content for pderiv_substitution and substitution_factorial_transpose;
admission_basis: escape-witness. The chain rule and bilinear transpose are used
on the live original source-inverse readout path. Normalization and finite-sum
helpers organize that path and do not provide independent admission witnesses.
Utility is none: arbitrary polynomials, occupations and integer modes are in
scope; finite sums express coefficients, not bounded certificate enumeration.
Factorial Fock and Gaussian calculus are classical; this carrier-specific
composition is repo-derived and makes no literature-priority claim. No affine
sewing, Laurent-transfer equation or global identityK is assumed or concluded.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient

open MvPolynomial LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeAllStateField LatticeHalfFock LatticeInvolution
open OriginalCurrentMetric SignedOscillatorWick
open LatticeHalfFockChargedTensorCoefficients
open SourceBPZ.OriginalSourceCoevaluation SourceBPZ.SourcePairingLaws
open OriginalFourMChargeCoset OriginalNormalRowSource
open OriginalCorrectedRowRecompositionSource OriginalAffineRecompositionSource
open FactorialFockMetric (weight weight_pos)

private theorem weight_ne_zero {D : LatticeData} (alpha : Exponent D) :
    (weight alpha : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (weight_pos alpha))

section Transpose
variable {D : LatticeData}

private theorem substitution_constant
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Oscillator D) :
    (substitution A p).coeff 0 = p.coeff 0 := by
  classical
  change constantCoeff (substitution A p) = constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, map_mul, map_mul, hp, substitution_X]
    simp [variableImage, map_sum]

private theorem pderiv_variableImage
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (i : Fin D.rank) (k : ℕ) (x : Index D) :
    pderiv (i,k) (variableImage A x) =
      if k = x.2 then A k i x.1 • (1 : Oscillator D) else 0 := by
  classical
  by_cases h : k = x.2
  · subst k
    simp [variableImage, pderiv_X, Pi.single_apply, Prod.mk.injEq, eq_comm]
  · simp [variableImage, pderiv_X, Prod.mk.injEq, h, Ne.symm h]

/-- Actual polynomial chain rule for the existing same-mode substitution.
Its row/column order is fixed by variableImage, not by a Gaussian convention. -/
theorem pderiv_substitution
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    pderiv (i,k) (substitution A p) =
      ∑ a : Fin D.rank, A k i a • substitution A (pderiv (a,k) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p x hp =>
    rcases x with ⟨l,m⟩
    rw [map_mul, substitution_X, pderiv_mul, hp, pderiv_variableImage]
    simp only [pderiv_mul, map_add, map_mul, substitution_X,
      smul_add, Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_mul, smul_mul_assoc]
    · by_cases h : k = m
      · subst m
        simp [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      · simp [pderiv_X, Prod.mk.injEq, h, Ne.symm h]

/-! The lattice Gram matrix is symmetric, so the modewise inverse used by the
source transpose is symmetric as well.  This removes a purely notational
transpose before the finite coefficient is matched with the right affine row. -/

private theorem gramComplex_inverse_transpose (D : LatticeData) :
    ((gramComplex D)⁻¹)ᵀ = (gramComplex D)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  ext i j
  simp [gramComplex, D.symmetric]

theorem inverse_substitution_matrix_transpose (D : LatticeData) (k : ℕ) :
    (((-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹))ᵀ =
      (-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹ := by
  rw [Matrix.transpose_smul, gramComplex_inverse_transpose]

theorem inverse_substitution_coeff_transpose_free (D : LatticeData)
    (q : Oscillator D) (alpha : Exponent D) :
    (substitution (fun k =>
      (((-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹))ᵀ) q).coeff alpha =
      (substitution (fun k =>
        (-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹) q).coeff alpha := by
  have hfun : (fun k : ℕ =>
      (((-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹))ᵀ) =
      (fun k : ℕ => (-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹) := by
    funext k
    exact inverse_substitution_matrix_transpose D k
  exact congrArg (fun A => (substitution A q).coeff alpha) hfun

/-! Coefficient extraction commutes with the finite source polynomial used by
the inverse readout.  Keeping the scalar on the monomial explicit is useful
for the next affine-row identification: the remaining work is then entirely
the coefficient of one inverse-substituted monomial. -/

theorem substitution_finset_coeff (D : LatticeData)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (S : Finset (Exponent D)) (r : Exponent D → ℂ) (alpha : Exponent D) :
    (substitution A (∑ delta ∈ S, monomial delta (r delta))).coeff alpha =
      ∑ delta ∈ S, r delta *
        (substitution A (monomial delta 1)).coeff alpha := by
  classical
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro delta hdelta
  rw [show monomial delta (r delta) = r delta • monomial delta 1 by
    simp only [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coeff_smul, smul_eq_mul]

/-- Ordinary transpose, with no conjugation, for the original factorial form. -/
theorem substitution_factorial_transpose
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p q : Oscillator D) :
    FactorialBilinear.form (Index D) (substitution A p) q =
      FactorialBilinear.form (Index D) p
        (substitution (fun k => (A k)ᵀ) q) := by
  classical
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
    rw [show substitution A (C c) = C c from (substitution A).commutes c]
    change FactorialBilinear.form (Index D) (monomial 0 c) q =
      FactorialBilinear.form (Index D) (monomial 0 c)
        (substitution (fun k => (A k)ᵀ) q)
    rw [FactorialBilinear.monomial_left, FactorialBilinear.monomial_left,
      substitution_constant]
  | add p r hp hr =>
    simp only [map_add, LinearMap.add_apply, hp, hr]
  | mul_X p x hp =>
    rcases x with ⟨i,k⟩
    rw [map_mul, substitution_X, variableImage, Finset.mul_sum]
    simp only [mul_smul_comm, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply]
    calc
      (∑ a : Fin D.rank, A k a i *
          FactorialBilinear.form (Index D) (substitution A p * X (a,k)) q) =
          ∑ a : Fin D.rank, A k a i *
            FactorialBilinear.form (Index D) p
              (substitution (fun k => (A k)ᵀ) (pderiv (a,k) q)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [mul_comm (substitution A p), FactorialBilinear.creation, hp]
      _ = FactorialBilinear.form (Index D) p
          (pderiv (i,k) (substitution (fun k => (A k)ᵀ) q)) := by
        rw [pderiv_substitution]
        simp only [Matrix.transpose_apply, map_sum, map_smul, smul_eq_mul]
      _ = _ := by rw [mul_comm p, FactorialBilinear.creation]

private theorem form_eq_sum (p q : Oscillator D) :
    FactorialBilinear.form (Index D) p q =
      ∑ delta ∈ p.support, p.coeff delta * (weight delta : ℂ) * q.coeff delta := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, LinearMap.sum_apply, FactorialBilinear.monomial_left]
  apply Finset.sum_congr rfl
  intro delta hd
  ring

/-- Internal occupation identity BEFORE inserting either Gaussian row. -/
theorem inverse_occupation_coefficient
    (D : LatticeData) (alpha : Exponent D) (q : Oscillator D) :
    (∑ delta ∈ (inverseOscillator D (monomial alpha 1)).support,
      (inverseOscillator D (monomial alpha 1)).coeff delta *
        (weight delta : ℂ) * q.coeff delta) =
      (weight alpha : ℂ) *
        (substitution (fun k =>
          (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ) q).coeff alpha := by
  rw [← form_eq_sum]
  change FactorialBilinear.form (Index D)
      (substitution (fun k => (-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹)
        (monomial alpha 1)) q = _
  rw [substitution_factorial_transpose, FactorialBilinear.monomial_left, mul_one]

end Transpose

/-- Exact native positive-energy sublevel. In particular n=0 contains only 0.
Finiteness is reused from oscillatorLeFinite; no charge positivity is needed. -/
def oscillatorSublevel (D : LatticeData) (n : ℕ) : Finset (Exponent D) := by
  classical
  letI := oscillatorLeFinite D n
  letI := Fintype.ofFinite {alpha : Exponent D // oscillatorEnergy alpha ≤ n}
  exact (Finset.univ : Finset {alpha : Exponent D // oscillatorEnergy alpha ≤ n}).image
    Subtype.val

@[simp] private theorem mem_oscillatorSublevel (D : LatticeData) (n : ℕ)
    (alpha : Exponent D) :
    alpha ∈ oscillatorSublevel D n ↔ oscillatorEnergy alpha ≤ n := by
  classical
  simp [oscillatorSublevel]

/-- Factorial-normalized ordinary Taylor polynomial of an ORIGINAL functional.
This is a finite polynomial, not a sewing definition or an exponential ansatz. -/
def sourceTaylor (D : LatticeData) (f : Module.Dual ℂ (Oscillator D))
    (n : ℕ) : Oscillator D :=
  ∑ delta ∈ oscillatorSublevel D n,
    monomial delta ((weight delta : ℂ)⁻¹ * f (monomial delta 1))

theorem sourceTaylor_coeff (D : LatticeData) (f : Module.Dual ℂ (Oscillator D))
    (n : ℕ) (alpha : Exponent D) :
    (sourceTaylor D f n).coeff alpha =
      if oscillatorEnergy alpha ≤ n then
        (weight alpha : ℂ)⁻¹ * f (monomial alpha 1) else 0 := by
  classical
  simp [sourceTaylor, coeff_monomial, eq_comm]

private theorem integer_weight (D : LatticeData) (alpha : Exponent D) :
    Finsupp.weight (fun x : Index D => (x.2 : ℤ)+1) alpha =
      (oscillatorEnergy alpha : ℤ) := by
  simp [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_add]

/-- All nonzero terms of the LITERAL original inverse retain k+1 energy. -/
theorem inverse_support_energy (D : LatticeData) (alpha delta : Exponent D)
    (hd : delta ∈ (inverseOscillator D (monomial alpha 1)).support) :
    oscillatorEnergy delta = oscillatorEnergy alpha := by
  have hw := substitution_monomial_weight D
    (fun k => (-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹) alpha 1
  have he := hw (MvPolynomial.mem_support_iff.mp hd)
  rw [integer_weight, integer_weight] at he
  exact_mod_cast he

/-- Reorder the actual inverse-substitution occupations on ONE common finite
energy sublevel. The support extension is proved before Finset.sum_comm. -/
theorem inverse_occupation_interchange (D : LatticeData) (n : ℕ)
    (F G : Exponent D → ℂ) :
    (∑ alpha ∈ oscillatorSublevel D n, F alpha *
      ∑ delta ∈ (inverseOscillator D (monomial alpha 1)).support,
        (inverseOscillator D (monomial alpha 1)).coeff delta * G delta) =
    ∑ delta ∈ oscillatorSublevel D n, ∑ alpha ∈ oscillatorSublevel D n,
      F alpha * (inverseOscillator D (monomial alpha 1)).coeff delta * G delta := by
  classical
  have h (alpha : Exponent D) (ha : alpha ∈ oscillatorSublevel D n) :
      (∑ delta ∈ (inverseOscillator D (monomial alpha 1)).support,
        (inverseOscillator D (monomial alpha 1)).coeff delta * G delta) =
      ∑ delta ∈ oscillatorSublevel D n,
        (inverseOscillator D (monomial alpha 1)).coeff delta * G delta := by
    apply Finset.sum_subset
    · intro delta hd
      apply (mem_oscillatorSublevel D n delta).mpr
      rw [inverse_support_energy D alpha delta hd]
      exact (mem_oscillatorSublevel D n alpha).mp ha
    · intro delta hd hnot
      rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
  calc
    _ = ∑ alpha ∈ oscillatorSublevel D n, ∑ delta ∈ oscillatorSublevel D n,
        F alpha * (inverseOscillator D (monomial alpha 1)).coeff delta * G delta := by
      apply Finset.sum_congr rfl
      intro alpha ha
      rw [h alpha ha, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro delta hd
      ring
    _ = _ := Finset.sum_comm

private theorem functional_eq_form (D : LatticeData)
    (f : Module.Dual ℂ (Oscillator D)) (alpha : Exponent D)
    (n : ℕ) (ha : oscillatorEnergy alpha ≤ n) :
    f (inverseOscillator D (monomial alpha 1)) =
      FactorialBilinear.form (Index D)
        (inverseOscillator D (monomial alpha 1)) (sourceTaylor D f n) := by
  classical
  let p := inverseOscillator D (monomial alpha 1)
  have hmem := (mem_oscillatorSublevel D n alpha).mpr ha
  have hi := inverse_occupation_interchange D n
    (fun beta => if beta = alpha then 1 else 0)
    (fun delta => f (monomial delta 1))
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hmem, ite_true] at hi
  change f p = FactorialBilinear.form (Index D) p (sourceTaylor D f n)
  rw [FactorialBilinear.symmetric, sourceTaylor, map_sum, LinearMap.sum_apply]
  conv_lhs => rw [p.as_sum]
  simp only [map_sum]
  calc
    _ = ∑ delta ∈ p.support, p.coeff delta * f (monomial delta 1) := by
      apply Finset.sum_congr rfl
      intro delta hd
      rw [show monomial delta (p.coeff delta) =
        p.coeff delta • (monomial delta 1 : Oscillator D) by simp [smul_monomial],
        map_smul, smul_eq_mul]
    _ = ∑ delta ∈ oscillatorSublevel D n, p.coeff delta * f (monomial delta 1) := hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro delta hd
      rw [FactorialBilinear.monomial_left]
      field_simp [weight_ne_zero delta]
      <;> ring

/-- Native source coevaluation is exactly one coefficient after the proved
transpose substitution. Both factorials in this argument are CANCELLED, not
silently discarded. This applies to every original linear source readout. -/
theorem dual_readout_coefficient (D : LatticeData)
    (f : Module.Dual ℂ (Oscillator D)) (alpha : Exponent D)
    (n : ℕ) (ha : oscillatorEnergy alpha ≤ n) :
    f (dualOscillatorMonomial D alpha) =
      (substitution (fun k =>
        (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ)
        (sourceTaylor D f n)).coeff alpha := by
  rw [dualOscillatorMonomial, map_smul, smul_eq_mul,
    functional_eq_form D f alpha n ha, form_eq_sum,
    inverse_occupation_coefficient,
    ← mul_assoc, inv_mul_cancel₀ (weight_ne_zero alpha), one_mul]

/-- The actual infinite occupation coefficient has finite support at energy n.
No analytic sum, q=1 specialization, or norm premise occurs. -/
theorem energy_readout_finite (D : LatticeData)
    (f g : Module.Dual ℂ (Oscillator D)) (n : ℕ) :
    Function.HasFiniteSupport (fun alpha : Exponent D => if oscillatorEnergy alpha = n then
      f (monomial alpha 1) * g (dualOscillatorMonomial D alpha) else 0) := by
  apply (oscillatorSublevel D n).finite_toSet.subset
  intro alpha ha
  by_contra hn
  have he : oscillatorEnergy alpha ≠ n := by
    intro he
    exact hn ((mem_oscillatorSublevel D n alpha).mpr he.le)
  exact ha (ite_eq_right he)

/-- Coefficientwise finite native coevaluation, with exactly ONE internal
occupation factorial. f and g can be the actual charged corrected-row tests. -/
theorem finite_energy_inverse_coefficients (D : LatticeData)
    (f g : Module.Dual ℂ (Oscillator D)) (n : ℕ) :
    (∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      f (monomial alpha 1) * g (dualOscillatorMonomial D alpha) else 0) =
    ∑ alpha ∈ oscillatorSublevel D n, if oscillatorEnergy alpha = n then
      (weight alpha : ℂ) * (sourceTaylor D f n).coeff alpha *
        (substitution (fun k =>
          (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ)
          (sourceTaylor D g n)).coeff alpha else 0 := by
  classical
  rw [finsum_eq_sum_of_support_toFinset_subset _ (energy_readout_finite D f g n)
    (s := oscillatorSublevel D n)]
  · apply Finset.sum_congr rfl
    intro alpha ha
    have he := (mem_oscillatorSublevel D n alpha).mp ha
    rw [dual_readout_coefficient D g alpha n he, sourceTaylor_coeff, ite_eq_left he]
    by_cases hn : oscillatorEnergy alpha = n
    · rw [ite_eq_left hn, ite_eq_left hn]
      field_simp [weight_ne_zero alpha]
    · rw [ite_eq_right hn, ite_eq_right hn]
  · intro alpha ha
    have ha := (energy_readout_finite D f g n).mem_toFinset.mp ha
    by_contra hn
    have he : oscillatorEnergy alpha ≠ n := by
      intro he
      exact hn ((mem_oscillatorSublevel D n alpha).mpr he.le)
    exact ha (ite_eq_right he)

/-- The original corrected source readout, with arbitrary detector and input. -/
def correctedSourceReadout (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (R S : Oscillator D) :
    Module.Dual ℂ (Oscillator D) where
  toFun p := wick D S (oscillatorCorrected D hu a e p R)
  map_add' p q := by simp only [map_add, LinearMap.add_apply]
  map_smul' c p := by
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Applying the accepted-row SOURCE formula to the finite Taylor polynomial
cancels its source factorial, leaving both external factorials literally. -/
theorem corrected_sourceTaylor (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (beta gamma : Exponent D) (n : ℕ) :
    sourceTaylor D
      (correctedSourceReadout D hu a e (monomial beta 1) (monomial gamma 1)) n =
    ((weight beta : ℂ) * (weight gamma : ℂ)) •
      ∑ delta ∈ oscillatorSublevel D n,
        monomial delta
          (let K := rowSupport D delta beta gamma
           let label := supportLabel D K
           affineLaurent (correctedMatrix D label) (correctedMean D a label)
             (normalWeight D label)
             (threeOccupation (restricted D K delta) (restricted D K beta)
               (restricted D K gamma)) (e+chargeNorm D a)) := by
  classical
  rw [sourceTaylor, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro delta hd
  change monomial delta ((weight delta : ℂ)⁻¹ *
      wick D (monomial gamma 1)
        (oscillatorCorrected D hu a e (monomial delta 1) (monomial beta 1))) = _
  rw [original_corrected_gaussian_row, smul_monomial]
  congr 1
  dsimp only
  simp only [smul_eq_mul]
  field_simp [weight_ne_zero delta]

/-- A genuine two-original-row/source-inverse coefficient identity.
There is ONE internal alpha!, FOUR external factorials, both original charge
scalars, arbitrary charge and integer Laurent modes. The left theta projection
is applied only once in cosetKernel; it is deliberately not duplicated here.

The first remaining affine application is identification of the transposed
finite polynomial coefficient below with the FH right affine coefficient at
B=T^t A_R T, S=T^t H_R, v=T^t mu_R, uniformly in the external variables and
the signed Laurent selectors. This theorem does not assume that equation.
-/
theorem original_two_rows_inverse_coefficient
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n : ℕ) (ha : oscillatorEnergy alpha ≤ n) :
    chargeScalar D a * chargeScalar D (-a) *
      wick D (monomial gammaL 1)
        (oscillatorCorrected D hu a eL (monomial alpha 1) (monomial betaL 1)) *
      wick D (monomial gammaR 1)
        (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) =
    let row := fun (b : Charge D) (beta gamma delta : Exponent D) (e : ℤ) =>
      let K := rowSupport D delta beta gamma
      let label := supportLabel D K
      affineLaurent (correctedMatrix D label) (correctedMean D b label)
        (normalWeight D label)
        (threeOccupation (restricted D K delta) (restricted D K beta)
          (restricted D K gamma)) (e+chargeNorm D b)
    chargeScalar D a * chargeScalar D (-a) *
      (weight alpha : ℂ) * (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) * row a betaL gammaL alpha eL *
      (substitution (fun k =>
        (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ)
        (∑ delta ∈ oscillatorSublevel D n,
          monomial delta (row (-a) betaR gammaR delta eR))).coeff alpha := by
  classical
  have hr := dual_readout_coefficient D
    (correctedSourceReadout D hu (-a) eR
      (monomial betaR 1) (monomial gammaR 1)) alpha n ha
  rw [corrected_sourceTaylor, map_smul, coeff_smul] at hr
  change wick D (monomial gammaR 1)
      (oscillatorCorrected D hu (-a) eR
        (dualOscillatorMonomial D alpha) (monomial betaR 1)) = _ at hr
  rw [hr, original_corrected_gaussian_row]
  dsimp only
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
