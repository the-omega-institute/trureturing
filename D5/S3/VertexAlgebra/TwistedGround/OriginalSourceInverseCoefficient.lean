/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original source inverse transport into the native affine Gaussian with exact Laurent selectors. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
import D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
import D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport

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
composition is repo-derived and makes no literature-priority claim. The
native affine comparison in NativeAffineTransport and the original-row
source_inverse_affine_row_box supply the transport content; normalization helpers have actual proof consumers.
No full sewing equation or global identityK is assumed or concluded.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
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

The finite coefficient is transported to the native right affine Gaussian
in original_two_rows_inverse_affine_coefficient. External occupations and
the signed Laurent selectors are retained throughout that comparison.
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

section NativeTransport
open NativeAffineTransport
open OriginalChargedRowSource
open NativeGaussianMoment (weight_sub_single sub_single_degree occupation_nonzero)
open FactorialFockQuadraticEstimate (quadratic gaussianPiece gaussianPiece_pderiv)

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem correctedMatrix_symm (D : LatticeData) (label : I ↪ Index D) :
    ∀ i j, correctedMatrix D label i j = correctedMatrix D label j i := by
  rintro (i | (i | i)) (j | (j | j)) <;>
    simp only [correctedMatrix] <;>
    first | exact sourceCovariance_symm D label _ _ | exact normalMatrix_symm D label _ _


/-- Finite mode coordinates retain every colour at every included mode. -/
def boxLabel (D : LatticeData) (M : ℕ) : (Fin D.rank × Fin M) ↪ Index D where
  toFun b := (b.1,b.2.val)
  inj' := by
    rintro ⟨i,k⟩ ⟨j,l⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.ext h.2)

/-- The exact finite restriction of a mode-dependent coordinate substitution. -/
def boxMatrix (D : LatticeData) (M : ℕ)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Matrix (Fin D.rank × Fin M) (Fin D.rank × Fin M) ℂ :=
  fun i j => if i.2 = j.2 then A j.2.val i.1 j.1 else 0

def boxOccupation (D : LatticeData) (M : ℕ) (d : Exponent D) :
    (Fin D.rank × Fin M) →₀ ℕ :=
  d.comapDomain (boxLabel D M) (boxLabel D M).injective.injOn

theorem box_reconstruct (D : LatticeData) (M : ℕ) (d : Exponent D)
    (hd : ∀ b ∈ d.support, b.2 < M) :
    (boxOccupation D M d).embDomain (boxLabel D M) = d := by
  apply Finsupp.embDomain_comapDomain
  intro b hb
  exact ⟨(b.1,⟨b.2,hd b hb⟩),rfl⟩

private theorem box_degree (D : LatticeData) (M : ℕ) (d : Exponent D)
    (hd : ∀ b ∈ d.support, b.2 < M) :
    (boxOccupation D M d).degree = d.degree := by
  have h := congrArg Finsupp.degree (box_reconstruct D M d hd)
  simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using h

private theorem box_substitution (D : LatticeData) (M : ℕ)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : MvPolynomial (Fin D.rank × Fin M) ℂ) :
    rename (boxLabel D M) (linearSubstitution (boxMatrix D M A) p) =
      substitution A (rename (boxLabel D M) p) := by
  classical
  have he : (rename (boxLabel D M)).comp (linearSubstitution (boxMatrix D M A)) =
      (substitution A).comp (rename (boxLabel D M)) := by
    ext ⟨j,k⟩
    simp [linearSubstitution, boxMatrix, boxLabel, substitution_X, variableImage,
      Fintype.sum_prod_type, map_sum, map_smul, eq_comm]
  exact congrArg (fun f => f p) he

private theorem energy_degree (D : LatticeData) (d : Exponent D) :
    d.degree ≤ oscillatorEnergy d := by
  classical
  change (∑ b ∈ d.support, d b) ≤ ∑ b ∈ d.support, d b * (b.2+1)
  apply Finset.sum_le_sum
  intro b hb
  nlinarith

theorem energy_mode (D : LatticeData) (d : Exponent D) (n M : ℕ)
    (hd : oscillatorEnergy d ≤ n) (hn : n < M) :
    ∀ b ∈ d.support, b.2 < M := by
  intro b hb
  have hpos : 0 < d b := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hb)
  have hle : d b * (b.2+1) ≤ oscillatorEnergy d := by
    simpa only [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
      (Finset.single_le_sum (f := fun x : Index D => d x * (x.2+1))
        (fun _ _ => Nat.zero_le _) hb :
        d b * (b.2+1) ≤ ∑ x ∈ d.support, d x * (x.2+1))
  nlinarith

theorem correctedLaurentRow_on_box (D : LatticeData) (a : Charge D)
    (delta beta gamma : Exponent D) (M : ℕ)
    (hd : ∀ b ∈ delta.support, b.2 < M)
    (hb : ∀ b ∈ beta.support, b.2 < M)
    (hc : ∀ b ∈ gamma.support, b.2 < M) :
    (let L := rowSupport D delta beta gamma;
      affineLaurent (correctedMatrix D (supportLabel D L))
        (correctedMean D a (supportLabel D L)) (normalWeight D (supportLabel D L))
        (threeOccupation (restricted D L delta) (restricted D L beta)
          (restricted D L gamma))) =
      affineLaurent (correctedMatrix D (boxLabel D M))
        (correctedMean D a (boxLabel D M)) (normalWeight D (boxLabel D M))
        (threeOccupation (boxOccupation D M delta) (boxOccupation D M beta)
          (boxOccupation D M gamma)) := by
  classical
  let L := rowSupport D delta beta gamma
  have hL : ∀ b ∈ L, b.2 < M := by
    intro b hb'
    rcases Finset.mem_union.mp hb' with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hd b h
      · exact hb b h
    · exact hc b h
  let e : {b // b ∈ L} ↪ (Fin D.rank × Fin M) :=
    { toFun := fun b => (b.val.1,⟨b.val.2,hL b.val b.property⟩)
      inj' := by
        intro b c he
        apply Subtype.ext
        exact congrArg (boxLabel D M) he }
  have hi (p : Exponent D) (hp : p.support ⊆ L) :
      (restricted D L p).embDomain e = boxOccupation D M p := by
    apply Finsupp.embDomain_injective (boxLabel D M)
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
      Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_fun_comp]
    change (restricted D L p).mapDomain (supportLabel D L) =
      (boxOccupation D M p).mapDomain (boxLabel D M)
    rw [← Finsupp.embDomain_eq_mapDomain, ← Finsupp.embDomain_eq_mapDomain,
      restricted_reconstruct D L p hp, box_reconstruct D M p (fun b hb' => hL b (hp hb'))]
  have hdelta : delta.support ⊆ L :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hbeta : beta.support ⊆ L :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hgamma : gamma.support ⊆ L := Finset.subset_union_right
  dsimp only
  have he := affineLaurent_enlarge
    (correctedMatrix D (boxLabel D M)) (correctedMean D a (boxLabel D M))
    (normalWeight D (boxLabel D M)) (e.sumMap (e.sumMap e))
    (threeOccupation (restricted D L delta) (restricted D L beta) (restricted D L gamma))
  rw [map_three, hi delta hdelta, hi beta hbeta, hi gamma hgamma] at he
  have hA : (fun i j => correctedMatrix D (boxLabel D M)
      ((e.sumMap (e.sumMap e)) i) ((e.sumMap (e.sumMap e)) j)) =
      correctedMatrix D (supportLabel D L) := by
    funext x y
    rcases x with i | (i | i) <;> rcases y with j | (j | j) <;> rfl
  have hmu : (fun i => correctedMean D a (boxLabel D M)
      ((e.sumMap (e.sumMap e)) i)) = correctedMean D a (supportLabel D L) := by
    funext x
    rcases x with i | (i | i) <;> rfl
  have hw : (fun i => normalWeight D (boxLabel D M)
      ((e.sumMap (e.sumMap e)) i)) = normalWeight D (supportLabel D L) := by
    funext x
    rcases x with i | (i | i) <;> rfl
  rw [hA, hmu, hw] at he
  exact he.symm

private theorem substitution_coeff_energy (D : LatticeData)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p q : Oscillator D) (alpha : Exponent D) (c : ℂ)
    (h : ∀ delta, oscillatorEnergy delta = oscillatorEnergy alpha →
      p.coeff delta = c * q.coeff delta) :
    (substitution A p).coeff alpha = c * (substitution A q).coeff alpha := by
  classical
  have hw (delta : Exponent D)
      (hd : (substitution A (monomial delta 1)).coeff alpha ≠ 0) :
      oscillatorEnergy delta = oscillatorEnergy alpha := by
    have hh := substitution_monomial_weight D A delta 1 hd
    rw [integer_weight, integer_weight] at hh
    exact_mod_cast hh.symm
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [q.as_sum]
  simp only [map_sum, coeff_sum, Finset.mul_sum]
  have ht (delta : Exponent D) (z : ℂ) :
      (substitution A (monomial delta z)).coeff alpha =
        z * (substitution A (monomial delta 1)).coeff alpha := by
    rw [show monomial delta z = z • monomial delta 1 by simp [smul_monomial],
      map_smul, coeff_smul, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro delta hd hout
    rw [ht delta (p.coeff delta)]
    by_cases hz : (substitution A (monomial delta 1)).coeff alpha = 0
    · rw [hz, mul_zero]
    · rw [h delta (hw delta hz), MvPolynomial.notMem_support_iff.mp hout, mul_zero, zero_mul]
  · intro delta hd hout
    rw [ht delta (q.coeff delta)]
    by_cases hz : (substitution A (monomial delta 1)).coeff alpha = 0
    · rw [hz, mul_zero, mul_zero]
    · have hh := h delta (hw delta hz)
      rw [MvPolynomial.notMem_support_iff.mp hout] at hh
      rw [← mul_assoc, ← hh, zero_mul]
  · intro delta hd he
    rw [ht delta (p.coeff delta), ht delta (q.coeff delta)]
    by_cases hz : (substitution A (monomial delta 1)).coeff alpha = 0
    · rw [hz, mul_zero, mul_zero, mul_zero]
    · rw [h delta (hw delta hz), mul_assoc]


theorem box_energy (D : LatticeData) (M : ℕ) (d : Exponent D)
    (hd : ∀ b ∈ d.support, b.2 < M) :
    Finsupp.weight (fun i => LatticeHalfFockFiniteCorrection.sourceWeight D (boxLabel D M i))
      (boxOccupation D M d) = oscillatorEnergy d := by
  have h := congrArg (Finsupp.weight (fun b : Index D => b.2+1))
    (box_reconstruct D M d hd)
  simpa only [Finsupp.weight_apply, Finsupp.sum_embDomain, oscillatorEnergy,
    LatticeHalfFockFiniteCorrection.sourceWeight] using h

theorem source_inverse_affine_row_box
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha beta gamma : Exponent D) (e : ℤ) (n M : ℕ)
    (ha : oscillatorEnergy alpha ≤ n) (hn : n < M)
    (hb : ∀ b ∈ beta.support, b.2 < M) (hg : ∀ b ∈ gamma.support, b.2 < M) :
    wick D (monomial gamma 1) (oscillatorCorrected D hu a e
      (dualOscillatorMonomial D alpha) (monomial beta 1)) =
    let label := boxLabel D M
    let B := boxMatrix D M (fun k => (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ)
    let U := sourceBlock (J := (Fin D.rank × Fin M) ⊕ (Fin D.rank × Fin M)) B
    (weight beta : ℂ) * (weight gamma : ℂ) *
      affineLaurent (transportCovariance U (correctedMatrix D label))
        (transportMean U (correctedMean D a label)) (normalWeight D label)
        (threeOccupation (boxOccupation D M alpha) (boxOccupation D M beta)
          (boxOccupation D M gamma)) (e+chargeNorm D a) := by
  classical
  let label := boxLabel D M
  let A := correctedMatrix D label
  let mu := correctedMean D a label
  let h := (boxOccupation D M beta).sumElim (boxOccupation D M gamma)
  let d := boxOccupation D M alpha
  let N := n+beta.degree+gamma.degree
  let R := externalSection (expCut (affineExponent A mu) N) h
  let q : Oscillator D := rename label R
  let w := Finsupp.weight (normalWeight D label) (d.sumElim h)
  let c : ℂ := if e+chargeNorm D a = w then (weight beta : ℂ)*(weight gamma : ℂ) else 0
  let B := fun k : ℕ => (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ
  let f := correctedSourceReadout D hu a e (monomial beta 1) (monomial gamma 1)
  have hA : ∀ i j, A i j = A j i := correctedMatrix_symm D label
  have hmode := energy_mode D alpha n M ha hn
  have hdeg (delta : Exponent D) (hd : oscillatorEnergy delta ≤ n) :
      ((boxOccupation D M delta).sumElim h).degree ≤ N := by
    have ht : ((boxOccupation D M delta).sumElim h).degree =
        (boxOccupation D M delta).degree + (boxOccupation D M beta).degree +
          (boxOccupation D M gamma).degree := by
      simp only [h, Finsupp.degree_eq_sum, Fintype.sum_sum_type,
        Finsupp.sumElim_inl, Finsupp.sumElim_inr, add_assoc]
    rw [ht, box_degree D M delta (energy_mode D delta n M hd hn),
      box_degree D M beta hb, box_degree D M gamma hg]
    have hh := energy_degree D delta
    dsimp only [N]
    omega
  have hq (delta : Exponent D) (hd : oscillatorEnergy delta ≤ n) :
      q.coeff delta = affineCoefficient A mu
        ((boxOccupation D M delta).sumElim h) := by
    calc
      q.coeff delta = q.coeff ((boxOccupation D M delta).embDomain label) := by
        rw [box_reconstruct D M delta (energy_mode D delta n M hd hn)]
      _ = R.coeff (boxOccupation D M delta) :=
        coeff_rename_embDomain label R _
      _ = (expCut (affineExponent A mu) N).coeff
          ((boxOccupation D M delta).sumElim h) := externalSection_coeff _ _ _
      _ = _ := ((native_affine_eq_taylor A mu hA _).trans
          (taylorCoefficient_cut A mu _ N (hdeg delta hd))).symm
  have hs (delta : Exponent D) (he : oscillatorEnergy delta = oscillatorEnergy alpha) :
      (sourceTaylor D f n).coeff delta = c * q.coeff delta := by
    have hd : oscillatorEnergy delta ≤ n := he.trans_le ha
    have hdm := energy_mode D delta n M hd hn
    have hw : Finsupp.weight (normalWeight D label)
        ((boxOccupation D M delta).sumElim h) = w := by
      change Finsupp.weight (normalWeight D label)
        (threeOccupation (boxOccupation D M delta) (boxOccupation D M beta)
          (boxOccupation D M gamma)) = _
      dsimp only [w, d, h]
      rw [show (boxOccupation D M alpha).sumElim
          ((boxOccupation D M beta).sumElim (boxOccupation D M gamma)) =
          threeOccupation (boxOccupation D M alpha) (boxOccupation D M beta)
            (boxOccupation D M gamma) from rfl]
      rw [normal_weight_formula, normal_weight_formula,
        box_energy D M delta hdm, box_energy D M alpha hmode, he]
    have hr := original_corrected_gaussian_row D hu a delta beta gamma e
    have hh := congrArg (fun g : ℤ →₀ ℂ => g (e+chargeNorm D a))
      (correctedLaurentRow_on_box D a delta beta gamma M hdm hb hg)
    dsimp only at hr hh
    rw [hh] at hr
    rw [sourceTaylor_coeff, ite_eq_left hd, hq delta hd]
    change (weight delta : ℂ)⁻¹ *
      wick D (monomial gamma 1) (oscillatorCorrected D hu a e
        (monomial delta 1) (monomial beta 1)) = _
    rw [hr]
    change (weight delta : ℂ)⁻¹ * ((weight delta : ℂ)*(weight beta : ℂ)*
      (weight gamma : ℂ)*affineLaurent A mu (normalWeight D label)
        ((boxOccupation D M delta).sumElim h) (e+chargeNorm D a)) = _
    rw [affineLaurent_apply, hw]
    dsimp only [c]
    split_ifs <;> field_simp [weight_ne_zero delta] <;> ring
  have hc := substitution_coeff_energy D B (sourceTaylor D f n) q alpha c hs
  have ht : (substitution B q).coeff alpha =
      affineCoefficient
        (transportCovariance (sourceBlock (J := (Fin D.rank × Fin M) ⊕ (Fin D.rank × Fin M))
          (boxMatrix D M B)) A)
        (transportMean (sourceBlock (J := (Fin D.rank × Fin M) ⊕ (Fin D.rank × Fin M))
          (boxMatrix D M B)) mu) (d.sumElim h) := by
    change (substitution B (rename label R)).coeff alpha = _
    rw [← box_substitution D M B R]
    calc
      _ = (rename label (linearSubstitution (boxMatrix D M B) R)).coeff
          (d.embDomain label) := by rw [box_reconstruct D M alpha hmode]
      _ = (linearSubstitution (boxMatrix D M B) R).coeff d :=
        coeff_rename_embDomain label _ d
      _ = _ := externalSection_native (boxMatrix D M B) A mu hA d h N (hdeg alpha ha)
  have hh := dual_readout_coefficient D f alpha n ha
  rw [hc, ht] at hh
  change wick D (monomial gamma 1) (oscillatorCorrected D hu a e
      (dualOscillatorMonomial D alpha) (monomial beta 1)) = _ at hh
  rw [hh]
  dsimp only
  rw [affineLaurent_apply]
  change c * _ = (weight beta : ℂ)*(weight gamma : ℂ)*
    (if e+chargeNorm D a = w then _ else 0)
  dsimp only [c, B, A, mu, d, h, label, threeOccupation]
  split_ifs <;> ring


/-- Actual two original rows with the inverse transported into the native
right affine Gaussian. The right external variables and exact integer
Laurent selector are retained. The finite Taylor cutoff used in the proof
is n+betaR.degree+gammaR.degree, including both external degrees. -/
theorem original_two_rows_inverse_affine_coefficient
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n : ℕ) (ha : oscillatorEnergy alpha ≤ n) :
    chargeScalar D a * chargeScalar D (-a) *
      wick D (monomial gammaL 1)
        (oscillatorCorrected D hu a eL (monomial alpha 1) (monomial betaL 1)) *
      wick D (monomial gammaR 1)
        (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) =
    let K := rowSupport D alpha betaL gammaL
    let left := affineLaurent (correctedMatrix D (supportLabel D K))
      (correctedMean D a (supportLabel D K)) (normalWeight D (supportLabel D K))
      (threeOccupation (restricted D K alpha) (restricted D K betaL)
        (restricted D K gammaL)) (eL+chargeNorm D a)
    let M := n+1+betaR.support.sup Prod.snd+gammaR.support.sup Prod.snd
    let label := boxLabel D M
    let B := boxMatrix D M (fun k => (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ)
    let U := sourceBlock (J := (Fin D.rank × Fin M) ⊕ (Fin D.rank × Fin M)) B
    chargeScalar D a * chargeScalar D (-a) *
      (weight alpha : ℂ)*(weight betaL : ℂ)*(weight gammaL : ℂ)*
      (weight betaR : ℂ)*(weight gammaR : ℂ)*left *
        affineLaurent (transportCovariance U (correctedMatrix D label))
          (transportMean U (correctedMean D (-a) label)) (normalWeight D label)
          (threeOccupation (boxOccupation D M alpha) (boxOccupation D M betaR)
            (boxOccupation D M gammaR)) (eR+chargeNorm D (-a)) := by
  classical
  let M := n+1+betaR.support.sup Prod.snd+gammaR.support.sup Prod.snd
  have hn : n < M := by dsimp only [M]; omega
  have hb : ∀ b ∈ betaR.support, b.2 < M := by
    intro b hb
    have hh := Finset.le_sup (f := Prod.snd) hb
    dsimp only [M]
    omega
  have hg : ∀ b ∈ gammaR.support, b.2 < M := by
    intro b hg
    have hh := Finset.le_sup (f := Prod.snd) hg
    dsimp only [M]
    omega
  have hr := source_inverse_affine_row_box D hu (-a) alpha betaR gammaR eR n M ha hn hb hg
  have hd := dual_readout_coefficient D
    (correctedSourceReadout D hu (-a) eR (monomial betaR 1) (monomial gammaR 1))
    alpha n ha
  rw [corrected_sourceTaylor, map_smul, coeff_smul, smul_eq_mul] at hd
  dsimp only at hr
  have he := mul_left_cancel₀
    (mul_ne_zero (weight_ne_zero betaR) (weight_ne_zero gammaR)) (hd.symm.trans hr)
  rw [original_two_rows_inverse_coefficient D hu a alpha betaL gammaL betaR gammaR eL eR n ha]
  dsimp only
  rw [he]

end NativeTransport

end D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
