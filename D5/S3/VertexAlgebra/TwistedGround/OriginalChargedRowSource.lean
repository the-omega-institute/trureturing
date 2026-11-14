/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charged original correction coefficients and all-signed normal-current insertion. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
import D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard

/-!
Two actual source chains, with no assumed row equality:
* arbitrary charged Corr, retaining the unevaluated oscillator coordinates in
  its mean, has finite noncentral native Gaussian coefficients;
* the original all-signed normal-current recursion has the mixed binomial
  coefficient and Wick signs below, on the original oscillator carrier.

The charged evaluation and signed recursion supply the normal and corrected
Laurent rows in the downstream source modules. The complex evaluation alone
does not establish a formal Laurent identity or the downstream identityK.

Attribution: the actual lattice/half-Fock constructions and their inherited
FLM, Dong--Nagatomo, Bakalov--Kac and polynomial-Fock attributions are those of
the imported sources. The auxiliary-coordinate homogenization is classical
finite Gaussian algebra; no novelty or physical realization is asserted.
-/

/-
Proof-shape proposal: content through the non-binding occupation comparisons;
organizational normalization helpers are retained only with actual consumers.
Candidate escape witness: chargedMoment_affine compares the derived charged insertion recurrence with the independent finite affine Gaussian moments by strong occupation induction.
Admission basis proposed for independent review: escape-witness.
Utility kind is none: these are general algebraic identities for arbitrary
lattice data, finite embeddings and unbounded occupations or integer modes.
They are not bounded enumeration, a checker, a numerical reduction or a
certified finite instance. The finite sums implement general coefficients.
No novelty, substantive admission or downstream identityK completion is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource

open MvPolynomial LatticeGeneratingFieldLocality
open LatticeHalfFockFiniteCorrection LatticeHalfFockCurrentCorrection
open LatticeHalfFock LatticeActualAnnihilation
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField SignedOscillatorWick
open OriginalFourMChargeCoset
open NativeGaussianMoment (nativeMoment nativeMoment_step sub_single_degree occupation_nonzero)
open FactorialFockQuadraticEstimate (gaussianCoefficient gaussianCoefficient_zero)
open FactorialFockMetric (weight)
open OriginalCorrectionGaussian (covariance covarianceMatrix linearForm)
open ElementaryGaussianContraction (leftKernel)

-- These suppliers are independent of the charge of Corr. The neutral
-- sourceVacuum recurrence itself is deliberately not imported as a premise.
open D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
  (derivation_sum_apply derivation_finite sourceContraction formContraction substitution
   contraction_substitution covarianceMatrix_symm)
open D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
  (step_left left_symm left_vanish)
open D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField (jetScalar_contraction)

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- A quadratic homogenization: exp(Q_A(X) + Y sum_i mu_i X_i).
The auxiliary coordinate has zero self-covariance. -/
def affineKernel (A : Matrix I I ℂ) (mu : I → ℂ) :
    Matrix (I ⊕ Unit) (I ⊕ Unit) ℂ :=
  leftKernel A (fun i (_ : Unit) => mu i)

/-- Finite homogeneous interpretation of the coefficient of
exp(Q_A(X) + sum_i mu_i X_i): specialize the auxiliary variable to 1.
The auxiliary degree cannot exceed d.degree, by `auxiliary_vanish` below.
This is a sum of actual native exponential coefficients, not a recursively
defined Wick moment and not a truncation in the charge. -/
def affineCoefficient (A : Matrix I I ℂ) (mu : I → ℂ) (d : I →₀ ℕ) : ℂ :=
  ∑ k ∈ Finset.range (d.degree + 1),
    gaussianCoefficient (affineKernel A mu) (d.sumElim (Finsupp.single () k))

def auxiliaryMoment (A : Matrix I I ℂ) (mu : I → ℂ)
    (d : I →₀ ℕ) (k : ℕ) : ℂ :=
  nativeMoment (affineKernel A mu) (d.sumElim (Finsupp.single () k)) /
    (k.factorial : ℂ)

private theorem auxiliary_vanish (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (k : ℕ)
    (hk : d.degree < k) : auxiliaryMoment A mu d k = 0 := by
  have h := left_vanish A (fun i (_ : Unit) => mu i) hs d
    (Finsupp.single () k) (by simpa only [Finsupp.degree_single] using hk)
  simp only [auxiliaryMoment, affineKernel, h, zero_div]

theorem auxiliary_coefficient (A : Matrix I I ℂ) (mu : I → ℂ)
    (d : I →₀ ℕ) (k : ℕ) :
    auxiliaryMoment A mu d k = (weight d : ℂ) *
      gaussianCoefficient (affineKernel A mu) (d.sumElim (Finsupp.single () k)) := by
  have hw : weight (d.sumElim (Finsupp.single () k)) = weight d * k.factorial := by
    rw [weight, Finsupp.prod_sumElim]
    simp [weight, Finsupp.prod_single_index, Function.comp_def]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [auxiliaryMoment, nativeMoment, hw, Nat.cast_mul]
  field_simp

def affineMoment (A : Matrix I I ℂ) (mu : I → ℂ) (d : I →₀ ℕ) : ℂ :=
  ∑ k ∈ Finset.range (d.degree + 1), auxiliaryMoment A mu d k

theorem affineMoment_coefficient (A : Matrix I I ℂ) (mu : I → ℂ)
    (d : I →₀ ℕ) :
    affineMoment A mu d = (weight d : ℂ) * affineCoefficient A mu d := by
  simp only [affineMoment, affineCoefficient, auxiliary_coefficient, Finset.mul_sum]

theorem auxiliary_sum (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N) :
    (∑ k ∈ Finset.range (N + 1), auxiliaryMoment A mu d k) = affineMoment A mu d := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
  intro k hk hnot
  apply auxiliary_vanish A mu hs d k
  have : ¬ k < d.degree + 1 := by simpa only [Finset.mem_range] using hnot
  omega

private theorem auxiliary_step_raw (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (i : I) (k : ℕ) :
    nativeMoment (affineKernel A mu)
        ((d + Finsupp.single i 1).sumElim (Finsupp.single () k)) =
      (∑ j, (d j : ℂ) * A i j * nativeMoment (affineKernel A mu)
        ((d - Finsupp.single j 1).sumElim (Finsupp.single () k))) +
      (k : ℂ) * mu i * nativeMoment (affineKernel A mu)
        (d.sumElim (Finsupp.single () (k - 1))) := by
  have hsub : (Finsupp.single () k - Finsupp.single () 1 : Unit →₀ ℕ) =
      Finsupp.single () (k - 1) := (Finsupp.single_tsub).symm
  simpa only [affineKernel, leftKernel, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Fintype.sum_unique, Finsupp.single_eq_same, hsub]
    using step_left (affineKernel A mu)
      (left_symm A (fun i (_ : Unit) => mu i) hs) d (Finsupp.single () k) i

private theorem auxiliary_step (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (i : I) (k : ℕ) :
    auxiliaryMoment A mu (d + Finsupp.single i 1) k =
      (∑ j, (d j : ℂ) * A i j * auxiliaryMoment A mu (d - Finsupp.single j 1) k) +
      if k = 0 then 0 else mu i * auxiliaryMoment A mu d (k - 1) := by
  cases k with
  | zero =>
    simpa only [auxiliaryMoment, Nat.factorial_zero, Nat.cast_one, div_one,
      Nat.cast_zero, zero_mul, zero_add, ite_true, add_zero] using
      auxiliary_step_raw A mu hs d i 0
  | succ k =>
    simp only [auxiliaryMoment, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    rw [auxiliary_step_raw A mu hs, add_div, Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel]
      field_simp

theorem affineMoment_zero (A : Matrix I I ℂ) (mu : I → ℂ) :
    affineMoment A mu 0 = 1 := by
  simp [affineMoment, auxiliaryMoment, nativeMoment, gaussianCoefficient_zero, weight]

/-- The singleton term is obtained by shifting the auxiliary occupation and
cancelling its factorial. It is not supplied as a desired recurrence. -/
theorem affineMoment_step (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (i : I) :
    affineMoment A mu (d + Finsupp.single i 1) =
      mu i * affineMoment A mu d +
      ∑ j, (d j : ℂ) * A i j * affineMoment A mu (d - Finsupp.single j 1) := by
  have hd : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    simp only [map_add, Finsupp.degree_single]
  change (∑ k ∈ Finset.range ((d + Finsupp.single i 1).degree + 1),
    auxiliaryMoment A mu (d + Finsupp.single i 1) k) = _
  rw [hd]
  simp_rw [auxiliary_step A mu hs]
  rw [Finset.sum_add_distrib]
  have hcenter :
      (∑ k ∈ Finset.range (d.degree + 1 + 1),
        ∑ j, (d j : ℂ) * A i j * auxiliaryMoment A mu (d - Finsupp.single j 1) k) =
      ∑ j, (d j : ℂ) * A i j * affineMoment A mu (d - Finsupp.single j 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum, auxiliary_sum A mu hs]
    exact (Finsupp.degree_mono tsub_le_self).trans (Nat.le_succ d.degree)
  have hmean :
      (∑ k ∈ Finset.range (d.degree + 1 + 1),
        if k = 0 then 0 else mu i * auxiliaryMoment A mu d (k - 1)) =
      mu i * affineMoment A mu d := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel, ite_true, add_zero]
    rw [← Finset.mul_sum]
    rfl
  rw [hcenter, hmean, add_comm]

/-- Literal finite evaluation of charged Corr, with every residual oscillator
coordinate x retained. In particular, its singleton does not vanish. -/
def chargedReadout (D : LatticeData) (a : Charge D) (z : ℂ) (x : Index D → ℂ) :
    Oscillator D →ₗ[ℂ] ℂ :=
  (Finsupp.lsum ℂ (fun s => z ^ s • (aeval (R := ℂ) x).toLinearMap)).comp (Corr D a)

private def correctionEvaluation (D : LatticeData) (z : ℂ) (x : Index D → ℂ) :
    CorrectionPolynomial D →+* ℂ := eval (fun b => b.elim z x)

/-- The ordinary source frequency is index.2+1, not the half-Fock frequency. -/
def sourceMean (D : LatticeData) (a : Charge D) (z : ℂ) (x : Index D → ℂ)
    (b : Index D) : ℂ :=
  x b + halfBinomial (b.2 + 1) * (bilinear D (unitCharge D b.1) a : ℂ) * z ^ (b.2 + 1)

private theorem chargedReadout_evaluation (D : LatticeData) (a : Charge D)
    (z : ℂ) (x : Index D → ℂ) (p : Oscillator D) :
    chargedReadout D a z x p = correctionEvaluation D z x (correctionLift D a p) := by
  change ((correctionPolynomial D a p).toFinsupp.coeff.sum
    (fun s q => z ^ s * aeval x q)) = _
  have reconstruction (q : Polynomial (Oscillator D)) :
      q.toFinsupp.coeff.sum (fun s p => z ^ s * eval x p) =
        Polynomial.eval z (Polynomial.map (eval x) q) := by
    rw [← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact mul_comm _ _
  change ((correctionPolynomial D a p).toFinsupp.coeff.sum
    (fun s q => z ^ s * eval x q)) = _
  rw [reconstruction]
  symm
  simpa only [correctionEvaluation, optionEquivLeft_elim_eval,
    correctionPolynomial, correctionLift, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply]

private theorem evaluation_pair (D : LatticeData) (z : ℂ) (x : Index D → ℂ)
    (b c : Index D) :
    correctionEvaluation D z x (pairPolynomial D b c) = covariance D z b c := by
  simp [correctionEvaluation, pairPolynomial, sourceWeight,
    OriginalCorrectionGaussian.covariance]

private theorem evaluation_singleton (D : LatticeData) (a : Charge D)
    (z : ℂ) (x : Index D → ℂ) (b : Index D) :
    correctionEvaluation D z x (X (some b) + singletonPolynomial D a b) =
      sourceMean D a z x b := by
  simp [correctionEvaluation, singletonPolynomial, sourceWeight, sourceMean]

private theorem evaluation_contraction (D : LatticeData) (a : Charge D)
    (z : ℂ) (x : Index D → ℂ) (b : Index D) (p : Oscillator D) :
    correctionEvaluation D z x (pairDerivation D b (correctionLift D a p)) =
      chargedReadout D a z x (sourceContraction D z b p) := by
  classical
  let q := correctionLift D a p
  let s : Finset (Index D) := p.vars ∪ q.vars.biUnion (fun c => c.toFinset)
  have hp : p.vars ⊆ s := Finset.subset_union_left
  have hq : q.vars ⊆ insert none (s.image some) := by
    intro c hc
    cases c with
    | none => exact Finset.mem_insert_self _ _
    | some c =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨c, Finset.mem_union_right _ ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨some c, hc, by simp⟩
  rw [pairDerivation, derivation_finite _ q _ hq]
  simp only [map_sum, map_mul]
  rw [Finset.sum_insert (by simp)]
  simp only [Option.elim_none, map_zero, zero_mul, zero_add]
  rw [Finset.sum_image (by intro c _ d _ h; exact Option.some.inj h)]
  simp only [Option.elim_some, evaluation_pair]
  simp_rw [show ∀ c, pderiv (some c) q = correctionLift D a (pderiv c p) from
    fun c => correctionLift_partial D a c p, ← chargedReadout_evaluation]
  rw [sourceContraction, derivation_finite _ p _ hp, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [C_mul', map_smul]
  rfl

private theorem chargedReadout_C (D : LatticeData) (a : Charge D)
    (z : ℂ) (x : Index D → ℂ) (c : ℂ) : chargedReadout D a z x (C c) = c := by
  rw [chargedReadout_evaluation, correctionLift_C]
  simp [correctionEvaluation]

/-- Actual charged insertion: the linear term is evaluated from
singletonPolynomial, and the quadratic term from pairDerivation. -/
private theorem chargedReadout_X_mul (D : LatticeData) (a : Charge D)
    (z : ℂ) (x : Index D → ℂ) (b : Index D) (p : Oscillator D) :
    chargedReadout D a z x (p * X b) =
      sourceMean D a z x b * chargedReadout D a z x p +
        chargedReadout D a z x (sourceContraction D z b p) := by
  rw [chargedReadout_evaluation, correctionLift_X_mul]
  change correctionEvaluation D z x
    ((X (some b) + singletonPolynomial D a b) * correctionLift D a p +
      pairDerivation D b (correctionLift D a p)) = _
  rw [map_add, map_mul, evaluation_singleton, evaluation_contraction,
    ← chargedReadout_evaluation D a z x p]

def familyMean (D : LatticeData) (a : Charge D) (z : ℂ) (x : Index D → ℂ)
    (c : I → Index D →₀ ℂ) (i : I) : ℂ :=
  ∑ b ∈ (c i).support, c i b * sourceMean D a z x b

private theorem chargedReadout_form_mul (D : LatticeData) (a : Charge D)
    (z : ℂ) (x : Index D → ℂ) (c : I → Index D →₀ ℂ)
    (i : I) (p : Oscillator D) :
    chargedReadout D a z x (p * linearForm D (c i)) =
      familyMean D a z x c i * chargedReadout D a z x p +
        chargedReadout D a z x (formContraction D z (c i) p) := by
  simp only [linearForm, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    chargedReadout_X_mul, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    familyMean, Finset.sum_mul, mul_assoc, formContraction, derivation_sum_apply,
    Derivation.smul_apply] <;> rfl

private def chargedMoment (D : LatticeData) (a : Charge D) (z : ℂ)
    (x : Index D → ℂ) (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) : ℂ :=
  chargedReadout D a z x (substitution D c (monomial d 1))

private theorem chargedMoment_zero (D : LatticeData) (a : Charge D) (z : ℂ)
    (x : Index D → ℂ) (c : I → Index D →₀ ℂ) : chargedMoment D a z x c 0 = 1 := by
  change chargedReadout D a z x (substitution D c (C 1)) = 1
  simpa [substitution] using chargedReadout_C D a z x 1

private theorem chargedMoment_step (D : LatticeData) (a : Charge D) (z : ℂ)
    (x : Index D → ℂ) (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) (i : I) :
    chargedMoment D a z x c (d + Finsupp.single i 1) =
      familyMean D a z x c i * chargedMoment D a z x c d +
      ∑ j, (d j : ℂ) * covarianceMatrix D z c i j *
        chargedMoment D a z x c (d - Finsupp.single j 1) := by
  have hm : (monomial (d + Finsupp.single i 1) 1 : MvPolynomial I ℂ) =
      monomial d 1 * X i := by simp [X]
  unfold chargedMoment
  rw [hm, map_mul]
  rw [show substitution D c (X i) = linearForm D (c i) by
    simp only [substitution, aeval_X, Function.comp_apply]]
  rw [chargedReadout_form_mul, contraction_substitution, mkDerivation_monomial]
  congr 1
  simp only [one_smul, Finsupp.sum, map_sum, smul_eq_mul]
  rw [← Finset.sum_subset (Finset.subset_univ d.support)]
  · apply Finset.sum_congr rfl
    intro j hj
    have hterm : monomial (d - Finsupp.single j 1) (d j : ℂ) *
        (C (covarianceMatrix D z c i j) : MvPolynomial I ℂ) =
        ((d j : ℂ) * covarianceMatrix D z c i j) •
          (monomial (d - Finsupp.single j 1) 1 : MvPolynomial I ℂ) := by
      rw [mul_comm _ (C _), C_mul_monomial, smul_monomial]
      simp [smul_eq_mul, mul_comm]
    rw [hterm, map_smul, map_smul]
    rfl
  · intro j hj hnot
    simp [Finsupp.notMem_support_iff.mp hnot]

private theorem chargedMoment_affine (D : LatticeData) (a : Charge D) (z : ℂ)
    (x : Index D → ℂ) (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) :
    chargedMoment D a z x c d =
      affineMoment (covarianceMatrix D z c) (familyMean D a z x c) d := by
  have go : ∀ n (r : I →₀ ℕ), r.degree = n →
      chargedMoment D a z x c r =
        affineMoment (covarianceMatrix D z c) (familyMean D a z x c) r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r hr
      by_cases hz : r = 0
      · subst r
        rw [chargedMoment_zero, affineMoment_zero]
      obtain ⟨i, hi⟩ := occupation_nonzero r hz
      let t := r - Finsupp.single i 1
      have ht : t + Finsupp.single i 1 = r := Finsupp.sub_add_single_one_cancel hi
      have htd : t.degree + 1 = n := (sub_single_degree r i hi).trans hr
      rw [← ht, chargedMoment_step,
        affineMoment_step _ _ (covarianceMatrix_symm D z c), ih _ (by omega) _ rfl]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hle : (t - Finsupp.single j 1).degree ≤ t.degree :=
        Finsupp.degree_mono tsub_le_self
      rw [ih _ (by omega) _ rfl]
  exact go d.degree d rfl

/-- Substantive charged Corr result. No assumption a=0 or x=0, no rank or
positivity premise, no excluded zero occupation, and all finite families of
actual source linear forms. The covariance is literally the original
pairScalar r s * G * z^(r+s); the mean is literally x + h_r*(G a)*z^r. -/
theorem chargedCorr_linearForms (D : LatticeData) (a : Charge D) (z : ℂ)
    (x : Index D → ℂ) (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) :
    chargedReadout D a z x (∏ i, linearForm D (c i) ^ d i) =
      (weight d : ℂ) *
        affineCoefficient (covarianceMatrix D z c) (familyMean D a z x c) d := by
  have h := chargedMoment_affine D a z x c d
  have hp : substitution D c (monomial d 1) = ∏ i, linearForm D (c i) ^ d i := by
    change aeval (linearForm D ∘ c) (monomial d 1) = _
    rw [aeval_monomial]
    simp [Finsupp.prod_fintype]
  simpa only [chargedMoment, hp, affineMoment_coefficient] using h

/-- The existing current Ward contraction supplies the mixed coefficient
for every signed current mode. -/
theorem jet_mixed (k : ℕ) (m : ℤ) :
    frequency m * jetScalar k m =
      -(k + 1 : ℂ) * Ring.choose (-(m : ℂ) - 1 / 2) (k + 1) := by
  have hm : -(-m - 1) - 1 = m := by omega
  have hf : frequency (-m - 1) = -(m : ℂ) - 1 / 2 := by
    simp only [frequency, Int.cast_sub, Int.cast_neg, Int.cast_one]
    ring
  have h := jetScalar_contraction (-m - 1) k
  rw [hm] at h
  calc
    _ = -(frequency (-m - 1) * jetScalar k m) := by
      rw [frequency_opposite]
      ring
    _ = -((k + 1 : ℂ) * Ring.choose (frequency (-m - 1)) (k + 1)) := congrArg Neg.neg h
    _ = _ := by rw [hf]; ring

/-- Literal original normal-current recursion under the actual signed Wick
detector. A negative current differentiates the detector; a nonnegative
current differentiates the input. The exponent is the original doubled
shift, and the coefficient is derived from the original all-signed jetScalar.
No commutation through the charged seed or replacement field is used. -/
theorem wick_flat_cons (D : LatticeData) (a : Charge D)
    (b : Index D) (w : List (Index D)) (m : ℤ) (modes : ModeTuple D w)
    (e : ℤ) (p x : Oscillator D) :
    wick D p (oscillatorFlat D a (b :: w) (m, modes) e x) =
      (-(b.2 + 1 : ℂ) * Ring.choose (-(m : ℂ) - 1 / 2) (b.2 + 1)) *
        if m < 0 then
          wick D (annihilate D b.1 (-m-1).toNat p)
            (oscillatorFlat D a w modes (e + 2*m + 2*b.2 + 3) x)
        else
          wick D p (oscillatorFlat D a w modes (e + 2*m + 2*b.2 + 3)
            (annihilate D b.1 m.toNat x)) := by
  rw [← jet_mixed]
  by_cases hm : m < 0
  · let n := (-m-1).toNat
    have hn : m = -(n : ℤ)-1 := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -m-1)]
      omega
    have hcurrent : current D b.1 m = LinearMap.mulLeft ℂ (X (b.1,n)) := by
      rw [hn, current_negative]
    have hfrequency : frequency m = -frequency (n : ℤ) := by
      rw [hn, frequency_opposite]
    simp only [oscillatorFlat, if_pos hm, Module.End.mul_apply,
      oscillatorJet, LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hcurrent, LinearMap.mulLeft_apply, ← wick_lowering]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hfrequency]
    ring
  · simp only [oscillatorFlat, if_neg hm, Module.End.mul_apply,
      oscillatorJet, LinearMap.smul_apply, current, if_neg hm,
      map_smul, smul_eq_mul]
    ring

/-!
The original normal and corrected Gaussian Laurent rows are proved in
OriginalNormalRowSource and OriginalAffineRecompositionSource. They cover
arbitrary charge, every integer exponent and empty finite support. Their
source/source covariance is pairScalar(r,s) times the original Gram matrix,
and their source mean is halfBinomial(r) times the original charge pairing.
The charge shift and ordinary occupation factorials are retained.

The original identityK and two-row sewing remain open. In particular, the
four external factorials, both chargeScalar factors, single left average
and original inverse -Ginv/(k+1) still belong to that downstream problem.
-/

end D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
