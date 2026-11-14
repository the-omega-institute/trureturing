/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged correction support, exact shift coefficients and finite Laurent reduction. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
import D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock

/-! Finite support, ordinary coefficients and exact Laurent shifts for the original
charged correction. Residual support follows from `Corr_partial`; the insertion
formula follows from the original correction lift. The shift selector is the
original `Corr_coefficient_bidegree`, with arbitrary charge. -/

/-
Proof-shape proposal: content through the non-binding occupation comparisons;
organizational normalization helpers are retained only with actual consumers.
Candidate escape witness: finiteCorrection_moment compares the original correction insertion with the independent Gaussian kernel; original_corrected_row_finite_reduction uses the proved residual support and bidegree selector.
Admission basis proposed for independent review: escape-witness.
Utility kind is none: these are general algebraic identities for arbitrary
lattice data, finite embeddings and unbounded occupations or integer modes.
They are not bounded enumeration, a checker, a numerical reduction or a
certified finite instance. The finite sums implement general coefficients.
No novelty, substantive admission or downstream identityK completion is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource

open MvPolynomial LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCurrentCorrection LatticeHalfFockCorrectedField
open LatticeHalfFock LatticeActualAnnihilation LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open OriginalChargedRowSource OriginalNormalRowSource OriginalFourMChargeCoset SignedOscillatorWick
open NativeGaussianMoment (nativeMoment occupation_nonzero sub_single_degree weight_sub_single)
open FactorialFockMetric (weight weight_pos)
open FactorialFockQuadraticEstimate (gaussianCoefficient gaussianCoefficient_zero)
open ElementaryGaussianContraction (leftKernel)
open D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation (pairDerivation_source_partials)
open D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
  (affineMoment affineMoment_zero affineMoment_step affineMoment_coefficient)
open D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
  (restricted_reconstruct embedded_weight normalLaurentRow_native)
open D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction (shared_support)

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- No new residual variable can occur in the ORIGINAL charged correction.
This is a coefficient argument in characteristic zero, using the actual
partial-commuting theorem; it is not a support hypothesis. -/
theorem Corr_residual_support (D : LatticeData) (a : Charge D)
    (alpha delta : Index D →₀ ℕ) (s : ℕ)
    (hc : (Corr D a (monomial alpha 1) s).coeff delta ≠ 0) :
    delta.support ⊆ alpha.support := by
  classical
  intro j hj
  by_contra ha
  have hj0 : delta j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have ha0 : alpha j = 0 := Finsupp.notMem_support_iff.mp ha
  have hp : pderiv j (monomial alpha (1 : ℂ)) = 0 := by
    simp only [pderiv_monomial, ha0, Nat.cast_zero, mul_zero, monomial_zero]
  have hpartial : pderiv j (Corr D a (monomial alpha 1) s) = 0 := by
    rw [Corr_partial, hp, map_zero, Finsupp.zero_apply]
  have he := congrArg (fun p : Oscillator D => p.coeff (delta - Finsupp.single j 1))
    hpartial
  rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hj0, MvPolynomial.coeff_zero] at he
  have hcast : (((delta - Finsupp.single j 1 : Index D →₀ ℕ) j : ℕ) : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (delta - Finsupp.single j 1 : Index D →₀ ℕ) j + 1 ≠ 0 by omega)
  exact (mul_ne_zero hc hcast) he

/-- Formal polynomial specialization of the finite shift variable to 1.
The residual variables are still indeterminates. -/
private def shiftOne (D : LatticeData) :
    CorrectionPolynomial D →ₐ[ℂ] Oscillator D :=
  aeval (fun x => x.elim 1 X)

private def correctionOne (D : LatticeData) (a : Charge D) :
    Oscillator D →ₗ[ℂ] Oscillator D :=
  (shiftOne D).toLinearMap.comp (correctionLift D a)

private theorem shiftOne_option (D : LatticeData) (p : CorrectionPolynomial D) :
    shiftOne D p = Polynomial.eval 1 (optionEquivLeft ℂ (Index D) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [shiftOne, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, Polynomial.eval_mul, hp]
    congr 1
    cases x <;> simp [shiftOne, algebraMap_eq]

private theorem correctionOne_shifts (D : LatticeData) (a : Charge D)
    (p : Oscillator D) :
    correctionOne D a p = ∑ s ∈ (Corr D a p).support, Corr D a p s := by
  change shiftOne D (correctionLift D a p) = _
  rw [shiftOne_option]
  change Polynomial.eval 1 (correctionPolynomial D a p) = _
  rw [Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one]
  rfl

def sourceCovariance (D : LatticeData) (label : I ↪ Index D) :
    Matrix I I ℂ := fun i j =>
  pairScalar ((label i).2+1) ((label j).2+1) * (D.G (label i).1 (label j).1 : ℂ)

def sourceMean (D : LatticeData) (a : Charge D) (label : I ↪ Index D) : I → ℂ :=
  fun i => halfBinomial ((label i).2+1) * (bilinear D (unitCharge D (label i).1) a : ℂ)

theorem sourceCovariance_symm (D : LatticeData) (label : I ↪ Index D) :
    ∀ i j, sourceCovariance D label i j = sourceCovariance D label j i := by
  intro i j
  have hp (r s : ℕ) : pairScalar r s = pairScalar s r := by
    unfold pairScalar
    rw [add_comm (r : ℂ) (s : ℂ)]
    ring
  simp only [sourceCovariance]
  rw [hp, D.symmetric (label i).1 (label j).1]

/-- Actual polynomial insertion, before passing to any Gaussian expression.
The finite derivative expansion is the existing charged source-partials
supplier, whose proof uses correctionLift_partial. -/
private theorem correctionOne_insert (D : LatticeData) (a : Charge D)
    (b : Index D) (p : Oscillator D) :
    correctionOne D a (p * X b) =
      (X b + C (halfBinomial (b.2+1) * (bilinear D (unitCharge D b.1) a : ℂ))) *
        correctionOne D a p +
      ∑ j ∈ p.vars,
        C (pairScalar (b.2+1) (j.2+1) * (D.G b.1 j.1 : ℂ)) *
          correctionOne D a (pderiv j p) := by
  change shiftOne D (correctionLift D a (p * X b)) = _
  rw [correctionLift_X_mul]
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pairDerivation_source_partials, map_add, map_mul, map_sum]
  simp only [shiftOne, aeval_X, Option.elim_some, Option.elim_none,
    singletonPolynomial, pairPolynomial, sourceWeight, map_mul, map_pow,
    aeval_C, one_pow, mul_one, algebraMap_eq]
  rfl

private def finiteCorrection (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (d : I →₀ ℕ) : MvPolynomial I ℂ :=
  killCompl label.injective (correctionOne D a (monomial (d.embDomain label) 1))

private theorem finiteCorrection_coeff (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) :
    (finiteCorrection D a label d).coeff delta =
      ∑ s ∈ (Corr D a (monomial (d.embDomain label) 1)).support,
        (Corr D a (monomial (d.embDomain label) 1) s).coeff (delta.embDomain label) := by
  classical
  rw [finiteCorrection, coeff_killCompl, correctionOne_shifts, coeff_sum]
  simp only [Finsupp.embDomain_eq_mapDomain]

private theorem kill_variable (D : LatticeData) (label : I ↪ Index D) (i : I) :
    killCompl label.injective (X (label i) : Oscillator D) = X i := by
  simpa only [rename_X] using
    killCompl_rename_app label.injective (X i : MvPolynomial I ℂ)

private theorem finiteCorrection_zero (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) : finiteCorrection D a label 0 = 1 := by
  change killCompl label.injective (shiftOne D (correctionLift D a (C 1))) = 1
  rw [correctionLift_C]
  simp [shiftOne, algebraMap_eq]

private theorem finiteCorrection_insert (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d : I →₀ ℕ) (i : I) :
    finiteCorrection D a label (d + Finsupp.single i 1) =
      (X i + C (sourceMean D a label i)) * finiteCorrection D a label d +
        ∑ j, (d j : ℂ) •
          (C (sourceCovariance D label i j) *
            finiteCorrection D a label (d - Finsupp.single j 1)) := by
  classical
  have hm : (monomial ((d + Finsupp.single i 1).embDomain label) 1 : Oscillator D) =
      monomial (d.embDomain label) 1 * X (label i) := by
    simp only [X, monomial_mul, one_mul, Finsupp.embDomain_add,
      Finsupp.embDomain_single]
  have hp (j : I) : pderiv (label j) (monomial (d.embDomain label) (1 : ℂ)) =
      (d j : ℂ) • monomial ((d - Finsupp.single j 1).embDomain label) 1 := by
    simp only [pderiv_monomial, one_mul, Finsupp.embDomain_apply_self,
      ← Finsupp.embDomain_single label, ← Finsupp.embDomain_tsub,
      smul_monomial, smul_eq_mul, mul_one]
  unfold finiteCorrection
  rw [hm, correctionOne_insert]
  simp only [map_add, map_mul, map_sum, kill_variable, killCompl_C,
    vars_monomial (one_ne_zero : (1 : ℂ) ≠ 0), Finsupp.support_embDomain,
    Finset.sum_map, hp, map_smul, mul_smul_comm]
  simp only [← C_mul]
  simp only [sourceMean, sourceCovariance]
  congr 1
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j hj hout
  simp only [Finsupp.notMem_support_iff.mp hout, Nat.cast_zero, zero_smul]

/-- The correction's ordinary kernel: original SS, identity to the residual
variables, zero residual self-covariance. -/
def correctionMatrix (D : LatticeData) (label : I ↪ Index D) :
    Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  leftKernel (sourceCovariance D label) 1

def correctionMean (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    I ⊕ I → ℂ := Sum.elim (sourceMean D a label) (fun _ => 0)

private def correctionMoment (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (d delta : I →₀ ℕ) : ℂ :=
  affineMoment (correctionMatrix D label) (correctionMean D a label) (d.sumElim delta)

private theorem correctionMatrix_symm (D : LatticeData) (label : I ↪ Index D) :
    ∀ x y, correctionMatrix D label x y = correctionMatrix D label y x := by
  rintro (i | i) (j | j) <;>
    simp [correctionMatrix, leftKernel, Matrix.one_apply, eq_comm,
      sourceCovariance_symm D label]

private theorem correctionMoment_residual (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (i : I) :
    correctionMoment D a label d (delta + Finsupp.single i 1) =
      ∑ j, (d j : ℂ) * (1 : Matrix I I ℂ) j i *
        correctionMoment D a label (d - Finsupp.single j 1) delta := by
  classical
  have ha : d.sumElim (delta + Finsupp.single i 1) =
      d.sumElim delta + Finsupp.single (Sum.inr i) 1 := by
    ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hs (j : I) : d.sumElim delta - Finsupp.single (Sum.inl j) 1 =
      (d - Finsupp.single j 1).sumElim delta := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  simp only [correctionMoment]
  rw [ha, affineMoment_step _ _ (correctionMatrix_symm D label)]
  simp only [Fintype.sum_sum_type,
    correctionMean, Sum.elim_inr, zero_mul, zero_add,
    Finsupp.sumElim_inl, Finsupp.sumElim_inr, correctionMatrix, leftKernel,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
    Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hs]

private theorem correctionMoment_vanish (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (h : d.degree < delta.degree) :
    correctionMoment D a label d delta = 0 := by
  exact shared_support (correctionMoment D a label) (1 : Matrix I I ℂ)
    (correctionMoment_residual D a label) d delta h

private theorem correctionMoment_zero (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (delta : I →₀ ℕ) :
    correctionMoment D a label 0 delta = if delta = 0 then 1 else 0 := by
  classical
  by_cases hz : delta = 0
  · subst delta
    simp [correctionMoment, affineMoment_zero]
  · rw [if_neg hz]
    apply correctionMoment_vanish
    have hd : delta.degree ≠ 0 := by
      intro he
      exact hz ((Finsupp.degree_eq_zero_iff delta).mp he)
    simpa using Nat.pos_of_ne_zero hd

private theorem correctionMoment_source (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (i : I) :
    correctionMoment D a label (d + Finsupp.single i 1) delta =
      sourceMean D a label i * correctionMoment D a label d delta +
      (∑ j, (d j : ℂ) * sourceCovariance D label i j *
        correctionMoment D a label (d - Finsupp.single j 1) delta) +
      (delta i : ℂ) * correctionMoment D a label d (delta - Finsupp.single i 1) := by
  classical
  have ha : (d + Finsupp.single i 1).sumElim delta =
      d.sumElim delta + Finsupp.single (Sum.inl i) 1 := by
    ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hs (j : I) : d.sumElim delta - Finsupp.single (Sum.inl j) 1 =
      (d - Finsupp.single j 1).sumElim delta := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hr (j : I) : d.sumElim delta - Finsupp.single (Sum.inr j) 1 =
      d.sumElim (delta - Finsupp.single j 1) := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  simp only [correctionMoment]
  rw [ha, affineMoment_step _ _ (correctionMatrix_symm D label)]
  simp only [Fintype.sum_sum_type,
    correctionMean, Sum.elim_inl, correctionMatrix, leftKernel,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Finsupp.sumElim_inl, Finsupp.sumElim_inr, hs, hr, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The actual finite correction polynomial has the factorial Gaussian
moments. The insertion recurrence on the LHS has already been DERIVED from
the original lift. The RHS recurrence is the finite homogenized Gaussian
identity; neither recurrence is an assumption of this theorem. -/
private theorem finiteCorrection_moment (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) :
    (weight delta : ℂ) * (finiteCorrection D a label d).coeff delta =
      correctionMoment D a label d delta := by
  classical
  have go : ∀ N (d : I →₀ ℕ), d.degree = N → ∀ delta : I →₀ ℕ,
      (weight delta : ℂ) * (finiteCorrection D a label d).coeff delta =
        correctionMoment D a label d delta := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro d hd delta
      by_cases hz : d = 0
      · subst d
        rw [finiteCorrection_zero, correctionMoment_zero]
        by_cases hdelta : delta = 0
        · subst delta
          simp [weight]
        · simp [coeff_one, hdelta, Ne.symm hdelta]
      obtain ⟨i,hi⟩ := occupation_nonzero d hz
      let r := d - Finsupp.single i 1
      have hr : r + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
      have hrd : r.degree + 1 = N := (sub_single_degree d i hi).trans hd
      rw [← hr, finiteCorrection_insert, correctionMoment_source]
      simp only [add_mul, MvPolynomial.coeff_add, coeff_X_mul', coeff_C_mul, coeff_sum,
        coeff_smul, smul_eq_mul, mul_add, Finset.mul_sum]
      have hprev : ∀ delta : I →₀ ℕ,
          (weight delta : ℂ) * (finiteCorrection D a label r).coeff delta =
            correctionMoment D a label r delta := ih _ (by omega) r rfl
      have hpair : ∀ j : I,
          (weight delta : ℂ) * (finiteCorrection D a label (r - Finsupp.single j 1)).coeff delta =
            correctionMoment D a label (r - Finsupp.single j 1) delta := by
        intro j
        apply ih _ (by
          have := Finsupp.degree_mono (show r - Finsupp.single j 1 ≤ r from tsub_le_self)
          omega) _ rfl
      have hX : (weight delta : ℂ) *
          (if i ∈ delta.support then
            (finiteCorrection D a label r).coeff (delta - Finsupp.single i 1) else 0) =
          (delta i : ℂ) * correctionMoment D a label r (delta - Finsupp.single i 1) := by
        by_cases hi0 : delta i = 0
        · simp [Finsupp.mem_support_iff, hi0]
        · rw [if_pos (Finsupp.mem_support_iff.mpr hi0)]
          have hw : (weight delta : ℂ) =
              (delta i : ℂ) * (weight (delta - Finsupp.single i 1) : ℂ) := by
            exact_mod_cast weight_sub_single delta i hi0
          rw [hw, mul_assoc, hprev]
      have hmean : (weight delta : ℂ) *
          (sourceMean D a label i * (finiteCorrection D a label r).coeff delta) =
          sourceMean D a label i * correctionMoment D a label r delta := by
        calc
          _ = sourceMean D a label i *
              ((weight delta : ℂ) * (finiteCorrection D a label r).coeff delta) := by ring
          _ = _ := by rw [hprev]
      have hsum : (∑ j, (weight delta : ℂ) *
          ((r j : ℂ) * (sourceCovariance D label i j *
            (finiteCorrection D a label (r - Finsupp.single j 1)).coeff delta))) =
          ∑ j, (r j : ℂ) * sourceCovariance D label i j *
            correctionMoment D a label (r - Finsupp.single j 1) delta := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = (r j : ℂ) * sourceCovariance D label i j *
              ((weight delta : ℂ) *
                (finiteCorrection D a label (r - Finsupp.single j 1)).coeff delta) := by ring
          _ = _ := by rw [hpair]
      rw [hX, hmean, hsum]
      ring
  exact go d.degree d rfl delta

/-- Reconstruction of ALL ordinary residual coefficients from the actual
charged correction, on an arbitrary injective finite set, including empty.
The RHS has the original covariance and mean and the source factorial.
The empty finite label is included. -/
theorem charged_correction_coefficients (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) :
    (∑ s ∈ (Corr D a (monomial (d.embDomain label) 1)).support,
      (Corr D a (monomial (d.embDomain label) 1) s).coeff (delta.embDomain label)) =
      (weight d : ℂ) * affineCoefficient (correctionMatrix D label)
        (correctionMean D a label) (d.sumElim delta) := by
  rw [← finiteCorrection_coeff]
  have h := finiteCorrection_moment D a label d delta
  rw [correctionMoment, affineMoment_coefficient] at h
  have hw : weight (d.sumElim delta) = weight d * weight delta :=
    Finsupp.prod_sumElim d delta (fun _ k => k.factorial)
  rw [hw, Nat.cast_mul] at h
  have hdelta : (weight delta : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (weight_pos delta))
  apply mul_left_cancel₀ hdelta
  rw [h]
  ring

private theorem sourceWeight_embedded (D : LatticeData) (label : I ↪ Index D)
    (d : I →₀ ℕ) :
    Finsupp.weight (sourceWeight D) (d.embDomain label) =
      Finsupp.weight (fun i => sourceWeight D (label i)) d := by
  simp only [Finsupp.weight_apply, Finsupp.sum_embDomain]

/-- Exact formal shift coefficient. At most one shift can contribute to a
fixed residual monomial; this is the frozen bidegree theorem, with its
original arbitrary charge. No Laurent evaluation argument is needed. -/
theorem charged_correction_shift_coefficient (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (s : ℕ) :
    (Corr D a (monomial (d.embDomain label) 1) s).coeff (delta.embDomain label) =
      if s + Finsupp.weight (fun i => sourceWeight D (label i)) delta =
          Finsupp.weight (fun i => sourceWeight D (label i)) d then
        (weight d : ℂ) * affineCoefficient (correctionMatrix D label)
          (correctionMean D a label) (d.sumElim delta)
      else 0 := by
  classical
  let c := Corr D a (monomial (d.embDomain label) 1)
  have hb : ∀ t : ℕ, (c t).coeff (delta.embDomain label) ≠ 0 →
      t + Finsupp.weight (fun i => sourceWeight D (label i)) delta =
        Finsupp.weight (fun i => sourceWeight D (label i)) d := by
    intro t ht
    have hh := HalfFock.ActualCorrCovariance.Corr_coefficient_bidegree D a
      (monomial (d.embDomain label) 1)
      (Finsupp.weight (sourceWeight D) (d.embDomain label))
      (isWeightedHomogeneous_monomial (sourceWeight D) (d.embDomain label) (1 : ℂ) rfl)
      t (delta.embDomain label) ht
    simpa only [sourceWeight_embedded] using hh
  by_cases hs : s + Finsupp.weight (fun i => sourceWeight D (label i)) delta =
      Finsupp.weight (fun i => sourceWeight D (label i)) d
  · rw [if_pos hs, ← charged_correction_coefficients D a label d delta]
    symm
    apply Finset.sum_eq_single s
    · intro t ht hts
      by_contra hne
      have hh := hb t hne
      omega
    · intro hout
      have hz : c s = 0 := Finsupp.notMem_support_iff.mp hout
      change (c s).coeff (delta.embDomain label) = 0
      rw [hz]
      rfl
  · rw [if_neg hs]
    by_contra hn
    exact hs (hb s hn)

private theorem join_map {J : Type v} (e : I → J) (f : Unit → Unit)
    (d : I →₀ ℕ) (k : Unit →₀ ℕ) :
    (d.sumElim k).mapDomain (Sum.map e f) =
      (d.mapDomain e).sumElim (k.mapDomain f) := by
  simp [Finsupp.sumElim_eq_add, Finsupp.mapDomain_add,
    ← Finsupp.mapDomain_fun_comp, Function.comp_def]

/-- The existing exact coefficient-enlargement theorem is used with the
auxiliary coordinate fixed; no rank or nonempty-label premise is needed. -/
private theorem affineCoefficient_enlarge {J : Type v} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (mu : J → ℂ) (e : I ↪ J) (d : I →₀ ℕ) :
    affineCoefficient A mu (d.embDomain e) =
      affineCoefficient (fun i j => A (e i) (e j)) (fun i => mu (e i)) d := by
  classical
  let f := e.sumMap (Function.Embedding.refl Unit)
  have hj (k : ℕ) :
      (d.embDomain e).sumElim (Finsupp.single () k) =
        (d.sumElim (Finsupp.single () k)).mapDomain f := by
    rw [Finsupp.embDomain_eq_mapDomain]
    change (d.mapDomain (e : I → J)).sumElim (Finsupp.single () k) =
      (d.sumElim (Finsupp.single () k)).mapDomain (Sum.map (e : I → J) id)
    simpa only [Finsupp.mapDomain_id] using
      (join_map (e : I → J) id d (Finsupp.single () k)).symm
  have hA : (fun i j => affineKernel A mu (f i) (f j)) =
      affineKernel (fun i j => A (e i) (e j)) (fun i => mu (e i)) := by
    funext x y
    rcases x with i | i <;> rcases y with j | j <;> rfl
  unfold affineCoefficient
  simp only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finsupp.embDomain_eq_mapDomain e, hj,
    InfiniteGaussianFock.gaussianCoefficient_enlarge _ f f.injective, hA]

private theorem affineLaurent_enlarge {J : Type v} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (mu : J → ℂ) (w : J → ℤ) (e : I ↪ J) (d : I →₀ ℕ) :
    affineLaurent A mu w (d.embDomain e) =
      affineLaurent (fun i j => A (e i) (e j)) (fun i => mu (e i))
        (fun i => w (e i)) d := by
  unfold affineLaurent
  rw [affineCoefficient_enlarge]
  congr 1
  simp only [Finsupp.weight_apply, Finsupp.sum_embDomain]

private theorem map_three {J : Type v} (e : I ↪ J) (d h l : I →₀ ℕ) :
    (threeOccupation d h l).embDomain (e.sumMap (e.sumMap e)) =
      threeOccupation (d.embDomain e) (h.embDomain e) (l.embDomain e) := by
  simp only [threeOccupation, Finsupp.embDomain_eq_mapDomain,
    Function.Embedding.sumMap]
  simp [Finsupp.sumElim_eq_add, Finsupp.mapDomain_add,
    ← Finsupp.mapDomain_fun_comp, Function.comp_def]

/-- The varying minimal support of a residual row can be enlarged to the
EXACT original union K. The proof uses gaussianCoefficient_enlarge, rather
than assuming compatibility of the ordinary affine coefficients. -/
private theorem normalLaurentRow_on_block (D : LatticeData) (a : Charge D)
    (delta beta gamma : Index D →₀ ℕ) (K : Finset (Index D))
    (hd : delta.support ⊆ K) (hb : beta.support ⊆ K) (hc : gamma.support ⊆ K) :
    normalLaurentRow D a delta beta gamma =
      affineLaurent (normalMatrix D (supportLabel D K))
        (normalMean D a (supportLabel D K)) (normalWeight D (supportLabel D K))
        (threeOccupation (restricted D K delta) (restricted D K beta)
          (restricted D K gamma)) := by
  classical
  let L := rowSupport D delta beta gamma
  have hLK : L ⊆ K := Finset.union_subset (Finset.union_subset hd hb) hc
  let e : {b // b ∈ L} ↪ {b // b ∈ K} :=
    { toFun := fun b => ⟨b.val,hLK b.property⟩
      inj' := by
        intro b c he
        apply Subtype.ext
        exact congrArg (fun x : {b // b ∈ K} => x.val) he }
  have hi (p : Index D →₀ ℕ) (hp : p.support ⊆ L) :
      (restricted D L p).embDomain e = restricted D K p := by
    apply Finsupp.embDomain_injective (supportLabel D K)
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
      Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_fun_comp]
    change (restricted D L p).mapDomain (supportLabel D L) =
      (restricted D K p).mapDomain (supportLabel D K)
    rw [← Finsupp.embDomain_eq_mapDomain, ← Finsupp.embDomain_eq_mapDomain,
      restricted_reconstruct D L p hp, restricted_reconstruct D K p (hp.trans hLK)]
  have hdelta : delta.support ⊆ L :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hbeta : beta.support ⊆ L :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hgamma : gamma.support ⊆ L := Finset.subset_union_right
  rw [normalLaurentRow_native]
  have he := affineLaurent_enlarge
    (normalMatrix D (supportLabel D K)) (normalMean D a (supportLabel D K))
    (normalWeight D (supportLabel D K)) (e.sumMap (e.sumMap e))
    (threeOccupation (restricted D L delta) (restricted D L beta) (restricted D L gamma))
  rw [map_three, hi delta hdelta, hi beta hbeta, hi gamma hgamma] at he
  have hA : (fun i j => normalMatrix D (supportLabel D K)
      ((e.sumMap (e.sumMap e)) i) ((e.sumMap (e.sumMap e)) j)) =
      normalMatrix D (supportLabel D L) := by
    funext x y
    rcases x with i | (i | i) <;> rcases y with j | (j | j) <;> rfl
  have hmu : (fun i => normalMean D a (supportLabel D K)
      ((e.sumMap (e.sumMap e)) i)) = normalMean D a (supportLabel D L) := by
    funext x
    rcases x with i | (i | i) <;> rfl
  have hw : (fun i => normalWeight D (supportLabel D K)
      ((e.sumMap (e.sumMap e)) i)) = normalWeight D (supportLabel D L) := by
    funext x
    rcases x with i | (i | i) <;> rfl
  rw [hA, hmu, hw] at he
  exact he.symm

private theorem normal_weight_formula (D : LatticeData) (label : I ↪ Index D)
    (d h l : I →₀ ℕ) :
    Finsupp.weight (normalWeight D label) (threeOccupation d h l) =
      -2 * (Finsupp.weight (fun i => sourceWeight D (label i)) d : ℤ) -
        Finsupp.weight (fun i => (omega D (label i) : ℤ)) h +
        Finsupp.weight (fun i => (omega D (label i) : ℤ)) l := by
  classical
  have hs : (∑ i, (d i : ℤ) * (-2*((label i).2 : ℤ)-2)) =
      -2 * (Finsupp.weight (fun i => sourceWeight D (label i)) d : ℤ) := by
    simp only [Finsupp.weight_eq_sum, sourceWeight, nsmul_eq_mul,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  have hh : (∑ i, (h i : ℤ) * (-(omega D (label i) : ℤ))) =
      -Finsupp.weight (fun i => (omega D (label i) : ℤ)) h := by
    simp [Finsupp.weight_eq_sum, nsmul_eq_mul, Finset.sum_neg_distrib]
  simp only [Finsupp.weight_eq_sum, threeOccupation, Fintype.sum_sum_type,
    Finsupp.sumElim_inl, Finsupp.sumElim_inr, normalWeight, nsmul_eq_mul]
  rw [hs, hh]
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul]
  ring

/-- Literal n+2s shift equivalence for a nonzero original Corr coefficient.
The bidegree is reused exactly once; no analytic t or z is introduced. -/
private theorem normal_shift_selector (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta h l : I →₀ ℕ) (s : ℕ) (n : ℤ)
    (hn : (Corr D a (monomial (d.embDomain label) 1) s).coeff
      (delta.embDomain label) ≠ 0) :
    (n + 2*(s : ℤ) = Finsupp.weight (normalWeight D label) (threeOccupation delta h l)) ↔
      n = Finsupp.weight (normalWeight D label) (threeOccupation d h l) := by
  have hc := charged_correction_shift_coefficient D a label d delta s
  have hb : s + Finsupp.weight (fun i => sourceWeight D (label i)) delta =
      Finsupp.weight (fun i => sourceWeight D (label i)) d := by
    by_contra hh
    rw [if_neg hh] at hc
    exact hn hc
  have hb' : (s : ℤ) +
      (Finsupp.weight (fun i => sourceWeight D (label i)) delta : ℤ) =
      (Finsupp.weight (fun i => sourceWeight D (label i)) d : ℤ) := by
    exact_mod_cast hb
  rw [normal_weight_formula, normal_weight_formula]
  omega

/-- The normal row coefficient is a literal singleton of its finite weight.
This local helper makes the shift direction explicit in the actual row proof. -/
theorem affineLaurent_apply (A : Matrix I I ℂ) (mu : I → ℂ)
    (w : I → ℤ) (d : I →₀ ℕ) (n : ℤ) :
    affineLaurent A mu w d n =
      if n = Finsupp.weight w d then affineCoefficient A mu d else 0 := by
  classical
  simp only [affineLaurent, Finsupp.single_apply, eq_comm]

/-- The finite polynomial readout used on the actual residual correction.
It contains the residual factorial, with both external factorials left for
the final original-row statement. -/
private def normalReadout (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (h l : I →₀ ℕ) : MvPolynomial I ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials I ℂ).constr ℂ (fun delta =>
    (weight delta : ℂ) * affineCoefficient (normalMatrix D label) (normalMean D a label)
      (threeOccupation delta h l))

private theorem normalReadout_monomial (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (h l delta : I →₀ ℕ) (c : ℂ) :
    normalReadout D a label h l (monomial delta c) =
      c * (weight delta : ℂ) *
        affineCoefficient (normalMatrix D label) (normalMean D a label)
          (threeOccupation delta h l) := by
  have hm : (monomial delta c : MvPolynomial I ℂ) = c • monomial delta 1 := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul]
  have hb := (basisMonomials I ℂ).constr_basis ℂ (fun delta =>
    (weight delta : ℂ) * affineCoefficient (normalMatrix D label) (normalMean D a label)
      (threeOccupation delta h l)) delta
  change normalReadout D a label h l (monomial delta 1) = _ at hb
  rw [hb, smul_eq_mul, mul_assoc]

private theorem normalReadout_expansion (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (h l : I →₀ ℕ) (p : MvPolynomial I ℂ) :
    normalReadout D a label h l p =
      ∑ delta ∈ p.support, p.coeff delta * (weight delta : ℂ) *
        affineCoefficient (normalMatrix D label) (normalMean D a label)
          (threeOccupation delta h l) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, normalReadout_monomial]

private theorem normalReadout_projection (D : LatticeData) (a : Charge D)
    (K : Finset (Index D)) (h l : {b // b ∈ K} →₀ ℕ) (p : Oscillator D)
    (hp : ∀ delta ∈ p.support, delta.support ⊆ K) :
    normalReadout D a (supportLabel D K) h l
        (killCompl (supportLabel D K).injective p) =
      ∑ delta ∈ p.support, p.coeff delta * (weight (restricted D K delta) : ℂ) *
        affineCoefficient (normalMatrix D (supportLabel D K))
          (normalMean D a (supportLabel D K)) (threeOccupation (restricted D K delta) h l) := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro delta hd
  have hs : (↑delta.support : Set (Index D)) ⊆ Set.range (supportLabel D K) := by
    intro b hb
    exact ⟨⟨b,hp delta hd hb⟩,rfl⟩
  rw [killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hs,
    normalReadout_monomial]
  rfl

/-- The residual-degree bound is derived from the correction's zero
residual/residual block, using ElementaryGaussianContraction.shared_support.
It is not an extra hypothesis on the actual Corr polynomial. -/
private theorem finiteCorrection_degree (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (h : d.degree < delta.degree) :
    (finiteCorrection D a label d).coeff delta = 0 := by
  have hm := finiteCorrection_moment D a label d delta
  rw [correctionMoment_vanish D a label d delta h] at hm
  have hw : (weight delta : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (weight_pos delta))
  exact (mul_eq_zero.mp hm).resolve_left hw

/-- Concrete finite amplitude left after the exact Laurent selector has
been eliminated. The finite bound is the original source occupation degree,
not a frequency cutoff. -/
def recompositionAmplitude (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (d h l : I →₀ ℕ) : ℂ :=
  (weight d : ℂ) *
    ∑ delta ∈ (Finsupp.finite_of_degree_le (σ := I) d.degree).toFinset,
      (weight delta : ℂ) * affineCoefficient (correctionMatrix D label)
        (correctionMean D a label) (d.sumElim delta) *
          affineCoefficient (normalMatrix D label) (normalMean D a label)
            (threeOccupation delta h l)

private theorem finiteCorrection_readout (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) :
    normalReadout D a label h l (finiteCorrection D a label d) =
      recompositionAmplitude D a label d h l := by
  classical
  let F := (Finsupp.finite_of_degree_le (σ := I) d.degree).toFinset
  let p := finiteCorrection D a label d
  have hF : p.support ⊆ F := by
    intro delta hd
    have hn : p.coeff delta ≠ 0 := mem_support_iff.mp hd
    have hle : delta.degree ≤ d.degree := by
      by_contra hh
      exact hn (finiteCorrection_degree D a label d delta (Nat.lt_of_not_ge hh))
    simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hle
  rw [normalReadout_expansion]
  calc
    _ = ∑ delta ∈ F, p.coeff delta * (weight delta : ℂ) *
        affineCoefficient (normalMatrix D label) (normalMean D a label)
          (threeOccupation delta h l) := by
      apply Finset.sum_subset hF
      intro delta hd hout
      change p.coeff delta * _ * _ = 0
      rw [notMem_support_iff.mp hout, zero_mul, zero_mul]
    _ = recompositionAmplitude D a label d h l := by
      unfold recompositionAmplitude
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro delta hd
      dsimp only [p]
      rw [finiteCorrection_coeff, charged_correction_coefficients]
      ring

/-- Actual oscillatorCorrected row, reduced to a bounded finite Gaussian
contraction on exactly K=alpha.support union beta.support union gamma.support.
All three original factorials remain: beta!, gamma! here, and alpha! in
recompositionAmplitude. Empty K is admitted. The remaining finite amplitude is identified in
`OriginalAffineRecompositionSource`. -/
theorem original_corrected_row_finite_reduction (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (alpha beta gamma : Index D →₀ ℕ) (e : ℤ) :
    wick D (monomial gamma 1)
        (oscillatorCorrected D hu a e (monomial alpha 1) (monomial beta 1)) =
      let K := rowSupport D alpha beta gamma
      let label := supportLabel D K
      let d := restricted D K alpha
      let h := restricted D K beta
      let l := restricted D K gamma
      (weight beta : ℂ) * (weight gamma : ℂ) *
        (if e+chargeNorm D a = Finsupp.weight (normalWeight D label) (threeOccupation d h l)
          then recompositionAmplitude D a label d h l else 0) := by
  classical
  let K := rowSupport D alpha beta gamma
  let label := supportLabel D K
  let d := restricted D K alpha
  let h := restricted D K beta
  let l := restricted D K gamma
  let n := e+chargeNorm D a
  let W := Finsupp.weight (normalWeight D label) (threeOccupation d h l)
  let c := Corr D a (monomial alpha 1)
  have ha : alpha.support ⊆ K := Finset.subset_union_left.trans Finset.subset_union_left
  have hb : beta.support ⊆ K := Finset.subset_union_right.trans Finset.subset_union_left
  have hc : gamma.support ⊆ K := Finset.subset_union_right
  have hda : d.embDomain label = alpha := restricted_reconstruct D K alpha ha
  have hsupport (s : ℕ) (delta : Index D →₀ ℕ) (hd : delta ∈ (c s).support) :
      delta.support ⊆ K :=
    (Corr_residual_support D a alpha delta s (mem_support_iff.mp hd)).trans ha
  have hreadout : normalReadout D a label h l (finiteCorrection D a label d) =
      ∑ s ∈ c.support, ∑ delta ∈ (c s).support,
        (c s).coeff delta * (weight (restricted D K delta) : ℂ) *
          affineCoefficient (normalMatrix D label) (normalMean D a label)
            (threeOccupation (restricted D K delta) h l) := by
    rw [finiteCorrection, hda, correctionOne_shifts]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact normalReadout_projection D a K h l (c s) (hsupport s)
  have hterm (s : ℕ) (delta : Index D →₀ ℕ) (hd : delta ∈ (c s).support) :
      (c s).coeff delta * (weight delta : ℂ) *
          normalLaurentRow D a delta beta gamma (e+2*(s : ℤ)+chargeNorm D a) =
        if n = W then
          (c s).coeff delta * (weight (restricted D K delta) : ℂ) *
            affineCoefficient (normalMatrix D label) (normalMean D a label)
              (threeOccupation (restricted D K delta) h l)
        else 0 := by
    have hr : (restricted D K delta).embDomain label = delta :=
      restricted_reconstruct D K delta (hsupport s delta hd)
    have hw : weight (restricted D K delta) = weight delta := by
      rw [← embedded_weight D label, hr]
    have hn : (Corr D a (monomial (d.embDomain label) 1) s).coeff
        ((restricted D K delta).embDomain label) ≠ 0 := by
      rw [hda, hr]
      exact mem_support_iff.mp hd
    have he := normal_shift_selector D a label d (restricted D K delta) h l s n hn
    have hexp : e+2*(s : ℤ)+chargeNorm D a = n+2*(s : ℤ) := by dsimp [n]; omega
    rw [normalLaurentRow_on_block D a delta beta gamma K (hsupport s delta hd) hb hc,
      hexp, affineLaurent_apply, ← hw]
    change _ = if n = W then _ else _
    by_cases hW : n = W
    · rw [if_pos hW, if_pos (he.mpr hW)]
    · rw [if_neg hW, if_neg (fun hh => hW (he.mp hh)), mul_zero]
  rw [original_corrected_normal_convolution]
  change (weight beta : ℂ) * (weight gamma : ℂ) *
    (∑ s ∈ c.support, ∑ delta ∈ (c s).support, _) = _
  congr 1
  have hsum :
      (∑ s ∈ c.support, ∑ delta ∈ (c s).support,
        (c s).coeff delta * (weight delta : ℂ) *
          normalLaurentRow D a delta beta gamma (e+2*(s : ℤ)+chargeNorm D a)) =
      if n = W then normalReadout D a label h l (finiteCorrection D a label d) else 0 := by
    rw [hreadout]
    by_cases hn : n = W
    · rw [if_pos hn]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro delta hd
      rw [hterm s delta hd, if_pos hn]
    · rw [if_neg hn]
      apply Finset.sum_eq_zero
      intro s hs
      apply Finset.sum_eq_zero
      intro delta hd
      rw [hterm s delta hd, if_neg hn]
  rw [hsum, finiteCorrection_readout]

/-- The target's ORIGINAL SS completion of the normalMatrix. Every
SI/SO/IO entry and every other external block is retained literally. -/
def correctedMatrix (D : LatticeData) (label : I ↪ Index D) :
    Matrix (I ⊕ (I ⊕ I)) (I ⊕ (I ⊕ I)) ℂ := fun x y =>
  match x,y with
  | .inl i, .inl j => sourceCovariance D label i j
  | _, _ => normalMatrix D label x y

/-- Only the source mean is completed; the two charged external means
remain literal. -/
def correctedMean (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    I ⊕ (I ⊕ I) → ℂ := fun x =>
  match x with
  | .inl i => sourceMean D a label i
  | .inr _ => normalMean D a label x



end D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource
