/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual neutral correction moments and native Gaussian coefficients. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian

open MvPolynomial LatticeGeneratingFieldLocality
open LatticeHalfFockFiniteCorrection LatticeHalfFockCurrentCorrection
open FactorialFockQuadraticEstimate
open NativeGaussianMoment (nativeMoment nativeMoment_step sub_single_degree occupation_nonzero)

/-- Finite shift evaluation of the actual neutral correction, followed by
its oscillator constant coefficient. This linear map is not multiplicative. -/
def sourceVacuum (D : LatticeData) (z : ℂ) : Oscillator D →ₗ[ℂ] ℂ :=
  (Finsupp.lsum ℂ (fun s => z ^ s • (lcoeff ℂ (0 : Index D →₀ ℕ)))).comp
    (Corr D 0)

/-- Bilinear covariance, with the actual shift evaluation and no conjugates. -/
def covariance (D : LatticeData) (z : ℂ) (a b : Index D) : ℂ :=
  pairScalar (a.2 + 1) (b.2 + 1) * (D.G a.1 b.1 : ℂ) *
    z ^ ((a.2 + 1) + (b.2 + 1))

private def evaluateCorrection (D : LatticeData) (z : ℂ) :
    CorrectionPolynomial D →+* ℂ :=
  eval (fun a => a.elim z (fun _ => 0))

private theorem shift_reconstruction (D : LatticeData) (z : ℂ)
    (q : Polynomial (Oscillator D)) :
    q.toFinsupp.coeff.sum (fun s p => z ^ s * constantCoeff p) =
      Polynomial.eval z (Polynomial.map constantCoeff q) := by
  rw [← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact mul_comm _ _

/-- The actual finite Corr readout is evaluation of its option-variable lift.
The shift sum is reconstructed before the ordinary oscillator variables vanish. -/
theorem sourceVacuum_eq_evaluation (D : LatticeData) (z : ℂ) (p : Oscillator D) :
    sourceVacuum D z p = evaluateCorrection D z (correctionLift D 0 p) := by
  change (shiftCoefficients D (correctionPolynomial D 0 p)).sum _ = _
  change ((correctionPolynomial D 0 p).toFinsupp.coeff.sum
    (fun s p => z ^ s * constantCoeff p)) = _
  rw [shift_reconstruction]
  symm
  simpa only [evaluateCorrection, optionEquivLeft_elim_eval, eval_zero',
    correctionPolynomial, correctionLift, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]

theorem covariance_symm (D : LatticeData) (z : ℂ) (a b : Index D) :
    covariance D z a b = covariance D z b a := by
  have hs (m n : ℕ) : pairScalar m n = pairScalar n m := by
    unfold pairScalar
    rw [add_comm (m : ℂ) (n : ℂ)]
    ring
  unfold covariance
  rw [hs, D.symmetric a.1 b.1, Nat.add_comm (a.2 + 1) (b.2 + 1)]

private theorem eval_pair (D : LatticeData) (z : ℂ) (a b : Index D) :
    evaluateCorrection D z (pairPolynomial D a b) = covariance D z a b := by
  simp [evaluateCorrection, pairPolynomial, sourceWeight, covariance]

private theorem eval_singleton (D : LatticeData) (z : ℂ) (a : Index D) :
    evaluateCorrection D z (singletonPolynomial D 0 a) = 0 := by
  simp [singletonPolynomial, LatticeGeneratingFieldLocality.bilinear,
    evaluateCorrection]

private theorem derivation_sum_apply {σ α : Type*} (s : Finset α)
    (f : α → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (p : MvPolynomial σ ℂ) : (∑ a ∈ s, f a) p = ∑ a ∈ s, f a p := by
  change (Derivation.coeFnAddMonoidHom (∑ a ∈ s, f a)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply]

private theorem derivation_finite {σ : Type*} (f : σ → MvPolynomial σ ℂ)
    (p : MvPolynomial σ ℂ) (s : Finset σ) (hs : p.vars ⊆ s) :
    mkDerivation ℂ f p = ∑ a ∈ s, f a * pderiv a p := by
  classical
  let δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
    ∑ a ∈ s, f a • pderiv a
  have h : mkDerivation ℂ f p = δ p := by
    apply derivation_eq_of_forall_mem_vars
    intro a ha
    simp [δ, derivation_sum_apply, Derivation.smul_apply,
      mkDerivation_X, pderiv_X, Pi.single_apply, hs ha]
  simpa [δ, derivation_sum_apply, Derivation.smul_apply, smul_eq_mul] using h

private def sourceContraction (D : LatticeData) (z : ℂ) (a : Index D) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  mkDerivation ℂ (fun b => C (covariance D z a b))

private theorem eval_contraction (D : LatticeData) (z : ℂ) (a : Index D)
    (p : Oscillator D) :
    evaluateCorrection D z (pairDerivation D a (correctionLift D 0 p)) =
      sourceVacuum D z (sourceContraction D z a p) := by
  classical
  let q := correctionLift D 0 p
  let s : Finset (Index D) := p.vars ∪ q.vars.biUnion (fun b => b.toFinset)
  have hp : p.vars ⊆ s := Finset.subset_union_left
  have hq : q.vars ⊆ insert none (s.image some) := by
    intro b hb
    cases b with
    | none => exact Finset.mem_insert_self _ _
    | some b =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨b, Finset.mem_union_right _ ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨some b, hb, by simp⟩
  rw [pairDerivation, derivation_finite _ q _ hq]
  simp only [map_sum, map_mul]
  rw [Finset.sum_insert (by simp)]
  simp only [Option.elim_none, map_zero, zero_mul, zero_add]
  rw [Finset.sum_image (by intro b _ c _ h; exact Option.some.inj h)]
  simp only [Option.elim_some, eval_pair]
  simp_rw [show ∀ b, pderiv (some b) q = correctionLift D 0 (pderiv b p) from
    fun b => correctionLift_partial D 0 b p, ← sourceVacuum_eq_evaluation]
  rw [sourceContraction, derivation_finite _ p _ hp, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [C_mul', map_smul]
  rfl

private theorem sourceVacuum_C (D : LatticeData) (z a : ℂ) :
    sourceVacuum D z (C a) = a := by
  rw [sourceVacuum_eq_evaluation, correctionLift_C]
  simp [evaluateCorrection]

private theorem sourceVacuum_X_mul (D : LatticeData) (z : ℂ)
    (a : Index D) (p : Oscillator D) :
    sourceVacuum D z (p * X a) =
      sourceVacuum D z (sourceContraction D z a p) := by
  rw [sourceVacuum_eq_evaluation, correctionLift_X_mul]
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_mul]
  rw [eval_singleton]
  have hx : evaluateCorrection D z (X (some a)) = 0 := by simp [evaluateCorrection]
  rw [hx, zero_add, zero_mul, zero_add]
  exact eval_contraction D z a p

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- An arbitrary finite-support complex linear form in the actual oscillator variables. -/
def linearForm (D : LatticeData) (c : Index D →₀ ℂ) : Oscillator D :=
  ∑ a ∈ c.support, c a • X a

/-- The full bilinear covariance matrix of the chosen finite family. -/
def covarianceMatrix (D : LatticeData) (z : ℂ) (c : I → Index D →₀ ℂ) :
    Matrix I I ℂ := fun i j =>
  ∑ a ∈ (c i).support, ∑ b ∈ (c j).support, c i a * c j b * covariance D z a b

private theorem covarianceMatrix_symm (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (i j : I) :
    covarianceMatrix D z c i j = covarianceMatrix D z c j i := by
  unfold covarianceMatrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [covariance_symm D z a b]
  ring

private def formContraction (D : LatticeData) (z : ℂ) (c : Index D →₀ ℂ) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  ∑ a ∈ c.support, c a • sourceContraction D z a

private theorem sourceVacuum_form_mul (D : LatticeData) (z : ℂ)
    (c : Index D →₀ ℂ) (p : Oscillator D) :
    sourceVacuum D z (p * linearForm D c) =
      sourceVacuum D z (formContraction D z c p) := by
  simp only [linearForm, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    sourceVacuum_X_mul, formContraction, derivation_sum_apply, Derivation.smul_apply]

private theorem formContraction_linearForm (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (i j : I) :
    formContraction D z (c i) (linearForm D (c j)) =
      C (covarianceMatrix D z c i j) := by
  calc
    _ = ∑ a ∈ (c i).support, ∑ b ∈ (c j).support,
        (c i a * c j b) • C (covariance D z a b) := by
      simp only [formContraction, derivation_sum_apply, Derivation.smul_apply]
      simp only [linearForm, map_sum, Derivation.map_smul, sourceContraction,
        mkDerivation_X, Finset.smul_sum, smul_smul]
    _ = _ := by
      simp only [covarianceMatrix, map_sum, smul_eq_C_mul, ← map_mul]

private def substitution (D : LatticeData) (c : I → Index D →₀ ℂ) :
    MvPolynomial I ℂ →ₐ[ℂ] Oscillator D := aeval (linearForm D ∘ c)

private theorem contraction_substitution (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (i : I) (p : MvPolynomial I ℂ) :
    formContraction D z (c i) (substitution D c p) =
      substitution D c (mkDerivation ℂ (fun j => C (covarianceMatrix D z c i j)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [substitution]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp,
      mkDerivation_X]
    simp only [substitution, aeval_X, Function.comp_apply,
      formContraction_linearForm, aeval_C, algebraMap_eq]

private def sourceMoment (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) : ℂ :=
  sourceVacuum D z (substitution D c (monomial d 1))

private theorem sourceMoment_zero (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) : sourceMoment D z c 0 = 1 := by
  change sourceVacuum D z (substitution D c (C 1)) = 1
  simpa [substitution] using sourceVacuum_C D z 1

private theorem sourceMoment_step (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (r : I →₀ ℕ) (i : I) :
    sourceMoment D z c (r + Finsupp.single i 1) =
      ∑ j, (r j : ℂ) * covarianceMatrix D z c i j *
        sourceMoment D z c (r - Finsupp.single j 1) := by
  have hm : (monomial (r + Finsupp.single i 1) 1 : MvPolynomial I ℂ) =
      monomial r 1 * X i := by simp [X]
  unfold sourceMoment
  rw [hm, map_mul]
  rw [show substitution D c (X i) = linearForm D (c i) by
    simp only [substitution, aeval_X, Function.comp_apply]]
  rw [sourceVacuum_form_mul, contraction_substitution, mkDerivation_monomial]
  simp only [one_smul, Finsupp.sum, map_sum, smul_eq_mul]
  rw [← Finset.sum_subset (Finset.subset_univ r.support)]
  · apply Finset.sum_congr rfl
    intro j hj
    have hterm : monomial (r - Finsupp.single j 1) (r j : ℂ) *
        (C (covarianceMatrix D z c i j) : MvPolynomial I ℂ) =
        ((r j : ℂ) * covarianceMatrix D z c i j) •
          (monomial (r - Finsupp.single j 1) 1 : MvPolynomial I ℂ) := by
      rw [mul_comm _ (C _), C_mul_monomial, smul_monomial]
      simp [smul_eq_mul, mul_comm]
    rw [hterm, map_smul, map_smul]
    rfl
  · intro j hj hnot
    simp [Finsupp.notMem_support_iff.mp hnot]

private theorem sourceMoment_odd (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) (hd : d.degree % 2 = 1) :
    sourceMoment D z c d = 0 := by
  have go : ∀ n (e : I →₀ ℕ), e.degree = n → n % 2 = 1 →
      sourceMoment D z c e = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he ho
      have hne : e ≠ 0 := by intro h; subst e; simp at he; omega
      obtain ⟨i, hi⟩ := occupation_nonzero e hne
      let r := e - Finsupp.single i 1
      have hr : r + Finsupp.single i 1 = e := Finsupp.sub_add_single_one_cancel hi
      have hrd : r.degree + 1 = n := (sub_single_degree e i hi).trans he
      rw [← hr, sourceMoment_step]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hz : r j = 0
      · simp [hz]
      · have hsub := sub_single_degree r j hz
        have hlt : (r - Finsupp.single j 1).degree < n := by omega
        have hodd : (r - Finsupp.single j 1).degree % 2 = 1 := by omega
        rw [ih _ hlt _ rfl hodd, mul_zero]
  exact go d.degree d rfl hd

private theorem sourceMoment_eq_nativeMoment (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) :
    sourceMoment D z c d = nativeMoment (covarianceMatrix D z c) d := by
  have go : ∀ n (e : I →₀ ℕ), e.degree = n →
      sourceMoment D z c e = nativeMoment (covarianceMatrix D z c) e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he
      by_cases hz : e = 0
      · subst e
        simp [sourceMoment_zero, nativeMoment, gaussianCoefficient_zero,
          FactorialFockMetric.weight]
      by_cases hodd : e.degree % 2 = 1
      · rw [sourceMoment_odd D z c e hodd]
        simp [nativeMoment, gaussianCoefficient_odd _ _ hodd]
      obtain ⟨i, hi⟩ := occupation_nonzero e hz
      let r := e - Finsupp.single i 1
      have hr : r + Finsupp.single i 1 = e := Finsupp.sub_add_single_one_cancel hi
      have hrd : r.degree + 1 = n := (sub_single_degree e i hi).trans he
      rw [← hr, sourceMoment_step,
        nativeMoment_step _ (covarianceMatrix_symm D z c)]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hzero : r j = 0
      · simp [hzero]
      · have hsub := sub_single_degree r j hzero
        rw [ih _ (by omega) _ rfl]
  exact go d.degree d rfl

/-- Every occupation of every finite family of finite-support complex linear
forms has the exact factorial-weighted native Gaussian coefficient as its
actual neutral Corr vacuum readout. No positivity or nondegeneracy is
required; all complex shift parameters and empty mode types are included. -/
theorem sourceVacuum_linearForms (D : LatticeData) (z : ℂ)
    (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) :
    sourceVacuum D z (∏ i, linearForm D (c i) ^ d i) =
      (FactorialFockMetric.weight d : ℂ) *
        gaussianCoefficient (covarianceMatrix D z c) d := by
  have h := sourceMoment_eq_nativeMoment D z c d
  have hp : substitution D c (monomial d 1) = ∏ i, linearForm D (c i) ^ d i := by
    change aeval (linearForm D ∘ c) (monomial d 1) = _
    rw [aeval_monomial]
    simp [Finsupp.prod_fintype]
  simpa only [sourceMoment, nativeMoment, hp] using h

#print axioms sourceVacuum_eq_evaluation
#print axioms sourceVacuum_linearForms

end D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
