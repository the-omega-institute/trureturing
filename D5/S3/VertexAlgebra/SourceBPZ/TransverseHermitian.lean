/- GID: D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/TransverseHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv]
   utility: none
   digest: Original transverse BPZ form, exact factorial/frequency norm and strict positivity. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import D5.S3.VertexAlgebra.FactorialFockMetric
import D5.S3.VertexAlgebra.OriginalCurrentMetric

/-!
The original integral charge carrier, source pairing, theta reflection and canonical
Matter coefficient conjugation are retained. A real Gram-orthonormal transverse frame
gives a polynomial substitution into the original oscillator. The genuine integer Wick
recurrence is transported through its Gram directional derivative and compared with
the native factorial form after invertible scaling by sqrt(r+1).

The resulting finite-charge norm has coefficient weights
prod_(j,r) alpha(j,r)! * (r+1)^alpha(j,r). Every nonzero transverse family has
strictly positive original Hermitian norm. No positivity of the whole Gram, rank
restriction, charge restriction, BRST cohomology or analytic completion is asserted.
This is classical symmetric/Bargmann Fock normalization, without a novelty claim;
the native source, factorial and substitution suppliers retain their provenance.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators InnerProductSpace lp
open ComplexConjugate

namespace D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian

open LatticeGeneratingFieldLocality LatticeInvolution
open OriginalSourcePairing OriginalMatterHermitian
open MvPolynomial
open private integerWick_constant_left Hm_finset_sum_left Hm_finset_sum_right from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

variable {D : LatticeData} {t : ℕ}

abbrev E (D : LatticeData) := Fin D.rank → ℂ

def originalG (D : LatticeData) (u v : E D) : ℂ :=
  ∑ i, ∑ k, u i * (D.G i k : ℂ) * v k

/-- A real orthonormal positive subspace of the original, possibly indefinite Gram. -/
structure RealOrthonormalFrame (D : LatticeData) (t : ℕ) where
  B : Fin t → E D
  real_B : ∀ j i, conj (B j i) = B j i
  orthonormal : ∀ j k, originalG D (B j) (B k) = if j = k then 1 else 0

abbrev Polynomial (t : ℕ) := MvPolynomial (Fin t × ℕ) ℂ
abbrev Occupation (t : ℕ) := Fin t × ℕ →₀ ℕ

def lin (B : RealOrthonormalFrame D t) (j : Fin t) (r : ℕ) : Oscillator D :=
  ∑ i : Fin D.rank, B.B j i • X (i,r)

def phi (B : RealOrthonormalFrame D t) : Polynomial t →ₐ[ℂ] Oscillator D :=
  MvPolynomial.aeval (fun x : Fin t × ℕ => lin B x.1 x.2)

private theorem phi_X (B : RealOrthonormalFrame D t) (j : Fin t) (r : ℕ) :
    phi B (X (j,r)) = lin B j r := by simp [phi]

private theorem phi_constant (B : RealOrthonormalFrame D t) (P : Polynomial t) :
    (phi B P).coeff 0 = P.coeff 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [show phi B (C c) = C c from (phi B).commutes c]; simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
      rcases x with ⟨j,r⟩
      rw [map_mul, phi_X]
      simp [lin, Finset.mul_sum, MvPolynomial.coeff_mul_X']

/-- This derivation uses the actual original Gram-weighted annihilators. -/
def annihilateAlong (B : RealOrthonormalFrame D t) (j : Fin t) (r : ℕ) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  ∑ i : Fin D.rank, B.B j i • LatticeActualAnnihilation.annihilationDerivation D i r

private theorem annihilateAlong_apply (B : RealOrthonormalFrame D t)
    (j : Fin t) (r : ℕ) (p : Oscillator D) :
    annihilateAlong B j r p =
      ∑ i : Fin D.rank, B.B j i • LatticeActualAnnihilation.annihilate D i r p := by
  unfold annihilateAlong
  change (Derivation.coeFnAddMonoidHom (∑ i : Fin D.rank,
    B.B j i • LatticeActualAnnihilation.annihilationDerivation D i r)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply, LatticeActualAnnihilation.annihilation_apply]

private theorem annihilateAlong_lin (B : RealOrthonormalFrame D t)
    (j k : Fin t) (r s : ℕ) :
    annihilateAlong B j r (lin B k s) =
      if (j,r) = (k,s) then 1 else 0 := by
  classical
  rw [annihilateAlong_apply]
  simp only [lin, map_sum, map_smul, LatticeActualAnnihilation.annihilate_X]
  by_cases hrs : r = s
  · subst s
    simp only [ite_true, Finset.smul_sum, smul_smul]
    have hg : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
        (B.B j i * (B.B k l * (D.G i l : ℂ))) • (1 : Oscillator D)) =
        (originalG D (B.B j) (B.B k)) • (1 : Oscillator D) := by
      simp only [originalG, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [mul_assoc, mul_comm (D.G i l : ℂ) (B.B k l)]
    rw [hg, B.orthonormal]
    by_cases h : j = k <;> simp [h]
  · simp [hrs, Prod.mk.injEq]

theorem annihilateAlong_phi (B : RealOrthonormalFrame D t)
    (j : Fin t) (r : ℕ) (Q : Polynomial t) :
    annihilateAlong B j r (phi B Q) = phi B (MvPolynomial.pderiv (j,r) Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c =>
      rw [show phi B (C c) = C c from (phi B).commutes c]
      simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P x hP =>
      rcases x with ⟨k,s⟩
      rw [map_mul, (annihilateAlong B j r).leibniz,
        (MvPolynomial.pderiv (j,r)).leibniz]
      simp only [smul_eq_mul, map_add, map_mul, hP, phi_X, annihilateAlong_lin]
      by_cases h : (j,r) = (k,s) <;> simp [MvPolynomial.pderiv_X, h, eq_comm]

def bpzOsc (B : RealOrthonormalFrame D t) (P Q : Polynomial t) : ℂ :=
  integerWick D (sigma D (kappaOsc (phi B P))) (phi B Q)

private theorem conjugate_reflect_lin (B : RealOrthonormalFrame D t)
    (j : Fin t) (r : ℕ) : sigma D (kappaOsc (lin B j r)) = -lin B j r := by
  classical
  have hk : kappaOsc (lin B j r) = lin B j r := by
    simp [lin, kappaOsc, smul_eq_C_mul, B.real_B]
  rw [hk]
  simp only [lin, map_sum, sigma_smul, sigma_X, smul_neg, Finset.sum_neg_distrib]

private theorem integerWick_phi_creation (B : RealOrthonormalFrame D t)
    (j : Fin t) (r : ℕ) (p q : Oscillator D) :
    integerWick D (lin B j r * p) q =
      integerWick D p (-((r : ℂ) + 1) • annihilateAlong B j r q) := by
  classical
  simp only [lin, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, integerWick_creation]
  rw [annihilateAlong_apply, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm, mul_left_comm]

private theorem bpz_creation (B : RealOrthonormalFrame D t)
    (j : Fin t) (r : ℕ) (P Q : Polynomial t) :
    bpzOsc B (X (j,r) * P) Q =
      ((r : ℂ) + 1) * bpzOsc B P (MvPolynomial.pderiv (j,r) Q) := by
  unfold bpzOsc
  rw [map_mul, phi_X, kappaOsc_mul, map_mul, conjugate_reflect_lin,
    neg_mul, map_neg, LinearMap.neg_apply, integerWick_phi_creation,
    annihilateAlong_phi, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The integer frequency is r+1, before the complex cast. -/
def frequencyScale (r : ℕ) : ℂ := (Real.sqrt (r + 1 : ℝ) : ℂ)

private theorem frequencyScale_ne_zero (r : ℕ) : frequencyScale r ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

private def frequencyMatrix (t : ℕ) (r : ℕ) : Matrix (Fin t) (Fin t) ℂ :=
  frequencyScale r • (1 : Matrix (Fin t) (Fin t) ℂ)

private def inverseFrequencyMatrix (t : ℕ) (r : ℕ) : Matrix (Fin t) (Fin t) ℂ :=
  (frequencyScale r)⁻¹ • (1 : Matrix (Fin t) (Fin t) ℂ)

private theorem frequencyMatrix_mul_inverse (t r : ℕ) :
    frequencyMatrix t r * inverseFrequencyMatrix t r = 1 := by
  rw [frequencyMatrix, inverseFrequencyMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_inv_cancel₀ (frequencyScale_ne_zero r), one_smul, Matrix.one_mul]

private theorem inverseFrequencyMatrix_mul (t r : ℕ) :
    inverseFrequencyMatrix t r * frequencyMatrix t r = 1 := by
  rw [frequencyMatrix, inverseFrequencyMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, inv_mul_cancel₀ (frequencyScale_ne_zero r), one_smul, Matrix.one_mul]

/-- Reuses the native finite substitution equivalence; no form is defined here. -/
def rescale (t : ℕ) : Polynomial t ≃ₐ[ℂ] Polynomial t :=
  OriginalCurrentMetric.substitutionEquiv
    (frequencyMatrix t) (inverseFrequencyMatrix t)
    (frequencyMatrix_mul_inverse t) (inverseFrequencyMatrix_mul t)

private theorem rescale_X (j : Fin t) (r : ℕ) :
    rescale t (X (j,r)) = frequencyScale r • X (j,r) := by
  change OriginalCurrentMetric.substitution (frequencyMatrix t) (X (j,r)) = _
  rw [OriginalCurrentMetric.substitution_X, OriginalCurrentMetric.variableImage]
  simp [frequencyMatrix, Matrix.one_apply]

private theorem rescale_pderiv (P : Polynomial t) (j : Fin t) (r : ℕ) :
    MvPolynomial.pderiv (j,r) (rescale t P) =
      frequencyScale r • rescale t (MvPolynomial.pderiv (j,r) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [show rescale t (C c) = C c from (rescale t).commutes c]
      simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add]
  | mul_X P x hP =>
      rcases x with ⟨k,s⟩
      rw [map_mul, rescale_X, (MvPolynomial.pderiv (j,r)).leibniz]
      simp only [hP]
      by_cases h : r = s
      · subst s
        by_cases hjk : j = k
        · subst k
          simp [MvPolynomial.pderiv_X, rescale_X]
        · simp [MvPolynomial.pderiv_X, Prod.mk.injEq, hjk, rescale_X,
            ]
      · simp [MvPolynomial.pderiv_X, Prod.mk.injEq, Ne.symm h, rescale_X]

private theorem frequencyScale_square (r : ℕ) :
    frequencyScale r * frequencyScale r = (r : ℂ) + 1 := by
  have h := Real.mul_self_sqrt (show 0 ≤ (r + 1 : ℝ) by positivity)
  simpa [frequencyScale] using congrArg (Complex.ofReal : ℝ → ℂ) h

private def target (t : ℕ) (P Q : Polynomial t) : ℂ :=
  FactorialFockMetric.inner (rescale t P) (rescale t Q)

private theorem target_creation (P Q : Polynomial t) (j : Fin t) (r : ℕ) :
    target t (X (j,r) * P) Q =
      ((r : ℂ) + 1) * target t P (MvPolynomial.pderiv (j,r) Q) := by
  unfold target
  rw [map_mul, rescale_X, smul_mul_assoc]
  have hs (p q : Polynomial t) (c : ℂ) :
      FactorialFockMetric.inner (c • p) q =
        conj c * FactorialFockMetric.inner p q := by
    simp only [FactorialFockMetric.inner, map_smul, inner_smul_left]
  rw [hs, FactorialFockMetric.mul_X_pderiv_pairing, rescale_pderiv]
  have ht (p q : Polynomial t) (c : ℂ) :
      FactorialFockMetric.inner p (c • q) =
        c * FactorialFockMetric.inner p q := by
    simp only [FactorialFockMetric.inner, map_smul, inner_smul_right]
  rw [ht, show conj (frequencyScale r) = frequencyScale r by simp [frequencyScale],
    ← mul_assoc, frequencyScale_square]

private theorem rescale_constant (P : Polynomial t) :
    (rescale t P).coeff 0 = P.coeff 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [show rescale t (C c) = C c from (rescale t).commutes c]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
      rcases x with ⟨j,r⟩
      rw [map_mul, rescale_X, mul_smul_comm]
      simp [MvPolynomial.coeff_mul_X']

/-- The original retuned Wick form is compared with the independently defined factorial form. -/
theorem bpzOsc_eq_target (B : RealOrthonormalFrame D t) (P Q : Polynomial t) :
    bpzOsc B P Q = FactorialFockMetric.inner (rescale t P) (rescale t Q) := by
  change bpzOsc B P Q = target t P Q
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
      unfold bpzOsc target
      rw [show phi B (C c) = C c from (phi B).commutes c, kappaOsc_C,
        sigma_C,
        integerWick_constant_left, phi_constant,
        show rescale t (C c) = C c from (rescale t).commutes c]
      change _ = FactorialFockMetric.inner (monomial 0 c) _
      rw [FactorialFockMetric.inner_monomial_left, rescale_constant]
      simp [FactorialFockMetric.weight]
  | add P R hP hR =>
      simp only [bpzOsc, map_add, kappaOsc_add, LinearMap.add_apply] at *
      rw [hP, hR]
      simp [target, FactorialFockMetric.inner_add_first]
  | mul_X P x hP =>
      rcases x with ⟨j,r⟩
      rw [mul_comm P, bpz_creation, target_creation, hP]

def delta (B : RealOrthonormalFrame D t) (a : Charge D) (P : Polynomial t) :
    Carrier D := Finsupp.single a (phi B P)

theorem source_delta_delta_eq_factorial (B : RealOrthonormalFrame D t)
    (a b : Charge D) (P Q : Polynomial t) :
    Hm (delta B a P) (delta B b Q) =
      if a = b then FactorialFockMetric.inner (rescale t P) (rescale t Q) else 0 := by
  unfold Hm delta
  rw [kappaCarrier_single]
  change sourcePairing D (thetaLinear D (Finsupp.single a (kappaOsc (phi B P))))
    (Finsupp.single b (phi B Q)) = _
  rw [theta_single, sourcePairing_single_single]
  simp only [neg_neg]
  rw [show integerWick D (sigma D (kappaOsc (phi B P))) (phi B Q) =
      FactorialFockMetric.inner (rescale t P) (rescale t Q) from bpzOsc_eq_target B P Q]
  simp only [eq_comm]

def transverseEmbed (B : RealOrthonormalFrame D t) :
    (Charge D →₀ Polynomial t) → Carrier D := Finsupp.mapRange (phi B) (by simp)

def frequencyWeight (α : Occupation t) : ℕ := α.prod fun x n => (x.2 + 1) ^ n

def exactWeight (α : Occupation t) : ℕ := FactorialFockMetric.weight α * frequencyWeight α

private theorem exactWeight_pos (α : Occupation t) : 0 < exactWeight α := by
  classical
  apply Nat.mul_pos (FactorialFockMetric.weight_pos α)
  unfold frequencyWeight Finsupp.prod
  exact Finset.prod_pos fun _ _ => pow_pos (Nat.succ_pos _) _

private def frequencyAmplitude (α : Occupation t) : ℂ :=
  α.prod fun x n => frequencyScale x.2 ^ n

private theorem rescale_monomial (α : Occupation t) (c : ℂ) :
    rescale t (monomial α c) = monomial α (frequencyAmplitude α * c) := by
  classical
  rw [monomial_eq, map_mul, show rescale t (C c) = C c from (rescale t).commutes c]
  simp only [Finsupp.prod, map_prod, map_pow]
  have hx (x : Fin t × ℕ) : rescale t (X x) = frequencyScale x.2 • X x :=
    rescale_X x.1 x.2
  simp_rw [hx, smul_pow]
  rw [Finset.prod_smul, MvPolynomial.prod_X_pow_eq_monomial]
  rw [mul_smul_comm, C_mul_monomial, smul_monomial]
  simp [frequencyAmplitude, Finsupp.prod]

private theorem rescale_coeff (P : Polynomial t) (α : Occupation t) :
    (rescale t P).coeff α = frequencyAmplitude α * P.coeff α := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial β c =>
      by_cases h : β = α
      · subst β; simp [rescale_monomial]
      · simp [rescale_monomial, coeff_monomial, h]
  | add P Q hP hQ => simp [hP, hQ, mul_add]

private theorem frequencyAmplitude_real (α : Occupation t) :
    conj (frequencyAmplitude α) = frequencyAmplitude α := by
  simp [frequencyAmplitude, Finsupp.prod, frequencyScale]

private theorem frequencyAmplitude_square (α : Occupation t) :
    frequencyAmplitude α * frequencyAmplitude α = (frequencyWeight α : ℂ) := by
  classical
  simp only [frequencyAmplitude, frequencyWeight, Finsupp.prod, Nat.cast_prod,
    Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _
  rw [← mul_pow, frequencyScale_square]

theorem rescaled_inner_coeff_sum (P : Polynomial t) :
    FactorialFockMetric.inner (rescale t P) (rescale t P) =
      ∑ α ∈ P.support, (exactWeight α : ℂ) * (Complex.normSq (P.coeff α) : ℂ) := by
  classical
  have he : rescale t P =
      ∑ α ∈ P.support, rescale t (monomial α (P.coeff α)) := by
    rw [← map_sum, ← MvPolynomial.as_sum]
  rw [he]
  have hs (s : Finset (Occupation t)) (f : Occupation t → Polynomial t)
      (q : Polynomial t) : FactorialFockMetric.inner (∑ α ∈ s, f α) q =
        ∑ α ∈ s, FactorialFockMetric.inner (f α) q := by
    simp only [FactorialFockMetric.inner, map_sum, sum_inner]
  rw [hs]
  apply Finset.sum_congr rfl
  intro α _
  rw [← he, rescale_monomial, FactorialFockMetric.inner_monomial_left,
    rescale_coeff, map_mul, frequencyAmplitude_real]
  calc
    _ = (FactorialFockMetric.weight α : ℂ) *
        (frequencyAmplitude α * frequencyAmplitude α) *
        (conj (P.coeff α) * P.coeff α) := by ring
    _ = _ := by
      rw [frequencyAmplitude_square, Complex.normSq_eq_conj_mul_self]
      simp only [exactWeight, Nat.cast_mul]

/-- All original integral charges, including zero, contribute their exact coefficient norm. -/
theorem Hm_self_eq_exact_finite_sum (B : RealOrthonormalFrame D t)
    (x : Charge D →₀ Polynomial t) :
    Hm (transverseEmbed B x) (transverseEmbed B x) =
      ∑ a ∈ x.support, ∑ α ∈ (x a).support,
        (exactWeight α : ℂ) * (Complex.normSq ((x a).coeff α) : ℂ) := by
  classical
  have he : transverseEmbed B x =
      ∑ a ∈ x.support, delta B a (x a) := by
    apply Finsupp.ext
    intro a
    simp [transverseEmbed, delta, Finsupp.coe_finsetSum, Finsupp.single_apply,
      Finset.sum_ite_eq', apply_ite]
    intro h
    rw [h, map_zero]
  rw [he, Hm_finset_sum_left]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Hm_finset_sum_right]
  simp_rw [source_delta_delta_eq_factorial]
  simp_rw [eq_comm (a := a)]
  rw [Finset.sum_ite_eq' x.support a]
  simp only [ha, ite_true, rescaled_inner_coeff_sum]

private theorem Hm_self_re_sum (B : RealOrthonormalFrame D t)
    (x : Charge D →₀ Polynomial t) :
    (Hm (transverseEmbed B x) (transverseEmbed B x)).re =
      ∑ a ∈ x.support, ∑ α ∈ (x a).support,
        (exactWeight α : ℝ) * Complex.normSq ((x a).coeff α) := by
  rw [Hm_self_eq_exact_finite_sum]
  simp

/-- Strict positivity is on the actual embedded transverse subspace only. -/
theorem Hm_self_strict_positive (B : RealOrthonormalFrame D t)
    {x : Charge D →₀ Polynomial t} (hx : x ≠ 0) :
    (Hm (transverseEmbed B x) (transverseEmbed B x)).im = 0 ∧
      0 < (Hm (transverseEmbed B x) (transverseEmbed B x)).re := by
  classical
  constructor
  · rw [Hm_self_eq_exact_finite_sum]; simp
  · rw [Hm_self_re_sum]
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hx
    have ha' : a ∈ x.support := Finsupp.mem_support_iff.mpr (by simpa using ha)
    obtain ⟨α, hα⟩ := MvPolynomial.exists_coeff_ne_zero (by simpa using ha)
    apply Finset.sum_pos'
    · intro b _
      exact Finset.sum_nonneg fun β _ => mul_nonneg (Nat.cast_nonneg _)
        (Complex.normSq_nonneg _)
    · refine ⟨a, ha', ?_⟩
      apply Finset.sum_pos'
      · intro β _
        exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
      · exact ⟨α, MvPolynomial.mem_support_iff.mpr hα,
          mul_pos (by exact_mod_cast exactWeight_pos α) (Complex.normSq_pos.mpr hα)⟩

end D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
