/- GID: D5/S3/Quantum/Recovery/FiniteKrausReversibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteKrausReversibility
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   digest: Scalar error products construct a finite normalized Kraus left inverse, and characterize exact reversibility in the finite Kraus representation. -/

import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
import D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
import Mathlib.Analysis.Matrix.PosDef

/-!
# Exact finite Kraus reversibility

The spectral theorem and positive eigenvalues are reused from Mathlib. The
orthogonal-syndrome recovery and full-space completion are reused from their
existing owners. Zero spectral weights are removed by an actual subtype sum;
there is no division by a zero probability. The only local mixing calculation
is rectangular: the existing repository Kraus-mixing result has square Kraus
matrices and cannot directly type this input/output pair.

The final iff quantifies over all finite Kraus representations. It does not
silently assume the representation theorem for the separately bundled
all-amplification CP interface. The forward construction nevertheless returns
an actual channel in that canonical interface.

The criterion and construction are classical Knill--Laflamme and Nayak--Sen
results. No new correction criterion is claimed.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.FiniteKrausReversibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
open D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
open D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {s n d : Type*} [Fintype s] [DecidableEq s]
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]

private def rotateErrors (E : s → Matrix n d ℂ) (V : Matrix s s ℂ) (j : s) :
    Matrix n d ℂ := ∑ a, V a j • E a

private theorem rotated_gram (E : s → Matrix n d ℂ) (c V : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)) (j k : s) :
    (rotateErrors E V j)ᴴ * rotateErrors E V k =
      (Vᴴ * c * V) j k • (1 : Matrix d d ℂ) := by
  calc
    _ = ∑ a, ∑ b, (star (V a j) * c a b * V b k) • (1 : Matrix d d ℂ) := by
      simp only [rotateErrors, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hE]
      simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul, Finset.sum_smul]
      rw [Finset.sum_comm]

private theorem rotated_action (E : s → Matrix n d ℂ) (V : Matrix s s ℂ)
    (hV : V * Vᴴ = 1) (X : Matrix d d ℂ) :
    (∑ j, rotateErrors E V j * X * (rotateErrors E V j)ᴴ) =
      ∑ a, E a * X * (E a)ᴴ := by
  have hcoeff (a b : s) : (∑ j, V a j * star (V b j)) =
      if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix s s ℂ => M a b) hV
  calc
    _ = ∑ j, ∑ a, ∑ b, (V a j * star (V b j)) • (E a * X * (E b)ᴴ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [rotateErrors, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp [smul_smul, mul_comm]
    _ = ∑ a, ∑ b, (∑ j, V a j * star (V b j)) • (E a * X * (E b)ᴴ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = _ := by simp_rw [hcoeff]; simp

private theorem sum_on_positive {M : Type*} [AddCommMonoid M]
    (lam : s → ℝ) (f : s → M) (hz : ∀ j, ¬ 0 < lam j → f j = 0) :
    (∑ j, f j) = ∑ j : {j : s // 0 < lam j}, f j := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun j => 0 < lam j) f
  have hc : (∑ j : {j : s // ¬ 0 < lam j}, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j j.property
  simpa only [hc, add_zero] using h.symm

/-- The scalar criterion builds a finite, normalized, actual left inverse. All zero eigenvalue errors are explicitly eliminated. -/
theorem scalar_products_construct_left_inverse (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1) (v : d) (c : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)) :
    ∃ r : ℕ, ∃ A : Fin r → Matrix d n ℂ,
      (∑ b, (A b)ᴴ * A b) = 1 ∧
      ∀ X : Matrix d d ℂ,
        (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X := by
  classical
  let R : Matrix n s ℂ := fun x a => E a x v
  have hcGram : c = Rᴴ * R := by
    ext a b
    have h := congrArg (fun M : Matrix d d ℂ => M v v) (hE a b)
    simpa only [R, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using h.symm
  have hc : c.PosSemidef := by rw [hcGram]; exact Matrix.posSemidef_conjTranspose_mul_self R
  have hcTrace : Matrix.trace c = 1 := by
    have h := congrArg (fun M : Matrix d d ℂ => M v v) hTP
    have hdiag (a : s) : ((E a)ᴴ * E a) v v = c a a := by
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using
        congrArg (fun M : Matrix d d ℂ => M v v) (hE a a)
    simpa only [Matrix.sum_apply, hdiag, Matrix.one_apply_eq, Matrix.trace,
      Matrix.diag_apply] using h
  let lam : s → ℝ := hc.isHermitian.eigenvalues
  let V : Matrix.unitaryGroup s ℂ := hc.isHermitian.eigenvectorUnitary
  let F : s → Matrix n d ℂ := rotateErrors E V
  have hlam (j : s) : 0 ≤ lam j := hc.eigenvalues_nonneg j
  have hV : (V : Matrix s s ℂ) * (V : Matrix s s ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  have hdiagV : (V : Matrix s s ℂ)ᴴ * c * (V : Matrix s s ℂ) =
      Matrix.diagonal (fun j => (lam j : ℂ)) := by
    simpa only [V, lam, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using
        hc.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hFgram (j k : s) : (F j)ᴴ * F k =
      if j = k then (lam j : ℂ) • (1 : Matrix d d ℂ) else 0 := by
    change (rotateErrors E V j)ᴴ * rotateErrors E V k = _
    rw [rotated_gram E c V hE, hdiagV]
    by_cases h : j = k
    · subst k; simp
    · simp [Matrix.diagonal_apply, h]
  have hzero (j : s) (hj : ¬ 0 < lam j) : F j = 0 := by
    have hl : lam j = 0 := le_antisymm (le_of_not_gt hj) (hlam j)
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [hFgram j j, if_pos rfl, hl, Complex.ofReal_zero, zero_smul]
  have hlamSum : (∑ j, (lam j : ℂ)) = 1 := by
    rw [← Matrix.IsHermitian.trace_eq_sum_eigenvalues hc.isHermitian]
    exact hcTrace
  let J := {j : s // 0 < lam j}
  let S : J → Matrix n d ℂ := fun j => (Real.sqrt (lam j) : ℂ)⁻¹ • F j
  have hroot (j : J) : (Real.sqrt (lam j) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 j.property)
  have hrootsq (j : J) : (Real.sqrt (lam j) : ℂ) ^ 2 = (lam j : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hlam j)
  have hS : OrthogonalSyndromes S := by
    intro j k
    change (((Real.sqrt (lam j) : ℂ)⁻¹ • F j)ᴴ *
      ((Real.sqrt (lam k) : ℂ)⁻¹ • F k)) = _
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hstar : star ((Real.sqrt (lam j) : ℂ)⁻¹) = (Real.sqrt (lam j) : ℂ)⁻¹ := by simp
    rw [hstar, hFgram]
    by_cases h : j = k
    · subst k
      simp only [if_pos rfl, smul_smul]
      have hz : (Real.sqrt (lam j) : ℂ)⁻¹ * (Real.sqrt (lam j) : ℂ)⁻¹ * (lam j : ℂ) = 1 := by
        rw [← hrootsq j]
        field_simp [hroot j]
      rw [hz, one_smul]
    · have hjk : (j : s) ≠ (k : s) := fun he => h (Subtype.ext he)
      simp [h, hjk]
  have hFrep (j : J) : F j = (Real.sqrt (lam j) : ℂ) • S j := by
    dsimp only [S]
    rw [smul_smul, mul_inv_cancel₀ (hroot j), one_smul]
  let sigma : Matrix J J ℂ := Matrix.diagonal (fun j => (lam j : ℂ))
  have hsigmatrace : Matrix.trace sigma = 1 := by
    dsimp only [sigma]
    rw [Matrix.trace_diagonal]
    rw [← sum_on_positive lam (fun j => (lam j : ℂ)) (fun j hj => by
      have hl : lam j = 0 := le_antisymm (le_of_not_gt hj) (hlam j)
      simp [hl])]
    exact hlamSum
  have hnoise (X : Matrix d d ℂ) :
      (∑ a, E a * X * (E a)ᴴ) = syndromeEncoding S sigma X := by
    calc
      _ = ∑ j, F j * X * (F j)ᴴ := (rotated_action E V hV X).symm
      _ = ∑ j : J, F j * X * (F j)ᴴ := sum_on_positive lam _ (fun j hj => by rw [hzero j hj]; simp)
      _ = ∑ j : J, (lam j : ℂ) • (S j * X * (S j)ᴴ) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = ((Real.sqrt (lam j) : ℂ) • S j) * X *
              (((Real.sqrt (lam j) : ℂ) • S j)ᴴ) :=
            congrArg (fun M : Matrix n d ℂ => M * X * Mᴴ) (hFrep j)
          _ = _ := by
            simp only [Matrix.conjTranspose_smul, Matrix.smul_mul,
              Matrix.mul_smul, smul_smul]
            have hs : star (Real.sqrt (lam j) : ℂ) = (Real.sqrt (lam j) : ℂ) := by simp
            rw [hs]
            have hsq : (Real.sqrt (lam j) : ℂ) * (Real.sqrt (lam j) : ℂ) = (lam j : ℂ) := by
              simpa only [pow_two] using hrootsq j
            rw [hsq]
      _ = syndromeEncoding S sigma X := by
        simp [syndromeEncoding, sigma, Matrix.diagonal_apply, ite_smul]
  let P := codeSupport S
  let A₀ : J ⊕ n → Matrix d n ℂ := completeKraus (fun j => (S j)ᴴ) P v
  obtain ⟨hP, hPP⟩ := code_support_projection S hS
  have hbase : (∑ j, ((S j)ᴴ)ᴴ * (S j)ᴴ) = P := by
    simp [P, codeSupport, logicalRepresentation]
  have hA₀ : (∑ b, (A₀ b)ᴴ * A₀ b) = 1 :=
    complete_kraus_normalised (fun j => (S j)ᴴ) P v hP hPP hbase
  have hrec (X : Matrix d d ℂ) :
      (∑ b, A₀ b * (∑ a, E a * X * (E a)ᴴ) * (A₀ b)ᴴ) = X := by
    change (∑ b, completeKraus (fun j => (S j)ᴴ) P v b *
      (∑ a, E a * X * (E a)ᴴ) * (completeKraus (fun j => (S j)ᴴ) P v b)ᴴ) = X
    rw [complete_kraus_action _ P v hP hPP, hnoise X]
    have hz : (1 - P) * syndromeEncoding S sigma X = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, code_support_on_encoding S hS, sub_self]
    rw [hz, Matrix.trace_zero, zero_smul, add_zero]
    simpa only [syndromeDecoding, Matrix.conjTranspose_conjTranspose] using
      trace_one_syndrome_recovery S hS sigma hsigmatrace X
  let e := (Fintype.equivFin (J ⊕ n)).symm
  refine ⟨Fintype.card (J ⊕ n), fun b => A₀ (e b), ?_, fun X => ?_⟩
  · calc
      _ = ∑ b, (A₀ b)ᴴ * A₀ b := Equiv.sum_comp e _
      _ = 1 := hA₀
  · calc
      _ = ∑ b, A₀ b * (∑ a, E a * X * (E a)ᴴ) * (A₀ b)ᴴ := Equiv.sum_comp e _
      _ = X := hrec X

/-- The normalized-trace error products exactly characterize finite-Kraus left inversion. -/
theorem finite_kraus_left_inverse_iff (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1) (v : d) :
    (∃ r : ℕ, ∃ A : Fin r → Matrix d n ℂ,
      (∑ b, (A b)ᴴ * A b) = 1 ∧
      ∀ X : Matrix d d ℂ,
        (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X) ↔
    (∀ a b, (E a)ᴴ * E b =
      (Matrix.trace ((E a)ᴴ * E b) / (Fintype.card d : ℂ)) • (1 : Matrix d d ℂ)) := by
  constructor
  · rintro ⟨r, A, hA, hleft⟩ a b
    exact left_inverse_normalized_trace_condition E A hA hleft v a b
  · intro hE
    exact scalar_products_construct_left_inverse E hTP v
      (fun a b => Matrix.trace ((E a)ᴴ * E b) / (Fintype.card d : ℂ)) hE

/-- The constructed inverse inhabits the repository's canonical all-amplification quantum channel interface. -/
theorem canonical_recovery_of_scalar_products (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1) (v : d) (c : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)) :
    ∃ recovery : QuantumChannel n d, ∀ X : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (∑ a, E a * X * (E a)ᴴ))) = X := by
  obtain ⟨r, A, hA, hrec⟩ := scalar_products_construct_left_inverse E hTP v c hE
  obtain ⟨recovery, haction⟩ := finite_kraus_quantum_channel A hA
  refine ⟨recovery, fun X => ?_⟩
  rw [haction, hrec]

#print axioms scalar_products_construct_left_inverse
#print axioms finite_kraus_left_inverse_iff
#print axioms canonical_recovery_of_scalar_products

end D5.S3.Quantum.Recovery.FiniteKrausReversibility
