/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/AlternatingSpectrum
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-copy comparison for an involutive pairing of the joint spectral blocks. -/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-! A spectral block sent by the Hermitian second factor to one paired
block contributes a positive fourth moment to the four-copy comparison. -/

namespace RefinedBMV.Tracial

open scoped BigOperators ComplexOrder

/-- Covariance of the second factor with two commuting operators groups
the odd and even gaps in every word with an even number of second factors. -/
theorem semiconj_paired_gap_prod {R : Type*} [Monoid R] {A T B : R}
    (hcov : SemiconjBy B A T) (ha : Commute (B ^ 2) A) (ht : Commute (B ^ 2) T)
    (hat : Commute A T) (gaps : List (ℕ × ℕ)) :
    (gaps.map fun g ↦ A ^ g.1 * B * A ^ g.2 * B).prod =
      A ^ (gaps.map Prod.fst).sum * T ^ (gaps.map Prod.snd).sum * (B ^ 2) ^ gaps.length := by
  have hpair (r s : ℕ) : A ^ r * B * A ^ s * B = A ^ r * T ^ s * B ^ 2 := by
    rw [mul_assoc (A ^ r) B (A ^ s), (hcov.pow_right s).eq, pow_two]
    simp only [mul_assoc]
  induction gaps with
  | nil => simp
  | cons g gs ih =>
    let i := (gs.map Prod.fst).sum
    let j := (gs.map Prod.snd).sum
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, ih]
    rw [hpair g.1 g.2]
    change _ = A ^ (g.1 + i) * T ^ (g.2 + j) * (B ^ 2) ^ (gs.length + 1)
    calc
      _ = A ^ g.1 * T ^ g.2 * (B ^ 2 * (A ^ i * T ^ j)) * (B ^ 2) ^ gs.length := by
        simp only [i, j, mul_assoc]
      _ = A ^ g.1 * (T ^ g.2 * A ^ i) * T ^ j * (B ^ 2 * (B ^ 2) ^ gs.length) := by
        rw [((ha.pow_right i).mul_right (ht.pow_right j)).eq]
        simp only [mul_assoc]
      _ = _ := by
        rw [(hat.pow_pow i g.2).symm.eq, pow_add A, pow_add T, pow_succ' (B ^ 2) gs.length]
        simp only [mul_assoc]

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]

/-- If the second factor couples each spectral block only to its involutive
partner, the four-copy deficit is a sum of nonnegative alternating traces. -/
theorem alternating_spectral_contraction_nonneg
    (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : ι → A) (B : A) (x : ι → ℝ) (p : ℕ) (σ : ι → ι)
    (hσ : Function.Involutive σ) (hx : ∀ i, 0 ≤ x i)
    (hP : ∀ i, star (P i) = P i) (hPP : ∀ i, P i * P i = P i)
    (hB : star B = B) (hsupport : ∀ i j, j ≠ σ i → P i * B * P j = 0) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, (FourCopyGap.gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
      τ ((P i * B) * (P j * B) * (P k * B) * (P l * B)) := by
  classical
  let F (i : ι) : A := P i * B
  let term (i j k l : ι) : ℂ :=
    (FourCopyGap.gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
      τ (F i * F j * F k * F l)
  have hzero {i j : ι} (h : j ≠ σ i) : F i * F j = 0 := by
    change (P i * B) * (P j * B) = 0
    rw [← mul_assoc, hsupport i j h, zero_mul]
  have htrace (i j : ι) : 0 ≤ τ (F i * F j * F i * F j) := by
    let C := P i * B * P j
    let W := F i * F j * F i * F j
    have hC : C * star C = P i * B * P j * B * P i := by
      dsimp only [C]
      simp only [star_mul, hP, hB]
      calc
        _ = (P i * B) * (P j * P j) * B * P i := by simp only [mul_assoc]
        _ = _ := by rw [hPP]
    have hWP : W * P i = (C * star C) ^ 2 := by
      rw [pow_two, hC]
      calc
        _ = P i * B * P j * B * (P i * P i) * B * P j * B * P i := by
          rw [hPP]
          simp only [W, F, mul_assoc]
        _ = _ := by simp only [mul_assoc]
    have hPW : P i * W = W := by
      dsimp only [W, F]
      calc
        _ = (P i * P i) * B * P j * B * P i * B * P j * B := by
          simp only [mul_assoc]
        _ = _ := by rw [hPP]; simp only [mul_assoc]
    have hG : star (C * star C) = C * star C := by simp
    have hpos : 0 ≤ τ ((C * star C) ^ 2) :=
      τ.map_nonneg (by simpa only [hG, ← pow_two] using star_mul_self_nonneg (C * star C))
    change 0 ≤ τ W
    rwa [← hWP, hτ W (P i), hPW] at hpos
  change 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, term i j k l
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [Finset.sum_eq_single (σ i)]
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single (σ i)]
      · have hR := FourCopyGap.gapDefect_nonneg p (hx i) (hx (σ i)) (hx i) (hx (σ i))
        have hK : 0 ≤ (FourCopyGap.gapDefect p (x i) (x (σ i)) (x i) (x (σ i)) : ℂ) := by
          exact Complex.nonneg_iff.mpr ⟨by simpa using hR, by simp⟩
        exact mul_nonneg hK (htrace i (σ i))
      · intro l _ hl
        simp only [term, mul_assoc (F i * F (σ i)), hzero hl, mul_zero, map_zero]
      · simp
    · intro k _ hk
      have h : F (σ i) * F k = 0 := hzero (by simpa only [hσ i] using hk)
      apply Finset.sum_eq_zero
      intro l _
      unfold term
      rw [show F i * F (σ i) * F k * F l = F i * ((F (σ i) * F k) * F l) by
        simp only [mul_assoc]]
      simp [h]
    · simp
  · intro j _ hj
    simp only [term, hzero hj, zero_mul, map_zero, mul_zero, Finset.sum_const_zero]
  · simp

open Matrix FourCopyGap
open scoped MatrixOrder Matrix.Norms.L2Operator

open private spectralMask_mul_self trace_mask_product contract diagonal_gap_scaled
  eigenDiagonal rootDiagonal gaps_card_pos wordMean_conjugation
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

/-- The actual ordered-word comparison in an eigenbasis when the second
factor couples each spectral fiber only to its involutive partner. -/
theorem diagonal_word_bound_of_involutive_support
    {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s]
    (p : ℕ) (label : n → s) (x : s → ℝ) (hx : ∀ i, 0 ≤ x i)
    (B : Matrix n n ℂ) (hB : B.IsHermitian) (σ : s → s) (hσ : Function.Involutive σ)
    (hsupport : ∀ i j, j ≠ σ i → spectralBlock label B i j = 0) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B := by
  have hstar (i : s) : star (spectralMask label i) = spectralMask label i := by
    rw [Matrix.star_eq_conjTranspose, spectralMask, diagonal_conjTranspose]
    congr 1
    funext a
    by_cases ha : label a = i <;> simp [ha]
  have hBstar : star B = B := by rw [Matrix.star_eq_conjTranspose, hB.eq]
  have hn := alternating_spectral_contraction_nonneg (tracePositiveLinearMap n ℂ ℂ)
    (fun X Y ↦ trace_mul_comm X Y) (spectralMask label) B x p σ hσ hx
    hstar (spectralMask_mul_self label) hBstar hsupport
  have hs : 0 ≤ ((gaps p).card : ℂ) *
      (FourCopyGap.wordMean p (eigenDiagonal label x) B - trace ((rootDiagonal label x p * B) ^ 4)) := by
    rw [diagonal_gap_scaled]
    simpa only [tracePositiveLinearMap_apply, trace_mask_product label B, contract,
      LinearMap.coe_mk, AddHom.coe_mk] using hn
  have hc : (0 : ℝ) < (gaps p).card := by exact_mod_cast gaps_card_pos p
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hs
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hre),
    (sub_eq_zero.mp ((mul_eq_zero.mp him.symm).resolve_left hc.ne')).symm⟩

/-- Four-copy product comparison for a Hermitian second factor with
involutive support in a spectral decomposition of the first. -/
theorem product_bound_of_involutive_support
    {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s]
    (p : ℕ) (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian)
    (label : n → s) (x : s → ℝ) (hx : ∀ i, 0 ≤ x i)
    (U : Matrix.unitaryGroup n ℂ)
    (hdiag : Unitary.conjStarAlgAut ℂ _ U A = eigenDiagonal label x)
    (σ : s → s) (hσ : Function.Involutive σ)
    (hsupport : ∀ i j, j ≠ σ i →
      spectralBlock label (Unitary.conjStarAlgAut ℂ _ U B) i j = 0) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  let φ := Unitary.conjStarAlgAut ℂ _ U
  have hB' : (φ B).IsHermitian := by
    change star (φ B) = φ B
    rw [← map_star, Matrix.star_eq_conjTranspose, hB.eq]
  have hr : φ (A ^ ((p : ℝ) / 4)) = rootDiagonal label x p := by
    let f : ℝ → ℝ := fun y ↦ y ^ ((p : ℝ) / 4)
    have hf : φ (cfc f A) = cfc f (φ A) :=
      StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) φ f A
        (hf := (Set.toFinite (spectrum ℝ A)).continuousOn f)
        (hφ := φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional)
        (ha := hA.isHermitian) (hφa := by
          have hSelf : IsSelfAdjoint A := hA.isHermitian
          exact hSelf.map φ)
    rw [CFC.rpow_eq_cfc_real hA.nonneg, hf, show φ A = _ from hdiag]
    exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
      f (fun a ↦ x (label a))
  have hm : FourCopyGap.wordMean p (eigenDiagonal label x) (φ B) =
      FourCopyGap.wordMean p A B := by
    rw [← hdiag]
    exact wordMean_conjugation p U A B
  have ht : trace ((rootDiagonal label x p * φ B) ^ 4) =
      trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) := by
    rw [← hr, ← map_mul φ, ← map_pow φ]
    exact trace_conjugation U _
  simpa only [ht, hm] using
    diagonal_word_bound_of_involutive_support p label x hx (φ B) hB' σ hσ hsupport

end RefinedBMV.Tracial
