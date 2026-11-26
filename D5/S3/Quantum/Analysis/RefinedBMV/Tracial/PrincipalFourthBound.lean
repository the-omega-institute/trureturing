/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/PrincipalFourthBound
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-copy refined BMV comparison from signed principal minors. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGram
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.PrincipalTraceCoefficients
import Mathlib.Data.Finsupp.Multiset

/-! Grouping cyclic traces by their spectral multiplicities transfers
the signs of principal minors to the four-copy product lower bound. -/

namespace RefinedBMV.Tracial

open Matrix FourCopyGap
open scoped ComplexOrder

open private contract trace_four_weighted diagonal_gap_scaled eigenDiagonal rootDiagonal
  gaps_card_pos from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

noncomputable section

private def listGap (p : ℕ) : List ℝ → ℝ
  | [a, b, c, d] => gapDefect p a b c d
  | _ => 0

private theorem listGap_perm (p : ℕ) {l l' : List ℝ} (h : l.Perm l') :
    ∀ pre : List ℝ, listGap p (pre ++ l) = listGap p (pre ++ l') := by
  induction h with
  | nil => simp
  | cons a _ ih =>
    intro pre
    simpa only [List.append_assoc, List.singleton_append] using ih (pre ++ [a])
  | swap a b tail =>
    intro pre
    rcases pre with _ | ⟨u, _ | ⟨v, _ | ⟨w, pre⟩⟩⟩
    · rcases tail with _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩ <;>
        simp only [List.nil_append, listGap, ThreeBlockGram.gapDefect_swap01 p b a]
    · rcases tail with _ | ⟨c, _ | ⟨d, tail⟩⟩ <;>
        simp only [List.cons_append, List.nil_append, listGap,
          ThreeBlockGram.gapDefect_swap12 p u b a]
    · rcases tail with _ | ⟨c, tail⟩ <;>
        simp only [List.cons_append, List.nil_append, listGap,
          ThreeBlockGram.gapDefect_swap23 p u v b a]
    · cases pre with
      | nil => rfl
      | cons _ rest => cases rest <;> rfl
  | trans _ _ ih₁ ih₂ => exact fun pre ↦ (ih₁ pre).trans (ih₂ pre)

private abbrev Labels (s : Type*) := s × s × s × s

private def multiplicities {s : Type*} (v : Labels s) : s →₀ ℕ :=
  Finsupp.single v.1 1 + Finsupp.single v.2.1 1 +
    Finsupp.single v.2.2.1 1 + Finsupp.single v.2.2.2 1

private def kernel {s : Type*} (p : ℕ) (x : s → ℝ) (v : Labels s) : ℝ :=
  gapDefect p (x v.1) (x v.2.1) (x v.2.2.1) (x v.2.2.2)

private theorem kernel_eq_of_multiplicities_eq {s : Type*} (p : ℕ) (x : s → ℝ)
    {v w : Labels s} (h : multiplicities v = multiplicities w) :
    kernel p x v = kernel p x w := by
  have hlist (v : Labels s) : Finsupp.toMultiset (multiplicities v) =
      ([v.1, v.2.1, v.2.2.1, v.2.2.2] : List s) := by
    simp only [multiplicities, Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul]
    simp
    rfl
  have hm : ([v.1, v.2.1, v.2.2.1, v.2.2.2] : Multiset s) =
      [w.1, w.2.1, w.2.2.1, w.2.2.2] := by
    rw [← hlist v, ← hlist w, h]
  simpa only [List.nil_append, List.map_cons, List.map_nil, listGap, kernel] using
    listGap_perm p ((Multiset.coe_eq_coe.mp hm).map x) []

private def cycleWeight {n s : Type*} [Fintype n] [DecidableEq n] [DecidableEq s]
    (label : n → s) (B : Matrix n n ℂ) (v : Labels s) : ℂ :=
  cycleTrace (spectralBlock label B) v.1 v.2.1 v.2.2.1 v.2.2.2

private theorem eval_cycle_monomial {s : Type*} (z : s → ℂ) (v : Labels s) (a : ℂ) :
    MvPolynomial.eval z (MvPolynomial.monomial (multiplicities v) a) =
      (z v.1 * z v.2.1 * z v.2.2.1 * z v.2.2.2) * a := by
  rw [show MvPolynomial.monomial (multiplicities v) a =
      MvPolynomial.C a * (MvPolynomial.X v.1 * MvPolynomial.X v.2.1 *
        MvPolynomial.X v.2.2.1 * MvPolynomial.X v.2.2.2) by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one, multiplicities,
      MvPolynomial.C_mul_monomial]]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  ac_rfl

private theorem trace_cycle_polynomial {n s : Type*}
    [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s]
    (label : n → s) (B : Matrix n n ℂ) :
    trace ((diagonal (fun i ↦ MvPolynomial.X (label i)) *
      B.map MvPolynomial.C) ^ 4) =
      ∑ v : Labels s, MvPolynomial.monomial (multiplicities v) (cycleWeight label B v) := by
  let : Infinite ℂ := Infinite.of_injective _ Complex.ofReal_injective
  apply MvPolynomial.funext
  intro z
  let f := MvPolynomial.eval z
  change f _ = f _
  rw [AddMonoidHom.map_trace f, ← RingHom.mapMatrix_apply, map_pow, map_mul]
  have hd : (f.mapMatrix (diagonal (fun i ↦ MvPolynomial.X (label i)))) =
      diagonal (fun i ↦ z (label i)) := by
    ext i j
    by_cases hij : i = j <;> simp [f, Matrix.diagonal, hij]
  have hB : f.mapMatrix (B.map MvPolynomial.C) = B := by
    ext i j
    simp [f]
  rw [hd, hB]
  simp only [f, map_sum, eval_cycle_monomial, Fintype.sum_prod_type, cycleWeight]
  simpa only [pow_succ, pow_zero, one_mul, contract, LinearMap.coe_mk, AddHom.coe_mk] using
    trace_four_weighted label B z z z z

private theorem scaled_gap_nonneg_of_trace_coeff_nonneg {n s : Type*}
    [Fintype n] [DecidableEq n] [Finite s]
    (p : ℕ) (label : n → s) (x : s → ℝ) (hx : ∀ i, 0 ≤ x i) (B : Matrix n n ℂ)
    (hCoeff : ∀ a : s →₀ ℕ, 0 ≤ (trace ((diagonal (fun i ↦ MvPolynomial.X (label i)) *
      B.map MvPolynomial.C) ^ 4)).coeff a) :
    0 ≤ ((gaps p).card : ℂ) *
      (FourCopyGap.wordMean p (eigenDiagonal label x) B -
        trace ((rootDiagonal label x p * B) ^ 4)) := by
  classical
  let _ := Fintype.ofFinite s
  rw [diagonal_gap_scaled]
  unfold contract
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have htuple :
      (∑ v : Labels s, (kernel p x v : ℂ) * cycleWeight label B v) =
        ∑ i, ∑ j, ∑ k, ∑ l, (gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
          cycleTrace (spectralBlock label B) i j k l := by
    simp only [Fintype.sum_prod_type, kernel, cycleWeight]
  rw [← htuple]
  rw [← Finset.sum_fiberwise_of_maps_to (g := multiplicities)
    (t := Finset.univ.image multiplicities) (fun v hv ↦ Finset.mem_image_of_mem _ hv)]
  refine Finset.sum_nonneg fun a ha ↦ ?_
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
  have hw : ∀ w ∈ (Finset.univ.filter (fun w : Labels s ↦
      multiplicities w = multiplicities v)), kernel p x w = kernel p x v :=
    fun w hw ↦ kernel_eq_of_multiplicities_eq p x (Finset.mem_filter.mp hw).2
  calc
    0 ≤ (kernel p x v : ℂ) *
        (trace ((diagonal (fun i ↦ MvPolynomial.X (label i)) *
          B.map MvPolynomial.C) ^ 4)).coeff (multiplicities v) := by
      exact mul_nonneg (Complex.zero_le_real.mpr (gapDefect_nonneg p (hx _) (hx _) (hx _) (hx _)))
        (hCoeff _)
    _ = _ := by
      rw [trace_cycle_polynomial, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [← Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w hw' ↦ by rw [hw w hw']

/-- The four-copy product lower bound under the signs of principal minors
of order at most four, relative to a spectral basis of the first factor. -/
theorem diagonal_word_bound_of_signed_minors {n : ℕ} {s : Type*}
    [Finite s] (p : ℕ) (label : Fin n → s)
    (x : s → ℝ) (hx : ∀ i, 0 ≤ x i) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ I : Finset (Fin n), 0 < I.card → I.card ≤ 4 →
      0 ≤ (-1 : ℂ) ^ (I.card + 1) *
        (B.submatrix (Subtype.val : I → Fin n) (Subtype.val : I → Fin n)).det) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B := by
  have hs := scaled_gap_nonneg_of_trace_coeff_nonneg p label x hx B
    (trace_pow_coeff_nonneg_of_signed_minors B label 4 (by decide) hB)
  have hc : (0 : ℝ) < (gaps p).card := by exact_mod_cast gaps_card_pos p
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hs
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hre),
    (sub_eq_zero.mp ((mul_eq_zero.mp him.symm).resolve_left hc.ne')).symm⟩

/-- The four-copy product bound for a Hermitian second factor with at
most one positive eigenvalue and nonnegative diagonal in the spectral basis. -/
theorem diagonal_word_bound_of_posIndex {n : ℕ} {s : Type*}
    [Finite s] (p : ℕ) (label : Fin n → s)
    (x : s → ℝ) (hx : ∀ i, 0 ≤ x i) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsHermitian) (hIndex : RHLinalg.posIndex hB ≤ 1) (hDiag : ∀ i, 0 ≤ B i i) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B :=
  diagonal_word_bound_of_signed_minors p label x hx B
    (fun I hI _ ↦ signed_principal_minors_nonneg_of_posIndex hB hIndex hDiag I hI)

end
end RefinedBMV.Tracial
