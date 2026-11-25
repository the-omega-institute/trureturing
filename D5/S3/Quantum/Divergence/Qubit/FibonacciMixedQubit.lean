/- GID: D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Fibonacci benchmark deficit for arbitrary mixed qubit preparations. -/

import D5.S3.Quantum.Divergence.FannesRootFidelityHolevo
import D5.S3.Quantum.Divergence.SupportedTraceLog
import D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile
import D5.S3.Quantum.Divergence.Qubit.SignedProfile
import D5.S3.Quantum.Recovery.PetzSpectralCoordinates

/-! The mixed Fibonacci qubit bound by independent spectral averaging. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit

open FannesRootFidelityHolevo.LogSum (relativeEntropy)
open SignedProfile (contrast overlap)
open SignedProfile.Pairing (trace_pair)
open FibonacciClippedProfile.Benchmark (inputWeights referenceWeights C3)
open SupportedTraceLog (traceLog_jointConvex)

private abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

private abbrev traceLog (A C : Qubit) : ℝ :=
  (A * (CFC.log A - CFC.log C)).trace.re

private abbrev weightedMix (a : Fin 3 → ℝ) (X : Fin 3 → Qubit) : Qubit :=
  ∑ i, a i • X i

private theorem weightedMix_nonneg (a : Fin 3 → ℝ) (X : Fin 3 → Qubit)
    (ha : ∀ i, 0 ≤ a i) (hX : ∀ i, (X i).PosSemidef) : 0 ≤ weightedMix a X :=
  Finset.sum_nonneg fun i _ => smul_nonneg (ha i) (hX i).nonneg

private theorem weightedMix_sub_smul (a b : Fin 3 → ℝ) (X : Fin 3 → Qubit) (r : ℝ) :
    weightedMix a X - r • weightedMix b X =
      weightedMix (fun i => a i - r * b i) X := by
  simp only [weightedMix, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]

private theorem fibonacci_properties (X : Fin 3 → Qubit) (hX : ∀ i, (X i).PosSemidef) :
    (weightedMix inputWeights X).PosSemidef ∧ (weightedMix referenceWeights X).PosSemidef ∧
      weightedMix inputWeights X ≤ (7 / 3 : ℝ) • weightedMix referenceWeights X := by
  refine ⟨(weightedMix_nonneg _ _ ?_ hX).posSemidef, (weightedMix_nonneg _ _ ?_ hX).posSemidef,
    ?_⟩
  · intro i
    fin_cases i <;> norm_num [inputWeights]
  · intro i
    fin_cases i <;> norm_num [referenceWeights]
  · apply sub_nonneg.mp
    rw [← neg_sub, weightedMix_sub_smul]
    simpa only [weightedMix, Finset.sum_neg_distrib, neg_smul] using
      (weightedMix_nonneg (fun i => -(inputWeights i - (7 / 3 : ℝ) * referenceWeights i))
        X (by intro i; fin_cases i <;> norm_num [inputWeights, referenceWeights]) hX)

private theorem spectral_qubit (X : Qubit) (hX : X.PosSemidef) (ht : X.trace = 1) :
    ∃ (l : Fin 2 → ℝ) (v : Fin 2 → Fin 2 → ℂ),
      (∀ k, 0 ≤ l k) ∧ (∑ k, l k) = 1 ∧
      (∀ k, star (v k) ⬝ᵥ v k = 1) ∧
      (∑ k, l k • Matrix.vecMulVec (v k) (star (v k))) = X := by
  let hH := hX.isHermitian
  let l := hH.eigenvalues
  let v : Fin 2 → Fin 2 → ℂ := fun k i => hH.eigenvectorBasis k i
  refine ⟨l, v, hX.eigenvalues_nonneg, ?_, ?_, ?_⟩
  · have h : (∑ i, (hH.eigenvalues i : ℂ)) = 1 :=
      hH.trace_eq_sum_eigenvalues.symm.trans ht
    simpa only [Complex.one_re, Complex.re_sum, Complex.ofReal_re, l] using congrArg Complex.re h
  · intro k
    rw [dotProduct_comm]
    simpa only [v, EuclideanSpace.inner_eq_star_dotProduct] using
      hH.eigenvectorBasis.inner_eq_one k
  · have h := D5.S3.Quantum.Recovery.PetzSpectralCoordinates.cfc_spectral_sum
      X hH (fun t : ℝ => t)
    rw [cfc_id' ℝ X hH.isSelfAdjoint] at h
    apply Matrix.ext
    intro i j
    have hij := congrArg (fun Y : Qubit => Y i j) h.symm
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.real_smul, smul_eq_mul, l, v] using hij

private abbrev Choice := Fin 2 × Fin 2 × Fin 2

private def chosenIndex (k : Choice) : Fin 3 → Fin 2 := ![k.1, k.2.1, k.2.2]

private def productWeight (l : Fin 3 → Fin 2 → ℝ) (k : Choice) : ℝ :=
  l 0 k.1 * l 1 k.2.1 * l 2 k.2.2

private theorem sum_product_smul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (l : Fin 3 → Fin 2 → ℝ) (F : Fin 2 → Fin 2 → Fin 2 → E) :
    (∑ k : Choice, productWeight l k • F k.1 k.2.1 k.2.2) =
      ∑ i, l 0 i • ∑ j, l 1 j • ∑ k, l 2 k • F i j k := by
  simp only [Fintype.sum_prod_type, productWeight, mul_smul, Finset.smul_sum]

private theorem sum_const_smul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (l : Fin 3 → Fin 2 → ℝ) (hl : ∀ i, ∑ k, l i k = 1) (i : Fin 3) (z : E) :
    (∑ k, l i k • z) = z := by
  rw [← Finset.sum_smul, hl i, one_smul]

private theorem sum_product_marginal {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (l : Fin 3 → Fin 2 → ℝ) (hl : ∀ i, ∑ k, l i k = 1) (i : Fin 3) (f : Fin 2 → E) :
    (∑ k : Choice, productWeight l k • f (chosenIndex k i)) = ∑ j, l i j • f j := by
  fin_cases i
  · change (∑ k : Choice, productWeight l k • f k.1) = ∑ j, l 0 j • f j
    rw [sum_product_smul l (fun x _ _ => f x)]
    simp only [sum_const_smul l hl]
  · change (∑ k : Choice, productWeight l k • f k.2.1) = ∑ j, l 1 j • f j
    rw [sum_product_smul l (fun _ y _ => f y)]
    simp only [sum_const_smul l hl]
  · change (∑ k : Choice, productWeight l k • f k.2.2) = ∑ j, l 2 j • f j
    rw [sum_product_smul l (fun _ _ z => f z)]
    simp only [sum_const_smul l hl]

private theorem average_trace_pair (a b : Fin 2 → ℝ) (P Q : Fin 2 → Qubit) :
    ((∑ i, a i • P i) * (∑ j, b j • Q j)).trace.re =
      ∑ i, a i * ∑ j, b j * (P i * Q j).trace.re := by
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]

private theorem rankOne_trace_overlap (v : Fin 3 → Fin 2 → ℂ) (i j : Fin 3) :
    (Matrix.vecMulVec (v i) (star (v i)) * Matrix.vecMulVec (v j) (star (v j))).trace.re =
      overlap v i j := by
  simpa only [overlap, Complex.ofReal_re] using congrArg Complex.re (trace_pair (v i) (v j))

/-- The exact Fibonacci benchmark gap for arbitrary mixed qubit preparations. -/
theorem traceLog_le_benchmark_sub_margin (X : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hX : ∀ i, (X i).PosSemidef) (htrace : ∀ i, (X i).trace = 1) :
    let A := ∑ i, (![88 / 141, 25 / 141, 28 / 141] : Fin 3 → ℝ) i • X i
    let C := ∑ i, (![66 / 141, 15 / 141, 12 / 141] : Fin 3 → ℝ) i • X i
    (A * (CFC.log A - CFC.log C)).trace.re ≤
      ((113 / 141 : ℝ) * Real.log (113 / 81) + (28 / 141) * Real.log (7 / 3)) -
        (3 * (1 - (X 0 * X 1).trace.re) + 11 * (X 0 * X 2).trace.re) / 63360 := by
  classical
  choose l v hl hn hu hspec using fun i => spectral_qubit (X i) (hX i) (htrace i)
  let P : Fin 3 → Fin 2 → Qubit := fun i j => Matrix.vecMulVec (v i j) (star (v i j))
  let ψ : Choice → Fin 3 → Fin 2 → ℂ := fun k i => v i (chosenIndex k i)
  let w : Choice → ℝ := productWeight l
  let A : Choice → Qubit := contrast inputWeights ∘ ψ
  let C : Choice → Qubit := contrast referenceWeights ∘ ψ
  -- Independent spectral choices carry the product of the three eigenvalues.
  have hw (k : Choice) : 0 ≤ w k := mul_nonneg
    (mul_nonneg (hl 0 k.1) (hl 1 k.2.1)) (hl 2 k.2.2)
  have hwSum : ∑ k, w k = 1 := by
    have h : (∑ k : Choice, productWeight l k • (1 : ℝ)) = 1 := by
      rw [sum_product_smul l (fun _ _ _ => (1 : ℝ))]
      simp only [sum_const_smul l hn]
    simpa only [w, smul_eq_mul, mul_one] using h
  have hP (k : Choice) (i : Fin 3) : (P i (chosenIndex k i)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  have hψ (k : Choice) (i : Fin 3) : star (ψ k i) ⬝ᵥ ψ k i = 1 :=
    hu i (chosenIndex k i)
  have hpair (k : Choice) := fibonacci_properties (fun i => P i (chosenIndex k i)) (hP k)
  have hA (k : Choice) : (A k).PosSemidef := (hpair k).1
  have hC (k : Choice) : (C k).PosSemidef := (hpair k).2.1
  have hsupport (k : Choice) (x : Fin 2 → ℂ) (hx : C k *ᵥ x = 0) : A k *ᵥ x = 0 := by
    apply FannesRootFidelityHolevo.supported_of_le (hA k) (hpair k).2.2 x
    change ((7 / 3 : ℝ) • C k) *ᵥ x = 0
    rw [Matrix.smul_mulVec, hx, smul_zero]
  -- Each one-coordinate marginal reconstructs the corresponding preparation.
  have hmarginal (a : Fin 3 → ℝ) :
      (∑ k, w k • contrast a (ψ k)) = weightedMix a X := by
    change (∑ k : Choice, w k • ∑ i, a i • P i (chosenIndex k i)) =
      ∑ i, a i • X i
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc
      (∑ k, w k • a i • P i (chosenIndex k i)) =
          ∑ k, a i • w k • P i (chosenIndex k i) :=
        Finset.sum_congr rfl fun k _ => smul_comm (w k) (a i) _
      _ = a i • X i := by
        rw [← Finset.smul_sum]
        change a i • (∑ k, productWeight l k • P i (chosenIndex k i)) = _
        rw [sum_product_marginal l hn i (P i)]
        exact congrArg (fun Y : Qubit => a i • Y) (hspec i)
  have hmixA : (∑ k, w k • A k) = weightedMix inputWeights X := hmarginal inputWeights
  have hmixC : (∑ k, w k • C k) = weightedMix referenceWeights X := hmarginal referenceWeights
  have hj := traceLog_jointConvex w A C hw hA hC hsupport
  dsimp only at hj
  rw [hmixA, hmixC] at hj
  -- The trace pairings use the two-coordinate marginals.
  have h01 :
      (∑ k, w k * overlap (ψ k) 0 1) = (X 0 * X 1).trace.re := by
    simp_rw [← rankOne_trace_overlap]
    change (∑ k : Choice, productWeight l k • (P 0 k.1 * P 1 k.2.1).trace.re) = _
    rw [sum_product_smul l (fun i j _ => (P 0 i * P 1 j).trace.re)]
    simp only [sum_const_smul l hn]
    rw [← hspec 0, ← hspec 1]
    simpa only [smul_eq_mul] using (average_trace_pair (l 0) (l 1) (P 0) (P 1)).symm
  have h02 :
      (∑ k, w k * overlap (ψ k) 0 2) = (X 0 * X 2).trace.re := by
    simp_rw [← rankOne_trace_overlap]
    change (∑ k : Choice, productWeight l k • (P 0 k.1 * P 2 k.2.2).trace.re) = _
    rw [sum_product_smul l (fun i _ k => (P 0 i * P 2 k).trace.re)]
    simp only [sum_const_smul l hn]
    rw [← hspec 0, ← hspec 2]
    simpa only [smul_eq_mul] using (average_trace_pair (l 0) (l 2) (P 0) (P 2)).symm
  have hdeficit :
      (∑ k, w k * (1 - overlap (ψ k) 0 1)) = 1 - (X 0 * X 1).trace.re := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hwSum, h01]
  have hpure (k : Choice) :
      relativeEntropy (A k) (C k) ≤ C3 -
        (3 * (1 - overlap (ψ k) 0 1) + 11 * overlap (ψ k) 0 2) / 63360 := by
    simpa only [relativeEntropy, C3, A, C, Function.comp_apply, inputWeights, referenceWeights]
      using FibonacciClippedProfile.traceLog_le_benchmark_sub_margin (ψ k) (hψ k)
  change traceLog (weightedMix inputWeights X) (weightedMix referenceWeights X) ≤ _
  calc
    _ ≤ ∑ k, w k * relativeEntropy (A k) (C k) := hj
    _ ≤ ∑ k, w k * (C3 -
        (3 * (1 - overlap (ψ k) 0 1) + 11 * overlap (ψ k) 0 2) / 63360) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hpure k) (hw k)
    _ = _ := by
      calc
        _ = ∑ k, (w k * C3 -
            (3 * (w k * (1 - overlap (ψ k) 0 1)) + 11 * (w k * overlap (ψ k) 0 2)) /
              63360) := Finset.sum_congr rfl fun k _ => by ring
        _ = (∑ k, w k) * C3 -
            (3 * (∑ k, w k * (1 - overlap (ψ k) 0 1)) +
              11 * (∑ k, w k * overlap (ψ k) 0 2)) / 63360 := by
          simp only [div_eq_mul_inv, Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_mul, Finset.mul_sum, add_mul]
        _ = _ := by rw [hwSum, one_mul, hdeficit, h02]

end D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit
