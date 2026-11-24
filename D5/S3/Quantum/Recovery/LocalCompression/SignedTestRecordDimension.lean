/- GID: D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound finite-environment label loss using the reconstruction error of signed tests. -/

import D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
import D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel

/-!
# Signed tests for finite quantum record dimension

The sign-leakage identity is the finite Kraus form of Kuroiwa, Chapter 4,
Lemma 4.6, equations (4.23)–(4.24). The dimension estimate compares
this exact quadratic form with the loss of an auxiliary label experiment
and uses the weighted spectral packing optimum for the encoder.
-/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder CStarAlgebra

namespace D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension

open _root_.Matrix RHLinalg
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_neg)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Measurement.Auric.DiamondBounds (twice_effect_trace_le_traceNorm)
open D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage (positiveSpectralProjection)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
  (slice reducedColumn trace_mul_reducedColumn)
open D5.S3.Quantum.Measurements.WeightedLabelRecordDilation

variable {B J I L κ : Type*} [Fintype B] [DecidableEq B]
  [Fintype J] [DecidableEq J] [Fintype I] [Fintype L] [Fintype κ]

private theorem kraus_apply {A C : Type*} [Fintype A]
    (K : κ → Matrix C A ℂ) (X : Matrix A A ℂ) :
    MatrixMap.of_kraus K K X = ∑ a, K a * X * (K a)ᴴ := by
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply]

/-- The two real trace pairings for sign leakage, using the full Jordan parts. -/
def signLeakage {H : Matrix B B ℂ} (hH : H.IsHermitian) (X : Matrix B B ℂ) : ℝ :=
  let P := positiveSpectralProjection hH
  ((1 - P) * (X * hermPosPart hH * Xᴴ)).trace.re +
    (P * (X * hermNegPart hH * Xᴴ)).trace.re

/-- The exact total sign leakage of a trace-preserving Kraus map, including singular tests. -/
theorem sum_signLeakage_eq (K : κ → Matrix B B ℂ)
    (hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix B B ℂ} (hH : H.IsHermitian) :
    ∑ a, signLeakage hH (K a) =
      (positiveSpectralProjection hH * (H - MatrixMap.of_kraus K K H)).trace.re := by
  let P := positiveSpectralProjection hH
  let T := MatrixMap.of_kraus K K
  let A := hermPosPart hH
  let N := hermNegPart hH
  have hPA : P * A = A := by
    change specMap hH _ * specMap hH _ = specMap hH _
    rw [← specMap_mul]
    congr 1
    funext x
    by_cases hx : 0 < x
    · simp [Pi.mul_apply, hx]
    · simp [Pi.mul_apply, hx, posPart_eq_zero.mpr (le_of_not_gt hx)]
  have hPN : P * N = 0 := by
    change specMap hH _ * specMap hH _ = 0
    rw [← specMap_mul, ← specMap_zero hH]
    congr 1
    funext x
    by_cases hx : 0 < x
    · simp [Pi.mul_apply, hx, hx.le]
    · simp [Pi.mul_apply, hx]
  have hsplit : A - N = H := hermPosPart_sub_hermNegPart hH
  calc
    ∑ a, signLeakage hH (K a) =
        ((1 - P) * T A).trace.re + (P * T N).trace.re := by
      simp only [T, kraus_apply, signLeakage, P, A, N,
        Matrix.mul_sum, trace_sum, Complex.re_sum, Finset.sum_add_distrib]
    _ = (P * (H - T H)).trace.re := by
      rw [← hsplit]
      simp only [map_sub, Matrix.mul_sub, hPA, hPN, sub_zero, trace_sub, Complex.sub_re]
      rw [show (1 - P) * T A = T A - P * T A by simp [Matrix.sub_mul],
        trace_sub, Complex.sub_re, hT A]
      ring

private theorem signLeakage_bound (K : κ → Matrix B B ℂ)
    (hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix B B ℂ} (hH : H.IsHermitian) :
    ∑ a, signLeakage hH (K a) ≤ traceNorm (H - MatrixMap.of_kraus K K H) / 2 := by
  let P := positiveSpectralProjection hH
  let T := MatrixMap.of_kraus K K
  have hP : P.PosSemidef := specMap_posSemidef hH (by intro i; split_ifs <;> norm_num)
  have hQ : (1 - P).PosSemidef := by
    have h1 : specMap hH 1 = 1 := by simp [specMap]
    rw [← h1, show P = specMap hH (fun x => if 0 < x then 1 else 0) from rfl,
      ← specMap_sub]
    apply specMap_posSemidef
    intro i
    simp only [Pi.sub_apply, Pi.one_apply]
    split_ifs <;> norm_num
  have htrace : (H - T H).trace = 0 := by rw [trace_sub, hT H, sub_self]
  have hHerm : (H - T H).IsHermitian := hH.sub (by
    rw [show T H = ∑ a, K a * H * (K a)ᴴ from kraus_apply K H]
    unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, mul_assoc])
  rw [sum_signLeakage_eq K hT hH]
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
    rw [mul_comm]
    exact twice_effect_trace_le_traceNorm _ P hHerm htrace hP hQ)

omit [Fintype I] [DecidableEq B] in
private theorem traceNorm_signed_sum (s : Finset I) (c : I → ℝ) (X : I → Matrix B B ℂ) :
    traceNorm (∑ i ∈ s, (c i : ℂ) • X i) ≤ ∑ i ∈ s, |c i| * traceNorm (X i) := by
  classical
  have hscale (i : I) : traceNorm ((c i : ℂ) • X i) = |c i| * traceNorm (X i) := by
    by_cases hi : 0 ≤ c i
    · rw [abs_of_nonneg hi, traceNorm_smul_nonneg _ _ hi]
    · rw [abs_of_neg (lt_of_not_ge hi), ← traceNorm_smul_nonneg _ _ (by linarith),
        Complex.ofReal_neg, neg_smul, traceNorm_neg]
  induction s using Finset.induction_on with
  | empty => simp [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le _ _).trans
      (add_le_add (hscale i).le hs)

/-- The diagonal projection onto the coordinates carrying a given label. -/
def labelProjection (label : B → J) (j : J) : Matrix B B ℂ :=
  diagonal fun b => if label b = j then 1 else 0

/-- The auxiliary label state in an adapted basis, with possible zero eigenvalues. -/
def labelDensity (label : B → J) (mass : B → ℝ) (j : J) : Matrix B B ℂ :=
  diagonal fun b => if label b = j then (mass b : ℂ) else 0

/-- Total density-weighted leakage out of the auxiliary label subspaces. -/
def labelLeakage (label : B → J) (mass : B → ℝ) (X : Matrix B B ℂ) : ℝ :=
  ∑ j, ((1 - labelProjection label j) * (X * labelDensity label mass j * Xᴴ)).trace.re

variable {d e : ℕ}

/-- Encoder Kraus matrices obtained by fixing the environment coordinate of the isometry. -/
def encoderSlice (V : Matrix (Fin d × Fin e) B ℂ) (t : Fin e) : Matrix (Fin d) B ℂ :=
  fun m b => slice V b t m

/-- Kraus matrices of the common decoder following the isometric encoder and environment trace. -/
def recordKraus (V : Matrix (Fin d × Fin e) B ℂ) (decoder : QuantumChannel (Fin d) B)
    (a : (Fin (Fintype.card B) × Fin (Fintype.card (Fin d))) × Fin e) : Matrix B B ℂ :=
  (actual_kraus_representation decoder).kraus a.1 * encoderSlice V a.2

omit [Fintype B] in
private theorem encoder_complete (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) :
    ∑ t, (encoderSlice V t)ᴴ * encoderSlice V t = 1 := by
  rw [← hV]
  ext b c
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, encoderSlice,
    slice, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

private theorem record_tp (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (decoder : QuantumChannel (Fin d) B) :
    (MatrixMap.of_kraus (recordKraus V decoder) (recordKraus V decoder)).IsTracePreserving := by
  let R := actual_kraus_representation decoder
  apply MatrixMap.IsTracePreserving.of_kraus_isTracePreserving
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl (fun t _ => ?_)) (encoder_complete V hV)
  calc
    ∑ a, (recordKraus V decoder (a, t))ᴴ * recordKraus V decoder (a, t) =
        (encoderSlice V t)ᴴ * (∑ a, (R.kraus a)ᴴ * R.kraus a) * encoderSlice V t := by
      simp only [recordKraus, conjTranspose_mul, Matrix.sum_mul, Matrix.mul_sum,
        Matrix.mul_assoc]
      rfl
    _ = _ := by rw [R.hkraus, Matrix.mul_one]

/-- The memory POVM obtained by pulling the auxiliary basis labels back through the decoder. -/
def decoderEffect (label : B → J) (decoder : QuantumChannel (Fin d) B) (j : J) :
    Matrix (Fin d) (Fin d) ℂ :=
  krausAdjoint (actual_kraus_representation decoder).kraus (labelProjection label j)

omit [Fintype J] in
private theorem effects_pos (label : B → J) (decoder : QuantumChannel (Fin d) B) (j : J) :
    (decoderEffect label decoder j).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k _
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  apply Matrix.PosSemidef.diagonal
  intro b
  change 0 ≤ (if label b = j then (1 : ℂ) else 0)
  split_ifs <;> simp

private theorem effects_complete (label : B → J) (decoder : QuantumChannel (Fin d) B) :
    ∑ j, decoderEffect label decoder j = 1 := by
  have hQ : ∑ j, labelProjection label j = 1 := by
    ext b c
    by_cases h : b = c
    · subst c
      simp [labelProjection, Matrix.sum_apply]
    · simp [labelProjection, Matrix.sum_apply, diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  unfold decoderEffect krausAdjoint
  rw [Finset.sum_comm]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum, hQ, Matrix.mul_one]
  exact (actual_kraus_representation decoder).hkraus

omit [DecidableEq B] in
private theorem label_mass_total (label : B → J) (mass : B → ℝ)
    (hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1) :
    ∑ b, mass b = (Fintype.card J : ℝ) := by
  calc
    ∑ b, mass b = ∑ b, ∑ j, (if label b = j then mass b else 0) := by simp
    _ = _ := by rw [Finset.sum_comm]; simp [hmass]

omit [Fintype J] in
private theorem density_trace (label : B → J) (mass : B → ℝ)
    (hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1) (j : J) :
    (labelDensity label mass j).trace = 1 := by
  rw [labelDensity, trace_diagonal]
  simpa only [Complex.ofReal_sum, Complex.ofReal_one, apply_ite, Complex.ofReal_zero]
    using congrArg Complex.ofReal (hmass j)

private theorem encode_density_pair (V : Matrix (Fin d × Fin e) B ℂ) (q : B → ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    (M * MatrixMap.of_kraus (encoderSlice V) (encoderSlice V) (diagonal q)).trace =
      ∑ b, q b * (M * reducedColumn V b).trace := by
  rw [kraus_apply]
  simp only [trace_sum, trace_mul_reducedColumn, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset B))]
  apply Finset.sum_congr rfl
  intro t _
  let A := encoderSlice V t
  change (M * (A * diagonal q * Aᴴ)).trace = _
  rw [← Matrix.mul_assoc M (A * diagonal q) Aᴴ, ← Matrix.mul_assoc M A (diagonal q),
    trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]
  rfl

private theorem record_apply (V : Matrix (Fin d × Fin e) B ℂ)
    (decoder : QuantumChannel (Fin d) B) (Y : Matrix B B ℂ) :
    MatrixMap.of_kraus (recordKraus V decoder) (recordKraus V decoder) Y =
      CStarMatrix.ofMatrix.symm (decoder.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (MatrixMap.of_kraus (encoderSlice V) (encoderSlice V) Y))) := by
  rw [(actual_kraus_representation decoder).haction]
  simp only [kraus_apply, Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    recordKraus, conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype J] in
private theorem compression_pair (label : B → J) (V : Matrix (Fin d × Fin e) B ℂ)
    (decoder : QuantumChannel (Fin d) B) (Y : Matrix B B ℂ) (j : J) :
    (labelProjection label j *
      MatrixMap.of_kraus (recordKraus V decoder) (recordKraus V decoder) Y).trace =
    (decoderEffect label decoder j *
      MatrixMap.of_kraus (encoderSlice V) (encoderSlice V) Y).trace := by
  rw [trace_mul_comm (labelProjection label j), trace_mul_comm (decoderEffect label decoder j),
    decoderEffect, actual_kraus_trace_pair, record_apply]

private theorem label_loss_sub_score (label : B → J) (mass : B → ℝ)
    (hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (decoder : QuantumChannel (Fin d) B) :
    ∑ a, labelLeakage label mass (recordKraus V decoder a) =
      (Fintype.card J : ℝ) - ∑ j, (decoderEffect label decoder j *
        MatrixMap.of_kraus (encoderSlice V) (encoderSlice V)
          (labelDensity label mass j)).trace.re := by
  let T := MatrixMap.of_kraus (recordKraus V decoder) (recordKraus V decoder)
  have hT := record_tp V hV decoder
  calc
    _ = ∑ j, ((1 - labelProjection label j) * T (labelDensity label mass j)).trace.re := by
      simp only [labelLeakage, T, kraus_apply, Matrix.mul_sum, trace_sum, Complex.re_sum]
      exact Finset.sum_comm
    _ = ∑ j, (1 - (labelProjection label j * T (labelDensity label mass j)).trace.re) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re, hT (labelDensity label mass j),
        density_trace _ _ hmass, Complex.one_re]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        T, compression_pair]

private theorem total_correct_score (label : B → J) (mass : B → ℝ)
    (V : Matrix (Fin d × Fin e) B ℂ) (decoder : QuantumChannel (Fin d) B) :
    ∑ j, (decoderEffect label decoder j *
      MatrixMap.of_kraus (encoderSlice V) (encoderSlice V) (labelDensity label mass j)).trace.re =
    ∑ b, mass b * (decoderEffect label decoder (label b) * reducedColumn V b).trace.re := by
  simp_rw [labelDensity, encode_density_pair, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul, Complex.zero_re, zero_mul, Complex.re_ofReal_mul, apply_ite]
  simp

private theorem basis_card_le (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) :
    Fintype.card B ≤ d * e := by
  have hInjective : Function.Injective V.mulVecLin := by
    apply Function.LeftInverse.injective (g := Vᴴ.mulVecLin)
    intro x
    change Vᴴ *ᵥ (V *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  have h := LinearMap.finrank_le_finrank_of_injective hInjective
  simpa using h

/-- The composite Kraus loss equals the number of labels times the actual average failure. -/
theorem label_deficit_eq [Nonempty J] (label : B → J) (mass : B → ℝ)
    (hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (decoder : QuantumChannel (Fin d) B) :
    ∑ a, labelLeakage label mass (recordKraus V decoder a) =
      (Fintype.card J : ℝ) * (1 - averageSuccess label
        (fun b => mass b / Fintype.card J) V (decoderEffect label decoder)) := by
  have hr : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [label_loss_sub_score label mass hmass V hV decoder, total_correct_score]
  simp only [averageSuccess, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  field_simp

/-- The label loss is at least the number of labels minus the memory dimension. -/
theorem label_count_sub_memory_le_deficit (label : B → J) (mass : B → ℝ)
    (hmass₀ : ∀ b, 0 ≤ mass b) (hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (decoder : QuantumChannel (Fin d) B) :
    (Fintype.card J : ℝ) - d ≤ ∑ a, labelLeakage label mass (recordKraus V decoder a) := by
  let E := MatrixMap.of_kraus (encoderSlice V) (encoderSlice V)
  have hE := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving
    (encoderSlice V) (encoderSlice V) (encoder_complete V hV)
  rw [label_loss_sub_score label mass hmass V hV decoder]
  apply sub_le_sub_left
  calc
    _ ≤ ∑ j, (decoderEffect label decoder j).trace.re := by
      apply Finset.sum_le_sum
      intro j _
      let A := E (labelDensity label mass j)
      have hA : A.PosSemidef := by
        change (E (labelDensity label mass j)).PosSemidef
        simp only [E, kraus_apply]
        apply Matrix.posSemidef_sum
        intro t _
        apply Matrix.PosSemidef.mul_mul_conjTranspose_same
        apply Matrix.PosSemidef.diagonal
        intro b
        change 0 ≤ (if label b = j then (mass b : ℂ) else 0)
        split_ifs
        · exact Complex.nonneg_iff.mpr ⟨hmass₀ b, rfl⟩
        · exact le_rfl
      have htr : A.trace = 1 := (hE _).trans (density_trace label mass hmass j)
      let H : HermitianMat (Fin d) ℂ := ⟨A, hA.isHermitian⟩
      have hle := HermitianMat.le_trace_smul_one (HermitianMat.zero_le_iff.mpr hA : 0 ≤ H)
      change A ≤ A.trace.re • (1 : Matrix (Fin d) (Fin d) ℂ) at hle
      rw [htr, Complex.one_re, one_smul] at hle
      have h := trace_mul_nonneg_of_posSemidef (effects_pos label decoder j)
        (Matrix.le_iff.mp hle)
      change 0 ≤ (decoderEffect label decoder j * (1 - A)).trace.re at h
      simpa only [Matrix.mul_sub, Matrix.mul_one, trace_sub, Complex.sub_re, sub_nonneg] using h
    _ = d := by
      rw [← Complex.re_sum, ← trace_sum, effects_complete, trace_one]
      simp

/-- The plain matrix of an input density state. -/
def preparation (ρ : I → DensityState B) (i : I) : Matrix B B ℂ :=
  CStarMatrix.ofMatrix.symm (ρ i).1

/-- A test formed by a real signed linear combination of input states. -/
def signedTest (ρ : I → DensityState B) (c : I → ℝ) : Matrix B B ℂ :=
  ∑ i, (c i : ℂ) • preparation ρ i

private theorem signedTest_hermitian (ρ : I → DensityState B) (c : I → ℝ) :
    (signedTest ρ c).IsHermitian := by
  unfold Matrix.IsHermitian signedTest
  rw [conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpos : (preparation ρ i).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (ρ i).nonnegative :
      0 ≤ preparation ρ i).posSemidef
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hpos.isHermitian.eq]

/-- Full sign leakage for the test with the specified real coefficients. -/
def signedTestLeakage (ρ : I → DensityState B) (c : I → ℝ) (X : Matrix B B ℂ) : ℝ :=
  signLeakage (signedTest_hermitian ρ c) X

private theorem signed_budget (ρ : I → DensityState B) (c : I → ℝ)
    (T : MatrixMap B B ℂ) (δ : ℝ)
    (hδ : ∀ i, traceNorm (preparation ρ i - T (preparation ρ i)) ≤ δ) :
    traceNorm (signedTest ρ c - T (signedTest ρ c)) ≤ δ * ∑ i, |c i| := by
  simp only [signedTest, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  refine (traceNorm_signed_sum Finset.univ c _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)

/-- A finite signed-test certificate for the reconstruction error of an actual common decoder
and a full-input isometry into memory times a positive-dimensional pure environment. -/
theorem signed_test_record_dimension [Nonempty J] (label : B → J) (mass : B → ℝ)
    (hmass₀ : ∀ b, 0 ≤ mass b) (hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) (he : 0 < e)
    (decoder : QuantumChannel (Fin d) B) (ρ : I → DensityState B) (c : L → I → ℝ)
    (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (hdom : ∀ X : Matrix B B ℂ, labelLeakage label mass X ≤
      ∑ l, w l * signedTestLeakage ρ (c l) X)
    (δ : ℝ) (hδ : ∀ i, traceNorm (preparation ρ i -
      CStarMatrix.ofMatrix.symm (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix
        (MatrixMap.of_kraus (encoderSlice V) (encoderSlice V) (preparation ρ i))))) ≤ δ) :
    (Fintype.card J : ℝ) * (1 - optimalSuccess label (fun b => mass b / Fintype.card J)
      (basis_card_le V hV)) ≤ δ * ∑ l, w l * ((∑ i, |c l i|) / 2) := by
  let r : ℝ := Fintype.card J
  let p : B → ℝ := fun b => mass b / r
  let K := recordKraus V decoder
  let T := MatrixMap.of_kraus K K
  have hr : 0 < r := Nat.cast_pos.mpr (Fintype.card_pos (α := J))
  have hp : ∀ b, 0 ≤ p b := fun b => div_nonneg (hmass₀ b) hr.le
  have hpSum : ∑ b, p b = 1 := by
    simp only [p, ← Finset.sum_div, label_mass_total label mass hmass, r, div_self hr.ne']
  have herror (i : I) : traceNorm (preparation ρ i - T (preparation ρ i)) ≤ δ := by
    simpa only [T, K, record_apply] using hδ i
  have hscore := (weightedLabelRecord_optimum label p hp hpSum he (basis_card_le V hV)).1
    V (decoderEffect label decoder) hV (effects_pos label decoder) (effects_complete label decoder)
  calc
    r * (1 - optimalSuccess label p (basis_card_le V hV)) ≤
        r * (1 - averageSuccess label p V (decoderEffect label decoder)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hscore _) hr.le
    _ = ∑ a, labelLeakage label mass (K a) := (label_deficit_eq label mass hmass V hV decoder).symm
    _ ≤ ∑ a, ∑ l, w l * signedTestLeakage ρ (c l) (K a) :=
      Finset.sum_le_sum fun a _ => hdom (K a)
    _ ≤ δ * ∑ l, w l * ((∑ i, |c l i|) / 2) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      calc
        _ = ∑ l, w l * ∑ a, signLeakage (signedTest_hermitian ρ (c l)) (K a) :=
          Finset.sum_congr rfl fun l _ => (Finset.mul_sum ..).symm
        _ ≤ _ := ?_
      apply Finset.sum_le_sum
      intro l _
      rw [mul_left_comm δ]
      apply mul_le_mul_of_nonneg_left _ (hw l)
      have h := (signLeakage_bound K (record_tp V hV decoder)
        (signedTest_hermitian ρ (c l))).trans
        (div_le_div_of_nonneg_right (signed_budget ρ (c l) T δ herror) (by norm_num))
      simpa only [mul_div_assoc, signedTestLeakage] using h

#print axioms signed_test_record_dimension

end D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
