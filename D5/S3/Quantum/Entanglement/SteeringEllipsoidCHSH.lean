/- GID: D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SteeringEllipsoidCHSH
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: CHSH nonlocality is sharply bounded by the steering-ellipsoid centre. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Information.ActualPureQubitCostInfimum
import D5.S3.Quantum.Information.ActualQubitChordObstruction
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen centre canonical_bound canonical_trace canonical_filter
    vlen_eq_norm blochVec blochVec_eq_bloch trace_mul_kron_one trace_mul_one_kron
    kron_sub vlen_e3 ev)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin sigma)
open D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit

open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation (pauli_hermitian)
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (trace_hermitian_product_real)

namespace D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

def bell (a a' b b' : Fin 3 → ℝ) : TwoQubit := spin a ⊗ₖ spin (b + b') + spin a' ⊗ₖ spin (b - b')
def chshValues (ρ : TwoQubit) : Set ℝ :=
  {r | ∃ a a' b b' : Fin 3 → ℝ, vlen a = 1 ∧ vlen a' = 1 ∧ vlen b = 1 ∧ vlen b' = 1 ∧
     r = ‖Matrix.trace (ρ * bell a a' b b')‖}
noncomputable def chsh (ρ : TwoQubit) : ℝ := sSup (chshValues ρ)
def bound (t : ℝ) : ℝ := max (2 * Real.sqrt (2 * (1 - t))) 2
def claim : Prop :=
  (∀ ρ : TwoQubit, ρ.PosSemidef → Matrix.trace ρ = 1 → chsh ρ ≤ bound (vlen (centre ρ))) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ ρ : TwoQubit,
     ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ vlen (centre ρ) = t ∧ bound t - ε < chsh ρ)

private lemma sigma_succ (i : Fin 3) : sigma i.succ = pauli i := by
  fin_cases i <;> rfl

private lemma unit_coord (u : Fin 3 → ℝ) (hu : vlen u = 1) (i : Fin 3) : |u i| ≤ 1 := by
  simpa only [Real.norm_eq_abs, ← vlen_eq_norm, hu] using
    PiLp.norm_apply_le (WithLp.toLp 2 u) i

private lemma bell_trace_expansion (ρ : TwoQubit) (a a' b b' : Fin 3 → ℝ) :
    trace (ρ * bell a a' b b') = ∑ i, ∑ j,
      ((a i * (b j + b' j) + a' i * (b j - b' j) : ℝ) : ℂ) *
        trace (ρ * (pauli i ⊗ₖ pauli j)) := by
  simp only [bell.eq_def, spin, sigma_succ, Fin.sum_univ_three, add_kronecker, kronecker_add,
    smul_kronecker, kronecker_smul, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul,
    smul_eq_mul, Pi.add_apply, Pi.sub_apply, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul]
  ring

private lemma chshValues_nonempty (ρ : TwoQubit) : (chshValues ρ).Nonempty := by
  rw [chshValues.eq_def]
  refine ⟨_, ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ?_, ?_, ?_, ?_, rfl⟩ <;>
    norm_num [vlen, Fin.sum_univ_succ]

private lemma chshValues_bddAbove (ρ : TwoQubit) : BddAbove (chshValues ρ) := by
  refine ⟨4 * ∑ i, ∑ j, ‖trace (ρ * (pauli i ⊗ₖ pauli j))‖, ?_⟩
  rintro r ⟨a, a', b, b', ha, ha', hb, hb', rfl⟩
  rw [bell_trace_expansion]
  calc
    ‖∑ i, ∑ j, ((a i * (b j + b' j) + a' i * (b j - b' j) : ℝ) : ℂ) *
        trace (ρ * (pauli i ⊗ₖ pauli j))‖
      ≤ ∑ i, ∑ j, ‖((a i * (b j + b' j) + a' i * (b j - b' j) : ℝ) : ℂ) *
          trace (ρ * (pauli i ⊗ₖ pauli j))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, 4 * ‖trace (ρ * (pauli i ⊗ₖ pauli j))‖ := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        |a i * (b j + b' j) + a' i * (b j - b' j)|
          ≤ |a i| * (|b j| + |b' j|) + |a' i| * (|b j| + |b' j|) := by
            calc
              _ ≤ |a i * (b j + b' j)| + |a' i * (b j - b' j)| := abs_add_le _ _
              _ ≤ |a i| * (|b j| + |b' j|) + |a' i| * (|b j| + |b' j|) := by
                rw [abs_mul, abs_mul]
                exact add_le_add
                  (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left
                    (by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (b j) (-b' j))
                    (abs_nonneg _))
        _ ≤ 1 * (1 + 1) + 1 * (1 + 1) := by
          gcongr <;> first | exact unit_coord a ha i | exact unit_coord a' ha' i |
            exact unit_coord b hb j | exact unit_coord b' hb' j
        _ = 4 := by norm_num
    _ = _ := by simp only [Finset.mul_sum]

private lemma setting_le_chsh (ρ : TwoQubit) (a a' b b' : Fin 3 → ℝ)
    (ha : vlen a = 1) (ha' : vlen a' = 1) (hb : vlen b = 1) (hb' : vlen b' = 1) :
    ‖trace (ρ * bell a a' b b')‖ ≤ chsh ρ :=
  le_csSup (chshValues_bddAbove ρ) ⟨a, a', b, b', ha, ha', hb, hb', rfl⟩

private def delta (X : TwoQubit) : ℝ :=
  (trace (X * X)).re - (trace (partialTraceRight X * partialTraceRight X)).re

private def filterBob (F : Matrix (Fin 2) (Fin 2) ℂ) (X : TwoQubit) : TwoQubit :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F) * X *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F)ᴴ

private lemma det_polarization (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (A * B) - trace A * trace B = det A + det B - det (A + B) := by
  simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two,
    Matrix.add_apply]
  ring

private lemma det_polarization_filter (A B F : Matrix (Fin 2) (Fin 2) ℂ) :
    trace ((F * A * Fᴴ) * (F * B * Fᴴ)) - trace (F * A * Fᴴ) * trace (F * B * Fᴴ) =
      (Complex.normSq (det F) : ℂ) * (trace (A * B) - trace A * trace B) := by
  rw [det_polarization, det_polarization,
    ← Matrix.add_mul, ← Matrix.mul_add]
  simp only [det_mul, det_conjTranspose]
  rw [← Complex.mul_conj (det F)]
  change det F * det A * star (det F) + det F * det B * star (det F) -
    det F * det (A + B) * star (det F) =
      (det F * star (det F)) * (det A + det B - det (A + B))
  ring

private def aliceBlock (X : TwoQubit) (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun k l => X (i, k) (j, l)

private lemma delta_filter (X : TwoQubit) (F : Matrix (Fin 2) (Fin 2) ℂ) :
    delta (filterBob F X) = Complex.normSq (det F) * delta X := by
  have hentry (i j : Fin 2) :
      aliceBlock (filterBob F X) i j = F * aliceBlock X i j * Fᴴ := by
    ext k l
    change (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F) * X *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F)ᴴ) (i, k) (j, l) = _
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      conjTranspose_apply, kronecker_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp <;> rfl
  have hblocks (Y : TwoQubit) :
      trace (Y * Y) - trace (partialTraceRight Y * partialTraceRight Y) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          (trace (aliceBlock Y i j * aliceBlock Y j i) -
            trace (aliceBlock Y i j) * trace (aliceBlock Y j i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, partialTraceRight, aliceBlock.eq_def]
    ring
  change (trace (filterBob F X * filterBob F X)).re -
    (trace (partialTraceRight (filterBob F X) * partialTraceRight (filterBob F X))).re =
      Complex.normSq (det F) *
        ((trace (X * X)).re - (trace (partialTraceRight X * partialTraceRight X)).re)
  rw [← Complex.sub_re, ← Complex.sub_re, hblocks, hblocks X]
  simp only [hentry, det_polarization_filter, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

private lemma sum_sq_le_two_mass {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (L : ℝ) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hcap : ∀ i, x i ≤ L) (hL₀ : 1 / 2 ≤ L) :
    ∑ i, x i ^ 2 ≤ L ^ 2 + (1 - L) ^ 2 := by
  classical
  by_cases hsmall : ∀ i, x i ≤ 1 / 2
  · calc
      ∑ i, x i ^ 2 ≤ ∑ i, (1 / 2 : ℝ) * x i :=
        Finset.sum_le_sum fun i _ => by nlinarith [mul_nonneg (hx i) (sub_nonneg.mpr (hsmall i))]
      _ = 1 / 2 := by rw [← Finset.mul_sum, hsum]; ring
      _ ≤ L ^ 2 + (1 - L) ^ 2 := by nlinarith [sq_nonneg (L - 1 / 2)]
  · push Not at hsmall
    obtain ⟨j, hj⟩ := hsmall
    have hrest : ∑ i ∈ Finset.univ.erase j, x i = 1 - x j := by
      have he := Finset.sum_erase_add (s := Finset.univ) x (Finset.mem_univ j)
      rw [hsum] at he
      linarith
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ.erase j) (fun i _ => hx i)
    rw [hrest] at hsq
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (fun i => x i ^ 2)
      (Finset.mem_univ j)
    nlinarith [mul_nonneg (sub_nonneg.mpr (hcap j))
      (show 0 ≤ L + x j - 1 by linarith)]

private lemma bloch_marginals (ρ : TwoQubit) (hρ : ρ.PosSemidef) :
    WithLp.toLp 2 (blochA ρ) =
        D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceRight ρ) ∧
      WithLp.toLp 2 (blochB ρ) =
        D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceLeft ρ) := by
  constructor
  · calc
      WithLp.toLp 2 (blochA ρ) = WithLp.toLp 2 (blochVec (partialTraceRight ρ)) := by
        congr 1; funext i; exact congrArg Complex.re (trace_mul_kron_one ρ (pauli i))
      _ = _ := blochVec_eq_bloch _ (partialTraceRight_posSemidef hρ).isHermitian
  · calc
      WithLp.toLp 2 (blochB ρ) = WithLp.toLp 2 (blochVec (partialTraceLeft ρ)) := by
        congr 1; funext i; exact congrArg Complex.re (trace_mul_one_kron ρ (pauli i))
      _ = _ := blochVec_eq_bloch _ (partialTraceLeft_posSemidef hρ).isHermitian

private lemma canonical_delta_le (σ : TwoQubit) (hσ : σ.PosSemidef)
    (hB : partialTraceLeft σ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    delta σ ≤ 1 / 2 - vlen (blochA σ) := by
  have htr : trace σ = 1 := canonical_trace σ hB
  have hread := (bloch_marginals σ hσ).1
  have hnorm : vlen (blochA σ) =
      ‖D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceRight σ)‖ := by
    rw [vlen_eq_norm, hread]
  have hc : vlen (blochA σ) ≤ 1 := by
    rw [hnorm]
    simpa only [trace_partialTraceRight, htr, Complex.one_re] using
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef
        (partialTraceRight σ) (partialTraceRight_posSemidef hσ)
  have hsum : ∑ i, hσ.isHermitian.eigenvalues i = 1 := by
    have ht := congrArg Complex.re htr
    rw [hσ.isHermitian.trace_eq_sum_eigenvalues] at ht
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re,
      Complex.one_re] using ht
  have hcap (i : Fin 2 × Fin 2) : hσ.isHermitian.eigenvalues i ≤ 1 - vlen (blochA σ) / 2 := by
    have hn : (star (⇑(hσ.isHermitian.eigenvectorBasis i)) ⬝ᵥ
        ⇑(hσ.isHermitian.eigenvectorBasis i)).re = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
      simp only [inner_self_eq_norm_sq_to_K, hσ.isHermitian.eigenvectorBasis.orthonormal.1 i,
        one_pow, RCLike.ofReal_one, Complex.one_re]
    rw [hσ.isHermitian.eigenvalues_eq]
    change (star (⇑(hσ.isHermitian.eigenvectorBasis i)) ⬝ᵥ
      (σ *ᵥ ⇑(hσ.isHermitian.eigenvectorBasis i))).re ≤ _
    simpa only [hn, mul_one] using
      canonical_bound σ hσ hB (⇑(hσ.isHermitian.eigenvectorBasis i))
  have hsq : (trace (σ * σ)).re = ∑ i, hσ.isHermitian.eigenvalues i ^ 2 := by
    have he := RHLinalg.frobSq_specMap hσ.isHermitian id
    rw [RHLinalg.specMap_id] at he
    change RCLike.re (trace (σᴴ * σ)) = ∑ i, hσ.isHermitian.eigenvalues i ^ 2 at he
    rw [RCLike.re_to_complex, hσ.isHermitian.eq] at he
    exact he
  have hpurA : (trace (partialTraceRight σ * partialTraceRight σ)).re =
      (1 + vlen (blochA σ) ^ 2) / 2 := by
    have he := D5.S3.Quantum.Information.ActualPureQubitCostInfimum.matrix_energy
      (partialTraceRight σ) (partialTraceRight_posSemidef hσ).isHermitian
    rw [trace_partialTraceRight, htr, Complex.one_re, ← hnorm] at he
    linarith
  have hmass := sum_sq_le_two_mass hσ.isHermitian.eigenvalues (1 - vlen (blochA σ) / 2)
    hσ.eigenvalues_nonneg hsum hcap (by linarith)
  change (trace (σ * σ)).re - (trace (partialTraceRight σ * partialTraceRight σ)).re ≤ _
  rw [hsq, hpurA]
  nlinarith

private def flipMatrix (n : Fin 3 → ℝ) : TwoQubit := pauli 1 ⊗ₖ (spin n * pauli 1)

private def flipped (X : TwoQubit) (n : Fin 3 → ℝ) : TwoQubit :=
  flipMatrix n * Xᵀ * (flipMatrix n)ᴴ

private lemma flip_purity_homogeneous (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (n : Fin 3 → ℝ) :
    2 * (trace (ρ * flipped ρ n)).re - vlen ((corr ρ) *ᵥ n) ^ 2 +
      (blochB ρ ⬝ᵥ n) ^ 2 =
      (∑ i, n i ^ 2) * ((trace ρ).re ^ 2 + 2 * delta ρ - ∑ i, ∑ j, corr ρ i j ^ 2) := by
  have hd (i : Fin 2 × Fin 2) : (ρ i i).im = 0 := by
    have he := congrArg Complex.im (hρ.apply i i)
    simp only [Complex.star_def, Complex.conj_im] at he
    linarith
  rw [vlen, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [flipped.eq_def, flipMatrix.eq_def, spin, sigma_succ, delta.eq_def,
    corr.eq_def, blochB.eq_def, pauli.eq_def,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_2,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_3,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_4,
    D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    kronecker_apply, conjTranspose_apply, transpose_apply, partialTraceRight,
    Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.one_apply]
  simp only [← hρ.apply (0, 1) (0, 0), ← hρ.apply (1, 0) (0, 0),
    ← hρ.apply (1, 1) (0, 0), ← hρ.apply (1, 0) (0, 1),
    ← hρ.apply (1, 1) (0, 1), ← hρ.apply (1, 1) (1, 0),
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im, hd,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero,
    Fin.isValue, one_ne_zero, zero_ne_one, ite_true, ite_false]
  ring

private lemma flip_purity_identity (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (htr : trace ρ = 1) (n : Fin 3 → ℝ) (hn : vlen n = 1) :
    2 * (trace (ρ * flipped ρ n)).re + (∑ i, ∑ j, corr ρ i j ^ 2) -
      vlen ((corr ρ) *ᵥ n) ^ 2 + (blochB ρ ⬝ᵥ n) ^ 2 = 1 + 2 * delta ρ := by
  have hs : ∑ i, n i ^ 2 = 1 := by
    have he := congrArg (fun r : ℝ => r ^ 2) hn
    rw [vlen, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at he
    simpa only [one_pow] using he
  have he := flip_purity_homogeneous ρ hρ n
  rw [hs, htr, Complex.one_re, one_pow, one_mul] at he
  linarith
private lemma vlen_sq (u : Fin 3 → ℝ) : vlen u ^ 2 = u ⬝ᵥ u := by
  simpa only [← vlen_eq_norm, EuclideanSpace.inner_toLp_toLp, star_trivial] using
    (real_inner_self_eq_norm_sq (WithLp.toLp 2 u)).symm

private def OrthoPair (u v : Fin 3 → ℝ) : Prop :=
  vlen u = 1 ∧ vlen v = 1 ∧ u ⬝ᵥ v = 0

private def planeSum (ρ : TwoQubit) (u v : Fin 3 → ℝ) : ℝ :=
  vlen ((corr ρ) *ᵥ u) ^ 2 + vlen ((corr ρ) *ᵥ v) ^ 2

private lemma plane_complement (T : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ)
    (he : OrthoPair u v) : vlen (crossProduct u v) = 1 ∧
    vlen (T *ᵥ u) ^ 2 + vlen (T *ᵥ v) ^ 2 =
      (∑ i, ∑ j, T i j ^ 2) - vlen (T *ᵥ crossProduct u v) ^ 2 := by
  rw [OrthoPair.eq_def] at he
  have hu : u ⬝ᵥ u = 1 := by rw [← vlen_sq, he.1]; norm_num
  have hv : v ⬝ᵥ v = 1 := by rw [← vlen_sq, he.2.1]; norm_num
  have hn : crossProduct u v ⬝ᵥ crossProduct u v = 1 := by
    rw [cross_dot_cross, hu, hv, he.2.2, dotProduct_comm v u, he.2.2]; norm_num
  have hnlen : vlen (crossProduct u v) = 1 := by
    have hs := vlen_sq (crossProduct u v)
    rw [hn] at hs
    have hz : 0 ≤ vlen (crossProduct u v) := Real.sqrt_nonneg _
    nlinarith
  let O : Matrix (Fin 3) (Fin 3) ℝ := ![u, v, crossProduct u v]
  have hOO : O * Oᵀ = 1 := by
    ext i j
    change O i ⬝ᵥ O j = _
    fin_cases i <;> fin_cases j <;>
      norm_num [O, hu, hv, hn, he.2.2, dot_self_cross, dot_cross_self,
        dotProduct_comm (crossProduct u v) u, dotProduct_comm (crossProduct u v) v,
        dotProduct_comm v u]
  have hrev : Oᵀ * O = 1 := mul_eq_one_comm.mp hOO
  have hr (r : Fin 3 → ℝ) : (r ⬝ᵥ u) ^ 2 + (r ⬝ᵥ v) ^ 2 +
      (r ⬝ᵥ crossProduct u v) ^ 2 = r ⬝ᵥ r := by
    have hh : (O *ᵥ r) ⬝ᵥ (O *ᵥ r) = r ⬝ᵥ r := by
      rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hrev, one_mulVec]
    rw [dotProduct, Fin.sum_univ_three] at hh
    change (u ⬝ᵥ r) * (u ⬝ᵥ r) + (v ⬝ᵥ r) * (v ⬝ᵥ r) +
      (crossProduct u v ⬝ᵥ r) * (crossProduct u v ⬝ᵥ r) = r ⬝ᵥ r at hh
    simpa only [dotProduct_comm u r, dotProduct_comm v r,
      dotProduct_comm (crossProduct u v) r, pow_two] using hh
  refine ⟨hnlen, ?_⟩
  have hsum : (∑ i, (T i ⬝ᵥ u) ^ 2) + (∑ i, (T i ⬝ᵥ v) ^ 2) +
      (∑ i, (T i ⬝ᵥ crossProduct u v) ^ 2) = ∑ i, T i ⬝ᵥ T i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hr (T i))
  rw [vlen_sq, vlen_sq, vlen_sq]
  simp only [Matrix.mulVec, dotProduct, pow_two] at hsum ⊢
  linarith

private lemma planeSum_le_purity (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (u v : Fin 3 → ℝ) (he : OrthoPair u v) : planeSum ρ u v ≤ 1 + 2 * delta ρ := by
  obtain ⟨hn, hp⟩ := plane_complement (corr ρ) u v he
  have hf : (flipped ρ (crossProduct u v)).PosSemidef :=
    hρ.transpose.mul_mul_conjTranspose_same _
  have hpos : 0 ≤ (trace (ρ * flipped ρ (crossProduct u v))).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hρ hf
  have hid := flip_purity_identity ρ hρ.isHermitian htr (crossProduct u v) hn
  rw [planeSum.eq_def]
  linarith [sq_nonneg (blochB ρ ⬝ᵥ crossProduct u v)]
private lemma normalized_unit (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    vlen ((vlen u)⁻¹ • u) = 1 ∧ vlen u • ((vlen u)⁻¹ • u) = u := by
  have hU : WithLp.toLp 2 u ≠ 0 := by simpa only [ne_eq, WithLp.toLp_eq_zero] using hu
  refine ⟨?_, ?_⟩
  · rw [vlen_eq_norm, WithLp.toLp_smul, vlen_eq_norm]
    exact NormedSpace.norm_normalize hU
  · have he := congrArg WithLp.ofLp (NormedSpace.norm_smul_normalize (WithLp.toLp 2 u))
    simpa only [NormedSpace.normalize, ← vlen_eq_norm, WithLp.ofLp_smul, WithLp.ofLp_toLp] using he

private lemma perpendicular_unit (u : Fin 3 → ℝ) :
    ∃ v : Fin 3 → ℝ, vlen v = 1 ∧ v ⬝ᵥ u = 0 := by
  obtain ⟨w, hw, hwu⟩ := exists_ne_zero_dotProduct_eq_zero u
  refine ⟨(vlen w)⁻¹ • w, (normalized_unit w hw).1, ?_⟩
  rw [smul_dotProduct, hwu, smul_zero]

private lemma direction_decomposition (u v : Fin 3 → ℝ) (huv : u ⬝ᵥ v = 0)
    (hs : vlen u ^ 2 + vlen v ^ 2 = 4) :
    ∃ e₁ e₂ : Fin 3 → ℝ, OrthoPair e₁ e₂ ∧
      u = vlen u • e₁ ∧ v = vlen v • e₂ := by
  by_cases hu : u = 0
  · subst u
    have hv : v ≠ 0 := by intro hv; rw [hv, vlen_sq] at hs; simp at hs
    obtain ⟨w, hw, hwu⟩ := perpendicular_unit ((vlen v)⁻¹ • v)
    refine ⟨w, (vlen v)⁻¹ • v, ⟨hw, (normalized_unit v hv).1, hwu⟩, ?_,
      (normalized_unit v hv).2.symm⟩
    rw [show vlen (0 : Fin 3 → ℝ) = 0 by simp [vlen], zero_smul]
  · by_cases hv : v = 0
    · subst v
      obtain ⟨w, hw, hwu⟩ := perpendicular_unit ((vlen u)⁻¹ • u)
      refine ⟨(vlen u)⁻¹ • u, w, ⟨(normalized_unit u hu).1, hw, ?_⟩,
        (normalized_unit u hu).2.symm, ?_⟩
      · rw [dotProduct_comm]; exact hwu
      · rw [show vlen (0 : Fin 3 → ℝ) = 0 by simp [vlen], zero_smul]
    · refine ⟨(vlen u)⁻¹ • u, (vlen v)⁻¹ • v,
        ⟨(normalized_unit u hu).1, (normalized_unit v hv).1, ?_⟩,
        (normalized_unit u hu).2.symm, (normalized_unit v hv).2.symm⟩
      rw [smul_dotProduct, dotProduct_smul, huv, smul_zero, smul_zero]

private lemma unit_dot_le (a x : Fin 3 → ℝ) (ha : vlen a = 1) :
    |a ⬝ᵥ x| ≤ vlen x := by
  simpa only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm x a,
    ← vlen_eq_norm, ha, one_mul] using
    abs_real_inner_le_norm (WithLp.toLp 2 a) (WithLp.toLp 2 x)

private lemma bob_radius_le (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vlen (blochB ρ) ≤ 1 := by
  have hn : vlen (blochB ρ) =
      ‖D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceLeft ρ)‖ := by
    rw [vlen_eq_norm, (bloch_marginals ρ hρ).2]
  rw [hn]
  simpa only [trace_partialTraceLeft, htr, Complex.one_re] using
    D5.S3.Quantum.Information.ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef
      (partialTraceLeft ρ) (partialTraceLeft_posSemidef hρ)

private lemma pure_bob_support (ρ : TwoQubit) (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) (hb : vlen (blochB ρ) = 1) :
    filterBob (partialTraceLeft ρ) ρ = ρ ∧ det (partialTraceLeft ρ) = 0 := by
  set B := partialTraceLeft ρ with hBdef
  have hB := partialTraceLeft_posSemidef hρ
  have ht : trace B = 1 := by rw [hBdef, trace_partialTraceLeft, htr]
  have hn : ‖D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch B‖ = 1 := by
    rw [← (bloch_marginals ρ hρ).2, ← vlen_eq_norm]
    exact hb
  have hd : det B = 0 := by
    rw [(D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
      B hB.isHermitian).1, ht, Complex.one_re,
      D5.S3.Quantum.Information.ActualQubitChordObstruction.det_bloch, hn]
    norm_num
  have hBB : B * B = B := by
    conv_lhs =>
      rw [(D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
        B hB.isHermitian).1, ht, Complex.one_re]
    rw [D5.S3.Quantum.Information.ActualQubitChordObstruction.pure _ hn]
    simpa only [ht, Complex.one_re] using
      (D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
        B hB.isHermitian).1.symm
  set E : TwoQubit := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 - B) with hEdef
  have hEH : Eᴴ = E := by
    rw [hEdef, conjTranspose_kronecker, conjTranspose_one, conjTranspose_sub,
      conjTranspose_one, hB.isHermitian.eq]
  have hEE : E * E = E := by
    rw [hEdef, ← mul_kronecker_mul, Matrix.one_mul]
    congr 1; noncomm_ring [hBB]
  have hpair : trace (ρ * E) = trace (B * (1 - B)) :=
    trace_mul_one_kron ρ (1 - B)
  have htz : trace (E * ρ * Eᴴ) = 0 := by
    rw [hEH, trace_mul_cycle, hEE, trace_mul_comm E ρ, hpair, Matrix.mul_sub, Matrix.mul_one,
      hBB, sub_self, trace_zero]
  have hZ : E * ρ * Eᴴ = 0 := (hρ.mul_mul_conjTranspose_same E).trace_eq_zero_iff.mp htz
  have hZ' : Eᴴ * ρ * E = 0 := by simpa only [hEH] using hZ
  have hρE : ρ * E = 0 := by
    ext i j
    have hz : ρ *ᵥ (E *ᵥ Pi.single j 1) = 0 :=
      (hρ.dotProduct_mulVec_zero_iff).mp (by
        rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
          hZ', zero_mulVec, dotProduct_zero])
    rw [mulVec_mulVec, mulVec_single_one] at hz
    exact congrFun hz i
  have hEρ : E * ρ = 0 := by
    have he := congrArg conjTranspose hρE
    simpa only [conjTranspose_mul, hEH, hρ.isHermitian.eq, conjTranspose_zero] using he
  refine ⟨?_, hd⟩
  have hI : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B = 1 - E := by
    rw [hEdef, kron_sub, one_kronecker_one, sub_sub_cancel]
  change ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) * ρ *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B)ᴴ = ρ
  rw [hI, conjTranspose_sub, conjTranspose_one, hEH]
  noncomm_ring [hρE, hEρ]

private lemma delta_le_centre (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    delta ρ ≤ (1 - vlen (blochB ρ) ^ 2) * (1 / 2 - vlen (centre ρ)) := by
  rcases lt_or_eq_of_le (bob_radius_le ρ hρ htr) with hb | hb
  · obtain ⟨σ, F, hσ, hσB, hσA, hback, _, hdet⟩ := canonical_filter ρ hρ htr hb
    calc
      delta ρ = (1 - vlen (blochB ρ) ^ 2) * delta σ := by
        conv_lhs => rw [hback]
        rw [← filterBob.eq_def, delta_filter, hdet]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [hσA] using canonical_delta_le σ hσ hσB)
        (by have hz : 0 ≤ vlen (blochB ρ) := Real.sqrt_nonneg _; nlinarith)
  · obtain ⟨hs, hd⟩ := pure_bob_support ρ hρ htr hb
    have he := delta_filter ρ (partialTraceLeft ρ)
    rw [hs, hd, Complex.normSq_zero, zero_mul] at he
    rw [he, hb]; norm_num

theorem trace_pauli_kronecker_eq_corr (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (i j : Fin 3) : trace (ρ * (pauli i ⊗ₖ pauli j)) = (corr ρ i j : ℂ) := by
  exact Complex.ext (by rfl) (by
    simpa only [Complex.ofReal_im] using
      trace_hermitian_product_real
        ρ (pauli i ⊗ₖ pauli j) hρ (isHermitian_kronecker
          (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pauli_hermitian i)
          (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pauli_hermitian j)))

private lemma bell_trace_real_expansion (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (a a' b b' : Fin 3 → ℝ) :
    trace (ρ * bell a a' b b') =
      ((a ⬝ᵥ (corr ρ *ᵥ (b + b')) + a' ⬝ᵥ (corr ρ *ᵥ (b - b')) : ℝ) : ℂ) := by
  rw [bell_trace_expansion]
  simp only [trace_pauli_kronecker_eq_corr ρ hρ, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply]
  congr 1
  ring

private lemma chsh_le_of_plane_bound (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (m : ℝ) (hm : 0 ≤ m)
    (hplane : ∀ u v : Fin 3 → ℝ, OrthoPair u v → planeSum ρ u v ≤ m) :
    chsh ρ ≤ 2 * Real.sqrt m := by
  rw [chsh.eq_def]
  apply csSup_le (chshValues_nonempty ρ)
  rintro r ⟨a, a', b, b', ha, ha', hb, hb', rfl⟩
  have hb2 : b ⬝ᵥ b = 1 := by rw [← vlen_sq, hb]; norm_num
  have hb2' : b' ⬝ᵥ b' = 1 := by rw [← vlen_sq, hb']; norm_num
  have hu : (b + b') ⬝ᵥ (b - b') = 0 := by
    simp only [add_dotProduct, dotProduct_sub,
      dotProduct_comm b' b, hb2, hb2']
    ring
  have hs : vlen (b + b') ^ 2 + vlen (b - b') ^ 2 = 4 := by
    rw [vlen_sq, vlen_sq]
    simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
      dotProduct_comm b' b, hb2, hb2']
    ring
  obtain ⟨u, v, he, hsum, hdiff⟩ := direction_decomposition (b + b') (b - b') hu hs
  have hpu := hplane u v he
  rw [planeSum.eq_def] at hpu
  have hcs : (vlen (b + b') * vlen (corr ρ *ᵥ u) +
      vlen (b - b') * vlen (corr ρ *ᵥ v)) ^ 2 ≤ 4 * m := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (![vlen (b + b'), vlen (b - b')] : Fin 2 → ℝ)
      (![vlen (corr ρ *ᵥ u), vlen (corr ρ *ᵥ v)] : Fin 2 → ℝ)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hs] at hc
    nlinarith
  have hx : 0 ≤ vlen (corr ρ *ᵥ u) := Real.sqrt_nonneg _
  have hy : 0 ≤ vlen (corr ρ *ᵥ v) := Real.sqrt_nonneg _
  have hr : 0 ≤ vlen (b + b') := Real.sqrt_nonneg _
  have ht : 0 ≤ vlen (b - b') := Real.sqrt_nonneg _
  have hmroot := Real.sq_sqrt hm
  rw [bell_trace_real_expansion ρ hρ, Complex.norm_real, Real.norm_eq_abs,
    hsum, hdiff, mulVec_smul (corr ρ) (vlen (b + b')) u,
    mulVec_smul (corr ρ) (vlen (b - b')) v, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  calc
    |vlen (b + b') * (a ⬝ᵥ (corr ρ *ᵥ u)) +
        vlen (b - b') * (a' ⬝ᵥ (corr ρ *ᵥ v))|
      ≤ vlen (b + b') * |a ⬝ᵥ (corr ρ *ᵥ u)| +
          vlen (b - b') * |a' ⬝ᵥ (corr ρ *ᵥ v)| := by
        simpa only [abs_mul, abs_of_nonneg hr, abs_of_nonneg ht] using abs_add_le
          (vlen (b + b') * (a ⬝ᵥ (corr ρ *ᵥ u)))
          (vlen (b - b') * (a' ⬝ᵥ (corr ρ *ᵥ v)))
    _ ≤ vlen (b + b') * vlen (corr ρ *ᵥ u) +
        vlen (b - b') * vlen (corr ρ *ᵥ v) :=
      add_le_add (mul_le_mul_of_nonneg_left (unit_dot_le _ _ ha) hr)
        (mul_le_mul_of_nonneg_left (unit_dot_le _ _ ha') ht)
    _ ≤ 2 * Real.sqrt m := by nlinarith [Real.sqrt_nonneg m]

private lemma universal_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    chsh ρ ≤ bound (vlen (centre ρ)) := by
  set c := vlen (centre ρ)
  set d := 1 - vlen (blochB ρ) ^ 2
  have hd : 0 ≤ d := by
    have hb := bob_radius_le ρ hρ htr
    have hz : 0 ≤ vlen (blochB ρ) := Real.sqrt_nonneg _
    dsimp only [d]; nlinarith
  have hd1 : d ≤ 1 := by dsimp only [d]; nlinarith [sq_nonneg (vlen (blochB ρ))]
  have hδ := delta_le_centre ρ hρ htr
  change delta ρ ≤ d * (1 / 2 - c) at hδ
  have hscalar : 1 + 2 * delta ρ ≤ max (2 * (1 - c)) 1 := by
    by_cases hc : c ≤ 1 / 2
    · apply le_trans _ (le_max_left _ _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (show 0 ≤ 1 / 2 - c by linarith)]
    · apply le_trans _ (le_max_right _ _)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd (show 1 / 2 - c ≤ 0 by linarith)]
  have hm : 0 ≤ max (2 * (1 - c)) 1 := le_trans (by norm_num) (le_max_right _ _)
  have hc := chsh_le_of_plane_bound ρ hρ.isHermitian _ hm
    (fun u v he => (planeSum_le_purity ρ hρ htr u v he).trans hscalar)
  have he : 2 * Real.sqrt (max (2 * (1 - c)) 1) = bound c := by
    rw [bound.eq_def, Real.sqrt_monotone.map_max, mul_max_of_nonneg _ _ (by norm_num),
      Real.sqrt_one]
    ring_nf
  exact hc.trans_eq he

private def tightVector (t s : ℝ) : Fin 2 × Fin 2 → ℂ :=
  fun k => ![![(Real.sqrt (1 + s) : ℂ), 0],
    ![0, (Real.sqrt ((1 - t) * (1 - s)) : ℂ)]] k.1 k.2

private def tightState (t s : ℝ) : TwoQubit :=
  (1 / 2 : ℂ) • vecMulVec (tightVector t s) (star (tightVector t s)) +
    ((t * (1 - s) / 2 : ℝ) : ℂ) • vecMulVec (fun k => (ev k : ℂ)) (star (fun k => (ev k : ℂ)))

private lemma tight_psd (t s : ℝ) (ht : 0 ≤ t) (hs : s ≤ 1) :
    (tightState t s).PosSemidef := by
  rw [tightState.eq_def]
  have hhalf : (0 : ℂ) ≤ (1 / 2 : ℂ) := by norm_num [Complex.le_def]
  have hc : (0 : ℂ) ≤ ((t * (1 - s) / 2 : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by positivity)
  exact ((posSemidef_vecMulVec_self_star _).smul hhalf).add
    ((posSemidef_vecMulVec_self_star _).smul hc)

private lemma tight_readouts (t s : ℝ) (ht₁ : t ≤ 1)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) : trace (tightState t s) = 1 ∧
    blochA (tightState t s) = ![0, 0, t + (1 - t) * s] ∧
    blochB (tightState t s) = ![0, 0, s] ∧
    corr (tightState t s) = diagonal
      ![Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s)),
        -(Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s))), 1 - t + t * s] := by
  have hx : Real.sqrt (1 + s) * Real.sqrt (1 + s) = 1 + s := Real.mul_self_sqrt (by positivity)
  have hy : Real.sqrt ((1 - t) * (1 - s)) * Real.sqrt ((1 - t) * (1 - s)) =
      (1 - t) * (1 - s) := Real.mul_self_sqrt (mul_nonneg (by linarith) (by linarith))
  have hxC : (Real.sqrt (1 + s) : ℂ) * Real.sqrt (1 + s) = (1 + s : ℝ) := by exact_mod_cast hx
  have hyC : (Real.sqrt ((1 - t) * (1 - s)) : ℂ) * Real.sqrt ((1 - t) * (1 - s)) =
      ((1 - t) * (1 - s) : ℝ) := by exact_mod_cast hy
  let R : TwoQubit := fun (k l : Fin 2 × Fin 2) =>
      ((![![![![(1 + s) / 2, 0], ![0, t * (1 - s) / 2]],
          ![![0, Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s)) / 2], ![0, 0]]],
        ![![![0, 0], ![Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s)) / 2, 0]],
          ![![0, 0], ![0, (1 - t) * (1 - s) / 2]]]]
        k.1 l.1 k.2 l.2 : ℝ) : ℂ)
  have hentry : tightState t s = R := by
    ext k l
    simp only [tightState.eq_def, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, Pi.star_apply, smul_eq_mul, tightVector.eq_def, ev.eq_def]
    rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [R, Complex.star_def, Pi.single_apply, hxC, hyC]
    all_goals ring
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rw [hentry]
  all_goals try (funext i; fin_cases i)
  all_goals try (funext j; fin_cases j)
  all_goals
    simp only [blochA.eq_def, blochB.eq_def, corr.eq_def, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, kronecker_apply]
    norm_num [R, pauli.eq_def,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_2,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_3,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_4,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      diagonal, Complex.mul_re, Complex.mul_im]
    try push_cast
    try ring

private lemma tight_centre (t s : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hs₀ : 0 ≤ s) (hs₁ : s < 1) : vlen (centre (tightState t s)) = t := by
  obtain ⟨_, ha, hb, hT⟩ := tight_readouts t s ht₁ hs₀ hs₁.le
  have hbl : vlen (blochB (tightState t s)) = s := by
    rw [hb, vlen_e3, abs_of_nonneg hs₀]
  have hden : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hc : centre (tightState t s) = ![0, 0, t] := by
    rw [centre, hbl, if_neg (ne_of_lt hs₁)]
    funext i
    fin_cases i <;> norm_num [ha, hb, hT, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, diagonal]
    field_simp [hden]
    ring
  rw [hc, vlen_e3, abs_of_nonneg ht₀]

private lemma tight_z_setting (t s : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) : 2 * (1 - t + t * s) ≤ chsh (tightState t s) := by
  have hz : 0 ≤ 1 - t + t * s := add_nonneg (by linarith) (mul_nonneg ht₀ hs₀)
  have hv : trace (tightState t s * bell ![0,0,1] ![0,0,1] ![0,0,1] ![0,0,1]) =
      ((2 * (1 - t + t * s) : ℝ) : ℂ) := by
    rw [bell_trace_real_expansion _ (tight_psd t s ht₀ hs₁).isHermitian,
      (tight_readouts t s ht₁ hs₀ hs₁).2.2.2]
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, diagonal]
    ring
  have hh := setting_le_chsh (tightState t s) ![0,0,1] ![0,0,1] ![0,0,1] ![0,0,1]
    (by norm_num [vlen, Fin.sum_univ_succ]) (by norm_num [vlen, Fin.sum_univ_succ])
    (by norm_num [vlen, Fin.sum_univ_succ]) (by norm_num [vlen, Fin.sum_univ_succ])
  rw [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hz)] at hh
  exact hh

private lemma tight_low_setting (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    2 * Real.sqrt (2 * (1 - t)) ≤ chsh (tightState t 0) := by
  have hunit : vlen (![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0] : Fin 3 → ℝ) = 1 ∧
      vlen (![1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0] : Fin 3 → ℝ) = 1 := by
    constructor <;> rw [vlen] <;> norm_num [Fin.sum_univ_succ, Real.sqrt_div,
      Real.sq_sqrt, Real.sqrt_sq_eq_abs]
  have hval :
      ((![1,0,0] : Fin 3 → ℝ) ⬝ᵥ ((corr (tightState t 0)) *ᵥ
        (![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0] + ![1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0])) +
        (![0,-1,0] : Fin 3 → ℝ) ⬝ᵥ ((corr (tightState t 0)) *ᵥ
        (![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0] - ![1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0]))) =
        2 * Real.sqrt (2 * (1 - t)) := by
    rw [(tight_readouts t 0 ht₁ (by norm_num) (by norm_num)).2.2.2]
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, diagonal]
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp (discharger := positivity)
    rw [hs]
    ring
  have hvalue := congrArg (fun x : ℝ => (x : ℂ)) hval
  -- The norm of the nonnegative real expectation is its ordinary value.
  have hv : trace (tightState t 0 * bell ![1,0,0] ![0,-1,0]
      ![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0] ![1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0]) =
      ((2 * Real.sqrt (2 * (1 - t)) : ℝ) : ℂ) :=
    (bell_trace_real_expansion _ (tight_psd t 0 ht₀ (by norm_num)).isHermitian _ _ _ _).trans hvalue
  have hh := setting_le_chsh (tightState t 0) ![1,0,0] ![0,-1,0]
    ![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0] ![1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0]
    (by norm_num [vlen, Fin.sum_univ_succ]) (by norm_num [vlen, Fin.sum_univ_succ]) hunit.1 hunit.2
  rw [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hh
  exact hh
theorem result : claim := by
  rw [claim.eq_def]
  refine ⟨universal_bound, ?_⟩
  intro t ht₀ ht₁ ε hε
  by_cases ht : t ≤ 1 / 2
  · have hb : bound t = 2 * Real.sqrt (2 * (1 - t)) := by
      rw [bound.eq_def, max_eq_left]
      have hs : 1 ≤ Real.sqrt (2 * (1 - t)) := Real.one_le_sqrt.mpr (by linarith)
      linarith
    refine ⟨tightState t 0, tight_psd t 0 ht₀ (by norm_num),
      (tight_readouts t 0 ht₁ (by norm_num) (by norm_num)).1,
      tight_centre t 0 ht₀ ht₁ (by norm_num) (by norm_num), ?_⟩
    rw [hb]
    exact lt_of_lt_of_le (by linarith) (tight_low_setting t ht₀ ht₁)
  · have hb : bound t = 2 := by
      rw [bound.eq_def, max_eq_right]
      have hs : Real.sqrt (2 * (1 - t)) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
      linarith
    by_cases htend : t = 1
    · subst t
      refine ⟨tightState 1 1, tight_psd 1 1 (by norm_num) (by norm_num),
        (tight_readouts 1 1 (by norm_num) (by norm_num) (by norm_num)).1,
        ?_, ?_⟩
      · have hdata := tight_readouts 1 1 (by norm_num) (by norm_num) (by norm_num)
        norm_num [centre, hdata.2.1, hdata.2.2.1, vlen, Fin.sum_univ_succ]
      · have he := tight_z_setting 1 1 (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
        rw [hb]
        norm_num at he
        linarith
    · let s : ℝ := 2 / (2 + ε)
      have hd : 0 < 2 + ε := by linarith
      have hs₀ : 0 ≤ s := by dsimp only [s]; positivity
      have hs₁ : s < 1 := by dsimp only [s]; exact (div_lt_one hd).mpr (by linarith)
      have he : 2 - ε < 2 * (1 - t + t * s) := by
        have hprod : (2 + ε) * s = 2 := by dsimp only [s]; field_simp
        have hgap : 0 < ε * (2 + ε - 2 * t) := mul_pos hε (by linarith)
        have hcert : (2 * (1 - t + t * s) - (2 - ε)) * (2 + ε) =
            ε * (2 + ε - 2 * t) := by
          linear_combination 2 * t * hprod
        exact (mul_pos_iff_of_pos_right hd).mp (by rw [hcert]; exact hgap) |> sub_pos.mp
      refine ⟨tightState t s, tight_psd t s ht₀ hs₁.le,
        (tight_readouts t s ht₁ hs₀ hs₁.le).1,
        tight_centre t s ht₀ ht₁ hs₀ hs₁, ?_⟩
      rw [hb]
      exact he.trans_le (tight_z_setting t s ht₀ ht₁ hs₀ hs₁.le)

end D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
