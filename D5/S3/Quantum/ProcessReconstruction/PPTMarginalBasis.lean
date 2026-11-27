/- GID: D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis
   generality: I
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/PPTMarginalBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transfers the PPT operational bound to arbitrary marginal bases. -/

import D5.S3.Quantum.ProcessReconstruction.PPTOperationalGain

/-!
# Weighted operational PPT gain for an arbitrary Bob marginal

Local conjugation on the untouched register commutes with the physical
channel output and preserves its squared Hilbert–Schmidt distance. Hence the
attained operational minimum is transported to the eigenbasis of the Bob
marginal, where the weighted PPT inequality applies. A singular marginal
forces the operational minimum to vanish.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

set_option autoImplicit false

namespace D5.S3.Quantum.ProcessReconstruction.PPTMarginalBasis

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf (MatrixMap)
open Original8340Global (inputChoi)
open PauliDiagonalPPTTomography (probeOutput hsSquare)
open PPTOperationalGain (squaredGain leastRealignmentSV_sq_cptp_attains
  leastRealignmentSV_sq_isLeast_cptp_gain)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceLeft_posSemidef)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
  (partialTranspose trace_local_left)
open D5.S3.Quantum.Entanglement.Witness.PPTWeightedReduction
  (leastRealignmentSV weighted_converse_of_ppt
    leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero)

section LocalConjugation

variable {I B : Type} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

/-- Conjugation on Bob, using the first-factor/second-factor product convention.
The first factor can be either the input or the output register. -/
def bobConjugate (V : Matrix B B ℂ) (M : Matrix (I × B) (I × B) ℂ) :
    Matrix (I × B) (I × B) ℂ :=
  ((1 : Matrix I I ℂ) ⊗ₖ V) * M * ((1 : Matrix I I ℂ) ⊗ₖ V)ᴴ

private theorem bobConjugate_add (V : Matrix B B ℂ)
    (X Y : Matrix (I × B) (I × B) ℂ) :
    bobConjugate V (X + Y) = bobConjugate V X + bobConjugate V Y := by
  simp only [bobConjugate, Matrix.mul_add, Matrix.add_mul]

private theorem bobConjugate_sub (V : Matrix B B ℂ)
    (X Y : Matrix (I × B) (I × B) ℂ) :
    bobConjugate V (X - Y) = bobConjugate V X - bobConjugate V Y := by
  simp only [bobConjugate, Matrix.mul_sub, Matrix.sub_mul]

private theorem bobConjugate_kronecker (V : Matrix B B ℂ)
    (X : Matrix I I ℂ) (Y : Matrix B B ℂ) :
    bobConjugate V (X ⊗ₖ Y) = X ⊗ₖ (V * Y * Vᴴ) := by
  simp only [bobConjugate, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one]

private theorem bob_isometry (V : Matrix B B ℂ) (hV : Vᴴ * V = 1) :
    ((1 : Matrix I I ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix I I ℂ) ⊗ₖ V) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, one_mul, hV, Matrix.one_kronecker_one]

private theorem trace_congruence {J : Type*} [Fintype J] [DecidableEq J]
    (K M : Matrix J J ℂ) (hK : Kᴴ * K = 1) :
    (K * M * Kᴴ).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, hK, one_mul]

private theorem hsSquare_congruence {J : Type*} [Fintype J] [DecidableEq J]
    (K M : Matrix J J ℂ) (hK : Kᴴ * K = 1) :
    hsSquare (K * M * Kᴴ) = hsSquare M := by
  have hprod : (K * M * Kᴴ)ᴴ * (K * M * Kᴴ) = K * (Mᴴ * M) * Kᴴ := by
    calc
      _ = K * Mᴴ * (Kᴴ * K) * M * Kᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = _ := by rw [hK, mul_one, Matrix.mul_assoc K Mᴴ M]
  change ((K * M * Kᴴ)ᴴ * (K * M * Kᴴ)).trace.re = (Mᴴ * M).trace.re
  rw [hprod, trace_congruence K (Mᴴ * M) hK]

theorem hsSquare_bobConjugate (V : Matrix B B ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix (I × B) (I × B) ℂ) : hsSquare (bobConjugate V M) = hsSquare M :=
  hsSquare_congruence _ M (bob_isometry V hV)

private theorem bobConjugate_posSemidef (V : Matrix B B ℂ)
    (M : Matrix (I × B) (I × B) ℂ) (hM : M.PosSemidef) :
    (bobConjugate V M).PosSemidef :=
  hM.mul_mul_conjTranspose_same ((1 : Matrix I I ℂ) ⊗ₖ V)

private theorem bobConjugate_trace (V : Matrix B B ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix (I × B) (I × B) ℂ) : (bobConjugate V M).trace = M.trace :=
  trace_congruence _ M (bob_isometry V hV)

private theorem partialTraceLeft_bobConjugate (V : Matrix B B ℂ)
    (M : Matrix (I × B) (I × B) ℂ) :
    partialTraceLeft (bobConjugate V M) = V * partialTraceLeft M * Vᴴ := by
  exact trace_local_left M (1 : Matrix I I ℂ) V (by simp)

private theorem partialTranspose_add (M N : Matrix (I × B) (I × B) ℂ) :
    partialTranspose (M + N) = partialTranspose M + partialTranspose N := rfl

private theorem partialTranspose_kronecker (X : Matrix I I ℂ) (Y : Matrix B B ℂ) :
    partialTranspose (X ⊗ₖ Y) = X ⊗ₖ Yᵀ := rfl

private theorem transpose_congruence (V Y : Matrix B B ℂ) :
    (V * Y * Vᴴ)ᵀ = V.map star * Yᵀ * (V.map star)ᴴ := by
  have hV : (V.map star)ᴴ = Vᵀ := by
    apply Matrix.ext
    intro i j
    change star (star (V j i)) = V j i
    exact star_star _
  simp only [Matrix.transpose_mul, Matrix.conjTranspose_transpose, hV, Matrix.mul_assoc]

/-- Partial transposition on Bob conjugates the local basis change entrywise. -/
theorem partialTranspose_bobConjugate (V : Matrix B B ℂ)
    (M : Matrix (I × B) (I × B) ℂ) :
    partialTranspose (bobConjugate V M) = bobConjugate (V.map star) (partialTranspose M) := by
  induction M using Matrix.induction_on' with
  | h_zero =>
    have hz : partialTranspose (0 : Matrix (I × B) (I × B) ℂ) = 0 := rfl
    simp only [bobConjugate, Matrix.mul_zero, Matrix.zero_mul, hz]
  | h_add X Y hX hY =>
    simp only [bobConjugate_add, partialTranspose_add, hX, hY]
  | h_std_basis p q z =>
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    have he : Matrix.single (i, a) (j, b) z =
        Matrix.single i j z ⊗ₖ Matrix.single a b (1 : ℂ) := by
      rw [Matrix.single_kronecker_single, mul_one]
    rw [he]
    simp only [bobConjugate_kronecker, partialTranspose_kronecker, transpose_congruence]

private theorem bobConjugate_ppt (V : Matrix B B ℂ)
    (M : Matrix (I × B) (I × B) ℂ) (hM : (partialTranspose M).PosSemidef) :
    (partialTranspose (bobConjugate V M)).PosSemidef := by
  rw [partialTranspose_bobConjugate]
  exact bobConjugate_posSemidef _ _ hM

end LocalConjugation

section OperationalCovariance

variable {d : ℕ}
local notation "A" => Fin d
variable {O : Type} [Fintype O] [DecidableEq O]

-- The tensor formula in PauliDiagonalPPTTomography is private.
private theorem probeOutput_on_kronecker (Φ : MatrixMap A O ℂ) (X Y : Matrix A A ℂ) :
    probeOutput Φ (X ⊗ₖ Y) = Φ X ⊗ₖ Y := by
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    ext i j
    simp [Matrix.single, Matrix.sum_apply, ite_and]
  have hΦ : Φ X = ∑ i, ∑ j, X i j • Φ (Matrix.single i j 1) := by
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul]
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [probeOutput, PhyslibLeaf.MatrixMap.kron_def, hΦ]
  simp [LinearMap.id_apply, Matrix.single, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, ite_and, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]

/-- A basis change on the untouched register commutes exactly with the
physical output map, for arbitrary finite output dimension. -/
theorem probeOutput_bobConjugate (V : Matrix A A ℂ) (Φ : MatrixMap A O ℂ)
    (ρ : Matrix (A × A) (A × A) ℂ) :
    probeOutput Φ (bobConjugate V ρ) = bobConjugate V (probeOutput Φ ρ) := by
  induction ρ using Matrix.induction_on' with
  | h_zero => simp [bobConjugate]
  | h_add X Y hX hY =>
    simp only [bobConjugate_add, map_add, hX, hY]
  | h_std_basis p q z =>
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    have he : Matrix.single (i, a) (j, b) z =
        Matrix.single i j z ⊗ₖ Matrix.single a b (1 : ℂ) := by
      rw [Matrix.single_kronecker_single, mul_one]
    rw [he]
    simp only [bobConjugate_kronecker, probeOutput_on_kronecker]

/-- Every fixed channel pair has precisely the same squared gain after
unitary conjugation on Bob. The Choi distance is independent of the probe. -/
theorem squaredGain_bobConjugate (V : Matrix A A ℂ) (hV : Vᴴ * V = 1)
    (ρ : Matrix (A × A) (A × A) ℂ) (Φ Ψ : MatrixMap A O ℂ) :
    squaredGain (bobConjugate V ρ) Φ Ψ = squaredGain ρ Φ Ψ := by
  unfold squaredGain
  simp only [probeOutput_bobConjugate, ← bobConjugate_sub, hsSquare_bobConjugate V hV]

-- Uniqueness of the attained physical minimum transports its exact value.
private theorem least_gain_bobConjugate (hd : 2 ≤ d)
    (V : Matrix A A ℂ) (hV : Vᴴ * V = 1)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.PosSemidef) :
    leastRealignmentSV hd (bobConjugate V ρ) ^ 2 = leastRealignmentSV hd ρ ^ 2 := by
  have horig := leastRealignmentSV_sq_isLeast_cptp_gain hd ρ hρ.isHermitian
  have hrot := leastRealignmentSV_sq_isLeast_cptp_gain hd (bobConjugate V ρ)
    (bobConjugate_posSemidef V ρ hρ).isHermitian
  simp only [squaredGain_bobConjugate V hV] at hrot
  exact hrot.unique horig

end OperationalCovariance

section ArbitraryMarginal

variable {d : ℕ}
local notation "A" => Fin d

private theorem exists_bob_diagonalization (ρ : Matrix (A × A) (A × A) ℂ)
    (h : (partialTraceLeft ρ).IsHermitian) :
    ∃ V : Matrix A A ℂ, Vᴴ * V = 1 ∧
      partialTraceLeft (bobConjugate V ρ) = diagonal (fun i => (h.eigenvalues i : ℂ)) := by
  let W : Matrix A A ℂ := h.eigenvectorUnitary
  refine ⟨Wᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]
    exact Unitary.coe_mul_star_self h.eigenvectorUnitary
  · rw [partialTraceLeft_bobConjugate, Matrix.conjTranspose_conjTranspose]
    change Wᴴ * partialTraceLeft ρ * W = diagonal (Complex.ofReal ∘ h.eigenvalues)
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, W] using h.conjStarAlgAut_star_eigenvectorUnitary

/-- For every square trace-one PPT probe with positive definite Bob marginal,
the attained physical minimum satisfies the weighted PPT upper bound in
terms of the eigenvalues of its actual marginal. -/
theorem exists_cptp_pair_weighted_ppt_of_posDef (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) (hppt : (partialTranspose ρ).PosSemidef)
    (hB : (partialTraceLeft ρ).PosDef) :
    ∃ Φ Ψ : MatrixMap A (Fin 2) ℂ,
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧
      0 < hsSquare (inputChoi Φ - inputChoi Ψ) ∧
      squaredGain ρ Φ Ψ = leastRealignmentSV hd ρ ^ 2 ∧
      squaredGain ρ Φ Ψ ≤
        ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * ((∑ i, (hB.isHermitian.eigenvalues i)⁻¹) - 1)) := by
  obtain ⟨V, hV, hb⟩ := exists_bob_diagonalization ρ hB.isHermitian
  let σ := bobConjugate V ρ
  have hσ : σ.PosSemidef := bobConjugate_posSemidef V ρ hρ
  have htσ : σ.trace = 1 := (bobConjugate_trace V hV ρ).trans ht
  have hpptσ : (partialTranspose σ).PosSemidef := bobConjugate_ppt V ρ hppt
  have hbound := weighted_converse_of_ppt hd σ hσ htσ hpptσ
    hB.isHermitian.eigenvalues hB.eigenvalues_pos hb
  have hmin : leastRealignmentSV hd σ ^ 2 = leastRealignmentSV hd ρ ^ 2 :=
    least_gain_bobConjugate hd V hV ρ hρ
  obtain ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hdist, hgain⟩ :=
    leastRealignmentSV_sq_cptp_attains hd ρ hρ.isHermitian
  refine ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hdist, hgain, ?_⟩
  rw [hgain, ← hmin]
  exact hbound

/-- A singular Bob marginal of a positive semidefinite square probe forces
the attained minimum to be zero, including for all singular PPT probes. -/
theorem exists_cptp_pair_zero_gain_of_singular_marginal (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.PosSemidef)
    (hB : ¬ (partialTraceLeft ρ).PosDef) :
    ∃ Φ Ψ : MatrixMap A (Fin 2) ℂ,
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧
      0 < hsSquare (inputChoi Φ - inputChoi Ψ) ∧
      squaredGain ρ Φ Ψ = leastRealignmentSV hd ρ ^ 2 ∧ squaredGain ρ Φ Ψ = 0 := by
  have hpsd := partialTraceLeft_posSemidef hρ
  have hnot : ¬ ∀ i, 0 < hpsd.isHermitian.eigenvalues i :=
    fun hall => hB (hpsd.isHermitian.posDef_iff_eigenvalues_pos.mpr hall)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hi0 : hpsd.isHermitian.eigenvalues i = 0 :=
    le_antisymm (le_of_not_gt hi) (hpsd.eigenvalues_nonneg i)
  obtain ⟨V, hV, hb⟩ := exists_bob_diagonalization ρ hpsd.isHermitian
  let σ := bobConjugate V ρ
  have hbi : partialTraceLeft σ i i = 0 := by
    change partialTraceLeft (bobConjugate V ρ) i i = 0
    rw [hb, Matrix.diagonal_apply_eq, hi0, Complex.ofReal_zero]
  have hm0 := leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero hd σ
    (bobConjugate_posSemidef V ρ hρ) i hbi
  have hmin : leastRealignmentSV hd σ ^ 2 = leastRealignmentSV hd ρ ^ 2 :=
    least_gain_bobConjugate hd V hV ρ hρ
  obtain ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hdist, hgain⟩ :=
    leastRealignmentSV_sq_cptp_attains hd ρ hρ.isHermitian
  refine ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hdist, hgain, ?_⟩
  rw [hgain, ← hmin, hm0] <;> norm_num

end ArbitraryMarginal

end D5.S3.Quantum.ProcessReconstruction.PPTMarginalBasis
