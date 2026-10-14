/- GID: D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact critical concurrence for universal teleportation through qubit channels. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen blochVec blochVec_eq_bloch vlen_eq_norm
    trace_mul_kron_one trace_mul_one_kron kron_sub vlen_e3)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin sigma)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
  (bloch blochMatrix matrix_energy bloch_geometry_of_isHermitian)
open D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (pauli_hermitian letter_mul)
open D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation (IsKrausChannel)

namespace D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence

set_option linter.style.longLine false

def psi (a : ℝ) (p : Fin 2 × Fin 2) : ℂ :=
  if p = (0, 0) then (Real.sqrt a : ℂ) else if p = (1, 1) then (Real.sqrt (1 - a) : ℂ) else 0
def initial (a : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (psi a)
def NonUnital {m : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ) : Prop := ∑ k, K k * (K k)ᴴ ≠ 1
def out {m : ℕ} (a : ℝ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let L : Fin m → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    fun k => (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K k
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus L L (initial a)
def UsefulUQT (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∃ (U V : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ),
    U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ (1 / 3 : ℝ) < t ∧
    corr ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) = fun i j => if i = j then -t else 0
def Cstar : ℝ := Real.sqrt (5 - 2 * Real.sqrt 3) / 3
def conc (a : ℝ) : ℝ := 2 * Real.sqrt (a * (1 - a))
def claim : Prop :=
  ∀ a : ℝ, (1 / 2 : ℝ) < a → a < 1 →
    (∀ (m : ℕ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ), IsKrausChannel (ι := Fin m) K → UsefulUQT (out a K) → Cstar < conc a) ∧
    (Cstar < conc a → ∃ (m : ℕ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ), IsKrausChannel (ι := Fin m) K ∧ NonUnital K ∧ UsefulUQT (out a K))

set_option linter.style.longLine true

private def rcrit : ℝ := (1 + Real.sqrt 3) / 3
private def tmax (r : ℝ) : ℝ :=
  (1 - r + Real.sqrt ((1 - r) * (1 + 3 * r))) / 2

private lemma critical_constants :
    2 / 3 < rcrit ∧ rcrit < 1 ∧ 0 ≤ Cstar ∧
      Cstar ^ 2 + rcrit ^ 2 = 1 ∧ rcrit ^ 2 - 2 / 3 * rcrit - 2 / 9 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlow : 1 < Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
  have hhigh : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hc := Real.sq_sqrt (show 0 ≤ 5 - 2 * Real.sqrt 3 by linarith)
  dsimp [rcrit, Cstar]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · positivity
  constructor <;> nlinarith

private lemma eliminate_beta (r t β : ℝ) (hr : 0 ≤ r) (ht : 0 < t)
    (hcorner : r + β ≤ 1 - t)
    (hminor : (r - β) ^ 2 ≤ (1 - t) * (1 + 3 * t)) :
    r ^ 2 + r * t + t ^ 2 ≤ r + t := by
  have ht1 : t ≤ 1 := by nlinarith [sq_nonneg (r - β)]
  by_cases hsign : 0 ≤ 2 * r + t - 1
  · have hz : 2 * r + t - 1 ≤ r - β := by linarith
    have hp := mul_nonneg (show 0 ≤ r - β - (2 * r + t - 1) by linarith)
      (show 0 ≤ r - β + (2 * r + t - 1) by linarith)
    nlinarith
  · have hp := mul_nonpos_of_nonneg_of_nonpos hr (show r + t - 1 ≤ 0 by linarith)
    have hq := mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr ht1)
    nlinarith

private lemma r_lt_critical (r t : ℝ) (ht : (1 / 3 : ℝ) < t)
    (hb : r ^ 2 + r * t + t ^ 2 ≤ r + t) : r < rcrit := by
  obtain ⟨hR, _, _, _, he⟩ := critical_constants
  by_contra hn
  have hr : rcrit ≤ r := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ r + rcrit + t - 1 by linarith)
  have hq := mul_pos (show 0 < t - 1 / 3 by linarith)
    (show 0 < rcrit + t - 2 / 3 by linarith)
  nlinarith

private lemma concurrence_threshold (a : ℝ) (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1) :
    Cstar < conc a ↔ 2 * a - 1 < rcrit := by
  obtain ⟨hR, _, hC, he, _⟩ := critical_constants
  have hs := Real.sq_sqrt (show 0 ≤ a * (1 - a) by positivity)
  have hn := Real.sqrt_nonneg (a * (1 - a))
  have hsq : (conc a) ^ 2 + (2 * a - 1) ^ 2 = 1 := by dsimp [conc]; nlinarith
  have hc0 : 0 ≤ conc a := by dsimp [conc]; positivity
  constructor <;> intro h <;> nlinarith

private lemma tmax_properties (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hrc : r < rcrit) :
    (1 / 3 : ℝ) < tmax r ∧ tmax r < 1 ∧
      (tmax r) ^ 2 = (1 - r) * (tmax r + r) := by
  have hs := Real.sq_sqrt (show 0 ≤ (1 - r) * (1 + 3 * r) by positivity)
  have hn := Real.sqrt_nonneg ((1 - r) * (1 + 3 * r))
  have ht : 0 < tmax r := by dsimp [tmax]; linarith
  have he : (tmax r) ^ 2 = (1 - r) * (tmax r + r) := by dsimp [tmax]; nlinarith
  have ht1 : tmax r < 1 := by
    by_contra h
    have hp := mul_nonneg (show 0 ≤ tmax r - 1 by linarith)
      (show 0 ≤ r + tmax r by linarith)
    nlinarith
  have hrt : 0 < r + tmax r - 1 := by
    have hp := mul_pos hr (show 0 < 1 - r by linarith)
    nlinarith
  obtain ⟨hR, _, _, _, hRe⟩ := critical_constants
  have hp := mul_neg_of_neg_of_pos (show r - rcrit < 0 by linarith)
    (show 0 < r + rcrit - 2 / 3 by linarith)
  have hthird : (1 / 3 : ℝ) < tmax r := by
    by_contra h
    have hq := mul_nonneg (show 0 ≤ 1 / 3 - tmax r by linarith)
      (show 0 ≤ r + 1 / 3 + tmax r - 1 by linarith)
    nlinarith
  exact ⟨hthird, ht1, he⟩

private def localConj (U V : Matrix (Fin 2) (Fin 2) ℂ) (ρ : TwoQubit) : TwoQubit :=
  (U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ

private lemma out_state (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {m : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : IsKrausChannel (ι := Fin m) K) :
    (out a K).PosSemidef ∧ trace (out a K) = 1 ∧
      partialTraceRight (out a K) = Matrix.diagonal ![(a : ℂ), 1 - (a : ℂ)] := by
  have hp : (out a K).PosSemidef := by
    simp only [out.eq_def,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
      LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact Matrix.posSemidef_sum _ fun k _ =>
      (Matrix.posSemidef_vecMulVec_self_star (psi a)).mul_mul_conjTranspose_same _
  have hm : partialTraceRight (out a K) = partialTraceRight (initial a) := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro H
    rw [← trace_mul_kron_one, ← trace_mul_kron_one]
    simp only [out.eq_def,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
      LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_mul,
      Matrix.trace_sum]
    have hsum : (∑ k, H ⊗ₖ ((K k)ᴴ * K k)) = H ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      change (∑ k, (Matrix.kroneckerBilinear (R := ℂ) H) ((K k)ᴴ * K k)) =
        (Matrix.kroneckerBilinear (R := ℂ) H) 1
      rw [← map_sum, hK]
    calc
      _ = ∑ k, trace (initial a * (H ⊗ₖ ((K k)ᴴ * K k))) := by
        apply Finset.sum_congr rfl
        intro k _
        exact D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.trace_conj_kron
          (K k) H (initial a)
      _ = _ := by
        rw [← Matrix.trace_sum, ← Matrix.mul_sum, hsum]
  have hs0 := Real.sq_sqrt ha0
  have hs1 := Real.sq_sqrt (sub_nonneg.mpr ha1)
  have hi : partialTraceRight (initial a) = Matrix.diagonal ![(a : ℂ), 1 - (a : ℂ)] := by
    let S : Matrix (Fin 2) (Fin 2) ℂ :=
      Matrix.diagonal ![(Real.sqrt a : ℂ), (Real.sqrt (1 - a) : ℂ)]
    have hpsi : psi a = Function.uncurry S := by
      funext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.diagonal, psi.eq_def, Function.uncurry]
    have hinit : initial a =
        D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling S := by
      change Matrix.vecMulVec (psi a) (star (psi a)) =
        Matrix.vecMulVec (Function.uncurry S) (star (Function.uncurry S))
      rw [hpsi]
    rw [hinit, D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_pure]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply,
        ← sq, hs0, hs1, Complex.ofReal_sub, ← Complex.ofReal_pow]
  refine ⟨hp, ?_, hm.trans hi⟩
  rw [← trace_partialTraceRight, hm, hi, Matrix.trace_diagonal]
  simp

private lemma output_frame (a : ℝ) (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1)
    {m : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : IsKrausChannel (ι := Fin m) K)
    (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (localConj U V (out a K)).PosSemidef ∧ trace (localConj U V (out a K)) = 1 ∧
      (∑ i, blochA (localConj U V (out a K)) i ^ 2) = (2 * a - 1) ^ 2 := by
  obtain ⟨hp, htr, hm⟩ := out_state a (by linarith) ha1.le K hK
  have hUV := Matrix.kronecker_mem_unitary hU hV
  have ht : trace (localConj U V (out a K)) = 1 := by
    have h := Matrix.trace_units_conj (Unitary.toUnits ⟨U ⊗ₖ V, hUV⟩) (out a K)
    change trace ((U ⊗ₖ V) * out a K * star (U ⊗ₖ V)) = trace (out a K) at h
    simpa only [localConj.eq_1, Matrix.star_eq_conjTranspose, htr] using h
  have hpos : (localConj U V (out a K)).PosSemidef := hp.mul_mul_conjTranspose_same _
  refine ⟨hpos, ht, ?_⟩
  let M := partialTraceRight (localConj U V (out a K))
  have hM : M = U * Matrix.diagonal ![(a : ℂ), 1 - (a : ℂ)] * Uᴴ := by
    dsimp only [M]
    rw [localConj.eq_def]
    rw [D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_right
      (out a K) U V (Matrix.mem_unitaryGroup_iff'.mp hV), hm]
  have htM : trace M = 1 := (trace_partialTraceRight _).trans ht
  have he := matrix_energy M (partialTraceRight_posSemidef hpos).isHermitian
  rw [htM, Complex.one_re] at he
  rw [← blochVec_eq_bloch M (partialTraceRight_posSemidef hpos).isHermitian,
    EuclideanSpace.real_norm_sq_eq] at he
  dsimp only [M] at he
  simp only [blochVec.eq_def, ← trace_mul_kron_one] at he
  have hs : trace (M * M) = (a : ℂ) ^ 2 + (1 - (a : ℂ)) ^ 2 := by
    let D := Matrix.diagonal ![(a : ℂ), 1 - (a : ℂ)]
    rw [hM]
    change trace ((U * D * Uᴴ) * (U * D * Uᴴ)) = _
    calc
      _ = trace (U * (D * D) * Uᴴ) := by
        have hu : Uᴴ * U = 1 := by
          simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
        congr 1
        calc
          _ = U * D * (Uᴴ * U) * D * Uᴴ := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = trace (D * D) := by
        have h := Matrix.trace_units_conj (Unitary.toUnits ⟨U, hU⟩) (D * D)
        change trace (U * (D * D) * star U) = trace (D * D) at h
        simpa only [Matrix.star_eq_conjTranspose] using h
      _ = _ := by
        simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
        ring
  rw [trace_mul_kron_one] at he
  change 2 * (trace (M * M)).re = 1 ^ 2 +
    ∑ i, blochA (localConj U V (out a K)) i ^ 2 at he
  rw [hs] at he
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.sub_im, pow_two, mul_zero,
    sub_zero] at he
  try simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re] at he
  simp only [← sq] at he
  nlinarith only [he]

private def projector (n : Fin 3 → ℝ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (s : ℂ) • spin n)

private def swapOp : TwoQubit :=
  Matrix.swap ℂ (0, 1) (1, 0)

private lemma projector_facts (n : Fin 3 → ℝ) (hn : ∑ i, n i ^ 2 = 1)
    (s : ℝ) (hs : s ^ 2 = 1) :
    (projector n s).IsHermitian ∧ projector n s * projector n s = projector n s := by
  have hnorm : ‖(WithLp.toLp 2 (fun i => s * n i) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have he : ‖(WithLp.toLp 2 (fun i => s * n i) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [mul_pow, ← Finset.mul_sum, hn, hs, mul_one]
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => s * n i) : EuclideanSpace ℝ (Fin 3))]
  have hpp := D5.S3.Quantum.Information.ActualQubitChordObstruction.pure _ hnorm
  constructor
  · rw [projector.eq_def]
    apply Matrix.IsHermitian.smul _ (by simp [IsSelfAdjoint])
    apply Matrix.IsHermitian.add Matrix.isHermitian_one
    apply Matrix.IsHermitian.smul _ (by simp [IsSelfAdjoint])
    rw [spin]
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    apply isSelfAdjoint_sum
    intro i _
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    apply Matrix.IsHermitian.smul _ (by simp [IsSelfAdjoint])
    fin_cases i
    · exact pauli_hermitian .X
    · exact pauli_hermitian .Y
    · exact pauli_hermitian .Z
  · ext i j
    have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hpp
    fin_cases i <;> fin_cases j <;>
      simp [projector.eq_def, spin, sigma, pauliMatrix.eq_2, pauliMatrix.eq_3, pauliMatrix.eq_4,
        qubitX, qubitZ, blochMatrix,
        Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] at hij ⊢ <;>
      linear_combination hij

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Tensor bilinearity expands the Pauli expectation into nine scalar terms.
private lemma projection_trace (ρ : TwoQubit) (htr : trace ρ = 1)
    (n : Fin 3 → ℝ) (hn : ∑ i, n i ^ 2 = 1) (t s u : ℝ)
    (hT : corr ρ = fun i j => if i = j then -t else 0) :
    (trace (ρ * (projector n s ⊗ₖ projector n u))).re =
      (1 + s * (∑ i, n i * blochA ρ i) + u * (∑ i, n i * blochB ρ i) - s * u * t) / 4 := by
  simp only [projector.eq_def, spin, Fin.sum_univ_three]
  change (trace (ρ *
    (((1 / 2 : ℂ) • (1 + (s : ℂ) •
      ((n 0 : ℂ) • pauli 0 + (n 1 : ℂ) • pauli 1 + (n 2 : ℂ) • pauli 2))) ⊗ₖ
     ((1 / 2 : ℂ) • (1 + (u : ℂ) •
      ((n 0 : ℂ) • pauli 0 + (n 1 : ℂ) • pauli 1 + (n 2 : ℂ) • pauli 2)))))).re = _
  simp only [add_kronecker, kronecker_add, smul_kronecker, kronecker_smul,
    Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul,
    one_kronecker_one, Matrix.mul_one, htr]
  norm_num only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, sub_zero, add_zero,
    div_zero, zero_div]
  simp only [← corr.eq_def, ← blochA.eq_def, ← blochB.eq_def, hT, ↓reduceIte]
  simp only [Fin.sum_univ_three] at hn
  norm_num [Fin.ext_iff]
  linear_combination -(s * u * t / 4) * hn

private lemma trace_cauchy_schwarz (ρ X Y : TwoQubit) (hρ : ρ.PosSemidef) :
    Complex.normSq (trace (ρ * (Xᴴ * Y))) ≤
      (trace (ρ * (Xᴴ * X))).re * (trace (ρ * (Yᴴ * Y))).re := by
  let _ := ρ.toMatrixSeminormedAddCommGroup hρ
  let _ := ρ.toMatrixInnerProductSpace hρ
  have e (A B : TwoQubit) : inner ℂ A B = trace (ρ * (Aᴴ * B)) := by
    change trace (B * ρ * Aᴴ) = _
    rw [trace_mul_cycle, trace_mul_comm]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) X Y
  rw [norm_inner_symm (𝕜 := ℂ) Y X, ← sq, ← Complex.normSq_eq_norm_sq] at h
  simpa only [e, RCLike.re_to_complex] using h

set_option maxHeartbeats 2000000 in
-- The sixteen matrix entries reduce to the unit-vector identity.
private lemma swap_projection_identity (n : Fin 3 → ℝ) (hn : ∑ i, n i ^ 2 = 1) :
    (4 : ℂ) • ((projector n 1 ⊗ₖ projector n (-1)) * swapOp) =
      (∑ i, pauli i ⊗ₖ pauli i) - spin n ⊗ₖ spin n + Complex.I •
        ((n 0 : ℂ) • (pauli 2 ⊗ₖ pauli 1 - pauli 1 ⊗ₖ pauli 2) +
         (n 1 : ℂ) • (pauli 0 ⊗ₖ pauli 2 - pauli 2 ⊗ₖ pauli 0) +
         (n 2 : ℂ) • (pauli 1 ⊗ₖ pauli 0 - pauli 0 ⊗ₖ pauli 1)) := by
  simp only [Fin.sum_univ_three] at hn
  ext ⟨i, b⟩ ⟨j, c⟩
  fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;> apply Complex.ext <;>
    norm_num [projector.eq_def, swapOp.eq_def, Matrix.swap, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, Equiv.swap_apply_def, spin, sigma, pauli.eq_def,
      pauliMatrix.eq_2, pauliMatrix.eq_3, pauliMatrix.eq_4, qubitX, qubitZ,
      Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Complex.mul_re, Complex.mul_im] <;>
    nlinarith only [hn]

private lemma swap_projection_trace (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (n : Fin 3 → ℝ) (hn : ∑ i, n i ^ 2 = 1) (t : ℝ)
    (hT : corr ρ = fun i j => if i = j then -t else 0) :
    trace (ρ * ((projector n 1 ⊗ₖ projector n (-1)) * swapOp)) = ((-t / 2 : ℝ) : ℂ) := by
  have hE (i j : Fin 3) :
      trace (ρ * (pauli i ⊗ₖ pauli j)) = ((if i = j then -t else 0 : ℝ) : ℂ) := by
    rw [D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.trace_pauli_kronecker_eq_corr ρ hρ,
      hT]
  have hN : trace (ρ * (spin n ⊗ₖ spin n)) = (-t : ℂ) := by
    simp only [spin, Fin.sum_univ_three]
    change trace (ρ *
      (((n 0 : ℂ) • pauli 0 + (n 1 : ℂ) • pauli 1 + (n 2 : ℂ) • pauli 2) ⊗ₖ
       ((n 0 : ℂ) • pauli 0 + (n 1 : ℂ) • pauli 1 + (n 2 : ℂ) • pauli 2))) = _
    simp only [add_kronecker, kronecker_add, smul_kronecker, kronecker_smul,
      Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul, hE]
    norm_num [Fin.ext_iff]
    have hn' : (n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2 = 1 := by
      exact_mod_cast (by simpa only [Fin.sum_univ_three] using hn)
    linear_combination - (t : ℂ) * hn'
  have h := congrArg (fun M : TwoQubit => trace (ρ * M)) (swap_projection_identity n hn)
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, trace_add, trace_sub, trace_smul,
    Fin.sum_univ_three, smul_eq_mul, hE, hN] at h
  norm_num [Fin.ext_iff] at h
  push_cast
  linear_combination h / 4

private lemma swap_kronecker (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    swapOp * (P ⊗ₖ Q) * swapOp = Q ⊗ₖ P := by
  ext ⟨i, b⟩ ⟨j, c⟩
  fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
    simp [swapOp.eq_def, Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix,
      Equiv.swap_apply_def, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      mul_comm]

private def damping (γ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![(Real.sqrt (1 - γ) : ℂ), 0; 0, 1], !![0, 0; (Real.sqrt γ : ℂ), 0]]

private lemma damping_channel (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsKrausChannel (ι := Fin 2) (damping γ) := by
  have hs0 := Real.sq_sqrt hγ0
  have hs1 := Real.sq_sqrt (sub_nonneg.mpr hγ1)
  unfold IsKrausChannel
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [damping.eq_def, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.of_apply, Matrix.one_apply, Complex.star_def]
  all_goals norm_num [hs0, hs1]
  all_goals nlinarith only [hs0, hs1]

private lemma damping_nonunital (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    NonUnital (damping γ) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hγ1)
  rw [NonUnital.eq_def]
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  simp only [damping.eq_def, Fin.sum_univ_two, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply, map_zero, Complex.star_def,
    Complex.conj_ofReal, Complex.add_re, ← sq] at he
  norm_num [← Complex.ofReal_pow, hs] at he
  linarith

set_option maxHeartbeats 2000000 in
-- The nine correlation entries include the explicit Kraus and Pauli products.
private lemma damping_useful (a t γ : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (ht : (1 / 3 : ℝ) < t)
    (hzz : 1 - 2 * a * γ = t) (hxy : 4 * a * (1 - a) * (1 - γ) = t ^ 2) :
    UsefulUQT (out a (damping γ)) := by
  have hs0 := Real.sq_sqrt ha0
  have hs1 := Real.sq_sqrt (sub_nonneg.mpr ha1)
  have hsγ := Real.sq_sqrt (sub_nonneg.mpr hγ1)
  have hsγ0 := Real.sq_sqrt hγ0
  have hcross : 2 * Real.sqrt a * Real.sqrt (1 - a) * Real.sqrt (1 - γ) = t := by
    have hnon : 0 ≤ 2 * Real.sqrt a * Real.sqrt (1 - a) * Real.sqrt (1 - γ) := by
      positivity
    have hs : (2 * Real.sqrt a * Real.sqrt (1 - a) * Real.sqrt (1 - γ)) ^ 2 = t ^ 2 := by
      calc
        _ = 4 * (Real.sqrt a) ^ 2 * (Real.sqrt (1 - a)) ^ 2 *
            (Real.sqrt (1 - γ)) ^ 2 := by ring
        _ = _ := by rw [hs0, hs1, hsγ]; exact hxy
    nlinarith
  ring_nf at hcross
  rw [UsefulUQT.eq_def]
  refine ⟨1, pauli 1, t, (Matrix.unitaryGroup (Fin 2) ℂ).one_mem, ?_, ht, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    change (pauliMatrix Pauli.Y)ᴴ * pauliMatrix Pauli.Y = 1
    rw [pauli_hermitian, letter_mul]
    simp [D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterPhase,
      D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterProduct,
      pauliMatrix.eq_1]
  · simp only [out.eq_def,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
      LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      initial.eq_def, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [corr.eq_def, psi.eq_def, damping.eq_def,
        pauli.eq_def, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply, Pi.star_apply, ← sq,
        Matrix.kronecker_apply, Matrix.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply, Matrix.diag_apply,
        Complex.star_def] <;>
      norm_num [pauliMatrix.eq_2, pauliMatrix.eq_3, pauliMatrix.eq_4,
        qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im, ← sq, hs0, hs1, hsγ] <;>
      ring_nf <;>
      norm_num [← Complex.ofReal_pow, hs0, hs1, hsγ, hsγ0] <;>
      nlinarith only [hcross, hzz]

private lemma sufficient_two (a : ℝ) (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1)
    (hC : Cstar < conc a) :
    ∃ K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      IsKrausChannel (ι := Fin 2) K ∧ NonUnital K ∧ UsefulUQT (out a K) := by
  let r := 2 * a - 1
  let t := tmax r
  let γ := (1 - t) / (1 + r)
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨ht, ht1, he⟩ := tmax_properties r hr hr1 ((concurrence_threshold a ha ha1).mp hC)
  have hγ0 : 0 < γ := div_pos (sub_pos.mpr ht1) (by linarith)
  have hγ1 : γ < 1 := by
    apply (div_lt_one (show 0 < 1 + r by linarith)).mpr
    linarith
  have hzz : 1 - 2 * a * γ = t := by
    dsimp [γ]
    field_simp
    dsimp [r]
    ring
  have hxy : 4 * a * (1 - a) * (1 - γ) = t ^ 2 := by
    dsimp [γ]
    change 4 * a * (1 - a) * (1 - (1 - t) / (1 + r)) = (tmax r) ^ 2
    rw [he]
    field_simp
    dsimp [r]
    ring
  exact ⟨damping γ, damping_channel γ hγ0.le hγ1.le,
    damping_nonunital γ hγ0 hγ1.le,
    damping_useful a t γ (by linarith) ha1.le hγ0.le hγ1.le ht hzz hxy⟩

private lemma normalize_bloch (v : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r)
    (hv : ∑ i, v i ^ 2 = r ^ 2) :
    (∑ i, (v i / r) ^ 2 = 1) ∧ (∑ i, (v i / r) * v i = r) := by
  constructor
  · simp only [div_pow, ← Finset.sum_div, hv]
    exact div_self (pow_ne_zero _ hr.ne')
  · simp only [div_mul_eq_mul_div, ← sq, ← Finset.sum_div, hv]
    field_simp

private lemma isotropic_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hA : ∑ i, blochA ρ i ^ 2 = r ^ 2)
    (hT : corr ρ = fun i j => if i = j then -t else 0) :
    r ^ 2 + r * t + t ^ 2 ≤ r + t := by
  let n : Fin 3 → ℝ := fun i => blochA ρ i / r
  let β := ∑ i, n i * blochB ρ i
  obtain ⟨hn, han⟩ := normalize_bloch (blochA ρ) r hr hA
  obtain ⟨hpH, hpp⟩ := projector_facts n hn 1 (by norm_num)
  obtain ⟨hmH, hmm⟩ := projector_facts n hn (-1) (by norm_num)
  let A := projector n 1 ⊗ₖ projector n (-1)
  let B := projector n (-1) ⊗ₖ projector n 1
  have hAH : A.IsHermitian := isHermitian_kronecker hpH hmH
  have hAA : A * A = A := by
    dsimp only [A]
    rw [← mul_kronecker_mul, hpp, hmm]
  have hcorner : 0 ≤ (trace (ρ * (projector n (-1) ⊗ₖ projector n (-1)))).re := by
    apply RHLinalg.trace_mul_nonneg_of_posSemidef hρ
    apply Matrix.PosSemidef.kronecker
    all_goals
      simpa only [hmH.eq, hmm] using Matrix.posSemidef_conjTranspose_mul_self (projector n (-1))
  have hXX : Aᴴ * A = A := by rw [hAH.eq, hAA]
  have hXY : Aᴴ * (A * swapOp) = A * swapOp := by
    rw [hAH.eq, ← Matrix.mul_assoc, hAA]
  have hYY : (A * swapOp)ᴴ * (A * swapOp) = B := by
    rw [Matrix.conjTranspose_mul, hAH.eq]
    rw [show swapOpᴴ = swapOp from Matrix.conjTranspose_swap _ _]
    rw [Matrix.mul_assoc swapOp A, ← Matrix.mul_assoc A,
      hAA, ← Matrix.mul_assoc]
    exact swap_kronecker _ _
  have hminor := trace_cauchy_schwarz ρ A (A * swapOp) hρ
  rw [hXX, hXY, hYY] at hminor
  dsimp only [A, B] at hminor
  rw [swap_projection_trace ρ hρ.isHermitian n hn t hT] at hminor
  rw [projection_trace ρ htr n hn t 1 (-1) hT,
    projection_trace ρ htr n hn t (-1) 1 hT] at hminor
  rw [projection_trace ρ htr n hn t (-1) (-1) hT] at hcorner
  simp only [neg_mul, one_mul, sub_neg_eq_add] at hcorner hminor
  change 0 ≤ (1 - (∑ i, n i * blochA ρ i) - β - t) / 4 at hcorner
  change Complex.normSq (((-t / 2 : ℝ) : ℂ)) ≤
    ((1 + (∑ i, n i * blochA ρ i) - β + t) / 4) *
    ((1 - (∑ i, n i * blochA ρ i) + β + t) / 4) at hminor
  rw [han] at hminor hcorner
  norm_num [Complex.normSq, pow_two] at hminor
  exact eliminate_beta r t β hr.le ht (by linarith) (by nlinarith only [hminor])

private lemma necessary (a : ℝ) (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1)
    {m : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : IsKrausChannel (ι := Fin m) K)
    (hUQT : UsefulUQT (out a K)) : Cstar < conc a := by
  obtain ⟨U, V, t, hU, hV, ht, hT⟩ := hUQT
  obtain ⟨hp, htr, hA⟩ := output_frame a ha ha1 K hK U V hU hV
  apply (concurrence_threshold a ha ha1).mpr
  exact r_lt_critical (2 * a - 1) t ht
    (isotropic_bound (localConj U V (out a K)) hp htr (2 * a - 1) t
      (by linarith) (by linarith) hA hT)

theorem result : claim := by
  rw [claim.eq_def]
  intro a ha ha1
  constructor
  · intro m K hK hUQT
    exact necessary a ha ha1 K hK hUQT
  · intro hC
    obtain ⟨K, hK⟩ := sufficient_two a ha ha1 hC
    exact ⟨2, K, hK⟩

end D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
