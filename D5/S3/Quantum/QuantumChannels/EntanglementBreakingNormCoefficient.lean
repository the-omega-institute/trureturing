/- GID: D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The coefficient d(d-1)/2 in the entanglement-breaking norm inequality is optimal. -/

/- Judgement:
   Each declaration below belongs to
   admission_basis: open-problem-resolution (#14492; Proved).
   Definitions have proof_shape: not-applicable; escape_witness: null:
   IsBlochBasis; IsEntanglementBreaking; blochA; blochC; claim; i0; pure0; replacer; vec; frame;
   frameBasis.
   Every theorem has proof_shape: bind-only; escape_witness: null, and each helper is consumed on
   the proof path of result:
   pure0_posSemidef, pure0_trace -> replacer_eb; replacer_apply -> replacer_eb, blochA_replacer,
   blochC_replacer; trace_mul_pure0 -> blochC_replacer, sum_sq_diag;
   inner_vec -> frame_orthonormal, sum_sq_diag; pure0_posSemidef, pure0_trace -> sum_sq_diag;
   frame_orthonormal, card_frame -> frameBasis (definition) -> sum_sq_diag;
   diag_real -> sum_sq_diag; traceNorm_zero -> result;
   replacer_eb, blochA_replacer, blochC_replacer, sum_sq_diag -> result.
   Direct frozen dependencies (GID):
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap;
   D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm and .traceNorm_of_posSemidef;
   D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM.
   computational_content: none for every declaration: the statement concerns every dimension,
   every admissible basis and every real coefficient, with no bounded enumeration, checker,
   numerical reduction or certified fixed instance.
-/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_of_posSemidef)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.QuantumChannels.EntanglementBreakingNormCoefficient

/-- A Hermitian traceless family `λ₁, …, λ_{d²−1}` with `Tr (λᵢ λⱼ) = 2 δᵢⱼ`. -/
def IsBlochBasis (d : ℕ) (lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, (lam i).IsHermitian) ∧ (∀ i, (lam i).trace = 0) ∧
    ∀ i j, (lam i * lam j).trace = if i = j then 2 else 0

/-- Holevo form: `Φ X = Σ_a Tr (E_a X) σ_a` for a POVM `E` and states `σ`. -/
def IsEntanglementBreaking {d : ℕ} (Φ : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (k : ℕ) (E σ : Fin k → Matrix (Fin d) (Fin d) ℂ), IsPOVM E ∧
    (∀ a, (σ a).PosSemidef ∧ (σ a).trace = 1) ∧ ∀ X, Φ X = ∑ a, (E a * X).trace • σ a

/-- The linear part of the Bloch representation, `A i j = Tr (λᵢ Φ λⱼ) / 2`. -/
def blochA {d : ℕ} (lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) : Matrix (Fin (d ^ 2 - 1)) (Fin (d ^ 2 - 1)) ℝ :=
  fun i j => (1 / 2 : ℝ) * (lam i * Φ (lam j)).trace.re

/-- The translation part of the Bloch representation, `c i = Tr (λᵢ Φ (I / d))`. -/
def blochC {d : ℕ} (lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) : Fin (d ^ 2 - 1) → ℝ :=
  fun i => (lam i * Φ ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))).trace.re

/-- No coefficient larger than `d (d − 1) / 2` keeps the inequality valid. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ, IsBlochBasis d lam →
    ∀ B : ℝ, (d : ℝ) * (d - 1) / 2 < B →
      ∃ Φ : MatrixMap (Fin d) (Fin d) ℂ, IsEntanglementBreaking Φ ∧
        ((d : ℝ) - 1) ^ 2 < traceNorm (blochA lam Φ) ^ 2 + B * ∑ i, blochC lam Φ i ^ 2

private def i0 {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- The pure state `|0⟩⟨0|`. -/
private def pure0 {d : ℕ} (hd : 2 ≤ d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single (i0 hd) (i0 hd) 1

/-- The constant channel `X ↦ Tr X · |0⟩⟨0|`. -/
private def replacer {d : ℕ} (hd : 2 ≤ d) : MatrixMap (Fin d) (Fin d) ℂ where
  toFun X := X.trace • pure0 hd
  map_add' X Y := by rw [trace_add, add_smul]
  map_smul' c X := by rw [trace_smul, RingHom.id_apply, smul_eq_mul, mul_smul]

private theorem replacer_apply {d : ℕ} (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    replacer hd X = X.trace • pure0 hd := rfl

private theorem pure0_posSemidef {d : ℕ} (hd : 2 ≤ d) : (pure0 hd).PosSemidef := by
  unfold pure0
  generalize i0 hd = i
  have : Matrix.single i i (1 : ℂ) = vecMulVec (Pi.single i 1) (star (Pi.single i 1)) := by
    ext a b
    simp only [Matrix.single_apply, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp [ha, hb, eq_comm]
  rw [this]
  exact posSemidef_vecMulVec_self_star _

private theorem pure0_trace {d : ℕ} (hd : 2 ≤ d) : (pure0 hd).trace = 1 := by
  simp [pure0, Matrix.trace_single_eq_same]

private theorem trace_mul_pure0 {d : ℕ} (hd : 2 ≤ d) (M : Matrix (Fin d) (Fin d) ℂ) :
    (M * pure0 hd).trace = M (i0 hd) (i0 hd) := by
  rw [pure0, Matrix.trace_mul_single, MulOpposite.op_one, one_smul]

private theorem replacer_eb {d : ℕ} (hd : 2 ≤ d) : IsEntanglementBreaking (replacer hd) := by
  refine ⟨1, fun _ => 1, fun _ => pure0 hd, ⟨fun _ => PosSemidef.one, by simp⟩,
    fun _ => ⟨pure0_posSemidef hd, pure0_trace hd⟩, fun X => ?_⟩
  simp [replacer_apply]

private theorem blochA_replacer {d : ℕ} (hd : 2 ≤ d)
    {lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hlam : IsBlochBasis d lam) :
    blochA lam (replacer hd) = 0 := by
  ext i j
  simp [blochA, replacer_apply, hlam.2.1 j]

private theorem traceNorm_zero (n : ℕ) : traceNorm (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  have h := traceNorm_of_posSemidef (R := ℝ) (PosSemidef.zero (n := Fin n) (R := ℝ))
  simpa using h

private theorem blochC_replacer {d : ℕ} (hd : 2 ≤ d)
    (lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) (i : Fin (d ^ 2 - 1)) :
    blochC lam (replacer hd) i = ((lam i) (i0 hd) (i0 hd)).re := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h1 : replacer hd ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) = pure0 hd := by
    rw [replacer_apply, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
      one_div, inv_mul_cancel₀ hd', one_smul]
  rw [blochC, h1, trace_mul_pure0]

/-- A matrix as a vector of the Hilbert–Schmidt space. -/
private def vec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p : Fin d × Fin d => M p.1 p.2)

private theorem inner_vec {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ) :
    ⟪vec M, vec N⟫_ℂ = (N * Mᴴ).trace := by
  rw [vec, vec, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The identity and the `λᵢ`, normalised for the Hilbert–Schmidt inner product. -/
private def frame {d : ℕ} (lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) :
    Option (Fin (d ^ 2 - 1)) → EuclideanSpace ℂ (Fin d × Fin d)
  | none => ((Real.sqrt d : ℝ) : ℂ)⁻¹ • vec (1 : Matrix (Fin d) (Fin d) ℂ)
  | some i => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • vec (lam i)

private theorem frame_orthonormal {d : ℕ} (hd : 2 ≤ d)
    {lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hlam : IsBlochBasis d lam) :
    Orthonormal ℂ (frame lam) := by
  have hdpos : (0 : ℝ) ≤ d := by positivity
  have hsd : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hdpos]; simp
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  have hd0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hsd
    exact (by exact_mod_cast (show d ≠ 0 by omega) : (d : ℂ) ≠ 0) hsd.symm
  have h20 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hs2; norm_num at hs2
  rw [orthonormal_iff_ite]
  rintro (_ | i) (_ | j)
  · simp only [frame, inner_smul_left, inner_smul_right, inner_vec, map_inv₀, Complex.conj_ofReal,
      conjTranspose_one, mul_one, trace_one, Fintype.card_fin, if_true]
    field_simp
    rw [← hsd]; ring
  · simp only [frame, inner_smul_left, inner_smul_right, inner_vec, conjTranspose_one, mul_one,
      hlam.2.1 j, mul_zero, reduceCtorEq, if_false]
  · simp only [frame, inner_smul_left, inner_smul_right, inner_vec, one_mul, trace_conjTranspose,
      hlam.2.1 i, star_zero, mul_zero, reduceCtorEq, if_false]
  · simp only [frame, inner_smul_left, inner_smul_right, inner_vec, map_inv₀, Complex.conj_ofReal,
      (hlam.1 i).eq, hlam.2.2 j i, Option.some.injEq]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      field_simp
      rw [← hs2]; ring
    · simp [hij, Ne.symm hij]

private theorem card_frame {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card (Option (Fin (d ^ 2 - 1))) =
      Module.finrank ℂ (EuclideanSpace ℂ (Fin d × Fin d)) := by
  rw [finrank_euclideanSpace, Fintype.card_option, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fin]
  have : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [Nat.sub_add_cancel this]
  ring

/-- The normalised family is an orthonormal basis of the Hilbert–Schmidt space. -/
private def frameBasis {d : ℕ} (hd : 2 ≤ d)
    {lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hlam : IsBlochBasis d lam) :
    OrthonormalBasis (Option (Fin (d ^ 2 - 1))) ℂ (EuclideanSpace ℂ (Fin d × Fin d)) :=
  OrthonormalBasis.mk (frame_orthonormal hd hlam)
    ((frame_orthonormal hd hlam).linearIndependent.span_eq_top_of_card_eq_finrank'
      (card_frame hd)).ge

private theorem diag_real {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) (a : Fin d) :
    ‖M a a‖ ^ 2 = (M a a).re ^ 2 := by
  have h : (starRingEnd ℂ) (M a a) = M a a := hM.apply a a
  have him : (M a a).im = 0 := Complex.conj_eq_iff_im.mp h
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
  ring

private theorem sum_sq_diag {d : ℕ} (hd : 2 ≤ d)
    {lam : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hlam : IsBlochBasis d lam) :
    ∑ i, ((lam i) (i0 hd) (i0 hd)).re ^ 2 = 2 * ((d : ℝ) - 1) / d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hP := (frameBasis hd hlam).sum_sq_norm_inner_right (vec (pure0 hd))
  have hnorm : ‖vec (pure0 hd)‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, inner_vec, (pure0_posSemidef hd).isHermitian.eq, trace_mul_pure0]
    simp [pure0]
  have hnone : ‖⟪frame lam none, vec (pure0 hd)⟫_ℂ‖ ^ 2 = 1 / d := by
    simp only [frame, inner_smul_left, inner_vec, conjTranspose_one, mul_one, pure0_trace,
      map_inv₀, Complex.conj_ofReal, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow,
      sq_abs, Real.sq_sqrt hdpos.le, one_div]
  have hsome : ∀ i, ‖⟪frame lam (some i), vec (pure0 hd)⟫_ℂ‖ ^ 2 =
      ((lam i) (i0 hd) (i0 hd)).re ^ 2 / 2 := by
    intro i
    have htr : (pure0 hd * (lam i)ᴴ).trace = (lam i) (i0 hd) (i0 hd) := by
      rw [(hlam.1 i).eq, trace_mul_comm, trace_mul_pure0]
    simp only [frame, inner_smul_left, inner_vec, htr, map_inv₀, Complex.conj_ofReal, norm_mul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), diag_real (hlam.1 i)]
    ring
  have hcoe : ⇑(frameBasis hd hlam) = frame lam := OrthonormalBasis.coe_mk _ _
  rw [Fintype.sum_option, hcoe, hnone, hnorm] at hP
  simp only [hsome] at hP
  rw [← Finset.sum_div] at hP
  field_simp at hP ⊢
  linarith

theorem result : claim := by
  intro d hd lam hlam B hB
  refine ⟨replacer hd, replacer_eb hd, ?_⟩
  rw [blochA_replacer hd hlam, traceNorm_zero]
  simp only [blochC_replacer]
  rw [sum_sq_diag hd hlam]
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (0 : ℝ) < d - 1 := by linarith
  have h2 : (0 : ℝ) < 2 * ((d : ℝ) - 1) / d := by positivity
  have h3 : (d : ℝ) * (d - 1) / 2 * (2 * ((d : ℝ) - 1) / d) = ((d : ℝ) - 1) ^ 2 := by
    field_simp
  have h4 := mul_lt_mul_of_pos_right hB h2
  rw [h3] at h4
  simpa using h4

end D5.S3.Quantum.QuantumChannels.EntanglementBreakingNormCoefficient
