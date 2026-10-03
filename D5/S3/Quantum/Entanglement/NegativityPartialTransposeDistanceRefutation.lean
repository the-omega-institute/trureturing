/- GID: D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.claim; result=D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result; claim=D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.claim
   digest: A two-qutrit state has negativity 1/34 and distance at least 2/51 to the PPT states. -/

/-
proof_shape: claim: definition (published conjecture, Conjecture 1 of arXiv:2111.11887, read for
  every state on C^d ⊗ C^d with the paper's partial-transpose distance and negativity)
proof_shape: witness: definition (the counterexample state)
proof_shape: ptPositive, ptNegative, u₁, u₂, u₃: private definition (the positive and negative
  parts of the partial transpose of the state and three signed-permutation unitaries)
proof_shape: result: bind-only (as local steps: an entrywise rational identity splits the partial
  transpose into positive parts, so traceNorm_add_le and traceNorm_of_posSemidef bound the
  negativity by 1/34; traceNorm_eq_max_re_tr_U at three unitaries, an entrywise trace identity
  and the positivity of two quadratic forms bound the distance to every PPT state below by 2/51)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12452; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB
    sha256:894491a0350c31f846bcfc59cbb3e13f12eb0801f6a00517db381f0dc0ecc393
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity
    sha256:0386217fa1109c4358c01b5fe2db195888fa2f776c05e63cec2e880416d1c8ff
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
    sha256:ec2ace26dd8d3b1f1b18defca9f881e75ab25f3e1a67abd2b14cdc72e2702569
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U
    sha256:3487611db943d93cce4a86af60f6499c8a001bc73fe819953d9bfd08a4e811b1
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le
    sha256:3db8d0cc1aa28c78624e69d989ca938ee9442b2409e1ba0ba39d593ce49d5512
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg
    sha256:d7a81ef774c91a733d963a18aa1a998fd412bb6e352db4f96b70ec875b1b00ec
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef
    sha256:f9f5b54d2f389f80229204551ad9217b56fb75ef8f081925f568f00cccca0db8
-/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.NegativityPartialTransposeDistanceRefutation

open Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity)

/-- Conjecture 1 of Ganardi, Miller, Paterek and Żukowski (arXiv:2111.11887) for states on
`ℂ^d ⊗ ℂ^d`: the infimum over PPT states `σ` of the partial-transpose distance
`d_T(ρ, σ) = ‖ρ^{T_B} - σ^{T_B}‖₁ / 2` is the negativity `N(ρ) = (‖ρ^{T_B}‖₁ - 1) / 2`. -/
def claim : Prop :=
  ∀ (d : ℕ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), IsDensity ρ →
    sInf {t : ℝ | ∃ σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, IsDensity σ ∧
        (partialTransposeB σ).PosSemidef ∧
        t = traceNorm (partialTransposeB ρ - partialTransposeB σ) / 2} =
      (traceNorm (partialTransposeB ρ) - 1) / 2

/-- The counterexample `ρ = R / 34` with
`R = |v⟩⟨v| + 4 (|02⟩⟨02| + |20⟩⟨20| + |12⟩⟨12| + |21⟩⟨21|)` and `v = |00⟩ + |11⟩ + 4 |22⟩`;
the basis vector `|ij⟩` sits at the index `(i, j)`. -/
noncomputable def witness : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 34 : ℂ) •
    (vecMulVec (Function.uncurry ![![1, 0, 0], ![0, 1, 0], ![0, 0, 4]] : Fin 3 × Fin 3 → ℂ)
        (star (Function.uncurry ![![1, 0, 0], ![0, 1, 0], ![0, 0, 4]] : Fin 3 × Fin 3 → ℂ)) +
      diagonal (Function.uncurry ![![0, 0, 4], ![0, 0, 4], ![4, 4, 0]] : Fin 3 × Fin 3 → ℂ))

private noncomputable def ptPositive : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 34 : ℂ) •
    (diagonal (Function.uncurry ![![1, 0, 0], ![0, 1, 0], ![0, 0, 16]] : Fin 3 × Fin 3 → ℂ) +
      (1 / 2 : ℂ) •
        vecMulVec (Function.uncurry ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Fin 3 × Fin 3 → ℂ)
          (star (Function.uncurry ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Fin 3 × Fin 3 → ℂ)) +
      (4 : ℂ) •
        vecMulVec (Function.uncurry ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Fin 3 × Fin 3 → ℂ)
          (star (Function.uncurry ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Fin 3 × Fin 3 → ℂ)) +
      (4 : ℂ) •
        vecMulVec (Function.uncurry ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Fin 3 × Fin 3 → ℂ)
          (star (Function.uncurry ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Fin 3 × Fin 3 → ℂ)))

private noncomputable def ptNegative : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 68 : ℂ) •
    vecMulVec (Function.uncurry ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]] : Fin 3 × Fin 3 → ℂ)
      (star (Function.uncurry ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]] : Fin 3 × Fin 3 → ℂ))

private def u₁ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  diagonal (Function.uncurry ![![-1, -1, 1], ![-1, -1, 1], ![1, 1, -1]] : Fin 3 × Fin 3 → ℂ)

private def u₂ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  -1 +
    vecMulVec (Function.uncurry ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Fin 3 × Fin 3 → ℂ)
      (star (Function.uncurry ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Fin 3 × Fin 3 → ℂ)) +
    vecMulVec (Function.uncurry ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Fin 3 × Fin 3 → ℂ)
      (star (Function.uncurry ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Fin 3 × Fin 3 → ℂ))

private def u₃ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  u₂ + diagonal (Function.uncurry ![![0, 0, 0], ![0, 0, 0], ![0, 0, 2]] : Fin 3 × Fin 3 → ℂ)

set_option maxHeartbeats 4000000 in -- the explicit 9 × 9 matrix identities share this declaration
/-- Conjecture 1 fails for `witness`: its negativity is at most `1/34`, while its
partial-transpose distance to every PPT state is at least `2/51`. -/
theorem result : ¬ claim := by
  intro hclaim
  have psd1 : ∀ v : Fin 3 × Fin 3 → ℂ, (vecMulVec v (star v)).PosSemidef :=
    fun v => posSemidef_vecMulVec_self_star v
  -- the state
  have hρpsd : witness.PosSemidef :=
    ((psd1 _).add (PosSemidef.diagonal (fun x => by
      rcases x with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp))).smul (by norm_num [Complex.le_def])
  have hρtr : witness.trace = 1 := by
    simp [witness, Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      map_ofNat]
    norm_num
  -- the negativity is at most `1/34`
  have hsplit : partialTransposeB witness = ptPositive - ptNegative := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [partialTransposeB, witness, ptPositive, ptNegative, vecMulVec_apply] <;>
      norm_num
  have hPpsd : ptPositive.PosSemidef :=
    (((PosSemidef.diagonal (fun x => by
      rcases x with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp)).add
      ((psd1 _).smul (by norm_num [Complex.le_def]))).add
      ((psd1 _).smul (by norm_num [Complex.le_def]))).add
      ((psd1 _).smul (by norm_num [Complex.le_def])) |>.smul (by norm_num [Complex.le_def])
  have hBpsd : ptNegative.PosSemidef := (psd1 _).smul (by norm_num [Complex.le_def])
  have hPtr : ptPositive.trace = 35 / 34 := by
    simp [ptPositive, Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
    norm_num
  have hBtr : ptNegative.trace = 1 / 34 := by
    simp [ptNegative, Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
    norm_num
  have hN : traceNorm (partialTransposeB witness) ≤ 18 / 17 := by
    have h1 := traceNorm_add_le ptPositive (-ptNegative)
    rw [traceNorm_neg, ← sub_eq_add_neg, ← hsplit] at h1
    have hPt := congrArg Complex.re (traceNorm_of_posSemidef hPpsd)
    change traceNorm ptPositive = (ptPositive.trace).re at hPt
    have hBt := congrArg Complex.re (traceNorm_of_posSemidef hBpsd)
    change traceNorm ptNegative = (ptNegative.trace).re at hBt
    rw [hPtr] at hPt
    rw [hBtr] at hBt
    norm_num at hPt hBt
    linarith
  -- three unitaries
  have hU₁ : u₁ ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [u₁]
  have hU₂ : u₂ ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [u₂, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, vecMulVec_apply,
        Matrix.one_apply]
  have hU₃ : u₃ ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [u₃, u₂, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
        vecMulVec_apply, Matrix.one_apply, map_ofNat, show (-1 : ℂ) + 2 = 1 by norm_num]
  have hT₁ : (u₁ * partialTransposeB witness).trace = -1 / 17 := by
    simp [u₁, partialTransposeB, witness, Matrix.trace, Matrix.mul_apply, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, map_ofNat]
    norm_num
  have hT₂ : (u₂ * partialTransposeB witness).trace = -1 / 17 := by
    simp [u₂, partialTransposeB, witness, Matrix.trace, Matrix.mul_apply, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.one_apply, map_ofNat]
    norm_num
  have hT₃ : (u₃ * partialTransposeB witness).trace = 15 / 17 := by
    simp [u₃, u₂, partialTransposeB, witness, Matrix.trace, Matrix.mul_apply, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.one_apply, map_ofNat]
    norm_num
  -- the witness `u₁ / 3 + u₂ / 6 + u₃ / 2` against a PPT state is at most `1/3`
  have hpair : ∀ σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      2 * (u₁ * partialTransposeB σ).trace + (u₂ * partialTransposeB σ).trace +
          3 * (u₃ * partialTransposeB σ).trace =
        2 * σ.trace -
          2 * (star (Function.uncurry ![![2, 0, 0], ![0, 2, 0], ![0, 0, -1]] :
              Fin 3 × Fin 3 → ℂ) ⬝ᵥ
            σ *ᵥ (Function.uncurry ![![2, 0, 0], ![0, 2, 0], ![0, 0, -1]] :
              Fin 3 × Fin 3 → ℂ)) -
          8 * (star (Function.uncurry ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]] :
              Fin 3 × Fin 3 → ℂ) ⬝ᵥ
            partialTransposeB σ *ᵥ (Function.uncurry ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]] :
              Fin 3 × Fin 3 → ℂ)) := by
    intro σ
    simp [u₁, u₃, u₂, partialTransposeB, Matrix.trace, Matrix.mul_apply, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.one_apply, dotProduct, mulVec, map_ofNat]
    ring
  have hfar : ∀ σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ, IsDensity σ →
      (partialTransposeB σ).PosSemidef →
      4 / 51 ≤ traceNorm (partialTransposeB witness - partialTransposeB σ) := by
    intro σ hσ hσpt
    set X := partialTransposeB witness - partialTransposeB σ
    have hk : ∀ u ∈ unitaryGroup (Fin 3 × Fin 3) ℂ,
        ((u * partialTransposeB witness).trace).re - ((u * partialTransposeB σ).trace).re ≤
          traceNorm X := by
      intro u hu
      have h := (traceNorm_eq_max_re_tr_U X).2 ⟨⟨u, hu⟩, rfl⟩
      simpa [X, Matrix.mul_sub, Matrix.trace_sub] using h
    have h₁ := hk u₁ hU₁
    have h₂ := hk u₂ hU₂
    have h₃ := hk u₃ hU₃
    rw [hT₁] at h₁
    rw [hT₂] at h₂
    rw [hT₃] at h₃
    have hb := (Complex.le_def.mp (hσ.1.dotProduct_mulVec_nonneg
      (Function.uncurry ![![2, 0, 0], ![0, 2, 0], ![0, 0, -1]] : Fin 3 × Fin 3 → ℂ))).1
    have hc := (Complex.le_def.mp (hσpt.dotProduct_mulVec_nonneg
      (Function.uncurry ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]] : Fin 3 × Fin 3 → ℂ))).1
    have hp := congrArg Complex.re (hpair σ)
    have htr := congrArg Complex.re hσ.2
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero, Complex.one_re] at hp htr
    simp only [Complex.zero_re] at hb hc
    norm_num at h₁ h₂ h₃
    linarith
  -- the claim at `witness`
  have hset : (2 : ℝ) / 51 ≤ sInf {t : ℝ | ∃ σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      IsDensity σ ∧ (partialTransposeB σ).PosSemidef ∧
      t = traceNorm (partialTransposeB witness - partialTransposeB σ) / 2} := by
    apply le_csInf
    · refine ⟨_, vecMulVec (Pi.single (0, 0) 1) (star (Pi.single (0, 0) 1)), ⟨psd1 _, ?_⟩, ?_,
        rfl⟩
      · simp [Matrix.trace, vecMulVec_apply, Pi.single_apply]
      · have hfix : partialTransposeB
            (vecMulVec (Pi.single ((0 : Fin 3), (0 : Fin 3)) (1 : ℂ))
              (star (Pi.single ((0 : Fin 3), (0 : Fin 3)) (1 : ℂ)))) =
            vecMulVec (Pi.single (0, 0) 1) (star (Pi.single (0, 0) 1)) := by
          ext ⟨a, b⟩ ⟨c, d⟩
          fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
            simp [partialTransposeB, vecMulVec_apply]
        rw [hfix]
        exact psd1 _
    · rintro t ⟨σ, hσ, hσpt, rfl⟩
      have := hfar σ hσ hσpt
      linarith
  have h := hclaim 3 witness ⟨hρpsd, hρtr⟩
  rw [h] at hset
  linarith

end D5.S3.Quantum.Entanglement.NegativityPartialTransposeDistanceRefutation
