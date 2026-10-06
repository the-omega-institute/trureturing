/- GID: D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.claim; result=D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.result; claim=D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.claim
   digest: A one-way LOCC channel strictly increases the binegativity of a two-qubit state. -/

/-
proof_shape: IsOneWayLOCC: definition (finite Alice instrument and conditional Bob channels)
proof_shape: claim: definition (the published universal monotonicity assertion)
proof_shape: result: bind-only (local positive/negative decomposition certificates,
  CFC.posPart_negPart_unique, finite Kraus normalization and square-root bounds)
escape_witness: none (the external named open-problem settlement supplies the admission)
admission_basis: open-problem-resolution (#12908; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.binegativity
    sha256:9449842909ab95d05ba0709c34fd9c49e4d2c3a91f1953cc5cf54a25e4756afd
  D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.vec4
    sha256:535a734670ec2b94c7ec30551e01ee87675a32bf1d9448a33d50bff2a62642a1
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB
    sha256:894491a0350c31f846bcfc59cbb3e13f12eb0801f6a00517db381f0dc0ecc393
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity
    sha256:0386217fa1109c4358c01b5fe2db195888fa2f776c05e63cec2e880416d1c8ff
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TwoQubitBinegativityMonotonicityRefutation

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity)
open D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation
  (binegativity vec4)

/-- A finite one-way LOCC channel: Alice's complete instrument, followed by a complete
Bob channel conditioned on her outcome, with the outcomes forgotten. -/
def IsOneWayLOCC
    (E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∃ (n : ℕ) (m : Fin n → ℕ)
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (B : (i : Fin n) → Fin (m i) → Matrix (Fin 2) (Fin 2) ℂ),
    (∑ i, (A i)ᴴ * A i) = 1 ∧
    (∀ i, (∑ j, (B i j)ᴴ * B i j) = 1) ∧
    ∀ σ, E σ = ∑ i, ∑ j, (A i ⊗ₖ B i j) * σ * (A i ⊗ₖ B i j)ᴴ

/-- Girard and Gour's binegativity monotonicity conjecture, restricted to finite
one-way LOCC channels on two qubits. -/
def claim : Prop :=
  ∀ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsDensity σ →
    ∀ E, IsOneWayLOCC E → binegativity (E σ) ≤ binegativity σ

set_option maxHeartbeats 4000000 in
/-- The local filter diag(1/2,1), with Bob resetting to |1> on its failure outcome,
increases binegativity on (3/4)|00><00| + (1/4)|psi+><psi+|. -/
theorem result : ¬ claim := by
  classical
  intro hclaim
  let R : ℝ → ℝ → ℝ → ℝ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    fun a b c z => Matrix.of fun x =>
      ![![vec4 a 0 0 0, vec4 0 b z 0], ![vec4 0 z c 0, vec4 0 0 0 0]] x.1 x.2
  have psd : ∀ v : Fin 2 × Fin 2 → ℂ, (vecMulVec v (star v)).PosSemidef :=
    posSemidef_vecMulVec_self_star
  have evaluation (a b c z D : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hz : 0 < z) (hD : 0 < D) (haD : a < D)
      (hsq : D ^ 2 = a ^ 2 + 4 * z ^ 2) :
      binegativity (R a b c z) = (D - a) / 2 + z * (D - a) / D := by
    let N := ((1 / (4 * D) : ℝ) : ℂ) • vecMulVec (vec4 (a-D) 0 0 (2*z)) (star (vec4 (a-D) 0 0 (2*z)))
    let P := ((1 / (4 * D) : ℝ) : ℂ) •
        vecMulVec (vec4 (a+D) 0 0 (2*z)) (star (vec4 (a+D) 0 0 (2*z))) +
      (b : ℂ) • vecMulVec (vec4 0 1 0 0) (star (vec4 0 1 0 0)) +
      (c : ℂ) • vecMulVec (vec4 0 0 1 0) (star (vec4 0 0 1 0))
    let k := z * (D-a) / (2*D)
    let N₂ := ((k/2 : ℝ) : ℂ) • vecMulVec (vec4 0 1 1 0) (star (vec4 0 1 1 0))
    let P₂ := (((a-D)^2/(4*D) : ℝ) : ℂ) •
        vecMulVec (vec4 1 0 0 0) (star (vec4 1 0 0 0)) +
      ((z^2/D : ℝ) : ℂ) • vecMulVec (vec4 0 0 0 1) (star (vec4 0 0 0 1)) +
      ((k/2 : ℝ) : ℂ) • vecMulVec (vec4 0 1 (-1) 0) (star (vec4 0 1 (-1) 0))
    have hDn : D ≠ 0 := ne_of_gt hD
    have hk : 0 ≤ k := le_of_lt (div_pos (mul_pos hz (sub_pos.mpr haD)) (by positivity))
    have hP : P.PosSemidef :=
      (((psd _).smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1/(4*D)))).add
        ((psd _).smul (by exact_mod_cast hb))).add ((psd _).smul (by exact_mod_cast hc))
    have hN : N.PosSemidef :=
      (psd _).smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1/(4*D)))
    have hP₂ : P₂.PosSemidef :=
      (((psd _).smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ (a-D)^2/(4*D)))).add
        ((psd _).smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ z^2/D)))).add
        ((psd _).smul (by exact_mod_cast (div_nonneg hk (by norm_num : (0:ℝ) ≤ 2))))
    have hN₂ : N₂.PosSemidef :=
      (psd _).smul (by exact_mod_cast (div_nonneg hk (by norm_num : (0:ℝ) ≤ 2)))
    have e1 : partialTransposeB (R a b c z) = P - N := by
      ext ⟨i,j⟩ ⟨l,m⟩
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
        apply Complex.ext <;>
        simp [R, partialTransposeB, P, N, vec4, vecMulVec_apply, Matrix.of_apply,
          Complex.mul_re, Complex.mul_im, Complex.inv_re,
          Complex.inv_im, Complex.normSq_ofReal] <;> field_simp [hDn] <;> ring
    have orth : star (vec4 (a+D) 0 0 (2*z)) ⬝ᵥ vec4 (a-D) 0 0 (2*z) = 0 := by
      apply Complex.ext <;>
        simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, vec4,
          map_ofNat, Complex.mul_re, Complex.mul_im] <;> nlinarith [hsq]
    have e2 : P * N = 0 := by
      simp only [P, N, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
        vecMulVec_mul_vecMulVec, orth]
      simp [dotProduct, vec4, Fintype.sum_prod_type, Fin.sum_univ_two]
    have e3 : partialTransposeB N = P₂ - N₂ := by
      ext ⟨i,j⟩ ⟨l,m⟩
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
        apply Complex.ext <;>
        simp [partialTransposeB, P₂, N₂, N, k, vec4, vecMulVec_apply,
          pow_two, Complex.mul_re, Complex.mul_im, Complex.inv_re,
          Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_ofReal] <;> field_simp [hDn] <;> ring
    have e4 : P₂ * N₂ = 0 := by
      ext ⟨i,j⟩ ⟨l,m⟩
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
        simp [P₂, N₂, vec4, vecMulVec_apply, Matrix.mul_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two, map_neg]
    have neg1 : (partialTransposeB (R a b c z))⁻ = N :=
      (CFC.posPart_negPart_unique e1 e2 hP.nonneg hN.nonneg).2
    have neg2 : (partialTransposeB N)⁻ = N₂ :=
      (CFC.posPart_negPart_unique e3 e4 hP₂.nonneg hN₂.nonneg).2
    rw [binegativity, neg1, neg2]
    simp [N, N₂, k, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two,
      vec4, vecMulVec_apply, map_ofNat]
    simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul]
    simp [Complex.div_re, Complex.normSq_ofReal]
    field_simp [hDn]
    nlinarith [hsq]
  have hs10 : (Real.sqrt 10)^2 = 10 := Real.sq_sqrt (by norm_num)
  have hs13 : (Real.sqrt 13)^2 = 13 := Real.sq_sqrt (by norm_num)
  have h10lo : 3 < Real.sqrt 10 := by nlinarith [Real.sqrt_nonneg 10]
  have h13lo : 3 < Real.sqrt 13 := by nlinarith [Real.sqrt_nonneg 13]
  have h10 : binegativity (R (3/4) (1/8) (1/8) (1/8)) = -1/4+7*Real.sqrt 10/80 := by
    rw [evaluation _ _ _ _ (Real.sqrt 10/4) (by norm_num) (by norm_num)
      (by norm_num) (by positivity) (by linarith) (by nlinarith)]
    field_simp
    nlinarith [hs10]
  have h13 : binegativity (R (3/16) (11/16) (1/8) (1/16)) = -1/32+7*Real.sqrt 13/416 := by
    rw [evaluation _ _ _ _ (Real.sqrt 13/16) (by norm_num) (by norm_num)
      (by norm_num) (by positivity) (by linarith) (by nlinarith)]
    field_simp
    nlinarith [hs13]
  let ρ := R (3/4) (1/8) (1/8) (1/8)
  have hρ : IsDensity ρ := by
    have e : ρ = (3/4:ℂ) • vecMulVec (vec4 1 0 0 0) (star (vec4 1 0 0 0)) +
        (1/8:ℂ) • vecMulVec (vec4 0 1 1 0) (star (vec4 0 1 1 0)) := by
      ext ⟨i,j⟩ ⟨l,m⟩
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
        norm_num [ρ, R, vec4, vecMulVec_apply, Matrix.of_apply, map_ofNat, map_div₀, map_neg]
    refine ⟨?_, ?_⟩
    · rw [e]; exact ((psd _).smul (by norm_num [Complex.le_def])).add
        ((psd _).smul (by norm_num [Complex.le_def]))
    · norm_num [ρ, R, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, vec4, Matrix.of_apply]
  let A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![diagonal ![1/2,1], diagonal ![((Real.sqrt 3/2:ℝ):ℂ),0]]
  let B : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![![1,0], ![single 1 0 1, single 1 1 1]]
  let E := fun σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ =>
    ∑ i, ∑ j, (A i ⊗ₖ B i j) * σ * (A i ⊗ₖ B i j)ᴴ
  have hs3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hE : IsOneWayLOCC E := by
    refine ⟨2, fun _ => 2, A, B, ?_, ?_, fun _ => rfl⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [A, Fin.sum_univ_two, Matrix.mul_apply, Matrix.diagonal,
          Matrix.conjTranspose_apply, map_ofNat,
          Complex.mul_re, Complex.mul_im] <;> nlinarith [hs3]
    · intro i; fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
        norm_num [B, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, map_ofNat, map_div₀, map_neg,
          Matrix.one_apply]
  have hout : E ρ = R (3/16) (11/16) (1/8) (1/16) := by
    ext ⟨i,j⟩ ⟨l,m⟩
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
      apply Complex.ext <;>
      simp [E, A, B, ρ, R, vec4, Fin.sum_univ_two, Fintype.sum_prod_type,
        Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.diagonal,
        Matrix.single, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        map_ofNat, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs3]
  have key := hclaim ρ hρ E hE
  rw [hout, h13, h10] at key
  have ub : Real.sqrt 10 < 31623/10000 := by nlinarith [Real.sqrt_nonneg 10]
  have lb : 36055/10000 < Real.sqrt 13 := by nlinarith [Real.sqrt_nonneg 13]
  linarith

#print axioms result

end D5.S3.Quantum.Entanglement.TwoQubitBinegativityMonotonicityRefutation
