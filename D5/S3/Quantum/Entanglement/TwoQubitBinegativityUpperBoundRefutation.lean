/- GID: D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.claim; result=D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result; claim=D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.claim
   digest: A rank-two two-qubit state has binegativity 1/7 above the conjectured bound 9/65. -/

/-
proof_shape: TwoQubit, binegativity, pureConcurrence, concurrence: definition (two-qubit matrices,
  the binegativity with the frozen partial transposition and Mathlib's negative part, and the
  convex-roof concurrence over pure-state decompositions)
proof_shape: claim: definition (published conjecture, the upper inequality of Eq. (9), read for
  every entangled two-qubit state with the frozen negativity)
proof_shape: vec4, witness: definition (basis vectors and the counterexample state)
proof_shape: rank1, negOne, posOne, negTwo, posTwo: private definition (rank-one matrices and the
  positive and negative parts of the two partial transposes)
proof_shape: result: content (as local steps: both partial transposes split into orthogonal
  positive parts, which identifies the negative parts; the trace of the negative part as the sum
  of the negative eigenvalues, which evaluates the frozen negativity; the convex-roof bound
  C >= 4/13 from the zero 11-entry and the triangle inequality, with a rational decomposition
  showing the set is nonempty; and the comparison with the bound)
escape_witness: result (form (2) of §3.2: the negative parts, the concurrence bound and the strict
  violation are produced by the explicit decompositions and the convex-roof estimate; no existing
  statement gives them)
admission_basis: open-problem-resolution (issue #12432; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.negativity
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.eigenvalues
-/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation

open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity negativity eigenvalues)

/-- Two-qubit matrices, indexed by the pairs `(a, b)` of computational-basis labels. -/
abbrev TwoQubit := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The binegativity `N₂(σ) = Tr[(σ^Γ)₋] + 2 Tr[(((σ^Γ)₋)^Γ)₋]`, with the frozen partial
transposition on the second qubit and the negative part `X₋` of a self-adjoint matrix
(`X = X₊ - X₋`). -/
noncomputable def binegativity (σ : TwoQubit) : ℝ :=
  ((partialTransposeB σ)⁻).trace.re +
    2 * ((partialTransposeB ((partialTransposeB σ)⁻))⁻).trace.re

/-- The concurrence `2 |ψ₀₀ ψ₁₁ - ψ₀₁ ψ₁₀|` of a pure two-qubit state. -/
noncomputable def pureConcurrence (ψ : Fin 2 × Fin 2 → ℂ) : ℝ :=
  2 * ‖ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)‖

/-- The concurrence of a two-qubit state: the infimum of `∑ pᵢ C(ψᵢ)` over the decompositions
`σ = ∑ pᵢ |ψᵢ⟩⟨ψᵢ|` into unit vectors with nonnegative weights. -/
noncomputable def concurrence (σ : TwoQubit) : ℝ :=
  sInf {s | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Fin 2 × Fin 2 → ℂ),
    (∀ i, 0 ≤ p i) ∧ (∀ i, ∑ x, ‖ψ i x‖ ^ 2 = 1) ∧
      σ = ∑ i, (p i : ℂ) • vecMulVec (ψ i) (star (ψ i)) ∧ s = ∑ i, p i * pureConcurrence (ψ i)}

/-- The upper half of the conjectured bound of Girard and Gour (arXiv:1701.02724, Eq. (9)):
`N₂(σ) ≤ (ν/2) (c + ν)² / (c² + ν²)` for every entangled two-qubit state, with `c = C(σ)` and
the negativity `ν = N(σ) = 2 Tr[(σ^Γ)₋]`, which is the frozen `negativity 2` (twice the sum of
the absolute values of the negative eigenvalues of `σ^Γ`). -/
def claim : Prop :=
  ∀ σ : TwoQubit, IsDensity σ → 0 < negativity 2 σ →
    binegativity σ ≤
      negativity 2 σ / 2 * (concurrence σ + negativity 2 σ) ^ 2 /
        (concurrence σ ^ 2 + negativity 2 σ ^ 2)

/-- The vector with coordinates `a, b, c, d` at `00, 01, 10, 11`. -/
def vec4 (a b c d : ℂ) : Fin 2 × Fin 2 → ℂ := fun x => ![![a, b], ![c, d]] x.1 x.2

/-- The counterexample `ρ = (|v⟩⟨v| + 9 |00⟩⟨00|) / 26` with `v = (3, 2, 2, 0)`. -/
noncomputable def witness : TwoQubit :=
  (1 / 26 : ℂ) • (vecMulVec (vec4 3 2 2 0) (star (vec4 3 2 2 0)) +
    (9 : ℂ) • vecMulVec (vec4 1 0 0 0) (star (vec4 1 0 0 0)))

private noncomputable def rank1 (v : Fin 2 × Fin 2 → ℂ) : TwoQubit := vecMulVec v (star v)

private noncomputable def negOne : TwoQubit := (1 / 91 : ℂ) • rank1 (vec4 (-1) 1 1 2)

private noncomputable def posOne : TwoQubit :=
  (64 / 91 : ℂ) • rank1 (vec4 1 (5 / 16) (5 / 16) (3 / 16)) +
    (5 / 52 : ℂ) • rank1 (vec4 0 1 (-3 / 5) (-1 / 5)) +
    (4 / 65 : ℂ) • rank1 (vec4 0 0 1 (-1 / 2))

private noncomputable def negTwo : TwoQubit := (3 / 2366 : ℂ) • rank1 (vec4 2 3 3 (-2))

private noncomputable def posTwo : TwoQubit :=
  (19 / 1183 : ℂ) • rank1 (vec4 1 (-4 / 19) (-4 / 19) (7 / 19)) +
    (75 / 3458 : ℂ) • rank1 (vec4 0 1 (-13 / 25) (18 / 25)) +
    (36 / 2275 : ℂ) • rank1 (vec4 0 0 1 (3 / 2))

set_option maxHeartbeats 4000000 in -- the explicit 4 × 4 matrix identities share this declaration
/-- The upper binegativity bound fails for `witness`: `N = 2/13`, `C ≥ 4/13` and `N₂ = 1/7`,
while the bound is at most `9/65`. -/
theorem result : ¬ claim := by
  intro hclaim
  have psd1 : ∀ v, (rank1 v).PosSemidef := fun v => posSemidef_vecMulVec_self_star v
  -- the first negative part
  have e1 : partialTransposeB witness = posOne - negOne := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [partialTransposeB, witness, posOne, negOne, rank1, vec4, vecMulVec_apply] <;> norm_num
  have e2 : posOne * negOne = 0 := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [posOne, negOne, rank1, vec4, vecMulVec_apply, map_ofNat, map_div₀, map_neg,
        Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num
  have e3 : partialTransposeB negOne = posTwo - negTwo := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [partialTransposeB, posTwo, negOne, negTwo, rank1, vec4, vecMulVec_apply] <;> norm_num
  have e4 : posTwo * negTwo = 0 := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [posTwo, negTwo, rank1, vec4, vecMulVec_apply, map_ofNat, map_div₀, map_neg,
        Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num
  have hQpos : negOne.PosSemidef := (psd1 _).smul (by norm_num [Complex.le_def])
  have hBpos : posOne.PosSemidef :=
    (((psd1 _).smul (by norm_num [Complex.le_def])).add
      ((psd1 _).smul (by norm_num [Complex.le_def]))).add
      ((psd1 _).smul (by norm_num [Complex.le_def]))
  have neg1 : (partialTransposeB witness)⁻ = negOne :=
    (CFC.posPart_negPart_unique e1 e2 (Matrix.nonneg_iff_posSemidef.mpr hBpos)
      (Matrix.nonneg_iff_posSemidef.mpr hQpos)).2
  have neg2 : (partialTransposeB negOne)⁻ = negTwo := by
    have hK : (0 : TwoQubit) ≤ negTwo := by
      rw [Matrix.nonneg_iff_posSemidef]
      exact (psd1 _).smul (by norm_num [Complex.le_def])
    have hB : (0 : TwoQubit) ≤ posTwo := by
      rw [Matrix.nonneg_iff_posSemidef]
      exact (((psd1 _).smul (by norm_num [Complex.le_def])).add
        ((psd1 _).smul (by norm_num [Complex.le_def]))).add
        ((psd1 _).smul (by norm_num [Complex.le_def]))
    exact (CFC.posPart_negPart_unique e3 e4 hB hK).2
  have tr1 : negOne.trace = 1 / 13 := by
    simp [negOne, rank1, vec4, vecMulVec_apply, Matrix.trace, Fintype.sum_prod_type, map_ofNat]
    norm_num
  have tr2 : negTwo.trace = 3 / 91 := by
    simp [negTwo, rank1, vec4, vecMulVec_apply, Matrix.trace, Fintype.sum_prod_type, map_ofNat]
    norm_num
  have hNeg : negativity 2 witness = 2 / 13 := by
    have hA : (partialTransposeB witness).IsHermitian := by
      rw [e1]
      exact (hBpos.1).sub (hQpos.1)
    have htr : ∑ i, (hA.eigenvalues i)⁻ = 1 / 13 := by
      have h := congrArg Complex.re
        (show ((partialTransposeB witness)⁻).trace = ∑ i, ((hA.eigenvalues i)⁻ : ℝ) by
          rw [CFC.negPart_def, cfcₙ_eq_cfc (hf0 := by simp), hA.cfc_eq, IsHermitian.cfc,
            Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
            Matrix.one_mul, Matrix.trace_diagonal]
          simp)
      rw [neg1, tr1] at h
      simpa using h.symm
    have hpart : ∀ x : ℝ, x⁻ = if x < 0 then |x| else 0 := by
      intro x
      split_ifs with h
      · rw [abs_of_neg h]; exact negPart_eq_neg.mpr h.le
      · exact negPart_eq_zero.mpr (not_lt.mp h)
    simp only [negativity, eigenvalues, dif_pos hA, Multiset.filter_map, Multiset.map_map]
    rw [show (((Finset.univ.val.filter ((fun x : ℝ => x < 0) ∘ hA.eigenvalues)).map
        (abs ∘ hA.eigenvalues)).sum) = ∑ i, (hA.eigenvalues i)⁻ by
      simp only [hpart, ← Finset.sum_filter]
      rfl, htr]
    norm_num
  have hBineg : binegativity witness = 1 / 7 := by
    rw [binegativity, neg1, neg2, tr1, tr2]; norm_num
  -- the concurrence is at least `2 |ρ₀₁,₁₀| = 4/13`
  have hConc : 4 / 13 ≤ concurrence witness := by
    apply le_csInf
    · refine ⟨_, 3, ![9 / 13, 1 / 26, 7 / 26],
        ![vec4 (-7 / 9) (-4 / 9) (-4 / 9) 0, vec4 (1 / 3) (-2 / 3) (-2 / 3) 0, vec4 1 0 0 0],
        ?_, ?_, ?_, rfl⟩
      · intro i; fin_cases i <;> norm_num
      · intro i; fin_cases i <;> simp [vec4, Fintype.sum_prod_type] <;> norm_num
      · ext ⟨a, b⟩ ⟨c, d⟩
        fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
          simp [witness, vec4, vecMulVec_apply, Fin.sum_univ_three] <;> norm_num
    · rintro s ⟨k, p, ψ, hp, -, hρ, rfl⟩
      have e11 := congrFun (congrFun hρ (1, 1)) (1, 1)
      have e0110 := congrFun (congrFun hρ (0, 1)) (1, 0)
      simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
        smul_eq_mul] at e11 e0110
      have r11 : witness (1, 1) (1, 1) = 0 := by simp [witness, vec4, vecMulVec_apply]
      have r0110 : witness (0, 1) (1, 0) = 2 / 13 := by
        simp [witness, vec4, vecMulVec_apply]; norm_num
      rw [r11] at e11
      rw [r0110] at e0110
      have hterm : ∀ i, p i * ‖ψ i (1, 1)‖ ^ 2 = 0 := by
        have hsum : ∑ i, p i * ‖ψ i (1, 1)‖ ^ 2 = 0 := by
          have h := congrArg Complex.re e11
          rw [Complex.zero_re, Complex.re_sum] at h
          refine Eq.trans ?_ h.symm
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
            ← Complex.ofReal_mul, Complex.ofReal_re]
        exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
          mul_nonneg (hp i) (sq_nonneg _)).mp hsum |> fun h i => h i (Finset.mem_univ i)
      have hcon : ∀ i, p i * pureConcurrence (ψ i) =
          2 * ‖(p i : ℂ) * (ψ i (0, 1) * star (ψ i (1, 0)))‖ := by
        intro i
        rcases mul_eq_zero.mp (hterm i) with h | h
        · simp [h, pureConcurrence]
        · have h11 : ψ i (1, 1) = 0 := by simpa using h
          simp [pureConcurrence, h11, abs_of_nonneg (hp i)]
          ring
      rw [Finset.sum_congr rfl fun i _ => hcon i, ← Finset.mul_sum]
      have hle := norm_sum_le Finset.univ fun i => (p i : ℂ) * (ψ i (0, 1) * star (ψ i (1, 0)))
      rw [← e0110] at hle
      have hn : ‖(2 / 13 : ℂ)‖ = 2 / 13 := by
        rw [norm_div]; simp
      linarith
  -- the state and the contradiction
  have hPSD : witness.PosSemidef :=
    ((psd1 _).add ((psd1 _).smul (by norm_num [Complex.le_def]))).smul
      (by norm_num [Complex.le_def])
  have hTr : witness.trace = 1 := by
    simp [witness, vec4, vecMulVec_apply, Matrix.trace, Fintype.sum_prod_type, map_ofNat]
    norm_num
  have key := hclaim witness ⟨hPSD, hTr⟩ (by rw [hNeg]; norm_num)
  rw [hBineg, hNeg] at key
  have hpos : 0 < concurrence witness ^ 2 + (2 / 13) ^ 2 := by positivity
  rw [le_div_iff₀ hpos] at key
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * concurrence witness - 2 / 13)
    (by linarith : (0 : ℝ) ≤ concurrence witness - 4 / 13)]

end D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation
