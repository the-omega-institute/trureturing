/- GID: D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.claim; result=D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result; claim=D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.claim
   digest: An asymmetric three-qutrit state lies outside the Allen–Meyer negativity family. -/

import D5.S3.QuantumBounds.NegativityReductionInclusionRefutation
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-!
# Allen–Meyer negativity region

An asymmetric normalized three-qutrit state violates a separating inequality satisfied
by every member of the family in Eq. (13) of arXiv:1502.04807v2.
The imported negativity is half the normalization used in that paper.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 2048

noncomputable section

namespace D5.S3.Quantum.Entanglement.AllenMeyerNegativityRegionRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
  (traceNorm_isometry traceNorm_smul_nonneg)

def pairAB (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => ∑ c, ψ (p.1, p.2, c) * star (ψ (q.1, q.2, c))

def pairAC (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => ∑ b, ψ (p.1, b, p.2) * star (ψ (q.1, b, q.2))

def whole (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × (Fin 3 × Fin 3)) (Fin 3 × (Fin 3 × Fin 3)) ℂ :=
  vecMulVec ψ (star ψ)

def negativityTriple (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) : ℝ × ℝ × ℝ :=
  (negativity (pairAB ψ), negativity (pairAC ψ), negativity (whole ψ))

def familyState (a b c d : ℝ) : Fin 3 × Fin 3 × Fin 3 → ℂ := fun p =>
  if p = (0, 0, 0) then (d : ℂ)
  else if p.1 ≠ 0 ∧ p.2.1 = 0 ∧ p.2.2 = p.1 then (a : ℂ)
  else if p.1 ≠ 0 ∧ p.2.1 = p.1 ∧ p.2.2 = 0 then (b : ℂ)
  else if p.1 ≠ 0 ∧ p.2.1 = p.1 ∧ p.2.2 = p.1 then (c : ℂ)
  else 0

def claim : Prop :=
  ∀ ψ : Fin 3 × Fin 3 × Fin 3 → ℂ, ∑ i, Complex.normSq (ψ i) = 1 →
    ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1 ∧
      negativityTriple (familyState a b c d) = negativityTriple ψ

private theorem psd_sub_bound {n : Type} [Fintype n]
    (P Q : Matrix n n ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    traceNorm (P - Q) ≤ P.trace.re + Q.trace.re := by
  classical
  have hp := congrArg Complex.re (traceNorm_of_posSemidef hP)
  have hq := congrArg Complex.re (traceNorm_of_posSemidef hQ)
  change traceNorm P = P.trace.re at hp
  change traceNorm Q = Q.trace.re at hq
  simpa only [← sub_eq_add_neg, traceNorm_neg, hp, hq] using traceNorm_add_le P (-Q)

private theorem unitary_bound {n : Type} [Fintype n] [DecidableEq n]
    (M U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    (U * M).trace.re ≤ traceNorm M :=
  (traceNorm_eq_max_re_tr_U M).2 ⟨⟨U, hU⟩, rfl⟩

private def schmidtPT (x : Fin 3 → ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then ((x p.1 * x p.2 : ℝ) : ℂ) else 0

private def edge (i j : Fin 3) (s : ℂ) : Fin 3 × Fin 3 → ℂ := fun p =>
  if p = (i, j) then 1 else if p = (j, i) then s else 0

set_option maxHeartbeats 1000000 in
-- The finite positive and negative decompositions have 81 entries.
private theorem schmidt_norm (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    traceNorm (schmidtPT x) = (x 0 + x 1 + x 2) ^ 2 := by
  let D : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    diagonal (fun p => if p.1 = p.2 then ((x p.1 ^ 2 : ℝ) : ℂ) else 0)
  let P := D + ((x 0 * x 1 / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 1 1) +
    ((x 0 * x 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 2 1) +
    ((x 1 * x 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 1 2 1)
  let Q := ((x 0 * x 1 / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 1 (-1)) +
    ((x 0 * x 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 2 (-1)) +
    ((x 1 * x 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 1 2 (-1))
  have hscalar (i j : Fin 3) : (0 : ℂ) ≤ ((x i * x j / 2 : ℝ) : ℂ) := by
    exact_mod_cast div_nonneg (mul_nonneg (hx i) (hx j)) (by norm_num : (0 : ℝ) ≤ 2)
  have hD : D.PosSemidef := by
    apply PosSemidef.diagonal
    intro p
    change 0 ≤ if p.1 = p.2 then ((x p.1 ^ 2 : ℝ) : ℂ) else 0
    split_ifs
    · exact_mod_cast sq_nonneg (x p.1)
    · exact le_rfl
  have hP : P.PosSemidef :=
    ((hD.add ((posSemidef_vecMulVec_self_star _).smul (hscalar 0 1))).add
      ((posSemidef_vecMulVec_self_star _).smul (hscalar 0 2))).add ((posSemidef_vecMulVec_self_star _).smul (hscalar 1 2))
  have hQ : Q.PosSemidef :=
    (((posSemidef_vecMulVec_self_star _).smul (hscalar 0 1)).add
      ((posSemidef_vecMulVec_self_star _).smul (hscalar 0 2))).add ((posSemidef_vecMulVec_self_star _).smul (hscalar 1 2))
  have hsplit : schmidtPT x = P - Q := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [schmidtPT.eq_1, P, Q, D, rankOneDensity, edge.eq_1, vecMulVec_apply,
        Matrix.diagonal, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow] <;> ring
  have htrace : P.trace.re + Q.trace.re = (x 0 + x 1 + x 2) ^ 2 := by
    simp [P, Q, D, Matrix.trace, rankOneDensity, edge.eq_1, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_pow]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  have hupper := psd_sub_bound P Q hP hQ
  rw [← hsplit, htrace] at hupper
  let U : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0
  have hU : U ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff]
    change U * Uᴴ = 1
    ext ⟨i, j⟩ ⟨k, l⟩
    change (∑ r, U (i, j) r * star (U (k, l) r)) = _
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [U, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.one_apply]
  have hcert : (U * schmidtPT x).trace.re = (x 0 + x 1 + x 2) ^ 2 := by
    change (∑ p, ∑ q, U p q * schmidtPT x q p).re = _
    simp [U, schmidtPT.eq_1, Fintype.sum_prod_type, Fin.sum_univ_three]
    ring
  have hlower := unitary_bound (schmidtPT x) U hU
  rw [hcert] at hlower
  exact le_antisymm hupper hlower

set_option maxHeartbeats 1000000 in
-- The rectangular Schmidt embedding is checked before the trace-norm application.
private theorem pure_norm {n : Type} [Fintype n]
    (W : Matrix n (Fin 3) ℝ) (hW : W.transpose * W = 1)
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    traceNorm (partialTranspose (rankOneDensity (fun p : Fin 3 × n =>
      ((x p.1 * W p.2 p.1 : ℝ) : ℂ)))) = (x 0 + x 1 + x 2) ^ 2 := by
  classical
  let V : Matrix (Fin 3 × n) (Fin 3 × Fin 3) ℂ :=
    fun p q => if p.1 = q.1 then (W p.2 q.2 : ℂ) else 0
  have hV : Vᴴ * V = 1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hw := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j l) hW
    change (∑ t, W t j * W t l) = _ at hw
    change (∑ p, star (V p (i, j)) * V p (k, l)) = _
    by_cases hik : i = k
    · subst k
      simp [V, Fintype.sum_prod_type, Matrix.one_apply, ← Complex.ofReal_mul,
        ← Complex.ofReal_sum, hw]
      split_ifs <;> rfl
    · simp [V, Fintype.sum_prod_type, hik, Ne.symm hik, mul_ite]
  have hmatrix : partialTranspose (rankOneDensity (fun p : Fin 3 × n =>
      ((x p.1 * W p.2 p.1 : ℝ) : ℂ))) = V * schmidtPT x * Vᴴ := by
    ext ⟨i, b⟩ ⟨j, d⟩
    change ((x i * W d i : ℝ) : ℂ) * star ((x j * W b j : ℝ) : ℂ) =
      ∑ r : Fin 3 × Fin 3, (∑ t : Fin 3 × Fin 3,
        V (i, b) t * schmidtPT x t r) * star (V (j, d) r)
    fin_cases i <;> fin_cases j <;>
      simp [V, schmidtPT.eq_1, Fintype.sum_prod_type, Fin.sum_univ_three,
        Complex.ofReal_mul] <;> ring
  rw [hmatrix, traceNorm_isometry V hV, schmidt_norm x hx]

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Entanglement.AllenMeyerNegativityRegionRefutation
