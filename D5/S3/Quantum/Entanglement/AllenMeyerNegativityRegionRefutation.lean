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
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
  (traceNorm_isometry traceNorm_smul_nonneg)

def pairAB (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  partialTraceRight (rankOneDensity (fun p : (Fin 3 × Fin 3) × Fin 3 =>
    ψ (p.1.1, p.1.2, p.2)))

def pairAC (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  partialTraceRight (rankOneDensity (fun p : (Fin 3 × Fin 3) × Fin 3 =>
    ψ (p.1.1, p.2, p.1.2)))

private theorem pairAB_entry (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (p q : Fin 3 × Fin 3) :
    pairAB ψ p q = ∑ c, ψ (p.1, p.2, c) * star (ψ (q.1, q.2, c)) := rfl

private theorem pairAC_entry (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (p q : Fin 3 × Fin 3) :
    pairAC ψ p q = ∑ b, ψ (p.1, b, p.2) * star (ψ (q.1, b, q.2)) := rfl

def negativityTriple (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) : ℝ × ℝ × ℝ :=
  (negativity (pairAB ψ), negativity (pairAC ψ), negativity (rankOneDensity ψ))

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

private theorem swap_entry (p q : Fin 3 × Fin 3) :
    ConicalDesignConcurrenceComparability.swap 3 p q =
      if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0 := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  simp [ConicalDesignConcurrenceComparability.swap, Matrix.one_apply, Prod.mk.injEq]

private theorem swap_unitary :
    ConicalDesignConcurrenceComparability.swap 3 ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
  have hperm : ConicalDesignConcurrenceComparability.swap 3 =
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 3) (Fin 3)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [swap_entry, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Prod.mk.injEq, and_comm]
  rw [hperm, mem_unitaryGroup_iff]
  simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]

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
  have hcert : ((ConicalDesignConcurrenceComparability.swap 3) * schmidtPT x).trace.re = (x 0 + x 1 + x 2) ^ 2 := by
    change (∑ p, ∑ q, (ConicalDesignConcurrenceComparability.swap 3) p q * schmidtPT x q p).re = _
    simp [swap_entry, schmidtPT.eq_1, Fintype.sum_prod_type, Fin.sum_univ_three]
    ring
  have hlower := unitary_bound (schmidtPT x) (ConicalDesignConcurrenceComparability.swap 3) swap_unitary
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

private theorem negativity_upper {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (ρ P Q : Matrix (a × b) (a × b) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hsplit : partialTranspose ρ = P - Q)
    (htrace : ρ.trace.re = 1) : 2 * negativity ρ ≤ 2 * Q.trace.re := by
  have h := psd_sub_bound P Q hP hQ
  have ht : (partialTranspose ρ).trace = ρ.trace := by
    rfl
  have ht2 := congrArg Complex.re (congrArg Matrix.trace hsplit)
  rw [ht, Matrix.trace_sub, Complex.sub_re, htrace] at ht2
  rw [← hsplit] at h
  rw [negativity.eq_1]
  linarith

private def single (i j : Fin 3) : Fin 3 × Fin 3 → ℂ := Pi.single (i, j) 1

private def blockVec (j : Fin 3) (x y z : ℝ) : Fin 3 × Fin 3 → ℂ :=
  fun p => if p = (0, j) then (x : ℂ) else if p = (j, 0) then (y : ℂ)
    else if p = (j, j) then (z : ℂ) else 0

private theorem family_pair_trace (a b c d : ℝ) :
    (pairAB (familyState a b c d)).trace.re = d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  simp [pairAB_entry, familyState.eq_1, Matrix.trace, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  ring

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem family_pair_loose (a b c d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hn : d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1) :
    2 * negativity (pairAB (familyState a b c d)) ≤ 2 * b ^ 2 + 4 * b * d := by
  let P := ((d ^ 2 : ℝ) : ℂ) • rankOneDensity (single 0 0) +
    ((b * d / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 1 1) +
    ((b * d / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 2 1) +
    rankOneDensity (blockVec 1 0 a c) + rankOneDensity (blockVec 2 0 a c) +
    ((b ^ 2 : ℝ) : ℂ) • rankOneDensity (single 1 1) +
    ((b ^ 2 : ℝ) : ℂ) • rankOneDensity (single 2 2) +
    ((b ^ 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 1 2 1)
  let Q := ((b * d / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 1 (-1)) +
    ((b * d / 2 : ℝ) : ℂ) • rankOneDensity (edge 0 2 (-1)) +
    ((b ^ 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 1 2 (-1))
  have hbd : (0 : ℂ) ≤ ((b * d / 2 : ℝ) : ℂ) := by
    exact_mod_cast div_nonneg (mul_nonneg hb hd) (by norm_num : (0 : ℝ) ≤ 2)
  have hb2 : (0 : ℂ) ≤ ((b ^ 2 : ℝ) : ℂ) := by exact_mod_cast sq_nonneg b
  have hbhalf : (0 : ℂ) ≤ ((b ^ 2 / 2 : ℝ) : ℂ) := by
    exact_mod_cast div_nonneg (sq_nonneg b) (by norm_num : (0 : ℝ) ≤ 2)
  have hd2 : (0 : ℂ) ≤ ((d ^ 2 : ℝ) : ℂ) := by exact_mod_cast sq_nonneg d
  have hP : P.PosSemidef :=
    ((((((((posSemidef_vecMulVec_self_star _).smul hd2).add ((posSemidef_vecMulVec_self_star _).smul hbd)).add
      ((posSemidef_vecMulVec_self_star _).smul hbd)).add (posSemidef_vecMulVec_self_star _)).add (posSemidef_vecMulVec_self_star _)).add
      ((posSemidef_vecMulVec_self_star _).smul hb2)).add ((posSemidef_vecMulVec_self_star _).smul hb2)).add
      ((posSemidef_vecMulVec_self_star _).smul hbhalf)
  have hQ : Q.PosSemidef :=
    (((posSemidef_vecMulVec_self_star _).smul hbd).add ((posSemidef_vecMulVec_self_star _).smul hbd)).add
      ((posSemidef_vecMulVec_self_star _).smul hbhalf)
  have hsplit : partialTranspose (pairAB (familyState a b c d)) = P - Q := by
    ext ⟨i, j⟩ ⟨k, l⟩
    change pairAB (familyState a b c d) (i, l) (k, j) = _
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [pairAB_entry, familyState.eq_1, P, Q, rankOneDensity,
        single.eq_1, blockVec.eq_1, edge.eq_1, vecMulVec_apply, Fin.sum_univ_three,
        Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow] <;> ring
  have hQt : 2 * Q.trace.re = 2 * b ^ 2 + 4 * b * d := by
    simp [Q, Matrix.trace, rankOneDensity, edge.eq_1, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [← hQt]
  exact negativity_upper _ P Q hP hQ hsplit
    ((family_pair_trace a b c d).trans hn)

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem family_pair_gram (a b c d : ℝ) (ha : 0 < a)
    (hn : d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1) :
    2 * negativity (pairAB (familyState a b c d)) ≤
      2 * b ^ 2 + 4 * (d ^ 2 * (b ^ 2 + c ^ 2) / a ^ 2) := by
  let v := fun j => blockVec j (b * d / a) a c
  let w := fun j => blockVec j (-c * d / a) 0 b
  let z : ℝ := d ^ 2 * (b ^ 2 + c ^ 2) / a ^ 2
  let P := ((d ^ 2 : ℝ) : ℂ) • rankOneDensity (single 0 0) +
    rankOneDensity (v 1) + rankOneDensity (w 1) + rankOneDensity (v 2) + rankOneDensity (w 2) +
    ((b ^ 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 1 2 1)
  let Q := (z : ℂ) • rankOneDensity (single 0 1) + (z : ℂ) • rankOneDensity (single 0 2) +
    ((b ^ 2 / 2 : ℝ) : ℂ) • rankOneDensity (edge 1 2 (-1))
  have hz : (0 : ℂ) ≤ (z : ℂ) := by
    exact_mod_cast div_nonneg (mul_nonneg (sq_nonneg d) (add_nonneg (sq_nonneg b)
      (sq_nonneg c))) (sq_nonneg a)
  have hbhalf : (0 : ℂ) ≤ ((b ^ 2 / 2 : ℝ) : ℂ) := by
    exact_mod_cast div_nonneg (sq_nonneg b) (by norm_num : (0 : ℝ) ≤ 2)
  have hd2 : (0 : ℂ) ≤ ((d ^ 2 : ℝ) : ℂ) := by exact_mod_cast sq_nonneg d
  have hP : P.PosSemidef :=
    ((((((posSemidef_vecMulVec_self_star _).smul hd2).add (posSemidef_vecMulVec_self_star _)).add (posSemidef_vecMulVec_self_star _)).add
      (posSemidef_vecMulVec_self_star _)).add (posSemidef_vecMulVec_self_star _)).add ((posSemidef_vecMulVec_self_star _).smul hbhalf)
  have hQ : Q.PosSemidef :=
    (((posSemidef_vecMulVec_self_star _).smul hz).add ((posSemidef_vecMulVec_self_star _).smul hz)).add
      ((posSemidef_vecMulVec_self_star _).smul hbhalf)
  have hsplit : partialTranspose (pairAB (familyState a b c d)) = P - Q := by
    have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    ext ⟨i, j⟩ ⟨k, l⟩
    change pairAB (familyState a b c d) (i, l) (k, j) = _
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [pairAB_entry, familyState.eq_1, P, Q, v, w, z, rankOneDensity,
        single.eq_1, blockVec.eq_1, edge.eq_1, vecMulVec_apply, Fin.sum_univ_three,
        Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow] <;>
      field_simp (discharger := first | exact hane | exact pow_ne_zero _ hane | norm_num) <;> ring
  have hQt : 2 * Q.trace.re = 2 * b ^ 2 + 4 * (d ^ 2 * (b ^ 2 + c ^ 2) / a ^ 2) := by
    simp [Q, Matrix.trace, rankOneDensity, single.eq_1, edge.eq_1, vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
    dsimp [z]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [← hQt]
  exact negativity_upper _ P Q hP hQ hsplit
    ((family_pair_trace a b c d).trans hn)

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem family_swap (a b c d : ℝ) :
    pairAC (familyState a b c d) = pairAB (familyState b a c d) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  refine (pairAC_entry (familyState a b c d) (i, j) (k, l)).trans
    (Eq.trans ?_ (pairAB_entry (familyState b a c d) (i, j) (k, l)).symm)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [familyState.eq_1, Fin.sum_univ_three]

private theorem separator_algebra (a b c d r x y z : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hrs : r ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (hn : d ^ 2 + 2 * r ^ 2 = 1)
    (hz : z = 4 * d * r + 2 * r ^ 2) (hy : y ≤ 2 * a ^ 2 + 4 * a * d)
    (hx : 0 < a → x ≤ 2 * b ^ 2 + 4 * (d ^ 2 * (b ^ 2 + c ^ 2) / a ^ 2))
    (hzmin : 14 / 11 ≤ z) (hdelta : z - y ≤ 2 / 209) : x ≤ 5 * (z - y) := by
  let u := b ^ 2 + c ^ 2
  have hu : 0 ≤ u := add_nonneg (sq_nonneg b) (sq_nonneg c)
  have hrsu : r ^ 2 = a ^ 2 + u := by dsimp [u]; linarith
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := le_antisymm (not_lt.mp h) hr
    subst r
    norm_num at hz
    linarith
  have hra : a ≤ r := by nlinarith only [hrsu, hu, ha, hr]
  have hdelta0 : 2 * u ≤ z - y := by nlinarith only [hy, hz, hrsu, mul_nonneg hd (sub_nonneg.mpr hra)]
  have hub : u ≤ 1 / 209 := by linarith only [hdelta0, hdelta]
  have hfactor : (7 * d - r) * (d - 3 * r) ≤ 0 := by nlinarith only [hn, hz, hzmin]
  have hdmax : d ≤ 3 * r := by
    by_contra h
    have h1 : 0 < d - 3 * r := sub_pos.mpr (not_le.mp h)
    have h2 : 0 < 7 * d - r := by linarith
    exact (not_lt_of_ge hfactor) (mul_pos h2 h1)
  have hdmin : r ≤ 7 * d := by
    by_contra h
    have h1 : 7 * d - r < 0 := sub_neg.mpr (not_le.mp h)
    have h2 : d - 3 * r < 0 := by linarith
    exact (not_lt_of_ge hfactor) (mul_pos_of_neg_of_neg h1 h2)
  have hdpos : 0 < d := by linarith
  have hrbound : 1 / 11 ≤ r ^ 2 := by
    have hs := mul_self_le_mul_self hd hdmax
    nlinarith only [hs, hn]
  have hur : 19 * u ≤ r ^ 2 := by linarith only [hub, hrbound]
  have ha2 : 18 * r ^ 2 ≤ 19 * a ^ 2 := by linarith only [hur, hrsu]
  have hapos : 0 < a := by nlinarith only [ha, ha2, sq_pos_of_pos hrpos]
  have hgap : u ≤ 2 * r * (r - a) := by nlinarith only [hrsu, sq_nonneg (r - a)]
  have hdelstrong : 2 * u * (r + d) ≤ r * (z - y) := by
    have h1 := mul_nonneg hr (sub_nonneg.mpr hy)
    have h2 := mul_nonneg hd (sub_nonneg.mpr hgap)
    have h3 := congrArg (fun t : ℝ => r * t) hrsu
    rw [hz]
    nlinarith only [h1, h2, h3]
  have hpoly : 19 * d ^ 2 ≤ 36 * r ^ 2 + 45 * d * r := by
    have h := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdmax)
      (show 0 ≤ 19 * d + 12 * r by positivity)
    nlinarith only [h]
  have hfac : 2 * d ^ 2 * r ≤ a ^ 2 * (4 * r + 5 * d) := by
    have h1 := mul_nonneg hr (sub_nonneg.mpr hpoly)
    have h2 := mul_nonneg (show 0 ≤ 4 * r + 5 * d from
      add_nonneg (mul_nonneg (by norm_num) hr) (mul_nonneg (by norm_num) hdpos.le))
      (sub_nonneg.mpr ha2)
    nlinarith only [h1, h2]
  have hxa : x * a ^ 2 ≤ 2 * u * a ^ 2 + 4 * d ^ 2 * u := by
    have hb : b ^ 2 ≤ u := by dsimp [u]; nlinarith [sq_nonneg c]
    have h := mul_le_mul_of_nonneg_right (hx hapos) (sq_nonneg a)
    rw [add_mul, mul_assoc 4, div_mul_cancel₀ _ (pow_ne_zero 2 hapos.ne')] at h
    dsimp [u] at hb ⊢
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hb)]
  have hfinal : x * (a ^ 2 * r) ≤ 5 * (z - y) * (a ^ 2 * r) := by
    have h1 := mul_nonneg hr (sub_nonneg.mpr hxa)
    have h2 := mul_nonneg hu (sub_nonneg.mpr hfac)
    have h3 := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hdelstrong)
    nlinarith only [h1, h2, h3]
  exact (mul_le_mul_iff_left₀ (show 0 < a ^ 2 * r by positivity)).mp hfinal

private def familyFrame (a b c r : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3) ℝ :=
  fun p j => if j = 0 then if p = (0, 0) then 1 else 0
    else if r = 0 then if p = (0, j) then 1 else 0
    else if p = (0, j) then a / r else if p = (j, 0) then b / r
    else if p = (j, j) then c / r else 0

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem family_whole (a b c d : ℝ) (hd : 0 ≤ d)
    (hn : d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1) :
    2 * negativity (rankOneDensity (familyState a b c d)) =
      4 * d * Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  let r := Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrs : r ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hW : (familyFrame a b c r).transpose * familyFrame a b c r = 1 := by
    by_cases hz : r = 0
    · ext i j
      change (∑ p, familyFrame a b c r p i * familyFrame a b c r p j) = _
      fin_cases i <;> fin_cases j <;>
        norm_num [familyFrame.eq_1, hz, Fintype.sum_prod_type,
          Fin.sum_univ_three, Matrix.one_apply]
    · ext i j
      change (∑ p, familyFrame a b c r p i * familyFrame a b c r p j) = _
      fin_cases i <;> fin_cases j <;>
        simp [familyFrame.eq_1, hz, Fintype.sum_prod_type,
          Fin.sum_univ_three]
      all_goals field_simp [hz]
      all_goals nlinarith [hrs]
  have heq : familyState a b c d = fun p : Fin 3 × (Fin 3 × Fin 3) =>
      ((![(d : ℝ), r, r] p.1 * familyFrame a b c r p.2 p.1 : ℝ) : ℂ) := by
    by_cases hz : r = 0
    · have ha : a = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
      have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      subst a b c
      ext ⟨i, j, k⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [familyState.eq_1, familyFrame.eq_1, hz]
    · ext ⟨i, j, k⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [familyState.eq_1, familyFrame.eq_1, hz, mul_div_cancel₀]
  have hnorm := pure_norm (familyFrame a b c r) hW ![d, r, r] (by
    intro i; fin_cases i
    · exact hd
    · exact hr
    · exact hr)
  rw [negativity.eq_1, heq]
  change 2 * ((traceNorm (partialTranspose (rankOneDensity _)) - 1) / 2) = _
  rw [hnorm]
  change 2 * (((d + r + r) ^ 2 - 1) / 2) =
    4 * d * r + 2 * (a ^ 2 + b ^ 2 + c ^ 2)
  nlinarith only [hn, hrs]

private theorem family_separator (a b c d : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hn : d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1)
    (hz : 14 / 11 ≤ 2 * negativity (rankOneDensity (familyState a b c d)))
    (hdelta : 2 * negativity (rankOneDensity (familyState a b c d)) -
      2 * negativity (pairAC (familyState a b c d)) ≤ 2 / 209) :
    2 * negativity (pairAB (familyState a b c d)) ≤
      5 * (2 * negativity (rankOneDensity (familyState a b c d)) -
        2 * negativity (pairAC (familyState a b c d))) := by
  let r := Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)
  have hrs : r ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  apply separator_algebra a b c d r _ _ _ ha hd (Real.sqrt_nonneg _) hrs
    (by nlinarith only [hn, hrs]) (by rw [family_whole a b c d hd hn, hrs]) ?_
    (fun hapos => family_pair_gram a b c d hapos hn) hz hdelta
  rw [family_swap]
  exact family_pair_loose b a c d ha hd (by nlinarith only [hn])

private def witnessRaw : Fin 3 × Fin 3 × Fin 3 → ℂ := fun p =>
  if p = (0, 0, 0) then 5 else if p = (1, 0, 1) then 3
  else if p = (2, 0, 2) then 1 else if p = (1, 1, 0) then 1 / 100
  else if p = (2, 2, 0) then 1 / 20 else 0

private def witness : Fin 3 × Fin 3 × Fin 3 → ℂ :=
  fun p => ((Real.sqrt (175013 / 5000) : ℝ) : ℂ)⁻¹ * witnessRaw p

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem witness_scale :
    pairAB witness = (5000 / 175013 : ℂ) • pairAB witnessRaw ∧
    pairAC witness = (5000 / 175013 : ℂ) • pairAC witnessRaw ∧
    rankOneDensity witness = (5000 / 175013 : ℂ) • rankOneDensity witnessRaw := by
  have hs : (Real.sqrt (175013 / 5000) : ℂ) * Real.sqrt (175013 / 5000) = 175013 / 5000 := by
    rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 175013 / 5000 by norm_num)]
    norm_num
  have hi : (Real.sqrt (175013 / 5000) : ℂ)⁻¹ *
      (Real.sqrt (175013 / 5000) : ℂ)⁻¹ = 5000 / 175013 := by
    rw [← mul_inv, hs]
    norm_num
  have hmul (u v : ℂ) :
      ((Real.sqrt (175013 / 5000) : ℂ)⁻¹ * u) *
          star ((Real.sqrt (175013 / 5000) : ℂ)⁻¹ * v) =
        (5000 / 175013 : ℂ) * (u * star v) := by
    simp only [star_mul]
    calc
      _ = ((Real.sqrt (175013 / 5000) : ℂ)⁻¹ *
        (Real.sqrt (175013 / 5000) : ℂ)⁻¹) * (u * star v) := by simp; ring
      _ = _ := by rw [hi]
  refine ⟨?_, ?_, ?_⟩
  · ext p q
    simp only [pairAB_entry, witness.eq_1, Matrix.smul_apply, smul_eq_mul, hmul,
      Finset.mul_sum]
  · ext p q
    simp only [pairAC_entry, witness.eq_1, Matrix.smul_apply, smul_eq_mul, hmul,
      Finset.mul_sum]
  · ext p q
    simp only [rankOneDensity, witness.eq_1, vecMulVec_apply, Pi.star_apply,
      Matrix.smul_apply, smul_eq_mul, hmul]

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem witness_unit : ∑ i, Complex.normSq (witness i) = 1 := by
  have ht := congrArg (fun M => M.trace.re) witness_scale.2.2
  have hn : (rankOneDensity witness).trace.re = ∑ i, Complex.normSq (witness i) := by
    simp [rankOneDensity, Matrix.trace, vecMulVec_apply, Complex.mul_conj]
  rw [hn] at ht
  norm_num [rankOneDensity, witnessRaw.eq_1, Matrix.trace, vecMulVec_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.trace_smul] at ht
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_three] using ht

private def witnessFrame (r s : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3) ℝ :=
  fun p j => if j = 0 then if p = (0, 0) then 1 else 0
    else if j = 1 then if p = (0, 1) then 3 / r else if p = (1, 0) then (1 / 100) / r else 0
    else if p = (0, 2) then 1 / s else if p = (2, 0) then (1 / 20) / s else 0

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem witness_whole :
    46 ≤ traceNorm (partialTranspose (rankOneDensity witnessRaw)) - 175013 / 5000 ∧
    traceNorm (partialTranspose (rankOneDensity witnessRaw)) - 175013 / 5000 ≤ 460203 / 10000 := by
  let r := Real.sqrt (90001 / 10000)
  let s := Real.sqrt (401 / 400)
  have hr : r ^ 2 = 90001 / 10000 := Real.sq_sqrt (by norm_num)
  have hs : s ^ 2 = 401 / 400 := Real.sq_sqrt (by norm_num)
  have hrlo : 3 ≤ r := by apply Real.le_sqrt_of_sq_le; norm_num
  have hslo : 1 ≤ s := by apply Real.le_sqrt_of_sq_le; norm_num
  have hrhi : r ≤ 180001 / 60000 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hshi : s ≤ 801 / 800 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hrne : r ≠ 0 := by linarith
  have hsne : s ≠ 0 := by linarith
  have hW : (witnessFrame r s).transpose * witnessFrame r s = 1 := by
    ext i j
    change (∑ p, witnessFrame r s p i * witnessFrame r s p j) = _
    fin_cases i <;> fin_cases j <;>
      simp [witnessFrame.eq_1, Fintype.sum_prod_type, Fin.sum_univ_three] <;>
      field_simp [hrne, hsne] <;> nlinarith
  have heq : witnessRaw = fun p : Fin 3 × (Fin 3 × Fin 3) =>
      ((![(5 : ℝ), r, s] p.1 * witnessFrame r s p.2 p.1 : ℝ) : ℂ) := by
    ext ⟨i, j, k⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [witnessRaw.eq_1, witnessFrame.eq_1, hrne, hsne, mul_div_cancel₀]
  have hnorm := pure_norm (witnessFrame r s) hW ![5, r, s] (by
    intro i; fin_cases i <;> simp <;> linarith)
  change 46 ≤ traceNorm (partialTranspose (rankOneDensity witnessRaw)) - 175013 / 5000 ∧
    traceNorm (partialTranspose (rankOneDensity witnessRaw)) - 175013 / 5000 ≤ 460203 / 10000
  simp only [heq, hnorm]
  change 46 ≤ (5 + r + s) ^ 2 - 175013 / 5000 ∧
    (5 + r + s) ^ 2 - 175013 / 5000 ≤ 460203 / 10000
  have hlo : 3 ≤ r * s := by
    simpa only [mul_one] using (mul_le_mul hrlo hslo (by norm_num) (by linarith))
  have hhi : r * s ≤ (180001 / 60000) * (801 / 800) :=
    mul_le_mul hrhi hshi (by linarith) (by norm_num)
  constructor <;> nlinarith

private def reflectionU : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  1 - (32 / 17 : ℂ) • rankOneDensity (fun p =>
    if p = (0, 2) then 1 else if p = (2, 0) then -(1 / 4) else 0) -
    rankOneDensity (edge 1 2 (-1))

set_option maxHeartbeats 1000000 in
-- The finite matrix certificates are expanded entry by entry.
private theorem witness_pairs :
    2 / 17 + 1 / 1000 ≤ traceNorm (partialTranspose (pairAB witnessRaw)) - 175013 / 5000 ∧
    46 - 26 / 10000 ≤ traceNorm (partialTranspose (pairAC witnessRaw)) - 175013 / 5000 := by
  have hU : reflectionU ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff]
    change reflectionU * reflectionUᴴ = 1
    ext ⟨i, j⟩ ⟨k, l⟩
    change (∑ p, reflectionU (i, j) p * star (reflectionU (k, l) p)) = _
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [reflectionU.eq_1, rankOneDensity, edge.eq_1, vecMulVec_apply,
        Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.one_apply]
    all_goals norm_num [map_ofNat]
  have htx : (reflectionU * partialTranspose (pairAB witnessRaw)).trace.re =
      175013 / 5000 + 2 / 17 + 1 / 1000 := by
    change (∑ p, ∑ q, reflectionU p q * pairAB witnessRaw (q.1, p.2) (p.1, q.2)).re = _
    norm_num [reflectionU.eq_1, rankOneDensity, edge.eq_1, vecMulVec_apply,
      pairAB_entry, witnessRaw.eq_1,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.one_apply]
  have hty : ((ConicalDesignConcurrenceComparability.swap 3) * partialTranspose (pairAC witnessRaw)).trace.re = 81 := by
    change (∑ p, ∑ q, (ConicalDesignConcurrenceComparability.swap 3) p q * pairAC witnessRaw (q.1, p.2) (p.1, q.2)).re = _
    norm_num [swap_entry, pairAC_entry, witnessRaw.eq_1,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  have hx := unitary_bound (partialTranspose (pairAB witnessRaw)) reflectionU hU
  have hy := unitary_bound (partialTranspose (pairAC witnessRaw)) (ConicalDesignConcurrenceComparability.swap 3) swap_unitary
  rw [htx] at hx
  rw [hty] at hy
  constructor <;> linarith

private theorem witness_bounds :
    14 / 11 ≤ 2 * negativity (rankOneDensity witness) ∧
    2 * negativity (rankOneDensity witness) - 2 * negativity (pairAC witness) ≤ 2 / 209 ∧
    5 * (2 * negativity (rankOneDensity witness) - 2 * negativity (pairAC witness)) <
      2 * negativity (pairAB witness) := by
  have hpt {a b : Type} (M : Matrix (a × b) (a × b) ℂ) (s : ℂ) :
      partialTranspose (s • M) = s • partialTranspose M := rfl
  have hscalar : (5000 / 175013 : ℂ) = ((5000 / 175013 : ℝ) : ℂ) := by norm_num
  have hxscale : traceNorm (partialTranspose (pairAB witness)) =
      (5000 / 175013) * traceNorm (partialTranspose (pairAB witnessRaw)) := by
    rw [witness_scale.1, hpt, hscalar, traceNorm_smul_nonneg _ _ (by norm_num)]
  have hyscale : traceNorm (partialTranspose (pairAC witness)) =
      (5000 / 175013) * traceNorm (partialTranspose (pairAC witnessRaw)) := by
    rw [witness_scale.2.1, hpt, hscalar, traceNorm_smul_nonneg _ _ (by norm_num)]
  have hzscale : traceNorm (partialTranspose (rankOneDensity witness)) =
      (5000 / 175013) * traceNorm (partialTranspose (rankOneDensity witnessRaw)) := by
    rw [witness_scale.2.2, hpt, hscalar, traceNorm_smul_nonneg _ _ (by norm_num)]
  obtain ⟨hzlo, hzhi⟩ := witness_whole
  obtain ⟨hxlo, hylo⟩ := witness_pairs
  delta negativity
  rw [hxscale, hyscale, hzscale]
  constructor
  · linarith
  constructor <;> linarith

theorem result : ¬ claim := by
  intro hclaim
  rw [claim.eq_1] at hclaim
  obtain ⟨a, b, c, d, ha, _, _, hd, hn, ht⟩ := hclaim witness witness_unit
  have hx := congrArg Prod.fst ht
  have hy := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) ht
  have hz := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) ht
  change negativity (pairAB (familyState a b c d)) = negativity (pairAB witness) at hx
  change negativity (pairAC (familyState a b c d)) = negativity (pairAC witness) at hy
  change negativity (rankOneDensity (familyState a b c d)) = negativity (rankOneDensity witness) at hz
  obtain ⟨hlarge, hgap, hstrict⟩ := witness_bounds
  have hsep := family_separator a b c d ha hd hn (by rwa [hz]) (by rwa [hz, hy])
  rw [hx, hy, hz] at hsep
  exact (not_le_of_gt hstrict) hsep


end D5.S3.Quantum.Entanglement.AllenMeyerNegativityRegionRefutation
