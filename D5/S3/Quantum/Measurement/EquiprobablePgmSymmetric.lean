/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmSymmetric
   mirror-E: none(waiver:universal-actual-object-proof)
   anchors: []
   utility: none
   digest: Complete actual symmetric qubit classification, CFC scores and failure iff. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity

/-!
Anonymous mechanism attribution is retained. The old literal byline is Wenlin
Zhang and Haobo / trureturing. The new note is by Haobo Ma then Wenlin Zhang;
its CC BY 4.0 grant applies to that note only. Hyunho Cha is credited for the
symmetric scores and the qubit and commuting constructions. No priority claim
is made. Normalization and algebra helpers are retained on actual consumer
paths; their presence is not an independent admission witness.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric

open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success pgmScore)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)
open D5.S3.Quantum.Matrix.SpectralPower (posDef_two)
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)

/-- The actual three symmetric qubit matrices, in label order plus, minus, third. -/
def rho (a b c : ℝ) : Fin 3 → QubitMatrix :=
  ![!![(a : ℂ), (b : ℂ); (b : ℂ), (1 - a : ℝ)],
    !![(a : ℂ), (-b : ℝ); (-b : ℝ), (1 - a : ℝ)],
    diagonal ![(c : ℂ), (1 - c : ℝ)]]

/-- The two orthogonal X projectors and a zero third effect. -/
def pairPovm : Fin 3 → QubitMatrix :=
  ![(1 / 2 : ℂ) • vecMulVec ![(1 : ℂ), 1] (star ![(1 : ℂ), 1]),
    (1 / 2 : ℂ) • vecMulVec ![(1 : ℂ), -1] (star ![(1 : ℂ), -1]), 0]

/-- The dual matrix in the two-active region. -/
def pairGamma (a b : ℝ) : QubitMatrix :=
  diagonal ![((a + b) / 3 : ℝ), ((1 - a + b) / 3 : ℝ)]

/-- Shared discrimination dual helper, consumed by the symmetric and commuting proofs. -/
theorem dual_score {k N : ℕ}
    (ρ E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : ∑ i, E i = 1) :
    success ρ E = (trace Γ).re -
      ∑ i, (trace ((Γ - (1 / (N : ℂ)) • ρ i) * E i)).re := by
  have hΓE : ∑ i, (trace (Γ * E i)).re = (trace Γ).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hE, mul_one]
  simp only [success, sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib, hΓE]
  ring

/-- Shared discrimination dual helper, consumed by the symmetric and commuting proofs. -/
theorem dual_bound {k N : ℕ}
    (ρ E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : finitePOVM E)
    (hΓ : ∀ i, (Γ - (1 / (N : ℂ)) • ρ i).PosSemidef) :
    success ρ E ≤ (trace Γ).re := by
  rw [dual_score ρ E Γ hE.2]
  exact sub_le_self _ (Finset.sum_nonneg fun i _ =>
    RHLinalg.trace_mul_nonneg_of_posSemidef (hΓ i) (hE.1 i))

private theorem pair_povm : finitePOVM pairPovm := by
  constructor
  · intro i
    fin_cases i
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
    · exact Matrix.PosSemidef.zero
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pairPovm, Fin.sum_univ_three, vecMulVec]

private theorem rho_trace (a b c : ℝ) (i : Fin 3) : trace (rho a b c i) = 1 := by
  fin_cases i <;> simp [rho, trace, Fin.sum_univ_two]

/-- The determinant domain certifies every actual state as strictly positive and normalized. -/
theorem states_posDef (a b c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hc1 : c < 1) (hd : 0 < a * (1 - a) - b ^ 2) :
    ∀ i, (rho a b c i).PosDef ∧ trace (rho a b c i) = 1 := by
  intro i
  refine ⟨?_, rho_trace a b c i⟩
  fin_cases i
  · exact posDef_two a b (1 - a) ha hd
  · exact posDef_two a (-b) (1 - a) ha (by nlinarith)
  · apply Matrix.posDef_diagonal_iff.mpr
    intro j
    fin_cases j
    · change (0 : ℂ) < (c : ℂ)
      exact_mod_cast hc
    · change (0 : ℂ) < ((1 - c : ℝ) : ℂ)
      exact_mod_cast sub_pos.mpr hc1

private theorem pair_slack_form (a b c : ℝ) (i : Fin 3) :
    pairGamma a b - (1 / 3 : ℂ) • rho a b c i =
      ![((b / 3 : ℝ) : ℂ) • !![1, -1; -1, 1],
        ((b / 3 : ℝ) : ℂ) • !![1, 1; 1, 1],
        diagonal ![(((b - (c - a)) / 3 : ℝ) : ℂ),
          (((b + (c - a)) / 3 : ℝ) : ℂ)]] i := by
  fin_cases i <;> ext j k
  all_goals fin_cases j <;> fin_cases k <;>
    simp [pairGamma, rho] <;> push_cast <;> ring

private theorem pair_slacks (a b c : ℝ) (hb : 0 ≤ b) (hδ : |c - a| ≤ b) :
    ∀ i, (pairGamma a b - (1 / 3 : ℂ) • rho a b c i).PosSemidef := by
  have hl : 0 ≤ b - (c - a) := sub_nonneg.mpr (abs_le.mp hδ).2
  have hr : 0 ≤ b + (c - a) := by linarith [(abs_le.mp hδ).1]
  intro i
  rw [pair_slack_form]
  fin_cases i
  · change (((b / 3 : ℝ) : ℂ) • !![1, -1; -1, 1] : QubitMatrix).PosSemidef
    have houter : (!![1, -1; -1, 1] : QubitMatrix) =
        vecMulVec ![(1 : ℂ), -1] (star ![(1 : ℂ), -1]) := by
      ext j k; fin_cases j <;> fin_cases k <;> norm_num [vecMulVec]
    rw [houter]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by
      exact_mod_cast div_nonneg hb (by norm_num : (0 : ℝ) ≤ 3))
  · change (((b / 3 : ℝ) : ℂ) • !![1, 1; 1, 1] : QubitMatrix).PosSemidef
    have houter : (!![1, 1; 1, 1] : QubitMatrix) =
        vecMulVec ![(1 : ℂ), 1] (star ![(1 : ℂ), 1]) := by
      ext j k; fin_cases j <;> fin_cases k <;> norm_num [vecMulVec]
    rw [houter]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by
      exact_mod_cast div_nonneg hb (by norm_num : (0 : ℝ) ≤ 3))
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    fin_cases j
    · change (0 : ℂ) ≤ (((b - (c - a)) / 3 : ℝ) : ℂ)
      exact_mod_cast div_nonneg hl (by norm_num : (0 : ℝ) ≤ 3)
    · change (0 : ℂ) ≤ (((b + (c - a)) / 3 : ℝ) : ℂ)
      exact_mod_cast div_nonneg hr (by norm_num : (0 : ℝ) ≤ 3)

private theorem pair_score (a b c : ℝ) : success (rho a b c) pairPovm = (1 + 2 * b) / 3 := by
  simp [success, rho, pairPovm, vecMulVec, Matrix.mul_apply, trace,
    Fin.sum_univ_three, Fin.sum_univ_two, Complex.mul_re]
  ring

private theorem pairGamma_trace (a b : ℝ) : (trace (pairGamma a b)).re = (1 + 2 * b) / 3 := by
  simp [pairGamma, trace, Fin.sum_univ_two]
  ring

/-- Shared discrimination dual helper, consumed by the symmetric and commuting proofs. -/
theorem complementary_products {k N : ℕ}
    (ρ E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : finitePOVM E)
    (hΓ : ∀ i, (Γ - (1 / (N : ℂ)) • ρ i).PosSemidef)
    (hs : success ρ E = (trace Γ).re) :
    ∀ i, (Γ - (1 / (N : ℂ)) • ρ i) * E i = 0 := by
  have hid := dual_score ρ E Γ hE.2
  have hsum : (∑ i, (trace ((Γ - (1 / (N : ℂ)) • ρ i) * E i)).re) = 0 := by
    linarith
  have hnon (i : Fin N) := RHLinalg.trace_mul_nonneg_of_posSemidef (hΓ i) (hE.1 i)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      hnon i)).mp hsum
  intro i
  apply D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero
    _ _ (hΓ i) (hE.1 i)
  have ht : star (trace ((Γ - (1 / (N : ℂ)) • ρ i) * E i)) =
      trace ((Γ - (1 / (N : ℂ)) • ρ i) * E i) := by
    rw [← trace_conjTranspose, Matrix.conjTranspose_mul, (hE.1 i).1.eq,
      (hΓ i).1.eq, Matrix.trace_mul_comm]
  have him := congrArg Complex.im ht
  simp only [Complex.star_def, Complex.conj_im] at him
  exact Complex.ext (hzero i (Finset.mem_univ i)) (by simp only [Complex.zero_im]; linarith)

private theorem x_null_shape (s : ℂ) (hs : s * s = 1) (E : QubitMatrix)
    (hL : (!![1, -s; -s, 1] : QubitMatrix) * E = 0)
    (hR : E * (!![1, -s; -s, 1] : QubitMatrix) = 0) :
    E = E 0 0 • (!![1, s; s, 1] : QubitMatrix) := by
  have h00 := congrArg (fun M : QubitMatrix => M 0 0) hL
  have h01 := congrArg (fun M : QubitMatrix => M 0 1) hL
  have hr00 := congrArg (fun M : QubitMatrix => M 0 0) hR
  have h00' : E 0 0 = s * E 1 0 := by
    apply sub_eq_zero.mp
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using h00
  have h01' : E 0 1 = s * E 1 1 := by
    apply sub_eq_zero.mp
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using h01
  have hr00' : E 0 0 = E 0 1 * s := by
    apply sub_eq_zero.mp
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using hr00
  have he10 : E 1 0 = s * E 0 0 := by
    calc
      E 1 0 = s * (s * E 1 0) := by rw [← mul_assoc, hs, one_mul]
      _ = s * E 0 0 := by rw [← h00']
  have he01 : E 0 1 = s * E 0 0 := by
    calc
      E 0 1 = s * (E 0 1 * s) := by rw [mul_comm (E 0 1) s, ← mul_assoc, hs, one_mul]
      _ = s * E 0 0 := by rw [← hr00']
  have he11 : E 1 1 = E 0 0 := by
    calc
      E 1 1 = s * (s * E 1 1) := by rw [← mul_assoc, hs, one_mul]
      _ = s * E 0 1 := by rw [← h01']
      _ = E 0 0 := by rw [he01, ← mul_assoc, hs, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [he01, he10, he11, mul_comm]

set_option maxHeartbeats 800000 in
private theorem pair_unique (a b c : ℝ) (hb : 0 < b) (hδ : |c - a| ≤ b)
    (E : Fin 3 → QubitMatrix) (hE : finitePOVM E)
    (hs : success (rho a b c) E = (1 + 2 * b) / 3) : E = pairPovm := by
  have hcomp := complementary_products (rho a b c) E (pairGamma a b) hE
    (pair_slacks a b c hb.le hδ) (hs.trans (pairGamma_trace a b).symm)
  change ∀ i, (pairGamma a b - (1 / 3 : ℂ) • rho a b c i) * E i = 0 at hcomp
  have hbC : ((b / 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_ne_zero hb.ne' (by norm_num : (3 : ℝ) ≠ 0))
  have hL0 : (!![1, -1; -1, 1] : QubitMatrix) * E 0 = 0 := by
    have h := hcomp 0
    rw [pair_slack_form] at h
    change (((b / 3 : ℝ) : ℂ) • !![1, -1; -1, 1]) * E 0 = 0 at h
    rw [smul_mul_assoc] at h
    exact (smul_eq_zero.mp h).resolve_left hbC
  have hL1 : (!![1, 1; 1, 1] : QubitMatrix) * E 1 = 0 := by
    have h := hcomp 1
    rw [pair_slack_form] at h
    change (((b / 3 : ℝ) : ℂ) • !![1, 1; 1, 1]) * E 1 = 0 at h
    rw [smul_mul_assoc] at h
    exact (smul_eq_zero.mp h).resolve_left hbC
  have hA0 : (!![1, -1; -1, 1] : QubitMatrix)ᴴ = !![1, -1; -1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
  have hA1 : (!![1, 1; 1, 1] : QubitMatrix)ᴴ = !![1, 1; 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
  have hR0 : E 0 * (!![1, -1; -1, 1] : QubitMatrix) = 0 := by
    simpa only [Matrix.conjTranspose_mul, (hE.1 0).1.eq, hA0,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hL0
  have hR1 : E 1 * (!![1, 1; 1, 1] : QubitMatrix) = 0 := by
    simpa only [Matrix.conjTranspose_mul, (hE.1 1).1.eq, hA1,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hL1
  let u := E 0 0 0
  let v := E 1 0 0
  have he0 : E 0 = u • (!![1, 1; 1, 1] : QubitMatrix) :=
    x_null_shape 1 (by norm_num) (E 0) hL0 hR0
  have he1 : E 1 = v • (!![1, -1; -1, 1] : QubitMatrix) := by
    apply x_null_shape (-(1 : ℂ)) (by norm_num) (E 1)
    · simpa only [neg_neg] using hL1
    · simpa only [neg_neg] using hR1
  have hsum := hE.2
  rw [Fin.sum_univ_three, he0, he1] at hsum
  have h00 := congrArg (fun M : QubitMatrix => M 0 0) hsum
  have h11 := congrArg (fun M : QubitMatrix => M 1 1) hsum
  have h01 := congrArg (fun M : QubitMatrix => M 0 1) hsum
  simp at h00 h11 h01
  have heq : E 2 0 0 = E 2 1 1 := by linear_combination h00 - h11
  have hC3 := hcomp 2
  rw [pair_slack_form] at hC3
  change (diagonal ![(((b - (c - a)) / 3 : ℝ) : ℂ),
    (((b + (c - a)) / 3 : ℝ) : ℂ)] : QubitMatrix) * E 2 = 0 at hC3
  have hc0 : (((b - (c - a)) / 3 : ℝ) : ℂ) * E 2 0 0 = 0 := by
    have h := congrArg (fun M : QubitMatrix => M 0 0) hC3
    simpa only [Matrix.diagonal_mul, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.zero_apply] using h
  have hc1 : (((b + (c - a)) / 3 : ℝ) : ℂ) * E 2 1 1 = 0 := by
    have h := congrArg (fun M : QubitMatrix => M 1 1) hC3
    simpa only [Matrix.diagonal_mul, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.zero_apply] using h
  push_cast at hc0 hc1
  rw [← heq] at hc1
  have hz : (b : ℂ) * E 2 0 0 = 0 := by
    linear_combination (3 / 2 : ℂ) * hc0 + (3 / 2 : ℂ) * hc1
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hz0 : E 2 0 0 = 0 := (mul_eq_zero.mp hz).resolve_left hb'
  have hz1 : E 2 1 1 = 0 := heq.symm.trans hz0
  have he2 : E 2 = 0 := (hE.1 2).trace_eq_zero_iff.mp (by
    simp [trace, Fin.sum_univ_two, hz0, hz1])
  rw [he2] at h00 h01
  simp only [Matrix.zero_apply, add_zero] at h00 h01
  have hu : u = 1 / 2 := by linear_combination (1 / 2 : ℂ) * h00 + (1 / 2 : ℂ) * h01
  have hv : v = 1 / 2 := by linear_combination (1 / 2 : ℂ) * h00 - (1 / 2 : ℂ) * h01
  funext i
  fin_cases i
  · change E 0 = pairPovm 0
    rw [he0, hu]
    ext j k; fin_cases j <;> fin_cases k <;> norm_num [pairPovm, vecMulVec]
  · change E 1 = pairPovm 1
    rw [he1, hv]
    ext j k; fin_cases j <;> fin_cases k <;> norm_num [pairPovm, vecMulVec]
  · exact he2

/-- The pair optimum is unique on both active-set equality boundaries as well as
in the strict pair region. This optimization statement itself needs no density
hypothesis; the density-domain theorems separately certify the actual states. -/
theorem pair_classification (a b c : ℝ) (hb : 0 < b) (hδ : |c - a| ≤ b) :
    finitePOVM pairPovm ∧ success (rho a b c) pairPovm = (1 + 2 * b) / 3 ∧
      ∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho a b c) F ≤ success (rho a b c) E) ↔
          E = pairPovm) := by
  refine ⟨pair_povm, pair_score a b c, ?_⟩
  intro E hE
  constructor
  · intro ho
    apply pair_unique a b c hb hδ E hE
    apply le_antisymm
    · exact (dual_bound (rho a b c) E (pairGamma a b) hE
        (pair_slacks a b c hb.le hδ)).trans_eq (pairGamma_trace a b)
    · exact (pair_score a b c).symm.trans_le (ho pairPovm pair_povm)
  · rintro rfl F hF
    rw [pair_score]
    exact (dual_bound (rho a b c) F (pairGamma a b) hF
      (pair_slacks a b c hb.le hδ)).trans_eq (pairGamma_trace a b)


/-- The three-active POVM when the third state is loaded toward the first basis ray. -/
def upperPovm (t : ℝ) : Fin 3 → QubitMatrix :=
  ![(1 / 2 : ℂ) • vecMulVec ![(t : ℂ), 1] (star ![(t : ℂ), 1]),
    (1 / 2 : ℂ) • vecMulVec ![(-t : ℂ), 1] (star ![(-t : ℂ), 1]),
    diagonal ![(1 - t ^ 2 : ℝ), (0 : ℂ)]]

/-- The diagonal dual certificate for the upper three-active region. -/
def upperGamma (a b c t : ℝ) : QubitMatrix :=
  diagonal ![(c / 3 : ℝ), ((1 - a + b * t) / 3 : ℝ)]

private theorem upper_povm (t : ℝ) (ht : t ^ 2 ≤ 1) : finitePOVM (upperPovm t) := by
  constructor
  · intro i
    fin_cases i
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
    · apply Matrix.posSemidef_diagonal_iff.mpr
      intro j
      fin_cases j
      · change (0 : ℂ) ≤ ((1 - t ^ 2 : ℝ) : ℂ)
        exact_mod_cast sub_nonneg.mpr ht
      · norm_num [upperPovm]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperPovm, Fin.sum_univ_three, vecMulVec] <;> push_cast <;> ring

private theorem upper_slack_form (a b c t : ℝ) (ht : (c - a) * t = b) (i : Fin 3) :
    upperGamma a b c t - (1 / 3 : ℂ) • rho a b c i =
      ![(((c - a) / 3 : ℝ) : ℂ) •
          vecMulVec ![(1 : ℂ), -t] (star ![(1 : ℂ), -t]),
        (((c - a) / 3 : ℝ) : ℂ) •
          vecMulVec ![(1 : ℂ), t] (star ![(1 : ℂ), t]),
        diagonal ![(0 : ℂ), (((c - a + b * t) / 3 : ℝ) : ℂ)]] i := by
  rw [← ht]
  fin_cases i <;> ext j k
  all_goals fin_cases j <;> fin_cases k <;>
    simp [upperGamma, rho, vecMulVec] <;> push_cast <;> ring

private theorem upper_slacks (a b c t : ℝ) (hδ : 0 < c - a) (hb : 0 < b)
    (ht0 : 0 < t) (ht : (c - a) * t = b) :
    ∀ i, (upperGamma a b c t - (1 / 3 : ℂ) • rho a b c i).PosSemidef := by
  intro i
  rw [upper_slack_form a b c t ht]
  fin_cases i
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by
      exact_mod_cast div_nonneg hδ.le (by norm_num : (0 : ℝ) ≤ 3))
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by
      exact_mod_cast div_nonneg hδ.le (by norm_num : (0 : ℝ) ≤ 3))
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    fin_cases j
    · norm_num
    · change (0 : ℂ) ≤ (((c - a + b * t) / 3 : ℝ) : ℂ)
      exact_mod_cast div_nonneg (by positivity : 0 ≤ c - a + b * t)
        (by norm_num : (0 : ℝ) ≤ 3)

private theorem upper_score (a b c t : ℝ) (ht : (c - a) * t = b) :
    success (rho a b c) (upperPovm t) = (1 + (c - a) + b * t) / 3 := by
  simp [success, rho, upperPovm, vecMulVec, Matrix.mul_apply, trace,
    Fin.sum_univ_three, Fin.sum_univ_two, Complex.mul_re]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← ht]
  ring

private theorem upperGamma_trace (a b c t : ℝ) :
    (trace (upperGamma a b c t)).re = (1 + (c - a) + b * t) / 3 := by
  simp [upperGamma, trace, Fin.sum_univ_two]
  ring

private theorem tilted_null_shape (t : ℂ) (E : QubitMatrix)
    (hL : (vecMulVec ![1, -t] (star ![1, -t])) * E = 0)
    (hR : E * (vecMulVec ![1, -t] (star ![1, -t])) = 0)
    (ht : star t = t) :
    E = E 1 1 • vecMulVec ![t, 1] (star ![t, 1]) := by
  have ht' : (starRingEnd ℂ) t = t := ht
  have h00 := congrArg (fun M : QubitMatrix => M 0 0) hL
  have h01 := congrArg (fun M : QubitMatrix => M 0 1) hL
  have hr10 := congrArg (fun M : QubitMatrix => M 1 0) hR
  have he01 : E 0 1 = t * E 1 1 := by
    apply sub_eq_zero.mp
    simpa [Matrix.mul_apply, Fin.sum_univ_two, vecMulVec, ht', sub_eq_add_neg] using h01
  have he10 : E 1 0 = E 1 1 * t := by
    apply sub_eq_zero.mp
    simpa [Matrix.mul_apply, Fin.sum_univ_two, vecMulVec, ht', sub_eq_add_neg] using hr10
  have he00 : E 0 0 = t * (E 1 1 * t) := by
    rw [← he10]
    apply sub_eq_zero.mp
    simpa [Matrix.mul_apply, Fin.sum_univ_two, vecMulVec, ht', sub_eq_add_neg] using h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec, ht', he01, he10, he00, mul_comm] <;> ring

set_option maxHeartbeats 800000 in
private theorem upper_unique (a b c t : ℝ) (hδ : 0 < c - a) (hb : 0 < b)
    (ht0 : 0 < t) (ht : (c - a) * t = b)
    (E : Fin 3 → QubitMatrix) (hE : finitePOVM E)
    (hs : success (rho a b c) E = (1 + (c - a) + b * t) / 3) :
    E = upperPovm t := by
  have hcomp := complementary_products (rho a b c) E (upperGamma a b c t) hE
    (upper_slacks a b c t hδ hb ht0 ht) (hs.trans (upperGamma_trace a b c t).symm)
  change ∀ i, (upperGamma a b c t - (1 / 3 : ℂ) • rho a b c i) * E i = 0 at hcomp
  have hδC : (((c - a) / 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_ne_zero hδ.ne' (by norm_num : (3 : ℝ) ≠ 0))
  have hL0 : (vecMulVec ![(1 : ℂ), -t] (star ![(1 : ℂ), -t])) * E 0 = 0 := by
    have h := hcomp 0
    rw [upper_slack_form a b c t ht] at h
    change ((((c - a) / 3 : ℝ) : ℂ) • _) * E 0 = 0 at h
    rw [smul_mul_assoc] at h
    exact (smul_eq_zero.mp h).resolve_left hδC
  have hL1 : (vecMulVec ![(1 : ℂ), t] (star ![(1 : ℂ), t])) * E 1 = 0 := by
    have h := hcomp 1
    rw [upper_slack_form a b c t ht] at h
    change ((((c - a) / 3 : ℝ) : ℂ) • _) * E 1 = 0 at h
    rw [smul_mul_assoc] at h
    exact (smul_eq_zero.mp h).resolve_left hδC
  have hR0 : E 0 * (vecMulVec ![(1 : ℂ), -t] (star ![(1 : ℂ), -t])) = 0 := by
    simpa only [Matrix.conjTranspose_mul, (hE.1 0).1.eq,
      Matrix.conjTranspose_vecMulVec, star_star, Matrix.conjTranspose_zero] using
      congrArg Matrix.conjTranspose hL0
  have hR1 : E 1 * (vecMulVec ![(1 : ℂ), t] (star ![(1 : ℂ), t])) = 0 := by
    simpa only [Matrix.conjTranspose_mul, (hE.1 1).1.eq,
      Matrix.conjTranspose_vecMulVec, star_star, Matrix.conjTranspose_zero] using
      congrArg Matrix.conjTranspose hL1
  let u := E 0 1 1
  let v := E 1 1 1
  have he0 : E 0 = u • vecMulVec ![(t : ℂ), 1] (star ![(t : ℂ), 1]) :=
    tilted_null_shape (t : ℂ) (E 0) hL0 hR0 (by simp)
  have he1 : E 1 = v • vecMulVec ![(-t : ℂ), 1] (star ![(-t : ℂ), 1]) := by
    apply tilted_null_shape (-(t : ℂ)) (E 1) _ _ (by simp)
    · simpa only [neg_neg] using hL1
    · simpa only [neg_neg] using hR1
  have hC3 := hcomp 2
  rw [upper_slack_form a b c t ht] at hC3
  change (diagonal ![(0 : ℂ), (((c - a + b * t) / 3 : ℝ) : ℂ)] : QubitMatrix) * E 2 = 0 at hC3
  have hr : (((c - a + b * t) / 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos (by positivity : 0 < c - a + b * t)
      (by norm_num : (0 : ℝ) < 3)).ne'
  have hz10 : E 2 1 0 = 0 := by
    have h := congrArg (fun M : QubitMatrix => M 1 0) hC3
    simp only [Matrix.diagonal_mul, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hr
  have hz11 : E 2 1 1 = 0 := by
    have h := congrArg (fun M : QubitMatrix => M 1 1) hC3
    simp only [Matrix.diagonal_mul, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hr
  have hz01 : E 2 0 1 = 0 := by
    have h := congrArg (fun M : QubitMatrix => M 0 1) (hE.1 2).1.eq
    simpa [Matrix.conjTranspose, hz10] using h.symm
  have hsum := hE.2
  rw [Fin.sum_univ_three, he0, he1] at hsum
  have h00 := congrArg (fun M : QubitMatrix => M 0 0) hsum
  have h11 := congrArg (fun M : QubitMatrix => M 1 1) hsum
  have h01 := congrArg (fun M : QubitMatrix => M 0 1) hsum
  simp [vecMulVec, hz11, hz01] at h00 h11 h01
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have huv : u = v := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (t : ℂ) * (u - v) = 0 by
      linear_combination h01)).resolve_left htC
  have hu : u = 1 / 2 := by linear_combination (1 / 2 : ℂ) * h11 + (1 / 2 : ℂ) * huv
  have hv : v = 1 / 2 := huv.symm.trans hu
  have hz00 : E 2 0 0 = ((1 - t ^ 2 : ℝ) : ℂ) := by
    rw [hu, hv] at h00
    push_cast
    linear_combination h00
  funext i
  fin_cases i
  · exact he0.trans (by rw [hu]; rfl)
  · exact he1.trans (by rw [hv]; rfl)
  · ext j k
    fin_cases j <;> fin_cases k <;> simp [upperPovm, hz00, hz01, hz10, hz11]

/-- In the strict upper three-active region the displayed actual POVM is the
unique optimum over all complex POVMs. All three effects are nonzero. -/
theorem upper_classification (a b c : ℝ) (hb : 0 < b) (hδ : b < c - a) :
    let t := b / (c - a)
    finitePOVM (upperPovm t) ∧
      success (rho a b c) (upperPovm t) = (1 + (c - a) + b * t) / 3 ∧
      ∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho a b c) F ≤ success (rho a b c) E) ↔
          E = upperPovm t) := by
  dsimp only
  let t := b / (c - a)
  have hδ0 : 0 < c - a := hb.trans hδ
  have ht0 : 0 < t := div_pos hb hδ0
  have ht1 : t < 1 := (div_lt_one hδ0).mpr hδ
  have ht : (c - a) * t = b := mul_div_cancel₀ b hδ0.ne'
  have hP := upper_povm t (by nlinarith)
  refine ⟨hP, upper_score a b c t ht, ?_⟩
  intro E hE
  constructor
  · intro ho
    apply upper_unique a b c t hδ0 hb ht0 ht E hE
    apply le_antisymm
    · exact (dual_bound (rho a b c) E (upperGamma a b c t) hE
        (upper_slacks a b c t hδ0 hb ht0 ht)).trans_eq (upperGamma_trace a b c t)
    · exact (upper_score a b c t ht).symm.trans_le (ho (upperPovm t) hP)
  · rintro rfl F hF
    rw [upper_score a b c t ht]
    exact (dual_bound (rho a b c) F (upperGamma a b c t) hF
      (upper_slacks a b c t hδ0 hb ht0 ht)).trans_eq (upperGamma_trace a b c t)

open D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity (diagonal_inverse_sqrt)

/-- Diagonal inverse square-root helper consumed by actual score and effect calculations. -/
theorem inverse_sqrt_two (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (diagonal ![(u : ℂ), (v : ℂ)]) ^ (-(1 / 2) : ℝ) =
      diagonal ![(((Real.sqrt u)⁻¹ : ℝ) : ℂ), (((Real.sqrt v)⁻¹ : ℝ) : ℂ)] := by
  have h := diagonal_inverse_sqrt (![u, v] : Fin 2 → ℝ) (by
    intro x; fin_cases x <;> assumption)
  have he : (fun x : Fin 2 => (![u, v] x : ℂ)) = ![(u : ℂ), (v : ℂ)] := by
    funext x; fin_cases x <;> rfl
  rw [he] at h
  convert h using 1 <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

private theorem quadratic_trace (a b c x y : ℝ) :
    (trace (!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] *
      (diagonal ![(x : ℂ), (y : ℂ)] * !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] *
        diagonal ![(x : ℂ), (y : ℂ)]))).re =
      a ^ 2 * x ^ 2 + 2 * b ^ 2 * (x * y) + c ^ 2 * y ^ 2 := by
  have hd : diagonal ![(x : ℂ), (y : ℂ)] = !![(x : ℂ), 0; 0, (y : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hd]
  simp [Matrix.trace_fin_two, Complex.add_re, Complex.mul_re]
  ring

theorem sqrt_inverse_square (u : ℝ) (hu : 0 ≤ u) :
    ((Real.sqrt u)⁻¹) ^ 2 = u⁻¹ := by rw [inv_pow, Real.sq_sqrt hu]

theorem sqrt_inverse_product (u v : ℝ) (hu : 0 ≤ u) :
    (Real.sqrt u)⁻¹ * (Real.sqrt v)⁻¹ = (Real.sqrt (u * v))⁻¹ := by
  rw [← mul_inv, ← Real.sqrt_mul hu]

/-- The actual original-prior pair and full PGM scores for every physical
symmetric qubit ensemble. The pair determinant may vanish. -/
theorem symmetric_scores (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    pgmScore (rho a b c) {0, 1} - 1 / 3 =
        2 * b ^ 2 / (3 * Real.sqrt (a * (1 - a))) ∧
      pgmScore (rho a b c) Finset.univ - 1 / 3 =
        4 * b ^ 2 / (3 * Real.sqrt ((2 * a + c) * (3 - 2 * a - c))) +
          2 * (c - a) ^ 2 / (3 * ((2 * a + c) * (3 - 2 * a - c))) := by
  have hv : 0 < 1 - a := sub_pos.mpr ha1
  have hu : 0 < 2 * a + c := by positivity
  have hw : 0 < 3 - 2 * a - c := by linarith
  have hSA : (∑ j ∈ ({0, 1} : Finset (Fin 3)), (1 / (3 : ℂ)) • rho a b c j) =
      diagonal ![((2 * a / 3 : ℝ) : ℂ), ((2 * (1 - a) / 3 : ℝ) : ℂ)] := by
    rw [Finset.sum_pair (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho] <;> push_cast <;> ring
  have hS : (∑ j : Fin 3, (1 / (3 : ℂ)) • rho a b c j) =
      diagonal ![(((2 * a + c) / 3 : ℝ) : ℂ), (((3 - 2 * a - c) / 3 : ℝ) : ℂ)] := by
    rw [Fin.sum_univ_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho] <;> push_cast <;> ring
  have hσ (i : Fin 3) : (1 / (3 : ℂ)) • rho a b c i =
      ![!![((a / 3 : ℝ) : ℂ), ((b / 3 : ℝ) : ℂ);
          ((b / 3 : ℝ) : ℂ), (((1 - a) / 3 : ℝ) : ℂ)],
        !![((a / 3 : ℝ) : ℂ), ((-b / 3 : ℝ) : ℂ);
          ((-b / 3 : ℝ) : ℂ), (((1 - a) / 3 : ℝ) : ℂ)],
        !![((c / 3 : ℝ) : ℂ), 0; 0, (((1 - c) / 3 : ℝ) : ℂ)]] i := by
    fin_cases i <;> ext j k
    all_goals fin_cases j <;> fin_cases k <;> simp [rho] <;> push_cast <;> ring
  constructor
  · unfold pgmScore
    simp only [Nat.cast_ofNat]
    rw [hSA, inverse_sqrt_two _ _ (by positivity) (by positivity),
      Finset.sum_pair (by decide)]
    simp only [Nat.cast_ofNat, hσ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [quadratic_trace, quadratic_trace]
    rw [sqrt_inverse_square _ (by positivity), sqrt_inverse_square _ (by positivity),
      sqrt_inverse_product _ _ (by positivity)]
    have hprod : 2 * a / 3 * (2 * (1 - a) / 3) = (2 / 3 : ℝ) ^ 2 * (a * (1 - a)) := by ring
    rw [hprod, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    have hq : Real.sqrt (a * (1 - a)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos ha hv)).ne'
    field_simp
    ring
  · unfold pgmScore
    simp only [Nat.cast_ofNat]
    rw [hS, inverse_sqrt_two _ _ (by positivity) (by positivity),
      Fin.sum_univ_three]
    simp only [Nat.cast_ofNat, hσ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ← Complex.ofReal_zero]
    rw [quadratic_trace, quadratic_trace, quadratic_trace]
    rw [sqrt_inverse_square _ (by positivity), sqrt_inverse_square _ (by positivity),
      sqrt_inverse_product _ _ (by positivity)]
    have hprod : (2 * a + c) / 3 * ((3 - 2 * a - c) / 3) =
        (1 / 3 : ℝ) ^ 2 * ((2 * a + c) * (3 - 2 * a - c)) := by ring
    rw [hprod, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    have hD : Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hu hw)).ne'
    field_simp [hu.ne', hw.ne', hD]
    <;> ring_nf
    <;> field_simp [show 3 - a * 2 - c ≠ 0 by linarith]
    <;> ring

open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success pgmScore)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- Exchange the two orthonormal basis vectors. -/
def basisFlip (M : QubitMatrix) : QubitMatrix := M.submatrix Fin.rev Fin.rev

private theorem basisFlip_involutive (M : QubitMatrix) : basisFlip (basisFlip M) = M := by
  ext i j
  simp [basisFlip]

private theorem flip_povm {N : ℕ} (E : Fin N → QubitMatrix) (hE : finitePOVM E) :
    finitePOVM (fun i => basisFlip (E i)) := by
  constructor
  · intro i
    exact (hE.1 i).submatrix Fin.rev
  · ext i j
    have h := congrArg (fun M : QubitMatrix => M (Fin.rev i) (Fin.rev j)) hE.2
    fin_cases i <;> fin_cases j <;>
      simpa [basisFlip, Matrix.sum_apply, Fin.rev] using h

private theorem flip_score {N : ℕ} (ρ E : Fin N → QubitMatrix) :
    success (fun i => basisFlip (ρ i)) (fun i => basisFlip (E i)) = success ρ E := by
  unfold success
  apply Finset.sum_congr rfl
  intro i _
  simp [basisFlip, trace, Matrix.mul_apply, Fin.sum_univ_two, Fin.rev]
  ring

private theorem flip_rho (a b c : ℝ) :
    rho (1 - a) b (1 - c) = fun i => basisFlip (rho a b c i) := by
  funext i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [rho, basisFlip, Fin.rev] <;> push_cast <;> ring

private theorem flip_symmetric_score (a b c : ℝ) (E : Fin 3 → QubitMatrix) :
    success (rho (1 - a) b (1 - c)) (fun i => basisFlip (E i)) =
      success (rho a b c) E := by
  rw [flip_rho]
  exact flip_score _ _

/-- The three actual effects in the lower orientation, given in the original basis. -/
def lowerPovm (t : ℝ) : Fin 3 → QubitMatrix := fun i => basisFlip (upperPovm t i)

/-- The negative-sign three-active region has the same unique classification,
with the third effect supported on the second basis ray. -/
theorem lower_classification (a b c : ℝ) (hb : 0 < b) (hδ : b < a - c) :
    let t := b / (a - c)
    finitePOVM (lowerPovm t) ∧
      success (rho a b c) (lowerPovm t) = (1 + (a - c) + b * t) / 3 ∧
      ∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho a b c) F ≤ success (rho a b c) E) ↔
          E = lowerPovm t) := by
  dsimp only
  have hd : (1 - c) - (1 - a) = a - c := by ring
  have hu := upper_classification (1 - a) b (1 - c) hb (by simpa only [hd] using hδ)
  dsimp only at hu
  rw [hd] at hu
  let t := b / (a - c)
  have hP := flip_povm (upperPovm t) hu.1
  have hback : (fun i => basisFlip (lowerPovm t i)) = upperPovm t := by
    funext i
    exact basisFlip_involutive _
  refine ⟨hP, ?_, ?_⟩
  · have h := flip_symmetric_score a b c (lowerPovm t)
    rw [hback] at h
    exact h.symm.trans hu.2.1
  · intro E hE
    constructor
    · intro hopt
      have hopt' : ∀ F, finitePOVM F →
          success (rho (1 - a) b (1 - c)) F ≤
            success (rho (1 - a) b (1 - c)) (fun i => basisFlip (E i)) := by
        intro F hF
        rw [flip_symmetric_score]
        have h := hopt (fun i => basisFlip (F i)) (flip_povm F hF)
        have hf := flip_symmetric_score a b c (fun i => basisFlip (F i))
        have hff : (fun i => basisFlip (basisFlip (F i))) = F := by
          funext i
          exact basisFlip_involutive _
        rw [hff] at hf
        exact hf.trans_le h
      have he := (hu.2.2 _ (flip_povm E hE)).mp hopt'
      funext i
      have hx := congrArg (fun F => basisFlip (F i)) he
      simpa only [basisFlip_involutive, lowerPovm] using hx
    · rintro rfl F hF
      have h := (hu.2.2 (upperPovm t) hu.1).mpr rfl
        (fun i => basisFlip (F i)) (flip_povm F hF)
      rw [flip_symmetric_score] at h
      have he := flip_symmetric_score a b c (lowerPovm t)
      rw [hback] at he
      exact h.trans_eq he

/-- The complete actual optimal POVM, with equality assigned to the two-active region. -/
def optimalPovm (a b c : ℝ) : Fin 3 → QubitMatrix :=
  if |c - a| ≤ b then pairPovm
  else if b < c - a then upperPovm (b / (c - a)) else lowerPovm (b / (a - c))

private theorem upper_nonzero (t : ℝ) (ht : t ^ 2 < 1) :
    ∀ i, upperPovm t i ≠ 0 := by
  intro i h
  fin_cases i
  · have he := congrArg (fun M : QubitMatrix => M 1 1) h
    norm_num [upperPovm, vecMulVec] at he
  · have he := congrArg (fun M : QubitMatrix => M 1 1) h
    norm_num [upperPovm, vecMulVec] at he
  · have he := congrArg (fun M : QubitMatrix => M 0 0) h
    have hz : (1 - t ^ 2 : ℝ) = 0 := by
      have he' : (((1 - t ^ 2 : ℝ) : ℂ)) = 0 := by simpa [upperPovm] using he
      exact_mod_cast he'
    linarith

private theorem pair_active :
    Finset.univ.filter (fun i => pairPovm i ≠ 0) = ({0, 1} : Finset (Fin 3)) := by
  have h0 : pairPovm 0 ≠ 0 := by
    intro h
    have he := congrArg (fun M : QubitMatrix => M 0 0) h
    norm_num [pairPovm, vecMulVec] at he
  have h1 : pairPovm 1 ≠ 0 := by
    intro h
    have he := congrArg (fun M : QubitMatrix => M 0 0) h
    norm_num [pairPovm, vecMulVec] at he
  ext i
  fin_cases i <;> simp [h0, h1, show pairPovm 2 = 0 from rfl]

/-- The complete classification is an equivalence for every actual complex POVM;
the active labels are exactly the pair in the closed pair region and all three otherwise. -/
theorem complete_classification (a b c : ℝ) (hb : 0 < b) :
    finitePOVM (optimalPovm a b c) ∧
      (∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho a b c) F ≤ success (rho a b c) E) ↔
          E = optimalPovm a b c)) ∧
      Finset.univ.filter (fun i => optimalPovm a b c i ≠ 0) =
        if |c - a| ≤ b then {0, 1} else Finset.univ := by
  by_cases hδ : |c - a| ≤ b
  · simpa only [optimalPovm, if_pos hδ] using
      And.intro (pair_classification a b c hb hδ).1
        ⟨(pair_classification a b c hb hδ).2.2, pair_active⟩
  · have hr : c - a < -b ∨ b < c - a := by
      rcases lt_or_gt_of_ne (show c - a ≠ 0 by
        intro h; simp [h, hb.le] at hδ) with hl | hr
      · left
        rw [abs_of_neg hl] at hδ
        linarith
      · right
        rw [abs_of_pos hr] at hδ
        exact lt_of_not_ge hδ
    rcases hr with hl | hr
    · have hl' : b < a - c := by linarith
      have hn : ¬ b < c - a := by linarith
      have hc := lower_classification a b c hb hl'
      dsimp only at hc
      have ht0 : 0 < b / (a - c) := div_pos hb (hb.trans hl')
      have ht1 : b / (a - c) < 1 := (div_lt_one (hb.trans hl')).mpr hl'
      have hall (i) : lowerPovm (b / (a - c)) i ≠ 0 := by
        intro he
        have hx := congrArg basisFlip he
        have hz := upper_nonzero (b / (a - c)) (by nlinarith) i
        apply hz
        change basisFlip (basisFlip (upperPovm (b / (a - c)) i)) = basisFlip 0 at hx
        rw [basisFlip_involutive] at hx
        simpa [basisFlip] using hx
      simp only [optimalPovm, if_neg hδ, if_neg hn]
      refine ⟨hc.1, hc.2.2, ?_⟩
      ext i
      simp [hall i]
    · have hc := upper_classification a b c hb hr
      dsimp only at hc
      have ht0 : 0 < b / (c - a) := div_pos hb (hb.trans hr)
      have ht1 : b / (c - a) < 1 := (div_lt_one (hb.trans hr)).mpr hr
      have hall := upper_nonzero (b / (c - a)) (by nlinarith [ht0, ht1])
      simp only [optimalPovm, if_neg hδ, if_pos hr]
      refine ⟨hc.1, hc.2.2, ?_⟩
      ext i
      simp [hall i]

open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)

private theorem gap_criterion (q D b δ : ℝ) (hq : 0 < q) (hD : 0 < D) :
    2 * (4 * b ^ 2 / (3 * Real.sqrt D) + 2 * δ ^ 2 / (3 * D)) <
        2 * b ^ 2 / (3 * Real.sqrt q) ↔
      16 * q < D ∧
        2 * δ ^ 2 * Real.sqrt q /
          (Real.sqrt D * (Real.sqrt D - 4 * Real.sqrt q)) < b ^ 2 := by
  let Q := Real.sqrt q
  let T := Real.sqrt D
  have hQ : 0 < Q := Real.sqrt_pos.mpr hq
  have hT : 0 < T := Real.sqrt_pos.mpr hD
  have hQsq : Q ^ 2 = q := Real.sq_sqrt hq.le
  have hTsq : T ^ 2 = D := Real.sq_sqrt hD.le
  by_cases hbig : 16 * q < D
  · have hdiff : 0 < T - 4 * Q := by nlinarith [sq_nonneg (T - 4 * Q)]
    have hid : 2 * b ^ 2 / (3 * Q) -
        2 * (4 * b ^ 2 / (3 * T) + 2 * δ ^ 2 / (3 * D)) =
        (2 * (T - 4 * Q) / (3 * Q * T)) *
          (b ^ 2 - 2 * δ ^ 2 * Q / (T * (T - 4 * Q))) := by
      rw [← hTsq]
      field_simp
      ring_nf
      field_simp [show T - Q * 4 ≠ 0 by linarith]
      ring
    have hfac : 0 < 2 * (T - 4 * Q) / (3 * Q * T) := by positivity
    change _ ↔ 16 * q < D ∧ 2 * δ ^ 2 * Q / (T * (T - 4 * Q)) < b ^ 2
    rw [and_iff_right hbig, ← sub_pos, hid, mul_pos_iff_of_pos_left hfac, sub_pos]
  · have hle : T ≤ 4 * Q := by nlinarith [sq_nonneg (T - 4 * Q)]
    have hcoh : 2 * b ^ 2 / (3 * Q) ≤ 8 * b ^ 2 / (3 * T) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 3 * Q)
        (by positivity : 0 < 3 * T)).mpr
      nlinarith [sq_nonneg b]
    have hcoh' : 2 * b ^ 2 / (3 * Q) ≤ 2 * (4 * b ^ 2 / (3 * T)) := by
      convert hcoh using 1 <;> ring
    have hpop : 0 ≤ 2 * δ ^ 2 / (3 * D) := by positivity
    have hn : ¬ 2 * (4 * b ^ 2 / (3 * T) + 2 * δ ^ 2 / (3 * D)) <
        2 * b ^ 2 / (3 * Q) := by
      intro h
      linarith [hcoh']
    exact iff_of_false hn (not_and_of_not_left _ hbig)

/-- Exact failure in the closed two-active region; either threshold equality
is nonfailure. The formulas remain actual matrix/CFC scores. -/
theorem pair_failure_iff (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
        pgmScore (rho a b c) {0, 1} - 1 / 3 ↔
      16 * (a * (1 - a)) < (2 * a + c) * (3 - 2 * a - c) ∧
        2 * (c - a) ^ 2 * Real.sqrt (a * (1 - a)) /
          (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) *
            (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) -
              4 * Real.sqrt (a * (1 - a)))) < b ^ 2 := by
  rw [(symmetric_scores a b c ha ha1 hc hc1).1,
    (symmetric_scores a b c ha ha1 hc hc1).2]
  exact gap_criterion _ _ _ _ (mul_pos ha (sub_pos.mpr ha1))
    (mul_pos (by positivity) (by linarith))

/-- The full active-set failure iff. It includes the closed pair region as an
essential conjunct; with three active effects the original comparison is equality. -/
theorem active_failure_iff (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 < a * (1 - a) - b ^ 2) :
    (∀ i, (rho a b c i).PosDef ∧ trace (rho a b c i) = 1) ∧
      (let A := Finset.univ.filter (fun i => optimalPovm a b c i ≠ 0)
       2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
           ((A.card : ℝ) - 1) * (pgmScore (rho a b c) A - 1 / 3) ↔
        |c - a| ≤ b ∧
          16 * (a * (1 - a)) < (2 * a + c) * (3 - 2 * a - c) ∧
          2 * (c - a) ^ 2 * Real.sqrt (a * (1 - a)) /
            (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) *
              (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) -
                4 * Real.sqrt (a * (1 - a)))) < b ^ 2) := by
  refine ⟨states_posDef a b c ha hc hc1 hd, ?_⟩
  dsimp only
  rw [(complete_classification a b c hb).2.2]
  by_cases hpair : |c - a| ≤ b
  · rw [if_pos hpair, and_iff_right hpair]
    norm_num only [Finset.card_pair (show (0 : Fin 3) ≠ 1 by decide),
      Nat.cast_ofNat, sub_self, sub_zero, one_mul, show (2 : ℝ) - 1 = 1 by norm_num]
    exact pair_failure_iff a b c ha ha1 hc hc1
  · norm_num [hpair]

theorem inverse_sqrt_residual (u : ℝ) (hu : 0 < 1 - u) :
    1 / Real.sqrt (1 - u) - 1 =
      u / (Real.sqrt (1 - u) * (1 + Real.sqrt (1 - u))) := by
  have hs := Real.sqrt_pos.mpr hu
  have he := Real.sq_sqrt hu.le
  field_simp
  nlinarith


end D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric

/- Escape-audit delivery: four registrations for centered_identity, random_guessing_le,
states_posDef and pair_classification have validated evidence. Remaining
theorem-specific bindings are unfinished; the concrete gaps are disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
The issue is not proof, validation or independent approval. -/
