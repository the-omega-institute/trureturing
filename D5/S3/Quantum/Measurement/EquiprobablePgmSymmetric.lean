/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmSymmetric
   mirror-E: none(waiver:parameter-universal-kernel-proof)
   anchors: []
   utility: none
   digest: Actual symmetric qubit states and their complete optimal measurements. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity

/-!
The symmetric score calculations and constructions are credited to Hyunho Cha.
The anonymous mechanism manuscript supplies the earlier nonstrict pair domain.
The full strict-positive classification, including both equality boundaries, is
from Haobo Ma and Wenlin Zhang, Verification of the unbounded centered PGM ratio,
4 November 2026, section 2 (new note only: CC BY 4.0).
Admission commitment: explicit actual optimal POVMs, their uniqueness at the
singular dual boundaries, and the strict-positive three-active classification.
These are parameter-universal matrix proofs, not finite numerical certificates;
computational utility is none. The I header inherits the existing score owner.
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

private theorem dual_score {k N : ℕ}
    (ρ E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : ∑ i, E i = 1) :
    success ρ E = (trace Γ).re -
      ∑ i, (trace ((Γ - (1 / (N : ℂ)) • ρ i) * E i)).re := by
  have hΓE : ∑ i, (trace (Γ * E i)).re = (trace Γ).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hE, mul_one]
  simp only [success, sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib, hΓE]
  ring

private theorem dual_bound {k N : ℕ}
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

private theorem complementary_products {k N : ℕ}
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

end D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
