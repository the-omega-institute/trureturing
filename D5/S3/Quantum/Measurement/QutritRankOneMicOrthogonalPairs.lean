/- GID: D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.claim; result=D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result; claim=D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.claim
   digest: A rank-one qutrit MIC has nine orthogonal pairs, refuting arXiv:1812.08762 Conj. 1. -/

/-
proof_shape: result: bind-only (explicit finite reconstruction and arithmetic, with the
  positive-semidefinite and rank bounds supplied by pinned Mathlib)
escape_witness: none
admission_basis: open-problem-resolution (#11474; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.QutritRankOneMicOrthogonalPairs

open Matrix Complex
open scoped ComplexOrder

/-- A rank-one MIC in dimension three: nine positive semidefinite effects summing to the
identity, each of rank one, whose real span is exactly the Hermitian matrices. -/
def IsRankOneMIC (E : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  (∀ a, (E a).PosSemidef) ∧ (∑ a, E a) = 1 ∧ (∀ a, (E a).rank = 1) ∧
    (∀ a, (E a).IsHermitian) ∧
    ∀ H : Matrix (Fin 3) (Fin 3) ℂ, H.IsHermitian →
      ∃ c : Fin 9 → ℝ, H = ∑ a, c a • E a

/-- Each unordered pair is represented once, by its increasing ordered pair of indices.
Orthogonality means that the corresponding Gram entry `tr(E_a E_b)` vanishes. -/
noncomputable def orthogonalPairs (E : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ) :
    Finset (Fin 9 × Fin 9) := by
  classical
  exact Finset.univ.filter (fun p => p.1 < p.2 ∧ Matrix.trace (E p.1 * E p.2) = 0)

/-- Conjecture 1 (printed page 6): "A rank-1 MIC in dimension 3 can have no more than 7
pairs of orthogonal elements." The statement imposes no unbiasedness condition. -/
def claim : Prop :=
  ∀ E : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ, IsRankOneMIC E → (orthogonalPairs E).card ≤ 7

private noncomputable def vec : Fin 9 → Fin 3 → ℂ :=
  ![![1, I, -1], ![1, -1, 1 + I], ![1 - I, 0, -1], ![1, -1 + I, 1 + I],
    ![0, 1, I], ![-1 - I, I, 1], ![1, 1, 1], ![1, I, -1 - I], ![1, -I, 0]]

private def k : Fin 9 → ℝ := ![3, 2, 2, 4, 3, 3, 9, 7, 11]

private noncomputable def effect (a : Fin 9) : Matrix (Fin 3) (Fin 3) ℂ :=
  (k a / 46) • vecMulVec (vec a) (star (vec a))

/-- The integer matrix `46 B⁻¹`, where the columns of `B` are the Hermitian coordinates
of the nine outer products, in the order used by `coords`. -/
private def J : Matrix (Fin 9) (Fin 9) ℝ :=
  !![30, -1, -26, -15, -29, 13, -21, -1, -27;
     20, -16, -2, -10, -4, 24, -14, -16, -18;
     20, -16, -2, -56, -4, 24, 32, 30, -18;
     -6, 14, -4, -20, -8, 2, 18, 14, 10;
     -16, -1, 20, -61, 17, 13, 25, 45, -27;
     -16, -1, 20, 31, 17, -33, -21, -1, 19;
     -2, -3, 14, 47, 5, -7, -17, -3, 11;
     -22, 13, 16, 57, 9, -31, -3, -33, 29;
     18, 27, -34, -9, 1, 17, 15, -19, -7]

private def coords (H : Matrix (Fin 3) (Fin 3) ℂ) : Fin 9 → ℝ :=
  ![(H 0 0).re, (H 1 1).re, (H 2 2).re,
    (H 0 1).re, (H 0 1).im, (H 0 2).re, (H 0 2).im, (H 1 2).re, (H 1 2).im]

private noncomputable def coeff (H : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 9) : ℝ :=
  (∑ j, J a j * coords H j) / k a

set_option maxHeartbeats 2000000 in
-- Entrywise reconstruction of nine outer products and nine trace products is finite arithmetic.
set_option backward.isDefEq.respectTransparency false in
/-- Conjecture 1 is false: the nine effects `(k_a/46) v_a v_a†` form a rank-one MIC,
and the nine consecutive pairs of a cycle are orthogonal. -/
theorem result : ¬ claim := by
  classical
  have hpsd : ∀ a, (effect a).PosSemidef := by
    intro a
    apply (Matrix.posSemidef_vecMulVec_self_star (vec a)).smul
    fin_cases a <;> norm_num [k]
  have hsum : (∑ a, effect a) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [effect, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.star_apply, Complex.real_smul]
    all_goals norm_num [k, vec, Fin.sum_univ_succ, Matrix.one_apply]
    all_goals apply Complex.ext <;> norm_num
  have hrank : ∀ a, (effect a).rank = 1 := by
    intro a
    have hle : (effect a).rank ≤ 1 := by
      have he : effect a = vecMulVec ((k a / 46) • vec a) (star (vec a)) := by
        ext i j
        simp only [effect, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
          Pi.star_apply, Complex.real_smul]
        ring
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _
    let t : Fin 3 := if a = 4 then 1 else 0
    have hn : ((effect a).submatrix (fun _ : Fin 1 => t)
        (fun _ : Fin 1 => t)).det ≠ 0 := by
      simp only [Matrix.det_fin_one, Matrix.submatrix_apply, effect, Matrix.smul_apply,
        vecMulVec_apply, Pi.star_apply, Complex.real_smul]
      fin_cases a <;> norm_num [t, vec, k, Fin.ext_iff, Matrix.cons_val, Complex.ext_iff]
    have hlo := Matrix.rank_submatrix_le (effect a) (fun _ : Fin 1 => t)
      (fun _ : Fin 1 => t)
    rw [Matrix.rank_of_det_ne_zero hn] at hlo
    simpa using Nat.le_antisymm hle hlo
  have hspan : ∀ H : Matrix (Fin 3) (Fin 3) ℂ, H.IsHermitian →
      ∃ c : Fin 9 → ℝ, H = ∑ a, c a • effect a := by
    intro H hH
    refine ⟨coeff H, ?_⟩
    have h00 := congrArg Complex.im (hH.apply 0 0)
    have h11 := congrArg Complex.im (hH.apply 1 1)
    have h22 := congrArg Complex.im (hH.apply 2 2)
    have h01r := congrArg Complex.re (hH.apply 0 1)
    have h01i := congrArg Complex.im (hH.apply 0 1)
    have h02r := congrArg Complex.re (hH.apply 0 2)
    have h02i := congrArg Complex.im (hH.apply 0 2)
    have h12r := congrArg Complex.re (hH.apply 1 2)
    have h12i := congrArg Complex.im (hH.apply 1 2)
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at *
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp only [effect, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.star_apply, Complex.real_smul]
    all_goals norm_num [k, vec, coeff, J, coords, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Fin.isValue]
    all_goals simp only [show (2 : Fin 3) = ⟨2, by decide⟩ from rfl] at *
    all_goals ring_nf
    all_goals linarith
  have hMIC : IsRankOneMIC effect :=
    ⟨hpsd, hsum, hrank, fun a => (hpsd a).isHermitian, hspan⟩
  let s : Finset (Fin 9 × Fin 9) :=
    {(0, 1), (0, 8), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8)}
  have hsub : s ⊆ orthogonalPairs effect := by
    intro p hp
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [orthogonalPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    all_goals constructor
    all_goals first | decide |
      (simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
       dsimp [effect, k, vec, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction,
         Fin.induction.go, Fin.ofNat,
         Matrix.vecMulVec, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply]
       apply Complex.ext <;> norm_num)
  have hc : s.card = 9 := by decide
  intro h
  have hle := h effect hMIC
  have hlo := Finset.card_le_card hsub
  omega

end D5.S3.Quantum.Measurement.QutritRankOneMicOrthogonalPairs
