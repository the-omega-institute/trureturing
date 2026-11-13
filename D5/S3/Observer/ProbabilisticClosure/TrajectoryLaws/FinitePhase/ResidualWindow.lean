/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite stochastic phase residuals control complex moving-window readouts. -/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-! Finite stochastic phase residuals and moving-window bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The complex-linear action of a real transition matrix. -/
def complexMatrix (P : Matrix I I ℝ) : Matrix I I ℂ := P.map Complex.ofRealHom

/-- Some return length at most the number of states has a small phase gap. -/
theorem phase_residual [Nonempty I] (P : Matrix I I ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (w : ℂ) (hw : ‖w‖ = 1)
    (v : I → ℂ) (hv : v ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ Fintype.card I ∧
      ‖1 - w ^ r‖ ^ 2 * ‖v‖ ≤
        8 * (Fintype.card I : ℝ) * ‖v - w • (complexMatrix P *ᵥ v)‖ := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖)
    Finset.univ_nonempty
  have hc : ‖v i₀‖ = ‖v‖ := le_antisymm (norm_le_pi_norm v i₀)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg (v i₀))).mpr fun i =>
      hi₀ i (Finset.mem_univ i))
  let c := v i₀
  let M : ℝ := ‖v‖
  let e : I → ℂ := v - w • (complexMatrix P *ᵥ v)
  let E : ℝ := ‖e‖
  let f : ℕ → I → ℝ := fun t i => (w ^ t * v i * conj c).re
  have hM : 0 < M := norm_pos_iff.mpr hv
  have hE : 0 ≤ E := norm_nonneg e
  have hcn : ‖c‖ = M := hc
  have hpow (t : ℕ) : ‖w ^ t‖ = 1 := by simp [norm_pow, hw]
  have hrec (t : ℕ) (i : I) : f t i =
      (∑ j, P i j * f (t+1) j) + (w ^ t * e i * conj c).re := by
    have he : v i = w * (∑ j, (P i j : ℂ) * v j) + e i := by
      dsimp [e, complexMatrix, Matrix.mulVec, dotProduct]
      ring
    have hz : w ^ t * v i * conj c =
        (∑ j, (P i j : ℂ) * (w ^ (t+1) * v j * conj c)) +
          w ^ t * e i * conj c := by
      rw [he, mul_add, add_mul]
      congr 1
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    change (w ^ t * v i * conj c).re = _
    rw [hz, Complex.add_re, Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  have herr (t : ℕ) (i : I) : (w ^ t * e i * conj c).re ≤ M * E := by
    calc
      _ ≤ ‖w ^ t * e i * conj c‖ := Complex.re_le_norm _
      _ = ‖e i‖ * M := by simp [norm_mul, hpow, hcn]
      _ ≤ E * M := mul_le_mul_of_nonneg_right (norm_le_pi_norm e i) hM.le
      _ = M * E := mul_comm _ _
  have hs : ∀ t : ℕ, ∃ i : I, M^2 - (t:ℝ)*M*E ≤ f t i := by
    intro t
    induction t with
    | zero =>
      refine ⟨i₀, ?_⟩
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      change M ^ 2 ≤ (w ^ 0 * c * conj c).re
      rw [pow_zero, one_mul]
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hcn]
    | succ t ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (f (t+1))
        Finset.univ_nonempty
      have hav : (∑ k, P i k * f (t+1) k) ≤ f (t+1) j := by
        calc
          _ ≤ ∑ k, P i k * f (t+1) j := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hj k (Finset.mem_univ k))
              (Matrix.nonneg_of_mem_rowStochastic hP)
          _ = f (t+1) j := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP, one_mul]
      have hr := hrec t i
      have he := herr t i
      refine ⟨j, ?_⟩
      push_cast
      nlinarith
  choose idx hidx using hs
  have hdist (t : ℕ) : ‖w ^ t * v (idx t) - c‖ ^ 2 ≤ 2*(t:ℝ)*M*E := by
    have hn : ‖w ^ t * v (idx t)‖ ≤ M := by
      simpa only [norm_mul, hpow, one_mul] using norm_le_pi_norm v (idx t)
    have hsquare := sq_le_sq₀ (norm_nonneg _) hM.le |>.mpr hn
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hcn]
    have hi := hidx t
    dsimp [f] at hi
    nlinarith
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin (Fintype.card I + 1) => idx t.val) (by simp)
  have habval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  wlog hlt : a.val < b.val generalizing a b
  · exact this b a (Ne.symm hab) heq.symm (Ne.symm habval) (by omega)
  let r := b.val - a.val
  have hr : 1 ≤ r ∧ r ≤ Fintype.card I := by
    dsimp [r]
    have := b.isLt
    omega
  refine ⟨r, hr.1, hr.2, ?_⟩
  let da := w ^ a.val * v (idx a.val) - c
  let db := w ^ b.val * v (idx b.val) - c
  have hid : db - w ^ r * da = c * (w ^ r - 1) := by
    dsimp [da, db]
    rw [heq, show b.val = a.val + r by dsimp [r]; omega, pow_add]
    ring
  have hda := hdist a.val
  have hdb := hdist b.val
  have htri : ‖db - w ^ r * da‖ ≤ ‖db‖ + ‖da‖ := by
    simpa only [norm_mul, hpow, one_mul] using norm_sub_le db (w^r*da)
  have htri2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖db‖+‖da‖)).mpr htri
  have hgap : ‖db - w ^ r * da‖ ^ 2 = M^2 * ‖1-w^r‖^2 := by
    rw [hid, norm_mul, hcn, norm_sub_rev]
    ring
  have habS : (a.val:ℝ) + (b.val:ℝ) ≤ 2*(Fintype.card I : ℝ) := by
    exact_mod_cast (show a.val + b.val ≤ 2*Fintype.card I from by
      have := a.isLt; have := b.isLt; omega)
  have hbound : M^2 * ‖1-w^r‖^2 ≤ 8*(Fintype.card I:ℝ)*M*E := by
    rw [hgap] at htri2
    have hsum := mul_le_mul_of_nonneg_right habS (mul_nonneg hM.le hE)
    change ‖da‖^2 ≤ _ at hda
    change ‖db‖^2 ≤ _ at hdb
    nlinarith [sq_nonneg (‖db‖-‖da‖)]
  have hcancel : M * (‖1-w^r‖^2 * M) ≤ M * (8*(Fintype.card I:ℝ)*E) := by
    nlinarith [hbound]
  exact (mul_le_mul_iff_right₀ hM).mp (by simpa only [mul_comm M] using hcancel)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
