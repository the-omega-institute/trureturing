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
      _ = ‖e i‖ * M := by simp [hpow, hcn]
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


private theorem weighted_bound (α : I → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hαsum : ∑ i, α i = 1) (v : I → ℂ) :
    ‖∑ i, (α i : ℂ) * v i‖ ≤ ‖v‖ := by
  calc
    _ ≤ ∑ i, ‖(α i : ℂ) * v i‖ := norm_sum_le _ _
    _ = ∑ i, α i * ‖v i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hα i)]
    _ ≤ ∑ i, α i * ‖v‖ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (hα i)
    _ = ‖v‖ := by rw [← Finset.sum_mul, hαsum, one_mul]

private theorem stochastic_contraction (P : Matrix I I ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (v : I → ℂ) :
    ‖complexMatrix P *ᵥ v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  exact weighted_bound (P i) (fun _ => Matrix.nonneg_of_mem_rowStochastic hP)
    (Matrix.sum_row_of_mem_rowStochastic hP i) v

/-- The exact complex moving average of the real stochastic readout at an integer frequency. -/
def phaseWindow (P : Matrix I I ℝ) (α b : I → ℝ) (z : ℂ) (j : ℤ) (m N : ℕ) : ℂ :=
  (∑ k ∈ Finset.range N,
    z ^ (j * (m+k : ℕ)) * ((α ⬝ᵥ ((P ^ (m+k)) *ᵥ b) : ℝ) : ℂ)) / (N : ℂ)

/-- Nonresonant phases have uniformly small moving-window averages. -/
theorem window_average [Nonempty I] (P : Matrix I I ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (z : ℂ) (hz : ‖z‖ = 1)
    (j : ℤ) (_hj : j ≠ 0) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ r : ℕ, 1 ≤ r → r ≤ Fintype.card I → γ ≤ ‖1-z^(j*(r:ℤ))‖)
    (α b : I → ℝ) (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) (m N : ℕ) (hN : 0 < N) :
    ‖phaseWindow P α b z j m N‖ ≤
      16 * (Fintype.card I : ℝ) / ((N : ℝ) * γ^2) := by
  let w : ℂ := z ^ j
  have hw : ‖w‖ = 1 := by simp [w, hz]
  have hp (t : ℕ) : z^(j*(t:ℤ)) = w^t := by
    rw [zpow_mul, zpow_natCast]
  let bc : I → ℂ := fun i => (b i : ℂ)
  let u : ℕ → I → ℂ := fun t => (complexMatrix P)^t *ᵥ bc
  have hbc : ‖bc‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    simpa only [bc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i).1]
      using (hb i).2
  have hu (t : ℕ) : ‖u t‖ ≤ 1 := by
    have h := stochastic_contraction (P^t) ((Matrix.rowStochastic ℝ I).pow_mem hP t) bc
    simpa only [u, complexMatrix, Matrix.map_pow] using h.trans hbc
  have hstep (t : ℕ) : complexMatrix P *ᵥ u t = u (t+1) := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, ← pow_succ']
  let V : I → ℂ := ∑ k ∈ Finset.range N, w^k • u (m+k)
  have htel : V - w • (complexMatrix P *ᵥ V) = u m - w^N • u (m+N) := by
    dsimp only [V]
    rw [Matrix.mulVec_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    have he : ∀ k : ℕ,
        w^k • u (m+k) - w • (complexMatrix P *ᵥ (w^k • u (m+k))) =
        (fun t => w^t • u (m+t)) k - (fun t => w^t • u (m+t)) (k+1) := by
      intro k
      rw [Matrix.mulVec_smul, smul_smul, hstep, ← pow_succ']
      congr 2 <;> omega
    simp_rw [he]
    rw [Finset.sum_range_sub']
    simp only [pow_zero, one_smul, Nat.add_zero]
  have hres : ‖V - w • (complexMatrix P *ᵥ V)‖ ≤ 2 := by
    rw [htel]
    have h := (norm_sub_le (u m) (w^N •u (m+N))).trans
      (add_le_add (hu m) (show ‖w^N •u (m+N)‖ ≤ 1 from by
        simpa only [norm_smul, norm_pow, hw, one_pow, one_mul] using hu (m+N)))
    norm_num at h ⊢
    exact h
  have hV : γ^2 * ‖V‖ ≤ 16 * (Fintype.card I : ℝ) := by
    by_cases hv : V = 0
    · simp only [hv, norm_zero, mul_zero]
      positivity
    obtain ⟨r, hr, hrS, h⟩ := phase_residual P hP w hw V hv
    have hg := hgap r hr hrS
    rw [hp] at hg
    have hsq : γ^2 ≤ ‖1-w^r‖^2 := (sq_le_sq₀ hγ.le (norm_nonneg _)).mpr hg
    have hfirst := mul_le_mul_of_nonneg_right hsq (norm_nonneg V)
    have hlast := mul_le_mul_of_nonneg_left hres
      (by positivity : 0 ≤ 8*(Fintype.card I:ℝ))
    nlinarith
  have hcast (t : ℕ) : ((α ⬝ᵥ ((P^t)*ᵥb) : ℝ) : ℂ) =
      ∑ i, (α i : ℂ) * u t i := by
    change Complex.ofRealHom (α ⬝ᵥ ((P^t)*ᵥb)) = _
    rw [Complex.ofRealHom.map_dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have he := Complex.ofRealHom.map_mulVec (P^t) b i
    simpa only [complexMatrix, Matrix.map_pow, u, bc, Function.comp_def, Complex.ofRealHom_eq_coe] using he
  have hav : phaseWindow P α b z j m N =
      (w^m * (∑ i, (α i : ℂ) * V i)) / (N:ℂ) := by
    unfold phaseWindow
    congr 1
    simp_rw [hp, hcast]
    rw [Finset.mul_sum]
    simp only [V, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  have hαV := weighted_bound α hα hαsum V
  have hN' : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hγ2 : 0 < γ^2 := sq_pos_of_pos hγ
  rw [hav, norm_div, norm_mul, norm_pow, hw, one_pow, one_mul,
    Complex.norm_natCast]
  apply (div_le_iff₀ hN').mpr
  have hbV : ‖V‖ ≤ 16*(Fintype.card I:ℝ)/γ^2 := (le_div_iff₀ hγ2).mpr (by nlinarith [hV])
  calc
    ‖∑ i, (α i : ℂ)*V i‖ ≤ ‖V‖ := hαV
    _ ≤ 16*(Fintype.card I:ℝ)/γ^2 := hbV
    _ = (16*(Fintype.card I:ℝ)/((N:ℝ)*γ^2)) * N := by
      field_simp

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
