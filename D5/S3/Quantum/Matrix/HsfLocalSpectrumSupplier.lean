/- GID: D5/S3/Quantum/Matrix/HsfLocalSpectrumSupplier
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfLocalSpectrumSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Actual finite-spectrum and uniform-radius factorial CFC suppliers. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfLocalSpectrumUniformKernel

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier

variable {n : Type*} [Fintype n] [DecidableEq n]

open private tr tr_comm tr_cycle frob_nonneg frob_mul frob_sq_sum
  abs_reTrace_mul frob_sq_hermitian spectralTau_bounds crossGap_pos schurFirst schurFirst_hermitian
  schurFirst_norm quadraticDefect frob_entry_mono rootP pencilDirection actualCoeff
  actual_first_second spectralTau_self quadraticDefect_eq balanceP_rpow balanced_trace_normalization allZ_polynomial
  radial_trace_reduction radial_coefficients actual_local_supplier
  from D5.S3.Quantum.Matrix.HsfLocalSpectrumCoefficients
open private spectralDen_comm spectralRho spectralRho_nonneg spectralRho_comm spectralRho_sq spectralRho_triangle
  cyclicGamma cyclicGamma_bounds defect_kernel_uniform
  from D5.S3.Quantum.Matrix.HsfLocalSpectrumUniformKernel

section DiagonalJets
open scoped Matrix.Norms.L2Operator
/-- Quantitative local all-Z supplier for actual factorial CFC derivatives at
an arbitrary finite positive diagonal spectrum. Equal-level blocks of H vanish;
the spectrum may have repeated levels, and H = 0 is included. -/
theorem finite_spectrum_local_supplier {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hlevels : ∃ i j, p i ≠ p j)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (hsupport : ∀ i j, p i = p j → H i j = 0)
    (hradius : frob H ≤ 3 * crossGap p hlevels / 32)
    (Z : Matrix (Fin d) (Fin d) ℂ) (hZ : Z.IsHermitian) :
    let P : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (p i : ℂ))
    let S := (1 : Matrix (Fin d) (Fin d) ℂ) + H
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P ^ 3 + t • (CFC.rpow P (3 / 2 : ℝ) * S *
        CFC.rpow P (3 / 2 : ℝ))) (2 / 3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    0 < crossGap p hlevels ∧ crossGap p hlevels * frob H ^ 2 / 6 ≤
      (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
        (5 / 48 : ℝ) • (B 1) ^ 3).trace.re := by
  dsimp only
  refine ⟨crossGap_pos hp hlevels, ?_⟩
  simpa only [actualCoeff, RpowPencilTaylor.jetCoeff, pencilDirection,
    balanceP_rpow hp, rootP, tr] using
      actual_local_supplier hp hlevels hH hsupport hradius hZ

#print axioms finite_spectrum_local_supplier

/-- General ordered shifted identity for actual factorial CFC jets.
This consumed bridge reuses the existing coordinate and trace-normalization
proofs; it asserts no new supplier positivity. Its full dependent
source-selection binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/23103. -/
theorem actual_shifted_supplier_identity (p : n → ℝ) (hp : ∀ i, 0 < p i)
    (S Z : Matrix n n ℂ) (hS : S.IsHermitian) :
    let P : Matrix n n ℂ := diagonal (fun i => (p i : ℂ))
    let F := fun t : ℝ => P⁻¹*CFC.rpow (P^3+t •
      (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    let X : Matrix n n ℂ := fun i j => (spectralTau (p i) (p j) : ℂ)*S i j
    let Q : Matrix n n ℂ := fun i j => ∑ k,
      (((2/3 : ℝ)*spectralTau (p i) (p k)*spectralTau (p k) (p j)+
        3*spectralKernel (p i) (p j) (p k) : ℝ) : ℂ)*S i k*S k j
    let W := Z+(1/3 : ℝ) • X
    6*(B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        4*(Q*W).trace.re+4*(X*W*W).trace.re := by
  let X := schurFirst p S
  let D := quadraticDefect p S
  let W := Z+(1/3 : ℝ) • X
  have hc := actual_first_second hp hS
  have hc₁ : actualCoeff p S 1 = (2/3 : ℝ) • X := hc.1
  have hc₂ : actualCoeff p S 2 =
      -(1/9 : ℝ) • (X*X)-(1/3 : ℝ) • D := by
    rw [hc.2]
    dsimp only [D, X]
    rw [quadraticDefect_eq]
    module
  have ht := (balanced_trace_normalization hp hS).2
  rw [hc₁, hc₂] at ht
  have hpoly := allZ_polynomial X D Z (actualCoeff p S 3) (tr (S^3)) ht
  have hcycle : tr (X*Z*X) = tr (X*X*Z) := by
    rw [tr_cycle, tr_cycle]
  have hcomm : tr (D*X) = tr (X*D) := tr_comm D X
  have heq :
      6*tr (actualCoeff p S 3+(2 : ℝ) • (Z*actualCoeff p S 2)+
        actualCoeff p S 1*Z^2-(5/48 : ℝ) • (actualCoeff p S 1)^3) =
      (4*tr (S^3)-tr (X^3))/3-4*tr ((X*X+D)*W)+4*tr (X*W*W) := by
    rw [hc₁, hc₂]
    dsimp only at hpoly
    dsimp only [W]
    simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, tr, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, Complex.real_smul, smul_eq_mul, pow_succ,
      pow_zero, mul_one, one_mul, ← mul_assoc] at hpoly ⊢
    dsimp only [tr] at hcycle hcomm
    rw [hcycle, hcomm] at hpoly ⊢
    norm_num at hpoly ⊢
    linear_combination (1/3 : ℂ)*hpoly
  have hQ : (fun i j => ∑ k,
      (((2/3 : ℝ)*spectralTau (p i) (p k)*spectralTau (p k) (p j)+
        3*spectralKernel (p i) (p j) (p k) : ℝ) : ℂ)*S i k*S k j) = X*X+D := by
    ext i j
    simp only [X, D, schurFirst, quadraticDefect, Matrix.add_apply,
      Matrix.mul_apply, mul_add, add_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [← hQ] at heq
  have hre := congrArg Complex.re heq
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr] at hre
  dsimp only [X, W, schurFirst] at hre
  convert hre using 1 <;>
    norm_num [actualCoeff, RpowPencilTaylor.jetCoeff, pencilDirection,
    balanceP_rpow hp, rootP, X, W, schurFirst, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, Complex.real_smul,
    Complex.add_re, Complex.sub_re, Complex.mul_re] <;> rfl

#print axioms actual_shifted_supplier_identity

end DiagonalJets

section Uniform

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

section UniformFrobenius
open scoped Matrix.Norms.Frobenius

private def modulusMatrix (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (‖H i j‖ : ℂ)

private def rhoMatrix (p : n → ℝ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (spectralRho (p i) (p j)*‖H i j‖ : ℝ)

private theorem modulusMatrix_frob (H : Matrix n n ℂ) : frob (modulusMatrix H) = frob H := by
  apply (sq_eq_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
  simp only [frob_sq_sum, modulusMatrix, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

private theorem rhoMatrix_gap {p : n → ℝ} (hp : ∀ i, 0 < p i) (H : Matrix n n ℂ) :
    frob (rhoMatrix p H)^2 = frob H^2-frob (schurFirst p H)^2 := by
  rw [frob_sq_sum, frob_sq_sum, frob_sq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rhoMatrix, schurFirst, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, mul_pow]
  rw [spectralRho_sq (hp i) (hp j)]
  ring

private theorem quadraticDefect_uniform {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (H : Matrix n n ℂ) :
    frob (quadraticDefect p H)^2 ≤ (1024/81)*frob H^2*
      (frob H^2-frob (schurFirst p H)^2) := by
  let B := modulusMatrix H
  let W := rhoMatrix p H
  have hentry (i j : n) : ‖quadraticDefect p H i j‖ ≤
      ‖((16/9 : ℝ) • (W*B+B*W)) i j‖ := by
    have he : (W*B+B*W) i j = ((∑ k,
        (spectralRho (p i) (p k)+spectralRho (p k) (p j))*‖H i k‖*‖H k j‖ : ℝ) : ℂ) := by
      simp only [W, B, rhoMatrix, modulusMatrix, Matrix.add_apply, Matrix.mul_apply,
        Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_add,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hn : 0 ≤ ∑ k, (spectralRho (p i) (p k)+spectralRho (p k) (p j))*‖H i k‖*‖H k j‖ := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (mul_nonneg (add_nonneg (spectralRho_nonneg _ _) (spectralRho_nonneg _ _))
        (norm_nonneg _)) (norm_nonneg _)
    simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 16/9), he, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hn]
    calc
      _ ≤ ∑ k, ‖((3*spectralKernel (p i) (p j) (p k)-
          spectralTau (p i) (p k)*spectralTau (p k) (p j)/3 : ℝ) : ℂ)*H i k*H k j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k, (16/9)*((spectralRho (p i) (p k)+spectralRho (p k) (p j))*‖H i k‖*‖H k j‖) := by
        apply Finset.sum_le_sum
        intro k _
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        nlinarith only [mul_le_mul_of_nonneg_right
          (defect_kernel_uniform (hp i) (hp j) (hp k))
          (mul_nonneg (norm_nonneg (H i k)) (norm_nonneg (H k j)))]
      _ = _ := by rw [Finset.mul_sum]
  have hnorm : frob (quadraticDefect p H) ≤ (32/9)*frob W*frob H := by
    calc
      _ ≤ frob ((16/9 : ℝ) • (W*B+B*W)) := frob_entry_mono _ _ hentry
      _ = (16/9)*frob (W*B+B*W) := by
        change ‖(16/9 : ℝ) • (W*B+B*W)‖ = _
        rw [norm_smul]; norm_num [frob]
      _ ≤ (16/9)*(frob (W*B)+frob (B*W)) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ (16/9)*(frob W*frob B+frob B*frob W) :=
        mul_le_mul_of_nonneg_left (add_le_add (frob_mul W B) (frob_mul B W)) (by norm_num)
      _ = _ := by rw [show frob B = frob H from modulusMatrix_frob H]; ring
  have hs := (sq_le_sq₀ (frob_nonneg (quadraticDefect p H))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32/9) (frob_nonneg W))
      (frob_nonneg H))).mpr hnorm
  have hg : frob W^2 = frob H^2-frob (schurFirst p H)^2 := rhoMatrix_gap hp H
  calc
    _ ≤ ((32/9)*frob W*frob H)^2 := hs
    _ = _ := by rw [← hg]; ring

private theorem sum_cycle {R : Type*} [AddCommMonoid R] (f : n → n → n → R) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f j k i := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private def phase (H : Matrix n n ℂ) (i j k : n) : ℂ := H i j*H j k*H k i

private theorem phase_sum_cycle (f : n → n → n → ℝ) (H : Matrix n n ℂ) :
    (∑ i, ∑ j, ∑ k, (f j k i : ℂ)*phase H i j k) =
      ∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k := by
  symm
  calc
    _ = ∑ i, ∑ j, ∑ k, (f j k i : ℂ)*phase H j k i :=
      sum_cycle (fun i j k => (f i j k : ℂ)*phase H i j k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [phase]
      ring

private theorem trace_cube_sum (M : Matrix n n ℂ) :
    tr (M^3) = ∑ i, ∑ j, ∑ k, phase M i j k := by
  simp only [tr, pow_succ, pow_zero, mul_one, one_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  rfl

private theorem spectralKernel_comm (a b c : ℝ) : spectralKernel a b c = spectralKernel b a c := by
  unfold spectralKernel
  rw [mul_comm a b, add_comm a b, spectralDen_comm b a,
    spectralDen_comm b c, spectralDen_comm c a]
  ring

private theorem trace_defect_cycle (p : n → ℝ) (H : Matrix n n ℂ) :
    tr (schurFirst p H*quadraticDefect p H) =
      ∑ i, ∑ j, ∑ k, (cyclicGamma (p i) (p j) (p k) : ℂ)*phase H i j k := by
  let f := fun i j k => spectralTau (p i) (p j)*spectralKernel (p i) (p j) (p k)
  have hc₁ := phase_sum_cycle f H
  have hc₂ := phase_sum_cycle (fun i j k => f j k i) H
  have hc₃ : (∑ i, ∑ j, ∑ k, (f k i j : ℂ)*phase H i j k) =
      ∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k := hc₂.trans hc₁
  have hentry : tr (schurFirst p H*quadraticDefect p H) =
      ∑ i, ∑ j, ∑ k,
        ((3*f i j k-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i)/3 : ℝ) : ℂ)*
          phase H i j k := by
    simp only [tr, Matrix.trace, Matrix.diag, Matrix.mul_apply, quadraticDefect,
      schurFirst, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [f, phase]
    rw [spectralKernel_comm (p j) (p i) (p k)]
    push_cast
    ring
  rw [hentry]
  have hg (i j k : n) : cyclicGamma (p i) (p j) (p k) =
      f i j k+f j k i+f k i j-
        spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i)/3 := rfl
  simp only [hg, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, sub_mul, add_mul, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hc₁ hc₃ ⊢
  rw [hc₁, hc₃]
  ring

private theorem phase_norm (H : Matrix n n ℂ) (i j k : n) :
    ‖phase H i j k‖ = ‖H i j‖*‖H j k‖*‖H k i‖ := by simp only [phase, norm_mul]

private theorem phase_sum_bound (f : n → n → n → ℝ) (H : Matrix n n ℂ) :
    |(∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k).re| ≤
      ∑ i, ∑ j, ∑ k, |f i j k| *‖H i j‖*‖H j k‖*‖H k i‖ := by
  calc
    _ ≤ ‖∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ∑ k, ‖(f i j k : ℂ)*phase H i j k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _))
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, phase_norm, mul_assoc]

private def cyclicMass (p : n → ℝ) (H : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ k, (spectralRho (p i) (p j)^2+spectralRho (p j) (p k)^2+
    spectralRho (p k) (p i)^2)*‖H i j‖*‖H j k‖*‖H k i‖

private theorem cyclicMass_bound {d : ℕ} {p : Fin d → ℝ} (hp : ∀ i, 0 < p i)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    cyclicMass p H ≤ 6*frob H*(frob H^2-frob (schurFirst p H)^2) := by
  let B := modulusMatrix H
  let W := rhoMatrix p H
  let t := fun i j k => spectralRho (p i) (p j)^2*‖H i j‖*‖H j k‖*‖H k i‖
  let u := fun i j k => spectralRho (p i) (p j)*spectralRho (p j) (p k)*‖H i j‖*‖H j k‖*‖H k i‖
  have ht₁ := sum_cycle t
  have ht₂ := sum_cycle (fun i j k => t j k i)
  have ht₃ : (∑ i, ∑ j, ∑ k, t k i j) = ∑ i, ∑ j, ∑ k, t i j k := (ht₁.trans ht₂).symm
  have hmass : cyclicMass p H = 3*∑ i, ∑ j, ∑ k, t i j k := by
    have he₁ : (∑ i, ∑ j, ∑ k, spectralRho (p j) (p k)^2*‖H i j‖*‖H j k‖*‖H k i‖) =
        ∑ i, ∑ j, ∑ k, t i j k := by
      calc
        _ = ∑ i, ∑ j, ∑ k, t j k i := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          dsimp only [t]
          ring
        _ = _ := ht₁.symm
    have he₂ : (∑ i, ∑ j, ∑ k, spectralRho (p k) (p i)^2*‖H i j‖*‖H j k‖*‖H k i‖) =
        ∑ i, ∑ j, ∑ k, t i j k := by
      calc
        _ = ∑ i, ∑ j, ∑ k, t k i j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          dsimp only [t]
          ring
        _ = _ := ht₃
    dsimp only [cyclicMass]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [he₁, he₂]
    change (∑ i, ∑ j, ∑ k, t i j k)+(∑ i, ∑ j, ∑ k, t i j k)+
      (∑ i, ∑ j, ∑ k, t i j k) = _
    ring
  have htbound : (∑ i, ∑ j, ∑ k, t i j k) ≤ 2*∑ i, ∑ j, ∑ k, u i j k := by
    have hm : (∑ i, ∑ j, ∑ k, t i j k) ≤
        (∑ i, ∑ j, ∑ k, u i j k)+(∑ i, ∑ j, ∑ k, u k i j) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have htri := spectralRho_triangle (hp i) (hp k) (hp j)
      rw [spectralRho_comm (p k) (p j)] at htri
      have h := mul_le_mul_of_nonneg_right htri
        (mul_nonneg (mul_nonneg (mul_nonneg (spectralRho_nonneg (p i) (p j)) (norm_nonneg (H i j)))
          (norm_nonneg (H j k))) (norm_nonneg (H k i)))
      dsimp [t, u]
      rw [spectralRho_comm (p k) (p i)]
      nlinarith only [h]
    have hu₁ := sum_cycle u
    have hu₂ := sum_cycle (fun i j k => u j k i)
    rw [← hu₂, ← hu₁] at hm
    linarith
  have htrace : (∑ i, ∑ j, ∑ k, u i j k) = (W*W*B).trace.re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul,
      W, B, rhoMatrix, modulusMatrix]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
    dsimp only [u]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hbound : (W*W*B).trace.re ≤ frob W^2*frob H := by
    calc
      _ ≤ |(W*W*B).trace.re| := le_abs_self _
      _ ≤ frob (W*W)*frob B := abs_reTrace_mul (W*W) B
      _ ≤ (frob W*frob W)*frob B := mul_le_mul_of_nonneg_right (frob_mul W W) (frob_nonneg B)
      _ = _ := by rw [show frob B = frob H from modulusMatrix_frob H]; ring
  have hgap := rhoMatrix_gap hp H
  change frob W^2 = _ at hgap
  rw [hmass]
  rw [htrace] at htbound
  rw [← hgap]
  nlinarith only [htbound, hbound]

private theorem cubic_uniform_bound {d : ℕ} {p : Fin d → ℝ} (hp : ∀ i, 0 < p i)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    |(4*tr (H^3)-4*tr ((schurFirst p H)^3)-6*tr (schurFirst p H*quadraticDefect p H)).re| ≤
      51*frob H*(frob H^2-frob (schurFirst p H)^2) := by
  have hAD : |(tr (schurFirst p H*quadraticDefect p H)).re| ≤ (3/4)*cyclicMass p H := by
    rw [trace_defect_cycle]
    apply (phase_sum_bound (fun i j k => cyclicGamma (p i) (p j) (p k)) H).trans
    rw [cyclicMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hg := cyclicGamma_bounds (hp i) (hp j) (hp k)
    rw [abs_of_nonneg hg.1]
    nlinarith only [mul_le_mul_of_nonneg_right hg.2
      (mul_nonneg (mul_nonneg (norm_nonneg (H i j)) (norm_nonneg (H j k))) (norm_nonneg (H k i)))]
  have hc : |(tr (H^3)-tr ((schurFirst p H)^3)).re| ≤ cyclicMass p H := by
    have he : tr (H^3)-tr ((schurFirst p H)^3) =
        ∑ i, ∑ j, ∑ k, ((1-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i) : ℝ) : ℂ)*
          phase H i j k := by
      rw [trace_cube_sum, trace_cube_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [phase, schurFirst]
      push_cast
      ring
    rw [he]
    apply (phase_sum_bound _ H).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    have ht := spectralTau_bounds (hp i) (hp j)
    have hu := spectralTau_bounds (hp j) (hp k)
    have hv := spectralTau_bounds (hp k) (hp i)
    have ht₀ := ht.1.le
    have hu₀ := hu.1.le
    have hv₀ := hv.1.le
    have ht₁ : 0 ≤ 1-spectralTau (p i) (p j) := sub_nonneg.mpr ht.2
    have hu₁ : 0 ≤ 1-spectralTau (p j) (p k) := sub_nonneg.mpr hu.2
    have hv₁ : 0 ≤ 1-spectralTau (p k) (p i) := sub_nonneg.mpr hv.2
    have htu : spectralTau (p i) (p j)*spectralTau (p j) (p k) ≤ 1 := by
      simpa using mul_le_mul ht.2 hu.2 hu₀ (by norm_num : (0 : ℝ) ≤ 1)
    have hn : 0 ≤ 1-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i) := by
      have h := mul_le_mul htu hv.2 hv₀ (by norm_num : (0 : ℝ) ≤ 1)
      norm_num at h
      linarith
    have hb : 1-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i) ≤
        spectralRho (p i) (p j)^2+spectralRho (p j) (p k)^2+spectralRho (p k) (p i)^2 := by
      rw [spectralRho_sq (hp i) (hp j), spectralRho_sq (hp j) (hp k), spectralRho_sq (hp k) (hp i)]
      have h₁ := mul_nonneg ht₁ hu₁
      have h₂ := mul_nonneg hv₁ (sub_nonneg.mpr htu)
      have h₃ := mul_nonneg ht₀ ht₁
      have h₄ := mul_nonneg hu₀ hu₁
      have h₅ := mul_nonneg hv₀ hv₁
      nlinarith only [h₁, h₂, h₃, h₄, h₅]
    rw [abs_of_nonneg hn]
    nlinarith only [mul_le_mul_of_nonneg_right hb
      (mul_nonneg (mul_nonneg (norm_nonneg (H i j)) (norm_nonneg (H j k))) (norm_nonneg (H k i)))]
  have hs := cyclicMass_bound hp hH
  calc
    _ = |4*(tr (H^3)-tr ((schurFirst p H)^3)).re+
        (-6)*(tr (schurFirst p H*quadraticDefect p H)).re| := by
      congr 1
      norm_num [Complex.sub_re, Complex.mul_re]
      ring
    _ ≤ |4*(tr (H^3)-tr ((schurFirst p H)^3)).re|+
        |(-6)*(tr (schurFirst p H*quadraticDefect p H)).re| := abs_add_le _ _
    _ = 4*|(tr (H^3)-tr ((schurFirst p H)^3)).re|+
        6*|(tr (schurFirst p H*quadraticDefect p H)).re| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 4*cyclicMass p H+6*((3/4)*cyclicMass p H) := by linarith only [hc, hAD]
    _ ≤ _ := by nlinarith only [hs]

private theorem quadratic_remainder_uniform {d : ℕ}
    (A D R : Matrix (Fin d) (Fin d) ℂ) (hR : R.IsHermitian)
    (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1/2) (hA : frob A ≤ r) :
    -6*frob D^2 ≤ 12*(((1+A)*R*R).trace.re-(D*R).trace.re) := by
  let q := frob R
  have hq : 0 ≤ q := frob_nonneg R
  have ha : |(A*(R*R)).trace.re| ≤ r*q^2 := by
    calc
      _ ≤ frob A*frob (R*R) := abs_reTrace_mul A (R*R)
      _ ≤ r*(q*q) := mul_le_mul hA (frob_mul R R) (frob_nonneg _) hr
      _ = r*q^2 := by ring
  have hd : |(D*R).trace.re| ≤ frob D*q := abs_reTrace_mul D R
  have he : ((1+A)*R*R).trace.re = q^2+(A*(R*R)).trace.re := by
    simp only [add_mul, one_mul, Matrix.trace_add, Complex.add_re, mul_assoc,
      frob_sq_hermitian hR]
    rfl
  rw [he]
  have hlow := (abs_le.mp ha).1
  have hhigh := (abs_le.mp hd).2
  have hhalf := mul_le_mul_of_nonneg_right hrsmall (sq_nonneg q)
  nlinarith [sq_nonneg (q-frob D)]


private theorem actual_uniform_supplier {d : ℕ} {p : Fin d → ℝ}
    (hp : ∀ i, 0 < p i) {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (hradius : frob H ≤ 1/20) {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.IsHermitian) :
    (frob H^2-frob (schurFirst p H)^2)/6 ≤
      (tr (actualCoeff p (1+H) 3+(2 : ℝ) • (Z*actualCoeff p (1+H) 2)+
        actualCoeff p (1+H) 1*Z^2-(5/48 : ℝ) • (actualCoeff p (1+H) 1)^3)).re := by
  let r := frob H
  let A := schurFirst p H
  let D := quadraticDefect p H
  let T := (1 : Matrix (Fin d) (Fin d) ℂ)+A
  let R := Z-(1/6 : ℝ) • T
  let g := frob H^2-frob A^2
  have hr : 0 ≤ r := frob_nonneg H
  have hrsmall : r ≤ 1/20 := hradius
  have hrhalf : r ≤ 1/2 := by linarith
  have hA : frob A ≤ r := schurFirst_norm hp H
  have hAh : A.IsHermitian := schurFirst_hermitian p hH
  have hTh : T.IsHermitian := Matrix.isHermitian_one.add hAh
  have hRh : R.IsHermitian :=
    hZ.sub (hTh.smul (IsSelfAdjoint.of_nonneg (by norm_num : (0 : ℝ) ≤ 1/6)))
  have hg : 0 ≤ g := by
    have hg := rhoMatrix_gap hp H
    change _ = g at hg
    rw [← hg]
    positivity
  have hD : frob D^2 ≤ (1024/81)*r^2*g := quadraticDefect_uniform hp H
  have hh := cubic_uniform_bound hp hH
  change |(4*tr (H^3)-4*tr (A^3)-6*tr (A*D)).re| ≤ 51*r*g at hh
  have he := quadratic_remainder_uniform A D R hRh r hr hrhalf hA
  have hs : ((1 : Matrix (Fin d) (Fin d) ℂ)+H).IsHermitian := Matrix.isHermitian_one.add hH
  obtain ⟨hc₁, hc₂, htraceD⟩ := radial_coefficients hp hH
  have ht := (balanced_trace_normalization hp hs).2
  rw [hc₁, hc₂] at ht
  have hpoly := allZ_polynomial T D Z (actualCoeff p (1+H) 3) (tr ((1+H)^3)) ht
  have hlin : tr H = tr A := by
    simp [A, schurFirst, tr, Matrix.trace, Matrix.diag, spectralTau_self (hp _)]
  have hrad := radial_trace_reduction H A D hlin htraceD
  have hid : 18*(tr (actualCoeff p (1+H) 3+
        (2 : ℝ) • (Z*actualCoeff p (1+H) 2)+actualCoeff p (1+H) 1*Z^2-
        (5/48 : ℝ) • (actualCoeff p (1+H) 1)^3)) =
      6*(tr (H*H)-tr (A*A))+(4*tr (H^3)-4*tr (A^3)-6*tr (A*D))+
        12*(tr (T*R*R)-tr (D*R)) := by
    rw [hc₁, hc₂]
    dsimp only at hpoly
    simp only [tr, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      Complex.real_smul, smul_eq_mul, pow_succ, pow_zero, mul_one, one_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← mul_assoc] at hpoly ⊢
    simp only [tr, pow_succ, pow_zero, mul_one, one_mul] at hrad
    dsimp only [T, R, A, D] at hpoly hrad ⊢
    norm_num at hpoly ⊢
    linear_combination hpoly+hrad
  have hidre := congrArg Complex.re hid
  have hgap : (tr (H*H)-tr (A*A)).re = g := by
    simp only [Complex.sub_re, tr, frob_sq_hermitian hH, frob_sq_hermitian hAh]
    rfl
  have hmargin : 3*g ≤ 6*g-51*r*g-6*frob D^2 := by
    have hr₂ : r^2 ≤ (1/20 : ℝ)^2 := (sq_le_sq₀ hr (by norm_num)).mpr hrsmall
    have h₁ := mul_le_mul_of_nonneg_right hrsmall hg
    have h₂ := mul_le_mul_of_nonneg_right hr₂ hg
    nlinarith only [hD, h₁, h₂, hg]
  have hl := (abs_le.mp hh).1
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr] at hidre hgap hl
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr, T] at he
  change g/6 ≤ _
  norm_num [tr, Complex.add_re, Complex.sub_re, Complex.mul_re]
  linarith

end UniformFrobenius

section UniformActual
open scoped Matrix.Norms.L2Operator

/-- Uniform-radius local all-Z supplier for actual factorial-normalized CFC
jets. The spectrum is arbitrary positive, including empty and repeated levels;
H and Z are arbitrary Hermitian matrices, with only a Frobenius bound on H. -/
theorem finite_spectrum_uniform_local_supplier {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (hradius : frob H ≤ 1/20) (Z : Matrix (Fin d) (Fin d) ℂ) (hZ : Z.IsHermitian) :
    let P : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (p i : ℂ))
    let S := (1 : Matrix (Fin d) (Fin d) ℂ)+H
    let F := fun t : ℝ => P⁻¹*
      CFC.rpow (P^3+t • (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    let A : Matrix (Fin d) (Fin d) ℂ := fun i j => (spectralTau (p i) (p j) : ℂ)*H i j
    (frob H^2-frob A^2)/6 ≤
      (B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re := by
  dsimp only
  change (frob H^2-frob (schurFirst p H)^2)/6 ≤ _
  simpa only [actualCoeff, RpowPencilTaylor.jetCoeff, pencilDirection,
    balanceP_rpow hp, rootP, tr] using actual_uniform_supplier hp hH hradius hZ

#print axioms finite_spectrum_uniform_local_supplier
end UniformActual

end Uniform

end D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
