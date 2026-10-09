/- GID: D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound
   mirror-E: none
   anchors: []
   utility: none
   digest: Two-qutrit Weyl–Bloch ℓ1 norm has sharp separable bound 25. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import D5.S3.QuantumContext.HesseSicCertificate
import D5.S3.Weil.ZetaLinear.PosIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

noncomputable section

open Matrix
open scoped Kronecker ComplexOrder

namespace D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound

def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

def W (k l : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun j c => if c = j + l then ω ^ (j.val * k.val) else 0

def bloch
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (i j k l : Fin 3) : ℂ :=
  (ρ * (W i j ⊗ₖ W k l)ᴴ).trace

def l1 (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ‖bloch ρ i j k l‖

def IsDensity {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

def IsSeparable
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ)
    (σ : Fin n → Matrix (Fin 3) (Fin 3) ℂ)
    (τ : Fin n → Matrix (Fin 3) (Fin 3) ℂ),
    (∀ t, 0 ≤ p t) ∧
      (∑ t, p t = 1) ∧
      (∀ t, IsDensity (σ t) ∧ IsDensity (τ t)) ∧
      ρ = ∑ t, (p t : ℂ) • (σ t ⊗ₖ τ t)

def claim : Prop :=
  (∀ ρ, IsSeparable ρ → l1 ρ ≤ 25) ∧
    (∃ ρ, IsSeparable ρ ∧ l1 ρ = 25) ∧
    (∃ ψ : Fin 3 × Fin 3 → ℂ,
      star ψ ⬝ᵥ ψ = 1 ∧ 25 < l1 (vecMulVec ψ (star ψ)))

private lemma omega_parts : ω.re = -1 / 2 ∧ ω.im = Real.sqrt 3 / 2 := by
  have harg : (2 * Real.pi * Complex.I / 3 : ℂ) =
      (2 * Real.pi / 3 : ℝ) * Complex.I := by push_cast; ring
  have hangle : (2 * Real.pi / 3 : ℝ) = 2 * (Real.pi / 3) := by ring
  unfold ω
  rw [harg]
  constructor
  · rw [Complex.exp_ofReal_mul_I_re, hangle, Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  · rw [Complex.exp_ofReal_mul_I_im, hangle, Real.sin_two_mul,
      Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring

private abbrev a (σ : Matrix (Fin 3) (Fin 3) ℂ) (k l : Fin 3) : ℂ :=
  (σ * (W k l)ᴴ).trace

private abbrev loc (σ : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  ∑ k, ∑ l, ‖a σ k l‖

private lemma coefficient_formula (σ : Matrix (Fin 3) (Fin 3) ℂ) (k l : Fin 3) :
    a σ k l = ∑ j, σ j (j + l) * star (ω ^ (j.val * k.val)) := by
  classical
  simp only [a, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (j + l)]
  · simp only [W]
    simp
  · intro c _ hc
    simp only [W, if_neg hc]
    simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

private lemma parseval_three (d : Fin 3 → ℂ) :
    (∑ k : Fin 3, ‖∑ j : Fin 3, d j * star (ω ^ (j.val * k.val))‖ ^ 2) =
      3 * ∑ j : Fin 3, ‖d j‖ ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs4 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hs]; norm_num
  have h3 : ω ^ 3 = 1 := D5.S3.QuantumContext.HesseSicCertificate.omega_cubed
  have h4 : ω ^ 4 = ω := by
    calc
      ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [h3]; ring
  simp only [Fin.sum_univ_succ]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.zero_mul, Nat.mul_zero, Nat.one_mul,
    Nat.mul_one, pow_zero, pow_one, star_one, mul_one]
  rw [h4]
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, pow_two,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, omega_parts.1, omega_parts.2,
    Complex.zero_re, Complex.zero_im]
  ring_nf
  simp only [hs, hs4]
  ring

private lemma density_purity (σ : Matrix (Fin 3) (Fin 3) ℂ) (hσ : IsDensity σ) :
    (∑ j, ∑ c, ‖σ j c‖ ^ 2) ≤ 1 := by
  have he : (∑ i, hσ.1.isHermitian.eigenvalues i) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    exact hσ.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hσ.2
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := hσ.1.isHermitian.eigenvalues)
    (fun i _ => hσ.1.eigenvalues_nonneg i)
  rw [he, one_pow, ← RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hσ.1.isHermitian]
    at hsq
  have hf : RHLinalg.frobSq σ = ∑ j, ∑ c, ‖σ j c‖ ^ 2 := by
    unfold RHLinalg.frobSq
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, RCLike.re_to_complex]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  rwa [hf] at hsq

private lemma coefficient_sq_sum (σ : Matrix (Fin 3) (Fin 3) ℂ)
    (hσ : IsDensity σ) : (∑ k, ∑ l, ‖a σ k l‖ ^ 2) ≤ 3 := by
  have hp (l : Fin 3) := parseval_three (fun j => σ j (j + l))
  simp_rw [← coefficient_formula σ] at hp
  have hr : (∑ l : Fin 3, ∑ j : Fin 3, ‖σ j (j + l)‖ ^ 2) =
      ∑ j : Fin 3, ∑ c : Fin 3, ‖σ j c‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Equiv.sum_comp (Equiv.addLeft j) (fun c => ‖σ j c‖ ^ 2)
  calc
    (∑ k, ∑ l, ‖a σ k l‖ ^ 2) = ∑ l, ∑ k, ‖a σ k l‖ ^ 2 := Finset.sum_comm
    _ = ∑ l, 3 * ∑ j, ‖σ j (j + l)‖ ^ 2 := by simp only [hp]
    _ = 3 * ∑ j, ∑ c, ‖σ j c‖ ^ 2 := by rw [← Finset.mul_sum, hr]
    _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left (density_purity σ hσ) (by norm_num)
    _ = 3 := by norm_num

private lemma local_bound (σ : Matrix (Fin 3) (Fin 3) ℂ) (hσ : IsDensity σ) :
    loc σ ≤ 5 := by
  classical
  have hzero : a σ 0 0 = 1 := by
    rw [coefficient_formula]
    simpa only [Fin.val_zero, Nat.mul_zero, pow_zero, star_one, mul_one,
      add_zero, Matrix.trace, Matrix.diag_apply] using hσ.2
  let s : Finset (Fin 3 × Fin 3) := Finset.univ.erase (0, 0)
  have hc : s.card = 8 := by decide
  have hsq := coefficient_sq_sum σ hσ
  have hsq' : (∑ q : Fin 3 × Fin 3, ‖a σ q.1 q.2‖ ^ 2) ≤ 3 := by
    simpa only [Fintype.sum_prod_type] using hsq
  have he := Finset.sum_erase_add Finset.univ
    (fun q : Fin 3 × Fin 3 => ‖a σ q.1 q.2‖ ^ 2) (Finset.mem_univ (0, 0))
  have hs : (∑ q ∈ s, ‖a σ q.1 q.2‖ ^ 2) ≤ 2 := by
    change (∑ q ∈ s, ‖a σ q.1 q.2‖ ^ 2) + ‖a σ 0 0‖ ^ 2 = _ at he
    rw [hzero, norm_one] at he
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun q => ‖a σ q.1 q.2‖)
  rw [hc] at hcs
  norm_num only [Nat.cast_ofNat] at hcs
  have hb : (∑ q ∈ s, ‖a σ q.1 q.2‖) ≤ 4 := by nlinarith
  have he' := Finset.sum_erase_add Finset.univ
    (fun q : Fin 3 × Fin 3 => ‖a σ q.1 q.2‖) (Finset.mem_univ (0, 0))
  change (∑ q ∈ s, ‖a σ q.1 q.2‖) + ‖a σ 0 0‖ = _ at he'
  rw [hzero, norm_one, Fintype.sum_prod_type] at he'
  change (∑ k, ∑ l, ‖a σ k l‖) ≤ 5
  linarith

private lemma product_coefficient (σ τ : Matrix (Fin 3) (Fin 3) ℂ)
    (i j k l : Fin 3) : bloch (σ ⊗ₖ τ) i j k l = a σ i j * a τ k l := by
  unfold bloch
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

private lemma product_l1 (σ τ : Matrix (Fin 3) (Fin 3) ℂ) :
    l1 (σ ⊗ₖ τ) = loc σ * loc τ := by
  simp only [l1, loc, product_coefficient, norm_mul]
  symm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  simp only [Finset.mul_sum]

private lemma product_bound (σ τ : Matrix (Fin 3) (Fin 3) ℂ)
    (hσ : IsDensity σ) (hτ : IsDensity τ) : l1 (σ ⊗ₖ τ) ≤ 25 := by
  rw [product_l1]
  calc
    loc σ * loc τ ≤ 5 * 5 := mul_le_mul (local_bound σ hσ) (local_bound τ hτ)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
      (by norm_num)
    _ = 25 := by norm_num

private lemma mixture_coefficient {n : ℕ} (p : Fin n → ℝ)
    (σ τ : Fin n → Matrix (Fin 3) (Fin 3) ℂ) (i j k l : Fin 3) :
    bloch (∑ t, (p t : ℂ) • (σ t ⊗ₖ τ t)) i j k l =
      ∑ t, (p t : ℂ) * bloch (σ t ⊗ₖ τ t) i j k l := by
  simp only [bloch, Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]

private lemma separable_bound (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hρ : IsSeparable ρ) : l1 ρ ≤ 25 := by
  obtain ⟨n, p, σ, τ, hp, hpone, hd, rfl⟩ := hρ
  have hterm (i j k l : Fin 3) :
      ‖bloch (∑ t, (p t : ℂ) • (σ t ⊗ₖ τ t)) i j k l‖ ≤
        ∑ t, p t * ‖bloch (σ t ⊗ₖ τ t) i j k l‖ := by
    rw [mixture_coefficient]
    calc
      ‖∑ t, (p t : ℂ) * bloch (σ t ⊗ₖ τ t) i j k l‖ ≤
          ∑ t, ‖(p t : ℂ) * bloch (σ t ⊗ₖ τ t) i j k l‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp _)]
  calc
    l1 (∑ t, (p t : ℂ) • (σ t ⊗ₖ τ t)) ≤
        ∑ i, ∑ j, ∑ k, ∑ l, ∑ t, p t * ‖bloch (σ t ⊗ₖ τ t) i j k l‖ := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro l _
      exact hterm i j k l
    _ = ∑ t, p t * l1 (σ t ⊗ₖ τ t) := by
      simp only [l1, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
    _ ≤ ∑ t, p t * 25 := Finset.sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_left (product_bound (σ t) (τ t) (hd t).1 (hd t).2) (hp t))
    _ = 25 := by rw [← Finset.sum_mul, hpone]; norm_num

private def sharpMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 0], ![0, 1 / 2, -1 / 2], ![0, -1 / 2, 1 / 2]]

private lemma sharp_density : IsDensity sharpMatrix := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let u : Fin 3 → ℂ := ![0, (Real.sqrt 2 / 2 : ℝ), -(Real.sqrt 2 / 2 : ℝ)]
  have hu : sharpMatrix = vecMulVec u (star u) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sharpMatrix, u, Matrix.vecMulVec_apply, Pi.star_apply,
        Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;> nlinarith
  constructor
  · rw [hu]
    exact Matrix.posSemidef_vecMulVec_self_star u
  · norm_num [sharpMatrix, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]

private lemma sharp_coefficients (k l : Fin 3) :
    ‖a sharpMatrix k l‖ = if k = 0 ∧ l = 0 then 1 else 1 / 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs4 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring, hs]
    norm_num
  have h3 : ω ^ 3 = 1 := D5.S3.QuantumContext.HesseSicCertificate.omega_cubed
  have h4 : ω ^ 4 = ω := by rw [show ω ^ 4 = ω ^ 3 * ω by ring, h3, one_mul]
  have hsq : ‖a sharpMatrix k l‖ ^ 2 =
      (if k = 0 ∧ l = 0 then 1 else 1 / 2 : ℝ) ^ 2 := by
    rw [coefficient_formula]
    fin_cases k <;> fin_cases l <;>
      norm_num [sharpMatrix, Fin.sum_univ_succ, Fin.add_def, h4] <;>
      simp_rw [← Complex.normSq_eq_norm_sq] <;>
      simp only [Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.neg_re, Complex.neg_im, Complex.ofNat_re, Complex.ofNat_im,
        Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
        omega_parts.1, omega_parts.2] <;>
      norm_num <;> ring_nf <;> simp only [hs, hs4] <;> ring
  have hr : 0 ≤ (if k = 0 ∧ l = 0 then 1 else 1 / 2 : ℝ) := by split_ifs <;> norm_num
  nlinarith [norm_nonneg (a sharpMatrix k l)]

private lemma sharp_local : loc sharpMatrix = 5 := by
  simp only [loc, sharp_coefficients]
  norm_num [Fin.sum_univ_succ]

private lemma sharp_separable : IsSeparable (sharpMatrix ⊗ₖ sharpMatrix) := by
  refine ⟨1, fun _ => 1, fun _ => sharpMatrix, fun _ => sharpMatrix, ?_, ?_, ?_, ?_⟩
  · intro t; norm_num
  · norm_num
  · intro t; exact ⟨sharp_density, sharp_density⟩
  · simp

private lemma sharpness : ∃ ρ, IsSeparable ρ ∧ l1 ρ = 25 := by
  refine ⟨sharpMatrix ⊗ₖ sharpMatrix, sharp_separable, ?_⟩
  rw [product_l1, sharp_local]
  norm_num

private lemma bipartite_coefficient
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (i j k l : Fin 3) :
    bloch ρ i j k l = ∑ a : Fin 3, ∑ b : Fin 3,
      ρ (a, b) (a + j, b + l) * star (ω ^ (a.val * i.val + b.val * k.val)) := by
  classical
  unfold bloch
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_eq_single (a + j)]
  · rw [Finset.sum_eq_single (b + l)]
    · simp only [Matrix.kroneckerMap_apply, W]
      simp [pow_add]
    · intro c _ hc
      simp only [Matrix.kroneckerMap_apply, W, if_neg hc]
      simp
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro c _ hc
    apply Finset.sum_eq_zero; intro d _
    simp only [Matrix.kroneckerMap_apply, W, if_neg hc]
    simp
  · intro h; exact (h (Finset.mem_univ _)).elim

end D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound
