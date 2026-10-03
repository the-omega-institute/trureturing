/- GID: D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.claim; result=D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result; claim=D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.claim
   digest: A property-T circulant on 3 vertices with universal PST refutes 1701.04145. -/

/-
proof_shape: result: bind-only (the Fourier diagonalization of `Circ(0, α, ᾱ)`, the evaluation
  of the three phases and `Matrix.exp_conj` / `Matrix.exp_diagonal` give `exp(-i t₁ C) = ω² P`;
  the determinant and cardinality comparisons exclude switching equivalence; every step is a
  local `have` of `result`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11528; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  (statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb) and
  .hamiltonianGenerator (statement_id
  sha256:4c0ebd78b0aa0a551d6207706ae2d39b87a3d18687dc8dcb29e00bd4e58a735a)
-/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.PropertyTCirculantUniversalTransfer

open Complex Matrix
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-!
E. Connelly, N. Grammel, M. Kraut, L. Serazo, C. Tamon, *Universality in perfect state
transfer*, arXiv:1701.04145 (Linear Algebra Appl. 531 (2017) 516–532). The continuous-time quantum
walk of a graph with Hermitian adjacency matrix `A` is `U(t) = exp(-i t A)`, the propagator
`hamiltonianPropagator A t` of `D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow`; it has universal
perfect state transfer if every entry of `U` reaches modulus `1` at some time. A graph has
property `𝕋` if every nonzero entry of `A` has modulus `1`. The paper conjectures that `K₂` and
`Circ(0, -i, i)` are, up to switching equivalence, the only circulants with property `𝕋` and
universal perfect state transfer. The circulant `Circ(0, α, ᾱ)` with `α = (-4√3 + i)/7` is a
counterexample: its eigenvalues are `(√3/7)(-8, 3, 5)`, so `U(14√3π/9) = ω² P` for the cyclic
permutation matrix `P` and `ω = e^{2πi/3}`, and its determinant `-360√3/343` is not `0`.
-/

/-- Property `𝕋`: every nonzero entry of `A` has modulus `1`. -/
def PropertyT {ι : Type*} (A : Matrix ι ι ℂ) : Prop :=
  ∀ j k, A j k ≠ 0 → ‖A j k‖ = 1

/-- Universal perfect state transfer: for all vertices `u, v` the `(v, u)` entry of
`U(t) = exp(-i t A)` has modulus `1` at some real time `t`. -/
def UPST {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ u v, ∃ t : ℝ, ‖hamiltonianPropagator A t v u‖ = 1

/-- Switching equivalence: `M A = B M` for a monomial matrix `M`, the product of a permutation
matrix and an invertible diagonal matrix. -/
def SwitchingEquivalent {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : Prop :=
  ∃ (σ : κ ≃ ι) (d : ι → ℂ), (∀ i, d i ≠ 0) ∧
    (σ.toPEquiv.toMatrix : Matrix κ ι ℂ) * diagonal d * A =
      B * ((σ.toPEquiv.toMatrix : Matrix κ ι ℂ) * diagonal d)

/-- `K₂ = Circ(0, 1)`; `Circ(a)` has entries `Circ(a)_{jk} = a_{k-j}`, the transpose of
Mathlib's `circulant`. -/
def K2 : Matrix (ZMod 2) (ZMod 2) ℂ :=
  (circulant (![0, 1] : ZMod 2 → ℂ))ᵀ

/-- The oriented triangle `Circ(0, -i, i)`. -/
def orientedTriangle : Matrix (ZMod 3) (ZMod 3) ℂ :=
  (circulant (![0, -I, I] : ZMod 3 → ℂ))ᵀ

/-- The conjecture of arXiv:1701.04145 (l. 1154 with l. 212): every Hermitian circulant
`Circ(a)` of order `n ≥ 2` without loops, with property `𝕋` and universal perfect state transfer,
is switching equivalent to `K₂` or to `Circ(0, -i, i)`. -/
def claim : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ a : ZMod n → ℂ, a 0 = 0 → (circulant a)ᵀ.IsHermitian →
    PropertyT (circulant a)ᵀ → UPST (circulant a)ᵀ →
    SwitchingEquivalent (circulant a)ᵀ K2 ∨ SwitchingEquivalent (circulant a)ᵀ orientedTriangle

/-! The counterexample `Circ(0, α, ᾱ)`, `α = (-4√3 + i)/7`, on `Fin 3`. -/

local notation "s₃" => ((Real.sqrt 3 : ℝ) : ℂ)

/-- `ω = e^{2πi/3}`. -/
private def ω : ℂ := (-1 + s₃ * I) / 2

private def α : ℂ := (-4 * s₃ + I) / 7

private def β : ℂ := (-4 * s₃ - I) / 7

/-- The adjacency matrix `Circ(0, α, ᾱ)`. -/
private def C : Matrix (Fin 3) (Fin 3) ℂ := !![0, α, β; β, 0, α; α, β, 0]

/-- The Fourier matrix `V_{km} = ω^{km}`, and `3 V⁻¹`. -/
private def V : Matrix (Fin 3) (Fin 3) ℂ := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

private def W : Matrix (Fin 3) (Fin 3) ℂ := !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2]

/-- The eigenvalues `μ_m = α ω^m + ᾱ ω^{2m}` of `C`. -/
private def μ : Fin 3 → ℂ := ![α + β, α * ω + β * ω ^ 2, α * ω ^ 2 + β * ω]

/-- The cyclic permutation matrix, `P_{jk} = 1` iff `k = j + 1`. -/
private def P : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- The phases `e^{-i t₁ μ_m}`. -/
private def e : Fin 3 → ℂ := ![ω ^ 2, 1, ω]

private def t₁ : ℝ := 14 * Real.sqrt 3 * Real.pi / 9

/-- The conjecture fails: `Circ(0, α, ᾱ)` with `α = (-4√3 + i)/7` is a Hermitian circulant of order
`3` without loops, with property `𝕋` and universal perfect state transfer, and it is switching
equivalent neither to `K₂` nor to `Circ(0, -i, i)`. -/
theorem result : ¬ claim := by
  have s_sq : s₃ ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have omega_rel : ω ^ 2 + ω + 1 = 0 := by
    unfold ω
    linear_combination (I ^ 2 / 4) * s_sq + (3 / 4 : ℂ) * I_sq
  have omega_cube : ω ^ 3 = 1 := by
    linear_combination (ω - 1) * omega_rel
  have norm_omega : ‖ω‖ = 1 := by
    have h := congrArg norm omega_cube
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h
  have exp_omega : Complex.exp (2 * Real.pi * I / 3) = ω := by
    have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]
      norm_num
    have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_three]
    rw [show 2 * (Real.pi : ℂ) * I / 3 = ((2 * Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I, ← ofReal_cos, ← ofReal_sin, hc, hs, ω]
    push_cast
    ring
  have conj_alpha : starRingEnd ℂ α = β := by
    simp only [α, β, map_div₀, map_add, map_mul, map_neg, map_ofNat, conj_ofReal, conj_I]
    ring
  have alpha_mul_beta : α * β = 1 := by
    unfold α β
    linear_combination (16 / 49 : ℂ) * s_sq + (-1 / 49 : ℂ) * I_sq
  have norm_alpha : ‖α‖ = 1 := by
    have h : ((‖α‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← normSq_eq_norm_sq, ← mul_conj, conj_alpha, alpha_mul_beta]
    have h' : ‖α‖ ^ 2 = 1 := by exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h'
  have norm_beta : ‖β‖ = 1 := by
    rw [← conj_alpha, RCLike.norm_conj, norm_alpha]
  have V_mul_W : V * W = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp only [V, W, Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk,
        Fin.sum_univ_three, Fin.zero_eta,
        Matrix.mul_apply, cons_val, cons_val', cons_val_fin_one, cons_val_one, cons_val_zero,
        mul_one,
        mul_zero, ne_eq, not_false_eq_true, of_apply, one_mul, one_ne_zero, zero_ne_one,
        Matrix.smul_apply, Nat.reduceAdd, one_apply_eq, one_apply_ne, smul_eq_mul] <;>
      first
      | ring1
      | linear_combination omega_rel
      | linear_combination (-1 : ℂ) * omega_rel
      | linear_combination (2 * (ω - 1)) * omega_rel
      | linear_combination (-2 * (ω - 1)) * omega_rel
      | linear_combination (ω ^ 2 - ω + 1) * omega_rel
  have C_mul_V : C * V = V * diagonal μ := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp only [C, V, μ, Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk,
        Fin.sum_univ_three, Fin.zero_eta,
        Matrix.mul_apply, cons_val, cons_val', cons_val_fin_one, cons_val_one, cons_val_zero,
        mul_one,
        mul_zero, ne_eq, not_false_eq_true, of_apply, one_mul, one_ne_zero, zero_ne_one,
        add_zero, diagonal_apply_eq, diagonal_apply_ne, zero_add, zero_mul] <;>
      first
      | ring1
      | linear_combination (-β) * omega_cube
      | linear_combination β * omega_cube
      | linear_combination (-α * ω - β) * omega_cube
      | linear_combination (α * ω + β) * omega_cube
      | linear_combination (-α - β * ω) * omega_cube
      | linear_combination (α + β * ω) * omega_cube
      | linear_combination (-α) * omega_cube
  have V_mul_e : V * diagonal e = (ω ^ 2 • P) * V := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp only [V, P, e, Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk,
        Fin.sum_univ_three, Fin.zero_eta,
        Matrix.mul_apply, cons_val, cons_val', cons_val_fin_one, cons_val_one, cons_val_zero,
        mul_one,
        mul_zero, ne_eq, not_false_eq_true, of_apply, one_mul, one_ne_zero, zero_ne_one,
        add_zero, diagonal_apply_eq, diagonal_apply_ne, smul_cons, smul_empty, smul_eq_mul, smul_of,
        zero_add, zero_mul] <;>
      first
      | ring1
      | linear_combination (-1 : ℂ) * omega_cube
      | linear_combination omega_cube
      | linear_combination (-ω) * omega_cube
  have det_V : IsUnit V.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := (1 / 3 : ℂ) • W) ?_
    rw [Matrix.mul_smul, V_mul_W, smul_smul]
    norm_num
  have exp_phases : (fun m => Complex.exp (((t₁ : ℂ) * -I) * μ m)) = e := by
    have hμ0 : μ 0 = -8 * s₃ / 7 := by
      change α + β = _
      unfold α β
      ring
    have hμ1 : μ 1 = 3 * s₃ / 7 := by
      change α * ω + β * ω ^ 2 = _
      unfold α β ω
      linear_combination (-(I ^ 2) * (I + 4 * s₃) / 28) * s_sq + (-(3 * I + 8 * s₃) / 28) * I_sq
    have hμ2 : μ 2 = 5 * s₃ / 7 := by
      change α * ω ^ 2 + β * ω = _
      unfold α β ω
      linear_combination (I ^ 3 / 28 - I ^ 2 * s₃ / 7) * s_sq + (3 * I / 28 - 4 * s₃ / 7) * I_sq
    have ht : (t₁ : ℂ) = 14 * s₃ * Real.pi / 9 := by simp only [t₁]; push_cast; ring
    funext m
    fin_cases m
    · have : ((t₁ : ℂ) * -I) * μ 0 = ((2 : ℕ) : ℂ) * (2 * Real.pi * I / 3) +
          ((2 : ℤ) : ℂ) * (2 * Real.pi * I) := by
        rw [hμ0, ht]
        push_cast
        linear_combination (16 / 9 * Real.pi * I) * s_sq
      simp only [Fin.zero_eta]
      rw [this, Complex.exp_add, Complex.exp_nat_mul, exp_omega, Complex.exp_int_mul_two_pi_mul_I,
        mul_one]
      rfl
    · have : ((t₁ : ℂ) * -I) * μ 1 = ((0 : ℕ) : ℂ) * (2 * Real.pi * I / 3) +
          ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) := by
        rw [hμ1, ht]
        push_cast
        linear_combination (-(2 / 3) * Real.pi * I) * s_sq
      simp only [Fin.mk_one]
      rw [this, Complex.exp_add, Complex.exp_nat_mul, exp_omega, Complex.exp_int_mul_two_pi_mul_I,
        mul_one, pow_zero]
      rfl
    · have : ((t₁ : ℂ) * -I) * μ 2 = ((1 : ℕ) : ℂ) * (2 * Real.pi * I / 3) +
          ((-2 : ℤ) : ℂ) * (2 * Real.pi * I) := by
        rw [hμ2, ht]
        push_cast
        linear_combination (-(10 / 9) * Real.pi * I) * s_sq
      simp only [Fin.reduceFinMk]
      rw [this, Complex.exp_add, Complex.exp_nat_mul, exp_omega, Complex.exp_int_mul_two_pi_mul_I,
        mul_one, pow_one]
      rfl
  have propagator_t1 : hamiltonianPropagator C t₁ = ω ^ 2 • P := by
    have hC : C = V * diagonal μ * V⁻¹ := by
      rw [← C_mul_V, Matrix.mul_nonsing_inv_cancel_right V C det_V]
    have hgen : t₁ • hamiltonianGenerator C = V * diagonal (((t₁ : ℂ) * -I) • μ) * V⁻¹ := by
      have e : t₁ • hamiltonianGenerator C = ((t₁ : ℂ) * -I) • C := by
        rw [hamiltonianGenerator, ← smul_smul, Complex.coe_smul]
      rw [e, hC, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    change NormedSpace.exp (t₁ • hamiltonianGenerator C) = ω ^ 2 • P
    rw [hgen, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det V).mpr det_V),
      Matrix.exp_diagonal]
    have he : NormedSpace.exp (((t₁ : ℂ) * -I) • μ) = e := by
      rw [← exp_phases]
      funext m
      rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
    rw [he, V_mul_e, Matrix.mul_nonsing_inv_cancel_right V _ det_V]
  have propagator_two_t1 : hamiltonianPropagator C (2 * t₁) = (ω ^ 2 • P) * (ω ^ 2 • P) := by
    rw [← propagator_t1]
    change NormedSpace.exp ((2 * t₁) • hamiltonianGenerator C) =
      NormedSpace.exp (t₁ • hamiltonianGenerator C) * NormedSpace.exp (t₁ • hamiltonianGenerator C)
    rw [two_mul, add_smul, Matrix.exp_add_of_commute _ _ (Commute.refl _)]
  have propagator_zero : hamiltonianPropagator C 0 = 1 := by
    change NormedSpace.exp ((0 : ℝ) • hamiltonianGenerator C) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have circ_eq : (circulant (![0, α, β] : Fin 3 → ℂ))ᵀ = C := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have upst_C : UPST (circulant (![0, α, β] : Fin 3 → ℂ))ᵀ := by
    rw [circ_eq]
    intro u v
    have h0 : ∀ w : Fin 3, ‖hamiltonianPropagator C 0 w w‖ = 1 := fun w => by
      rw [propagator_zero, Matrix.one_apply_eq, norm_one]
    have h1 : ∀ w : Fin 3, ‖hamiltonianPropagator C t₁ w (w + 1)‖ = 1 := fun w => by
      rw [propagator_t1]
      fin_cases w <;> simp [P, norm_omega]
    have h2 : ∀ w : Fin 3, ‖hamiltonianPropagator C (2 * t₁) (w + 1) w‖ = 1 := fun w => by
      rw [propagator_two_t1]
      fin_cases w <;> simp [P, Matrix.mul_apply, Fin.sum_univ_three, norm_omega]
    fin_cases u <;> fin_cases v
    exacts [⟨0, h0 0⟩, ⟨2 * t₁, h2 0⟩, ⟨t₁, h1 2⟩, ⟨t₁, h1 0⟩, ⟨0, h0 1⟩, ⟨2 * t₁, h2 1⟩,
      ⟨2 * t₁, h2 2⟩, ⟨t₁, h1 1⟩, ⟨0, h0 2⟩]
  have propertyT_C : PropertyT (circulant (![0, α, β] : Fin 3 → ℂ))ᵀ := by
    rw [circ_eq]
    intro j k
    fin_cases j <;> fin_cases k <;> simp [C, norm_alpha, norm_beta]
  have hermitian_C : (circulant (![0, α, β] : Fin 3 → ℂ))ᵀ.IsHermitian := by
    rw [circ_eq]
    have hb : starRingEnd ℂ β = α := by rw [← conj_alpha, Complex.conj_conj]
    ext j k
    fin_cases j <;> fin_cases k <;> simp [C, conj_alpha, hb]
  have det_C : C.det = -(360 / 343 : ℂ) * s₃ := by
    have h : C.det = α ^ 3 + β ^ 3 := by
      rw [Matrix.det_fin_three]
      simp [C]
      ring
    rw [h]
    unfold α β
    linear_combination (-128 * s₃ / 343) * s_sq + (-24 * s₃ / 343) * I_sq
  have det_orientedTriangle : orientedTriangle.det = 0 := by
    have h : (circulant (![0, -I, I] : Fin 3 → ℂ))ᵀ = !![0, -I, I; I, 0, -I; -I, I, 0] := by
      ext j k
      fin_cases j <;> fin_cases k <;> rfl
    change ((circulant (![0, -I, I] : Fin 3 → ℂ))ᵀ).det = 0
    rw [h, Matrix.det_fin_three]
    simp
  intro h
  rcases @h 3 _ (by norm_num) (![0, α, β] : ZMod 3 → ℂ) rfl hermitian_C propertyT_C upst_C with
    ⟨σ, -, -, -⟩ | ⟨σ, d, hd, hM⟩
  · have := Fintype.card_congr σ
    simp [ZMod.card] at this
  · have hPD : (σ.toPEquiv.toMatrix * diagonal d).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
      refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
      rw [show (σ.toPEquiv.toMatrix : Matrix (ZMod 3) (ZMod 3) ℂ) =
          Equiv.Perm.permMatrix ℂ σ from rfl, Matrix.det_permutation]
      exact Int.cast_ne_zero.mpr (Units.ne_zero _)
    have hdet := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul (orientedTriangle), mul_comm (orientedTriangle.det)] at hdet
    have hA := mul_left_cancel₀ hPD hdet
    rw [det_orientedTriangle] at hA
    have hA' : C.det = 0 := by
      rw [← circ_eq]
      exact hA
    rw [det_C] at hA'
    have hs : s₃ ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    exact hs (by linear_combination (-(343 / 360 : ℂ)) * hA')

end D5.S3.Quantum.Dynamics.PropertyTCirculantUniversalTransfer
