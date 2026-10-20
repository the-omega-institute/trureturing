/- GID: D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.claim; result=D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.result; claim=D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.claim
   digest: An exact positive-input certificate refutes the gcd-three equator formula. -/

/-
admission_basis: open-problem-resolution (#19282; Refuted).
escape_witness: none.
Definitions tau, hadamardMap, vr, IsLambdaMax, claim, amp, v, q, R:
proof_shape: bind-only (definitions and concrete certificate data).
amp_normalized: proof_shape: bind-only; consumer: result.
v_support: proof_shape: bind-only; consumer: weight_support.
weight_support: proof_shape: bind-only; consumer: hadamard_quadratic.
R_psd: proof_shape: bind-only; consumer: result.
shift_sq: proof_shape: bind-only; consumers: shift_cube, tau_quadratic.
shift_cube: proof_shape: bind-only; consumer: tau_quadratic.
tau_quadratic: proof_shape: bind-only; consumer: negative_quadratic.
hadamard_quadratic: proof_shape: bind-only; consumer: negative_quadratic.
negative_quadratic: proof_shape: bind-only; consumer: result.
result: proof_shape: bind-only; consumer: none (settling result).
Direct frozen dependencies: FiniteKrausChannel.PhyslibLeaf.MatrixMap
(statement_id sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7),
and FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
(statement_id sha256:ea609f8757aff57ac9337a56fd720e69e8fa0443362f0823aab28c4b2934d1f6).
After expanding same-delivery values, tau, tau_quadratic, hadamard_quadratic and
negative_quadratic use MatrixMap; IsLambdaMax, claim and result also use IsPositive.
The values of hadamardMap, vr, amp, v, q, R, amp_normalized, v_support,
weight_support, R_psd, shift_sq and shift_cube have no frozen D5 dependencies.
The prescribed diagonal-map composition, cyclic-matrix entries and conjugation
composition are inlined in tau; no forwarding projection, shift or conjugation
declaration is introduced. The diagonal composition on a matrix agrees with
ProjectedUnistochasticDynamics.projectiveReadout; its linear structure uses Mathlib.
All other expressions are the conventions of #19282; no exact maximum, pole,
interval assertion, unbounded family, or off-support Fourier equality is asserted.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.Foundation.FiniteKrausChannel

/-! Binding conventions for A. Bera, G. Sarbicki and D. Chruściński, "Optimizing positive maps in the matrix algebra
M_n", arXiv:2309.09621v1: the maps τ_{n,k} (Eqs. (3)–(5)), H_{|v⟩} (Eq. (6)), the vectors |v_r⟩ for GCD(n, k) = 3
(Eqs. (10)–(11)), λ^max_{|v⟩} ("the largest value of λ_{|v⟩} such that the map τ_{n,k} − λ_{|v⟩} H_{|v⟩} is positive") and
Conjecture 2, Eq. (13). -/

namespace D5.S3.Quantum.QuantumChannels.BeraSarbickiChruscinskiOptimizedMaps

open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

/-- `τ_{n,k}(X) = (n − k) ε(X) + Σ_{i=1}^{k} ε(S^i X S^{†i}) − X`, Eq. (3). -/
noncomputable def tau (n k : ℕ) [NeZero n] : MatrixMap (Fin n) (Fin n) ℂ :=
  ((n : ℂ) - k) • ((Matrix.diagonalLinearMap (Fin n) ℂ ℂ) ∘ₗ
    (Matrix.diagLinearMap (Fin n) ℂ ℂ)) +
    (∑ i ∈ Finset.Icc 1 k, ((Matrix.diagonalLinearMap (Fin n) ℂ ℂ) ∘ₗ
      (Matrix.diagLinearMap (Fin n) ℂ ℂ)) ∘ₗ ((LinearMap.mulLeft ℂ ((Matrix.of fun a b : Fin n => if a = b + 1 then 1 else 0) ^ i)) ∘ₗ
    (LinearMap.mulRight ℂ (((Matrix.of fun a b : Fin n => if a = b + 1 then 1 else 0) ^ i)ᴴ)))) - LinearMap.id

/-- `H_{|v⟩}(X) = P_{|v⟩} ∘ X` with `P_{|v⟩} = |v⟩⟨v|` and `∘` the Hadamard product, Eq. (6). -/
noncomputable def hadamardMap (n : ℕ) (v : Fin n → ℂ) : MatrixMap (Fin n) (Fin n) ℂ where
  toFun X := (Matrix.vecMulVec v (star v)) ⊙ X
  map_add' X Y := by ext i j; simp [Matrix.hadamard, mul_add]
  map_smul' c X := by ext i j; simp [Matrix.hadamard]; ring

/-- `|v_r⟩ = (1/√n) (1, ω^{nr/3}, (ω^{nr/3})², …)` with `ω = e^{2πi/n}`, so `(ω^{nr/3})^j = e^{2πi r j/3}`, Eqs. (10)–(11). -/
noncomputable def vr (n r : ℕ) (j : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * r * ((j : ℕ) : ℂ) / 3) / Real.sqrt n

/-- `λ^max_{|v⟩}`: the largest `λ ≥ 0` such that `τ_{n,k} − λ H_{|v⟩}` is positive. -/
def IsLambdaMax (n k : ℕ) [NeZero n] (v : Fin n → ℂ) (lam : ℝ) : Prop :=
  IsGreatest {l : ℝ | 0 ≤ l ∧ (tau n k - (l : ℂ) • hadamardMap n v).IsPositive} lam

/-- Conjecture 2, Eq. (13): for `k = 1, …, n − 1`, if `GCD(n, k) = 3` and `|v⟩ = α|v₁⟩ + β|v₂⟩` with `|α|² + |β|² = 1` and `|α| = |β|`, then
`λ^max_{|v⟩} = n − k + (n − 3)/(n − (2/3)k)`. -/
def claim : Prop :=
  ∀ (n k : ℕ) [NeZero n], 1 ≤ k → k < n → Nat.gcd n k = 3 →
    ∀ α β : ℂ, ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1 → ‖α‖ = ‖β‖ →
      IsLambdaMax n k (fun j => α * vr n 1 j + β * vr n 2 j)
        ((n : ℝ) - k + ((n : ℝ) - 3) / ((n : ℝ) - 2 / 3 * k))

end D5.S3.Quantum.QuantumChannels.BeraSarbickiChruscinskiOptimizedMaps

namespace D5.S3.Quantum.QuantumChannels.BeraSarbickiChruscinskiOptimizedMaps
open Matrix
open scoped ComplexOrder
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

private noncomputable def amp : ℂ := 1 / (Real.sqrt 2 : ℂ)
private noncomputable def v : Fin 6 → ℂ := fun j => amp * vr 6 1 j + amp * vr 6 2 j
private def q : Fin 6 → ℂ := ![1, 0, 0, 1, 0, 0]
private noncomputable def R : Matrix (Fin 6) (Fin 6) ℂ :=
  (1 / 60 : ℂ) • 1 + (27 / 60 : ℂ) • vecMulVec q (star q)

private theorem amp_normalized : ‖amp‖ ^ 2 + ‖amp‖ ^ 2 = 1 := by
  simp only [amp, one_div, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem v_support (i : Fin 6) (hi : i = 0 ∨ i = 3) :
    v i = (2 : ℂ) / ((Real.sqrt 2 : ℂ) * (Real.sqrt 6 : ℂ)) := by
  have h3 (r : ℕ) : vr 6 r 3 = 1 / (Real.sqrt 6 : ℂ) := by
    unfold vr
    change Complex.exp (2 * Real.pi * Complex.I * r * (3 : ℂ) / 3) /
      (Real.sqrt 6 : ℂ) = _
    rw [show (2 * Real.pi * Complex.I * r * (3 : ℂ) / 3) =
      (r : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_nat_mul_two_pi_mul_I]
  rcases hi with rfl | rfl
  · simp [v, vr, amp]
    ring
  · rw [v, h3, h3]
    simp only [amp]
    ring

private theorem weight_support (i j : Fin 6) (hi : i = 0 ∨ i = 3)
    (hj : j = 0 ∨ j = 3) : v i * star (v j) = 1 / 3 := by
  have hs : ((Real.sqrt 2 : ℂ) * (Real.sqrt 6 : ℂ)) ^ 2 = 12 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 * 6)]
    norm_num
  rw [v_support i hi, v_support j hj]
  simp only [star_div₀, star_ofNat, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = 4 / ((Real.sqrt 2 : ℂ) * (Real.sqrt 6 : ℂ)) ^ 2 := by ring
    _ = 1 / 3 := by rw [hs]; norm_num

private theorem R_psd : R.PosSemidef := by
  exact (Matrix.PosSemidef.one.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/60)).add
    ((Matrix.posSemidef_vecMulVec_self_star q).smul
      (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 27/60))

private theorem shift_sq : (Matrix.of fun i j : Fin 6 => if i = j + 1 then (1 : ℂ) else 0) ^ 2 =
    (Matrix.of fun i j : Fin 6 => if i = j + 2 then (1 : ℂ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Fin.add_def]

private theorem shift_cube : (Matrix.of fun i j : Fin 6 => if i = j + 1 then (1 : ℂ) else 0) ^ 3 =
    (Matrix.of fun i j : Fin 6 => if i = j + 3 then (1 : ℂ) else 0) := by
  rw [pow_succ, shift_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Fin.add_def]

private theorem tau_quadratic : star q ⬝ᵥ (tau 6 3 R *ᵥ q) = 59 / 30 := by
  have hi : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := Finset.val_inj.mp rfl
  unfold tau
  rw [hi, Finset.sum_insert (by decide : 1 ∉ ({2, 3} : Finset ℕ)),
    Finset.sum_insert (by decide : 2 ∉ ({3} : Finset ℕ)), Finset.sum_singleton,
    pow_one, shift_sq, shift_cube]
  norm_num [R, q, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.vecMulVec, Pi.star_apply,
    smul_eq_mul, Fin.sum_univ_succ, Fin.add_def]

private theorem hadamard_quadratic : star q ⬝ᵥ (hadamardMap 6 v R *ᵥ q) = 11 / 18 := by
  have h00 := weight_support 0 0 (Or.inl rfl) (Or.inl rfl)
  have h03 := weight_support 0 3 (Or.inl rfl) (Or.inr rfl)
  have h30 := weight_support 3 0 (Or.inr rfl) (Or.inl rfl)
  have h33 := weight_support 3 3 (Or.inr rfl) (Or.inr rfl)
  simp only [Complex.star_def] at h00 h03 h30 h33
  norm_num [hadamardMap, R, q, dotProduct, Matrix.mulVec, Matrix.hadamard,
    Matrix.vecMulVec, Fin.sum_univ_succ]
  rw [h00, h03, h30, h33]
  norm_num

private theorem negative_quadratic :
    star q ⬝ᵥ ((tau 6 3 - (15 / 4 : ℂ) • hadamardMap 6 v) R *ᵥ q) = -13 / 40 := by
  change star q ⬝ᵥ ((tau 6 3 R - (15 / 4 : ℂ) • hadamardMap 6 v R) *ᵥ q) = _
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    tau_quadratic, hadamard_quadratic]
  norm_num

theorem result : ¬ claim := by
  intro hc
  have hm := hc 6 3 (by norm_num) (by norm_num) (by norm_num) amp amp amp_normalized rfl
  have hl : IsLambdaMax 6 3 v (15/4) := by norm_num [v] at hm ⊢; exact hm
  have hp := hl.1.2 R_psd
  have hn := hp.dotProduct_mulVec_nonneg q
  have hcast : ((15 / 4 : ℝ) : ℂ) = (15 / 4 : ℂ) := by norm_num
  rw [hcast, negative_quadratic] at hn
  norm_num [Complex.le_def] at hn

end D5.S3.Quantum.QuantumChannels.BeraSarbickiChruscinskiOptimizedMaps
