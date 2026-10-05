/- GID: D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim; result=D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result; claim=D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim
   digest: Refutes the 25-edge lower bound of Barriga et al. for ten-mode Fourier transforms: a connected 23-edge real coupling matrix realizes F_10. -/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation

open Complex Matrix NormedSpace
open scoped Kronecker
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance (priority := 2000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAddCommGroup
local instance (priority := 2000) : NormedSpace ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedSpace
local instance (priority := 2000) : NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
local instance (priority := 2000) : NormedAlgebra ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAlgebra


local instance (priority := 2000) : NormedAlgebra ℚ (Matrix n n ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)

/-- The ten-dimensional discrete Fourier transform, entries exp(-2πi x y / 10) / √10. -/
def F10 : Matrix (Fin 10) (Fin 10) ℂ := fun x y =>
  Complex.exp (-(2 * Real.pi * Complex.I * (x : ℕ) * (y : ℕ)) / 10) / Real.sqrt 10

/-- Number of edges of the support graph: unordered pairs x < y with H x y ≠ 0. -/
def edgeCount (H : Matrix (Fin 10) (Fin 10) ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
    (fun p => p.1 < p.2 ∧ H p.1 p.2 ≠ 0)).card

/-- The support graph of H. -/
def supportGraph (H : Matrix (Fin 10) (Fin 10) ℝ) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun x y => H x y ≠ 0)

def IsUnimodularDiagonal (Φ : Matrix (Fin 10) (Fin 10) ℂ) : Prop :=
  ∃ z : Fin 10 → ℂ, (∀ x, ‖z x‖ = 1) ∧ Φ = Matrix.diagonal z

def claim : Prop :=
  ∀ H : Matrix (Fin 10) (Fin 10) ℝ, H.IsSymm →
    (∀ x y, x ≠ y → 0 ≤ H x y) → (supportGraph H).Connected →
    (∃ Φout Φin, IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
      Φout * hamiltonianPropagator (H.map (↑)) 1 * Φin = F10) → 25 ≤ edgeCount H

private def s : ℝ := Real.sqrt 5
private def c : ℝ := (s - 1) / 4
private def d : ℝ := Real.sqrt (10 + 2 * s) / 4
private def ω : ℂ := (c : ℂ) + (d : ℂ) * I
private def q : ℝ := (21 * s - 65) / 20
private def r : ℝ := Real.sqrt (1 - q ^ 2)
private def γ : ℂ := (q : ℂ) + (r : ℂ) * I
private def a : ℝ := Real.pi * (35 - 13 * s) / 25
private def b : ℝ := Real.pi * (35 + 13 * s) / 25

private def C0 : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  if j = k then 0 else if (k.val + 5 - j.val) % 5 = 1 ∨
    (k.val + 5 - j.val) % 5 = 4 then a else b

private def P : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  ((γ * ω ^ ((j.val + k.val + 4) % 5)).re +
    (ω ^ ((j.val + 5 - k.val) % 5)).re) / 5

private def K : Matrix (Fin 5) (Fin 5) ℝ := C0 + (2 * Real.pi) • P


private def u : ℝ := d * r

private def κ : Matrix (Fin 5) (Fin 5) ℝ :=
  !![2*u/5 - 43*s/100 + 5/4, 0, -2*u/5 - s/100 + 43/20,
      -u*s/5 + u/5 + 16*s/25 + 11/10, u*s/5 - u/5 - s/5 + 11/10;
    0, -2*u/5 - 43*s/100 + 5/4, -u*s/5 + u/5 - s/5 + 11/10,
      u*s/5 - u/5 + 16*s/25 + 11/10, 2*u/5 - s/100 + 43/20;
    -2*u/5 - s/100 + 43/20, -u*s/5 + u/5 - s/5 + 11/10,
      u*s/5 - u/5 + 11*s/50 + 1/5, 2*u/5 - 17*s/20 + 43/20, 21*s/25;
    -u*s/5 + u/5 + 16*s/25 + 11/10, u*s/5 - u/5 + 16*s/25 + 11/10,
      2*u/5 - 17*s/20 + 43/20, 21*s/50 - 9/10, -2*u/5 - 17*s/20 + 43/20;
    u*s/5 - u/5 - s/5 + 11/10, 2*u/5 - s/100 + 43/20, 21*s/25,
      -2*u/5 - 17*s/20 + 43/20, -u*s/5 + u/5 + 11*s/50 + 1/5]

private def Ccoeff : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  if j = k then 0 else if (k.val + 5 - j.val) % 5 = 1 ∨
    (k.val + 5 - j.val) % 5 = 4 then (35 - 13 * s) / 25 else (35 + 13 * s) / 25

private def V : Matrix (Fin 5) (Fin 5) ℂ := fun j k => ω ^ ((j.val * k.val) % 5)
private def W : Matrix (Fin 5) (Fin 5) ℂ := fun j k =>
  ω ^ ((5 - (j.val * k.val) % 5) % 5)
private def μ : Fin 5 → ℂ := ![28 / 5, -4, 6 / 5, 6 / 5, -4]
private def E : Fin 5 → ℂ := ![ω, 1, ω ^ 2, ω ^ 2, 1]
private def U5 : Matrix (Fin 5) (Fin 5) ℂ := fun j k =>
  ω / (s : ℂ) * ω ^ ((4 * (j.val + 5 - k.val) ^ 2) % 5)

private def L : Matrix (Fin 2) (Fin 2) ℂ →+*
    Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)
  map_zero' := by simp
  map_one' := one_kronecker_one
  map_add' A B := add_kronecker A B _
  map_mul' A B := by
    simpa using mul_kronecker_mul A B (1 : Matrix (Fin 5) (Fin 5) ℂ) 1
private def R : Matrix (Fin 5) (Fin 5) ℂ →+*
    Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) ℂ where
  toFun B := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B
  map_zero' := by simp
  map_one' := one_kronecker_one
  map_add' A B := kronecker_add _ A B
  map_mul' A B := by
    simpa using mul_kronecker_mul (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 A B
private def crt : Fin 10 ≃ Fin 2 × Fin 5 where
  toFun x := (⟨x.val % 2, Nat.mod_lt _ (by norm_num)⟩,
    ⟨x.val % 5, Nat.mod_lt _ (by norm_num)⟩)
  invFun p := ⟨(5 * p.1.val + 6 * p.2.val) % 10, Nat.mod_lt _ (by norm_num)⟩
  left_inv x := by fin_cases x <;> rfl
  right_inv p := by rcases p with ⟨a, j⟩; fin_cases a <;> fin_cases j <;> rfl

private def A2 : Matrix (Fin 2) (Fin 2) ℂ := (Real.pi / 4 : ℂ) • !![0, 1; 1, 0]
private def U2 : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (Real.sqrt 2 : ℂ)) • !![1, -I; -I, 1]
private def H : Matrix (Fin 10) (Fin 10) ℝ := fun x y =>
  (if x.val % 2 = y.val % 2 then
    K ⟨x.val % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨y.val % 5, Nat.mod_lt _ (by norm_num)⟩ else 0) +
  (if x ≠ y ∧ x.val % 5 = y.val % 5 then Real.pi / 4 else 0)

private def edgeRel (x y : Fin 10) : Prop :=
  x ≠ y ∧ ((x.val % 2 = y.val % 2 ∧
    ¬((x = 0 ∧ y = 6) ∨ (x = 6 ∧ y = 0) ∨
      (x = 1 ∧ y = 5) ∨ (x = 5 ∧ y = 1))) ∨ x.val % 5 = y.val % 5)

private def z (x : Fin 10) : ℂ :=
  (-I) ^ (x.val % 2) * ω ^ (4 * (x.val % 5) ^ 2)

set_option maxHeartbeats 4000000 in
/-- A connected real symmetric nonnegative coupling matrix with 23 edges realizes `F10`
after diagonal phase shifts, refuting the claimed 25-edge lower bound. -/
theorem result : ¬ claim := by
  classical
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : d ^ 2 = (5 + s) / 8 := by
    have h := Real.sq_sqrt (show 0 ≤ 10 + 2 * s by linarith)
    dsimp [d]
    nlinarith
  have h2 : ω ^ 2 = (-(s + 1) / 4 : ℝ) + (((s - 1) * d / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [ω, c, pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd]
  have h3 : ω ^ 3 = (-(s + 1) / 4 : ℝ) - (((s - 1) * d / 2 : ℝ) : ℂ) * I := by
    rw [pow_succ, h2]
    apply Complex.ext <;> simp [ω, c, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd, show s ^ 2 * d = 5 * d by rw [hs], show s * (d ^ 2) = s * ((5 + s) / 8) by rw [hd]]
  have h4 : ω ^ 4 = (c : ℂ) - (d : ℂ) * I := by
    rw [pow_succ, h3]
    apply Complex.ext <;> simp [ω, c, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd, show s ^ 2 * d = 5 * d by rw [hs], show s * (d ^ 2) = s * ((5 + s) / 8) by rw [hd]]
  have h5 : ω ^ 5 = 1 := by
    rw [pow_succ, h4]
    apply Complex.ext <;> simp [ω, c, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd]
  have hK : K = Real.pi • κ := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [K, C0, P, κ, h2, h3, h4] <;>
      simp [a, b, γ, ω, c, q, u] <;>
      nlinarith [hs, show Real.pi * s ^ 2 = Real.pi * 5 by rw [hs]]
  have hs_bounds : 11 / 5 < s ∧ s < 9 / 4 := by
    constructor <;> nlinarith [hs]
  have hq_bounds : -1 < q ∧ q < -7 / 8 := by
    dsimp [q]
    constructor <;> linarith [hs_bounds.1, hs_bounds.2]
  have hr : r ^ 2 = 1 - q ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [hq_bounds.1, hq_bounds.2]
  have hr_bounds : 0 ≤ r ∧ r < 1 / 2 := by
    have hn : 0 ≤ r := Real.sqrt_nonneg _
    constructor
    · exact hn
    · nlinarith [hr, hq_bounds.1, hq_bounds.2]
  have hd_bounds : 0 ≤ d ∧ d < 1 := by
    have hn : 0 ≤ d := by dsimp [d]; positivity
    constructor
    · exact hn
    · nlinarith [hd, hs_bounds.2]
  have ht_bounds : 0 ≤ u ∧ u < 1 / 2 := by
    change 0 ≤ d * r ∧ d * r < 1 / 2
    constructor
    · exact mul_nonneg hd_bounds.1 hr_bounds.1
    · nlinarith [mul_nonneg hd_bounds.1 hr_bounds.1]
  have hts_bounds : 0 ≤ u * s ∧ u * s < 9 / 8 := by
    constructor
    · exact mul_nonneg ht_bounds.1 hs_nonneg
    · nlinarith [ht_bounds.1, ht_bounds.2, hs_bounds.1, hs_bounds.2]
  have hκ_zero : ∀ j k : Fin 5, j ≠ k →
      (κ j k = 0 ↔ (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [κ] at hjk ⊢ <;>
      nlinarith [hs_bounds.1, hs_bounds.2, ht_bounds.1, ht_bounds.2,
        hts_bounds.1, hts_bounds.2]
  have hκ_nonneg : ∀ j k : Fin 5, j ≠ k → 0 ≤ κ j k := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [κ] at hjk ⊢ <;>
      nlinarith [hs_bounds.1, hs_bounds.2, ht_bounds.1, ht_bounds.2,
        hts_bounds.1, hts_bounds.2]
  have hs3 : s ^ 3 = 5 * s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ = 5 * s := by rw [hs]
  have hs4 : s ^ 4 = 25 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = 25 := by rw [hs]; norm_num
  have hu2 : u ^ 2 = 381 * s / 160 - 165 / 32 := by
    dsimp [u]
    rw [mul_pow, hd, hr]
    dsimp [q]
    ring_nf
    simp only [hs3, hs]
    ring
  have hPtable : P = (1 / 2 : ℝ) • (κ - Ccoeff) := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [P, κ, Ccoeff, h2, h3, h4] <;>
      simp [γ, ω, c, q, u] <;> nlinarith [hs]
  have hCcoeffP : Ccoeff * P = (-4 : ℝ) • P := by
    simp only [hPtable]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, κ, Ccoeff] <;>
      ring_nf <;> simp only [hs, hs3, hs4] <;> ring
  have hPP : P * P = P := by
    simp only [hPtable]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, κ, Ccoeff] <;>
      ring_nf <;> simp only [hs, hs3, hs4, hu2] <;>
      ring_nf <;> simp only [hs, hs3, hs4] <;> ring
  have hPsymm : P.IsSymm := by
    rw [hPtable]
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have hCcoeffsymm : Ccoeff.IsSymm := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have hPCcoeff : P * Ccoeff = (-4 : ℝ) • P := by
    have he := congrArg Matrix.transpose hCcoeffP
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul,
      show Pᵀ = P from hPsymm, show Ccoeffᵀ = Ccoeff from hCcoeffsymm] using he
  have hC0 : C0 = Real.pi • Ccoeff := by
    ext j k
    change C0 j k = Real.pi * Ccoeff j k
    unfold C0 Ccoeff a b
    split_ifs <;> ring
  have hcomm : Commute (C0.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) (P.map (↑)) := by
    have he : C0 * P = P * C0 := by
      rw [hC0, Matrix.smul_mul, Matrix.mul_smul, hCcoeffP, hPCcoeff]
    have he' := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M.map Complex.ofRealHom) he
    simp only [Matrix.map_mul] at he'
    exact he'
  have hPPc : (P.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) * P.map (↑) = P.map (↑) := by
    have he := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M.map Complex.ofRealHom) hPP
    simp only [Matrix.map_mul] at he
    exact he
  have hexp_idempotent : ∀ {n : Type} [Fintype n] [DecidableEq n]
      (Q : Matrix n n ℂ), Q * Q = Q → ∀ t : ℂ,
      NormedSpace.exp (t • Q) = 1 + (NormedSpace.exp t - 1) • Q := by
    intro n _ _ Q hQ t
    have hpow : ∀ k : ℕ, Q ^ (k + 1) = Q := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ, ih, hQ]
    have hs := expSeries_summable' (𝕂 := ℂ) t
    have hs' : Summable (fun k : ℕ => (((k + 1).factorial : ℂ)⁻¹) * t ^ (k + 1)) := by
      simpa only [smul_eq_mul] using (summable_nat_add_iff 1).mpr hs
    have ht : (∑' k : ℕ, (((k + 1).factorial : ℂ)⁻¹) * t ^ (k + 1)) = NormedSpace.exp t - 1 := by
      have he : NormedSpace.exp t = 1 + ∑' k : ℕ, (((k + 1).factorial : ℂ)⁻¹) * t ^ (k + 1) := by
        calc
          NormedSpace.exp t = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • t ^ k := congrFun (exp_eq_tsum ℂ) t
          _ = _ := by simpa using hs.tsum_eq_zero_add
      linear_combination -he
    calc
      NormedSpace.exp (t • Q) = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • (t • Q) ^ k :=
        congrFun (exp_eq_tsum ℂ) (t • Q)
      _ = 1 + ∑' k : ℕ, (((k + 1).factorial : ℂ)⁻¹) • (t • Q) ^ (k + 1) := by
        simpa using (expSeries_summable' (𝕂 := ℂ) (t • Q)).tsum_eq_zero_add
      _ = 1 + (∑' k : ℕ, (((k + 1).factorial : ℂ)⁻¹) * t ^ (k + 1)) • Q := by
        simp_rw [smul_pow, hpow, smul_smul]
        rw [hs'.tsum_smul_const]
      _ = _ := by rw [ht]
  have hexpP : NormedSpace.exp (((-I) * (2 * Real.pi : ℂ)) • P.map (↑)) =
      (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
    have he : NormedSpace.exp ((-I) * (2 * Real.pi : ℂ)) = (1 : ℂ) := by
      rw [← Complex.exp_eq_exp_ℂ,
        show (-I) * (2 * Real.pi : ℂ) = ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-1)
    rw [hexp_idempotent _ hPPc, he]
    simp
  have hexpK : hamiltonianPropagator (K.map (↑)) 1 =
      hamiltonianPropagator (C0.map (↑)) 1 := by
    have hKc : (K.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) =
        C0.map (↑) + (2 * Real.pi : ℂ) • P.map (↑) := by
      ext j k
      simp [K]
    simp only [hamiltonianPropagator, one_smul, hamiltonianGenerator, hKc,
      smul_add, smul_smul]
    rw [Matrix.exp_add_of_commute _ _ ((hcomm.smul_left (-I)).smul_right
      ((-I) * (2 * Real.pi : ℂ))), hexpP, mul_one]
  have hsC : (s : ℂ) ^ 2 = 5 := by exact_mod_cast hs
  have hsum : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
    rw [h2, h3, h4]
    dsimp [ω, c]
    push_cast
    ring
  have h6 : ω ^ 6 = ω := by
    calc
      ω ^ 6 = ω ^ 5 * ω := by ring
      _ = ω := by rw [h5]; simp
  have h7 : ω ^ 7 = ω ^ 2 := by
    calc
      ω ^ 7 = ω ^ 5 * ω ^ 2 := by ring
      _ = ω ^ 2 := by rw [h5]; simp
  have h8 : ω ^ 8 = ω ^ 3 := by
    calc
      ω ^ 8 = ω ^ 5 * ω ^ 3 := by ring
      _ = ω ^ 3 := by rw [h5]; simp
  have hVW : V * W = (5 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [V, W, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring_nf <;> (try simp only [h5, h6, h7, h8]) <;>
      first | ring1 | linear_combination hsum
  have hCV : (Ccoeff.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) * V =
      V * diagonal μ := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Ccoeff, V, μ, h2, h3, h4] <;>
      (try simp [ω, c]) <;> push_cast <;> ring_nf <;>
      (try simp only [hsC, Complex.I_sq]) <;> ring
  have hcos : Real.cos (2 * Real.pi / 5) = c := by
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
      Real.cos_two_mul, Real.cos_pi_div_five]
    change 2 * ((1 + s) / 4) ^ 2 - 1 = c
    dsimp [c]
    nlinarith [hs]
  have hsin : Real.sin (2 * Real.pi / 5) = d := by
    have ht := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
    rw [hcos] at ht
    have hn := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ 2 * Real.pi / 5 by linarith [Real.pi_pos])
      (show 2 * Real.pi / 5 ≤ Real.pi by linarith [Real.pi_pos])
    have hdn : 0 ≤ d := by dsimp [d]; positivity
    dsimp [c] at ht
    nlinarith [hs, hd]
  have hexpω : Complex.exp (2 * Real.pi * I / 5) = ω := by
    rw [show 2 * (Real.pi : ℂ) * I / 5 = ((2 * Real.pi / 5 : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      hcos, hsin]
    rfl
  let n5 : Fin 5 → ℕ := ![1, 0, 2, 2, 0]
  let m5 : Fin 5 → ℤ := ![-3, 2, -1, -1, 2]
  have hphase : ∀ k, (-I) * (Real.pi : ℂ) * μ k =
      ((n5 k : ℕ) : ℂ) * (2 * Real.pi * I / 5) +
      ((m5 k : ℤ) : ℂ) * (2 * Real.pi * I) := by
    intro k
    fin_cases k <;> simp [μ, n5, m5] <;> ring
  have hE : (fun k => Complex.exp ((-I) * (Real.pi : ℂ) * μ k)) = E := by
    funext k
    rw [hphase, Complex.exp_add, Complex.exp_nat_mul, hexpω,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
    fin_cases k <;> simp [n5, E]
  have hs_ne : (s : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have h9 : ω ^ 9 = ω ^ 4 := by
    calc
      ω ^ 9 = ω ^ 5 * ω ^ 4 := by ring
      _ = _ := by rw [h5]; simp
  have h10 : ω ^ 10 = 1 := by
    calc
      ω ^ 10 = (ω ^ 5) ^ 2 := by ring
      _ = _ := by rw [h5]; norm_num
  have hU : (1 / 5 : ℂ) • (V * diagonal E * W) = U5 := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [V, W, E, U5, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_succ] <;>
      field_simp [hs_ne] <;> ring_nf <;>
      (try simp only [h5, h6, h7, h8, h9, h10]) <;>
      (try simp only [h2, h3, h4]) <;> (try simp only [ω, c]) <;>
      push_cast <;> ring_nf <;> (try simp only [hsC, Complex.I_sq]) <;> ring
  have hright : V * ((1 / 5 : ℂ) • W) = 1 := by
    rw [Matrix.mul_smul, hVW, smul_smul]
    norm_num
  have hdet : IsUnit V.det := Matrix.isUnit_det_of_right_inverse hright
  have hVinv : V⁻¹ = (1 / 5 : ℂ) • W := Matrix.inv_eq_right_inv hright
  have hC0c : (C0.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) =
      (Real.pi : ℂ) • Ccoeff.map (↑) := by
    ext j k
    change (C0 j k : ℂ) = (Real.pi : ℂ) * Ccoeff j k
    unfold C0 Ccoeff a b
    split_ifs <;> push_cast <;> ring
  have hC0V : (C0.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) * V =
      V * diagonal ((Real.pi : ℂ) • μ) := by
    rw [hC0c, Matrix.smul_mul, hCV, Matrix.diagonal_smul, Matrix.mul_smul]
  have hC0diag : (C0.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) =
      V * diagonal ((Real.pi : ℂ) • μ) * V⁻¹ := by
    rw [← hC0V, Matrix.mul_nonsing_inv_cancel_right V _ hdet]
  have hgen : (-I) • (C0.map (↑) : Matrix (Fin 5) (Fin 5) ℂ) =
      V * diagonal (((-I) * (Real.pi : ℂ)) • μ) * V⁻¹ := by
    rw [hC0diag]
    simp only [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have hexpC0 : hamiltonianPropagator (C0.map (↑)) 1 = U5 := by
    simp only [hamiltonianPropagator, one_smul, hamiltonianGenerator]
    rw [hgen, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det V).mpr hdet),
      Matrix.exp_diagonal]
    have hEc : NormedSpace.exp (((-I) * (Real.pi : ℂ)) • μ) = E := by
      funext k
      rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
      exact congrFun hE k
    rw [hEc, hVinv, Matrix.mul_smul, hU]
  have hexp_tensor : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ)
      (B : Matrix (Fin 5) (Fin 5) ℂ), NormedSpace.exp (A ⊗ₖ 1 + 1 ⊗ₖ B) =
      NormedSpace.exp A ⊗ₖ NormedSpace.exp B := by
    intro A B
    have hL : Continuous L := by
      change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
        fun i j : Fin 2 × Fin 5 => A i.1 j.1 * (1 : Matrix (Fin 5) (Fin 5) ℂ) i.2 j.2)
      exact continuous_pi fun i => continuous_pi fun j =>
        ((continuous_apply j.1).comp
          (continuous_apply i.1 : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i.1))).mul
          continuous_const
    have hR : Continuous R := by
      change Continuous (fun B : Matrix (Fin 5) (Fin 5) ℂ =>
        fun i j : Fin 2 × Fin 5 => (1 : Matrix (Fin 2) (Fin 2) ℂ) i.1 j.1 * B i.2 j.2)
      exact continuous_pi fun i => continuous_pi fun j =>
        continuous_const.mul ((continuous_apply j.2).comp (continuous_apply i.2))
    have hc : Commute (L A) (R B) := by
      change (A ⊗ₖ 1) * (1 ⊗ₖ B) = (1 ⊗ₖ B) * (A ⊗ₖ 1)
      rw [← mul_kronecker_mul, ← mul_kronecker_mul]
      simp
    change NormedSpace.exp (L A + R B) = _
    rw [Matrix.exp_add_of_commute _ _ hc, ← NormedSpace.map_exp L hL,
      ← NormedSpace.map_exp R hR]
    change (NormedSpace.exp A ⊗ₖ 1) * (1 ⊗ₖ NormedSpace.exp B) = _
    rw [← mul_kronecker_mul]
    simp
  have hexpA2 : NormedSpace.exp ((-I) • A2) = U2 := by
    let V2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
    have hright : V2 * ((1 / 2 : ℂ) • V2) = 1 := by
      ext j k
      fin_cases j <;> fin_cases k <;> norm_num [V2, Matrix.mul_apply, Fin.sum_univ_two]
    have hdet : IsUnit V2.det := Matrix.isUnit_det_of_right_inverse hright
    have hVinv : V2⁻¹ = (1 / 2 : ℂ) • V2 := Matrix.inv_eq_right_inv hright
    have hgen : (-I) • A2 = V2 * diagonal ![-Real.pi * I / 4, Real.pi * I / 4] * V2⁻¹ := by
      rw [hVinv]
      ext j k
      fin_cases j <;> fin_cases k <;>
        simp [A2, V2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
    have hneg : Complex.exp (-(Real.pi * I / 4)) =
        (Real.sqrt 2 / 2 : ℂ) * (1 - I) := by
      rw [show -((Real.pi : ℂ) * I / 4) = ((-(Real.pi / 4) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
      push_cast
      ring
    have hpos : Complex.exp (Real.pi * I / 4) =
        (Real.sqrt 2 / 2 : ℂ) * (1 + I) := by
      rw [show (Real.pi : ℂ) * I / 4 = ((Real.pi / 4 : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp [Real.cos_pi_div_four, Real.sin_pi_div_four]
      ring
    have hphase : NormedSpace.exp (![-Real.pi * I / 4, Real.pi * I / 4] : Fin 2 → ℂ) =
        ![(Real.sqrt 2 / 2 : ℂ) * (1 - I), (Real.sqrt 2 / 2 : ℂ) * (1 + I)] := by
      funext k
      fin_cases k
      · simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
        convert hneg using 1 <;> ring
      · simpa [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ] using hpos
    rw [hgen, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det V2).mpr hdet),
      Matrix.exp_diagonal, hphase, hVinv]
    have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (by norm_num))
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [V2, U2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
      field_simp [hn] <;> ring_nf <;> (try rw [hs]) <;> ring
  have hHtensor : (H.map (↑) : Matrix (Fin 10) (Fin 10) ℂ) =
      Matrix.reindex crt.symm crt.symm
        (A2 ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) +
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K.map (↑)) := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [H, A2, crt, Matrix.reindex_apply, Matrix.kronecker_apply] <;> ring
  have hexpH : hamiltonianPropagator (H.map (↑)) 1 =
      Matrix.reindex crt.symm crt.symm (U2 ⊗ₖ U5) := by
    let T := Matrix.reindexRingEquiv ℂ crt.symm
    have hT : Continuous T := by
      change Continuous (fun M : Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) ℂ =>
        fun x y : Fin 10 => M (crt x) (crt y))
      exact continuous_pi fun x => continuous_pi fun y =>
        (continuous_apply (crt y)).comp (continuous_apply (crt x))
    have hG : (-I) • (H.map (↑) : Matrix (Fin 10) (Fin 10) ℂ) =
        T (((-I) • A2) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) +
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ((-I) • K.map (↑))) := by
      rw [hHtensor]
      ext x y
      simp [T, Matrix.reindex_apply, Matrix.kronecker_apply]
      ring
    have hexpK5 : NormedSpace.exp ((-I) • (K.map (↑) : Matrix (Fin 5) (Fin 5) ℂ)) = U5 := by
      have he := hexpK.trans hexpC0
      simpa only [hamiltonianPropagator, one_smul, hamiltonianGenerator] using he
    simp only [hamiltonianPropagator, one_smul, hamiltonianGenerator]
    rw [hG, ← NormedSpace.map_exp T hT, hexp_tensor, hexpA2, hexpK5]
    rfl
  have hnormω : ‖ω‖ = 1 := by
    have he := congrArg norm h5
    rw [norm_pow, norm_one] at he
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp he
  have hnormz : ∀ x, ‖z x‖ = 1 := by
    intro x
    simp [z, norm_mul, norm_pow, hnormω]
  have hω_ne : ω ≠ 0 := by intro he; simpa [he] using hnormω
  have hz_ne : ∀ x, z x ≠ 0 := by intro x he; simpa [he] using hnormz x
  have hfactor : Matrix.reindex crt.symm crt.symm (U2 ⊗ₖ U5) =
      ω • (diagonal z * F10 * diagonal z) := by
    let n10 (x y : Fin 10) : ℕ := (x.val % 2) * (y.val % 2)
    let m10 (x y : Fin 10) : ℕ := 2 * (x.val % 5) * (y.val % 5)
    let k10 (x y : Fin 10) : ℤ :=
      (-((x.val * y.val : ℕ) : ℤ) - 5 * (n10 x y : ℤ) - 2 * (m10 x y : ℤ)) / 10
    have hphase10 : ∀ x y : Fin 10,
        -(2 * Real.pi * I * (x : ℕ) * (y : ℕ)) / 10 =
        ((n10 x y : ℕ) : ℂ) * (Real.pi * I) +
        ((m10 x y : ℕ) : ℂ) * (2 * Real.pi * I / 5) +
        ((k10 x y : ℤ) : ℂ) * (2 * Real.pi * I) := by
      intro x y
      fin_cases x <;> fin_cases y <;> norm_num [n10, m10, k10] <;> ring
    have hFourier : ∀ x y : Fin 10, F10 x y =
        (-1 : ℂ) ^ ((x.val % 2) * (y.val % 2)) *
          ω ^ (2 * (x.val % 5) * (y.val % 5)) / Real.sqrt 10 := by
      intro x y
      unfold F10
      rw [hphase10, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul,
        Complex.exp_nat_mul, Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I, hexpω, mul_one]
    have hred : ∀ n : ℕ, 5 ≤ n → ω ^ n = ω ^ (n % 5) :=
      fun n _ => pow_eq_pow_mod n h5
    have hsqrt10 : (Real.sqrt 10 : ℂ) = (Real.sqrt 2 : ℂ) * (s : ℂ) := by
      have he : Real.sqrt 10 = Real.sqrt 2 * s := by
        dsimp [s]
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) 5]
        norm_num
      exact_mod_cast he
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hs2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (by norm_num))
    ext x y
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    rw [hFourier]
    fin_cases x <;> fin_cases y <;>
      simp [crt, Matrix.reindex_apply, Matrix.kronecker_apply, U2, U5, z, hsqrt10, hred] <;>
      field_simp [hs_ne, hs2_ne] <;> ring_nf <;>
      (try simp [hred, Complex.I_sq]) <;> ring
  have hsymm : H.IsSymm := by
    have hκ_symm : κ.IsSymm := by
      ext j k
      fin_cases j <;> fin_cases k <;> rfl
    have hK_symm : ∀ j k, K j k = K k j := by
      intro j k
      rw [hK]
      exact congrArg (fun t : ℝ => Real.pi * t) (congrFun (congrFun hκ_symm j) k).symm
    ext x y
    simp only [H, Matrix.transpose_apply]
    rw [hK_symm]
    simp only [eq_comm, ne_comm]

  have hnonneg : ∀ x y, x ≠ y → 0 ≤ H x y := by
    intro x y hxy
    unfold H
    apply add_nonneg
    · split_ifs with hp
      · rw [hK]
        apply mul_nonneg Real.pi_pos.le
        apply hκ_nonneg
        intro he
        have hm := congrArg Fin.val he
        change x.val % 5 = y.val % 5 at hm
        have hx := x.isLt
        have hy := y.isLt
        have hval : x.val = y.val := by omega
        exact hxy (Fin.ext hval)
      · exact le_refl 0
    · split_ifs <;> positivity

  have hH_nonzero : ∀ x y : Fin 10, x ≠ y → (H x y ≠ 0 ↔ edgeRel x y) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [H, hK, hκ_zero, edgeRel, Real.pi_ne_zero] at hxy ⊢
  have hgraph : ∀ x y, (supportGraph H).Adj x y ↔ edgeRel x y := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simp [supportGraph, edgeRel]
    · simp only [supportGraph, SimpleGraph.fromRel_adj,
        hH_nonzero x y hxy, hH_nonzero y x (Ne.symm hxy)]
      have he : edgeRel y x ↔ edgeRel x y := by
        simp only [edgeRel, eq_comm, ne_comm]
        tauto
      rw [he, or_self]
      exact and_iff_right_of_imp (fun h => h.1)
  have hconnected : (supportGraph H).Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable (supportGraph H)).mpr
    refine ⟨2, ?_⟩
    have h27 : (supportGraph H).Reachable 2 7 :=
      ((hgraph 2 7).mpr (by unfold edgeRel; decide)).reachable
    intro x
    fin_cases x
    · exact ((hgraph 2 0).mpr (by unfold edgeRel; decide)).reachable
    · exact h27.trans ((hgraph 7 1).mpr (by unfold edgeRel; decide)).reachable
    · exact .refl 2
    · exact h27.trans ((hgraph 7 3).mpr (by unfold edgeRel; decide)).reachable
    · exact ((hgraph 2 4).mpr (by unfold edgeRel; decide)).reachable
    · exact h27.trans ((hgraph 7 5).mpr (by unfold edgeRel; decide)).reachable
    · exact ((hgraph 2 6).mpr (by unfold edgeRel; decide)).reachable
    · exact h27
    · exact ((hgraph 2 8).mpr (by unfold edgeRel; decide)).reachable
    · exact h27.trans ((hgraph 7 9).mpr (by unfold edgeRel; decide)).reachable

  have hphases : ∃ Φout Φin, IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
      Φout * hamiltonianPropagator (H.map (↑)) 1 * Φin = F10 := by
    refine ⟨diagonal (fun x => ω⁻¹ * (z x)⁻¹), diagonal (fun x => (z x)⁻¹), ?_, ?_, ?_⟩
    · exact ⟨_, fun x => by simp [norm_mul, hnormω, hnormz], rfl⟩
    · exact ⟨_, fun x => by simp [hnormz], rfl⟩
    · rw [hexpH, hfactor]
      ext x y
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
      field_simp [hω_ne, hz_ne] <;> ring
  have hedges : edgeCount H = 23 := by
    have he : ∀ p : Fin 10 × Fin 10,
        (p.1 < p.2 ∧ H p.1 p.2 ≠ 0) ↔ (p.1 < p.2 ∧ edgeRel p.1 p.2) := by
      intro p
      by_cases hp : p.1 < p.2
      · simp only [hp, true_and, hH_nonzero p.1 p.2 (ne_of_lt hp)]
      · simp only [hp, false_and]
    letI : DecidableRel edgeRel := fun x y => by unfold edgeRel; infer_instance
    have hc : ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
        (fun p => p.1 < p.2 ∧ edgeRel p.1 p.2)).card = 23 := by decide
    unfold edgeCount
    rw [← hc]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgeCount]
    exact he p

  intro h
  have hbound := h H hsymm hnonneg hconnected hphases
  rw [hedges] at hbound
  omega

end D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
