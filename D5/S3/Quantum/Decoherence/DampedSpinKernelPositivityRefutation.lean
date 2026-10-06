/- GID: D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.claim; result=D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result; claim=D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.claim
   digest: The damped spin kernel criterion fails for spin three-halves. -/

/-
proof_shape: result: bind-only; all evaluation and normalization helpers are local have proofs.
escape_witness: none
admission_basis: open-problem-resolution (#12737; Refuted)
Direct frozen dependencies: D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity.
  statement_id: sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators ComplexOrder Classical
open Finset
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
namespace D5.S3.Quantum.Decoherence.DampedSpinKernelPositivityRefutation

/-- Admissibility of doubled spin and magnetic quantum numbers. -/
def SpinValid (j m : ℤ) : Prop := 0 ≤ j ∧ -j ≤ m ∧ m ≤ j ∧ (j - m) % 2 = 0

/-- All selection rules, including the triangle and parity conditions. -/
def CGValid (j₁ m₁ j₂ m₂ J M : ℤ) : Prop :=
  SpinValid j₁ m₁ ∧ SpinValid j₂ m₂ ∧ SpinValid J M ∧ M = m₁ + m₂ ∧
  J ≤ j₁ + j₂ ∧ j₁ - j₂ ≤ J ∧ j₂ - j₁ ≤ J ∧ (j₁ + j₂ + J) % 2 = 0

/-- Racah's closed formula for the Condon–Shortley Clebsch–Gordan coefficient.
Every argument is doubled; the prefactor's two square roots are combined.
Terms with a negative factorial argument are omitted. -/
def CG (j₁ m₁ j₂ m₂ J M : ℤ) : ℝ :=
  if CGValid j₁ m₁ j₂ m₂ J M then
    let fac (a : ℤ) : ℝ := (a.toNat.factorial : ℝ)
    let A := (j₁ + j₂ - J) / 2
    let B := (j₁ - m₁) / 2
    let C := (j₂ + m₂) / 2
    let D := (J - j₂ + m₁) / 2
    let E := (J - j₁ - m₂) / 2
    Real.sqrt (((J + 1 : ℤ) : ℝ) *
      fac ((J + j₁ - j₂) / 2) * fac ((J - j₁ + j₂) / 2) * fac A /
      fac ((j₁ + j₂ + J) / 2 + 1) *
      fac ((J + M) / 2) * fac ((J - M) / 2) *
      fac ((j₁ + m₁) / 2) * fac B * fac C * fac ((j₂ - m₂) / 2)) *
      ∑ z ∈ Finset.range (A.toNat + 1),
        if (z : ℤ) ≤ A ∧ (z : ℤ) ≤ B ∧ (z : ℤ) ≤ C ∧
          0 ≤ D + z ∧ 0 ≤ E + z then
          (-1 : ℝ) ^ z /
            (fac z * fac (A - z) * fac (B - z) * fac (C - z) *
              fac (D + z) * fac (E + z))
        else 0
  else 0

/-- The standard Jz basis is ordered J, J-1, ..., -J. -/
def mag (n : ℕ) (i : Fin (n+1)) : ℤ := (n : ℤ) - 2 * (i : ℕ)

/-- Equation (12), with row m' and column m. -/
def T (n L : ℕ) (k : ℤ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => (Real.sqrt ((2 * (L : ℝ) + 1) / (n + 1)) *
    CG n (mag n j) (2 * (L : ℤ)) (2 * k) n (mag n i) : ℝ)

/-- Equation (13), with the adjoint on the irreducible tensor. -/
def rhoCoeff {n : ℕ} (ρ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (L : ℕ) (k : ℤ) : ℂ :=
  Matrix.trace ((T n L k).conjTranspose * ρ)

/-- Standard Legendre polynomial, obtained from Mathlib's shifted polynomial
P_L(1-2x) by the inverse affine substitution. -/
def legendre (L : ℕ) : Polynomial ℝ :=
  ((Polynomial.shiftedLegendre L).map (Int.castRingHom ℝ)).comp
    (Polynomial.C (1/2) * (1 - Polynomial.X))

/-- Associated Legendre function with the Condon–Shortley phase.
On -1 ≤ x ≤ 1, sqrt(1-x²)^m is exactly (1-x²)^(m/2). -/
def assocLegendre (L m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^m * Real.sqrt (1 - x^2)^m *
    ((Polynomial.derivative^[m]) (legendre L)).eval x

/-- sqrt(4π) times the Condon–Shortley harmonic of nonnegative order. -/
def Ypos (L m : ℕ) (θ φ : ℝ) : ℂ :=
  if m ≤ L then
    (Real.sqrt ((2 * (L : ℝ) + 1) * ((L-m).factorial : ℝ) /
      ((L+m).factorial : ℝ)) * assocLegendre L m (Real.cos θ) : ℝ) *
      Complex.exp (Complex.I * (m : ℂ) * (φ : ℂ))
  else 0

/-- Negative orders obey Y_(L,-k) = (-1)^k conj(Y_(L,k));
the function is zero outside |k| ≤ L. -/
def Y (L : ℕ) (k : ℤ) (θ φ : ℝ) : ℂ :=
  if 0 ≤ k then Ypos L k.toNat θ φ
  else (-1 : ℂ)^k.natAbs * star (Ypos L k.natAbs θ φ)

/-- The binomial ratio in (44) and (53). -/
def r (n L : ℕ) : ℝ := (n.choose L : ℝ) / ((n+L+1).choose L : ℝ)

/-- Equation (44), summing all multipoles and magnetic orders. -/
def F (n : ℕ) (σ γ t : ℝ) (ρ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (θ φ : ℝ) : ℂ :=
  ((n+1 : ℝ)^(-(1:ℝ)/2) : ℝ) *
    ∑ L ∈ Finset.range (n+1), ∑ k ∈ Finset.Icc (-(L:ℤ)) (L:ℤ),
      (Real.exp (-γ * (L:ℝ) * (L+1) * t / 2) * (r n L)^(-σ/2) : ℝ) *
        rhoCoeff ρ L k * star (Y L k θ φ)

/-- The positivity conjecture of arXiv:2605.02696v1, Section VI, equation (53). -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ : ℝ, σ ∈ Set.Icc (-1:ℝ) 1 →
    ∀ γ : ℝ, 0 < γ → ∀ t : ℝ, 0 ≤ t →
      (∀ L : ℕ, L ≤ n → Real.exp (-γ * (L:ℝ) * (L+1) * t / 2) *
        (r n L)^(-σ/2) ≤ (r n L)^((1:ℝ)/2)) →
      ∀ ρ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ, IsDensity ρ →
        ∀ θ φ : ℝ, 0 ≤ (F n σ γ t ρ θ φ).re

/-- Refutation at J = 3/2, σ = 1, γ = log(20/11), t = 1. -/
theorem result : ¬ claim := by
  let bottom : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 3 3 1
  have legendre_one (L : ℕ) : (legendre L).eval 1 = 1 := by
    simp [legendre, Polynomial.shiftedLegendre, Polynomial.eval_comp,
      Polynomial.eval_map ]

  have Ypos_north (L m : ℕ) (φ : ℝ) :
      Ypos L m 0 φ = if m = 0 then (Real.sqrt (2*(L:ℝ)+1) : ℂ) else 0 := by
    by_cases hm : m = 0
    · subst m
      have hf : Real.sqrt (L.factorial : ℝ) ≠ 0 := by positivity
      simp [Ypos, assocLegendre, legendre_one, hf]
    · simp [Ypos, assocLegendre, hm, zero_pow hm]

  have Y_north (L : ℕ) (k : ℤ) (φ : ℝ) :
      Y L k 0 φ = if k = 0 then (Real.sqrt (2*(L:ℝ)+1) : ℂ) else 0 := by
    by_cases hk : 0 ≤ k
    · have hz : k.toNat = 0 ↔ k = 0 := by omega
      simp only [Y, if_pos hk, Ypos_north, hz]
    · have hne : k ≠ 0 := by omega
      simp [Y, hk, Ypos_north, hne]

  have cg0 : CG 3 (-3) 0 0 3 (-3) = 1 := by
    norm_num only [CG, CGValid, SpinValid, Int.toNat, Nat.factorial, Finset.sum_range_succ]
    norm_num

  have cg1 : CG 3 (-3) 2 0 3 (-3) = -Real.sqrt (3/5) := by
    norm_num only [CG, CGValid, SpinValid, Int.toNat, Nat.factorial, Finset.sum_range_succ]
    rw [show (12/5:ℝ) = 4*(3/5) by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
    ring

  have cg2 : CG 3 (-3) 4 0 3 (-3) = Real.sqrt (1/5) := by
    norm_num only [CG, CGValid, SpinValid, Int.toNat, Nat.factorial, Finset.sum_range_succ]
    rw [show (16/5:ℝ) = 16*(1/5) by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
    ring

  have cg3 : CG 3 (-3) 6 0 3 (-3) = -Real.sqrt (1/35) := by
    norm_num only [CG, CGValid, SpinValid, Int.toNat, Nat.factorial, Finset.sum_range_succ]
    rw [show (1296/35:ℝ) = 1296*(1/35) by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
    ring

  have bottom_density : IsDensity bottom := by
    constructor
    · have heq : bottom = Matrix.diagonal (fun i : Fin 4 => if i = 3 then (1:ℂ) else 0) := by
        ext i j
        change (if 3 = i ∧ 3 = j then (1:ℂ) else 0) =
          (if i = j then if i = 3 then 1 else 0 else 0)
        (split_ifs <;> simp_all); aesop
      rw [heq]
      apply Matrix.PosSemidef.diagonal
      intro i
      change (0:ℂ) ≤ if i = 3 then 1 else 0
      split_ifs <;> simp
    · simp [bottom]

  have bottom_coeff (L : ℕ) (k : ℤ) :
      rhoCoeff bottom L k =
        ((Real.sqrt ((2*(L:ℝ)+1)/4) * CG 3 (-3) (2*(L:ℤ)) (2*k) 3 (-3) : ℝ) : ℂ) := by
    norm_num [rhoCoeff, bottom, Matrix.trace_mul_single, T, mag]

  have F_north (σ γ t : ℝ) :
      F 3 σ γ t bottom 0 0 = (((4:ℝ)^(-(1:ℝ)/2) : ℝ) : ℂ) *
        ∑ L ∈ Finset.range 4,
          ((Real.exp (-γ * (L:ℝ) * (L+1) * t / 2) * (r 3 L)^(-σ/2) *
            (Real.sqrt ((2*(L:ℝ)+1)/4) * CG 3 (-3) (2*(L:ℤ)) 0 3 (-3)) *
            Real.sqrt (2*(L:ℝ)+1) : ℝ) : ℂ) := by
    simp only [F, Y_north, apply_ite, Complex.star_def, map_zero, Complex.conj_ofReal]
    norm_num [mul_ite, bottom_coeff, ← Complex.ofReal_mul]

  have damp (a : ℕ) :
      Real.exp ((a:ℝ) * (-Real.log (20/11))) = (11/20:ℝ)^a := by
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num

  have damp_L (L : ℕ) (hL : L ≤ 3) :
      Real.exp (-Real.log (20/11) * (L:ℝ) * (L+1) * 1 / 2) =
        (11/20:ℝ)^(L*(L+1)/2) := by
    interval_cases L
    · norm_num
    · calc
        _ = Real.exp ((1:ℝ) * (-Real.log (20/11))) := by congr 1; norm_num; ring
        _ = _ := by simpa using damp 1
    · calc
        _ = Real.exp ((3:ℝ) * (-Real.log (20/11))) := by congr 1; norm_num; ring
        _ = _ := by simpa using damp 3
    · calc
        _ = Real.exp ((6:ℝ) * (-Real.log (20/11))) := by congr 1; norm_num; ring
        _ = _ := by simpa using damp 6

  have premise : ∀ L : ℕ, L ≤ 3 →
      Real.exp (-Real.log (20/11) * (L:ℝ) * (L+1) * 1 / 2) *
        (r 3 L)^(-(1:ℝ)/2) ≤ (r 3 L)^((1:ℝ)/2) := by
    intro L hL
    have hr : 0 < r 3 L := by
      interval_cases L <;> norm_num [r, Nat.choose]
    rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring, Real.rpow_neg hr.le,
      ← Real.sqrt_eq_rpow]
    rw [← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.2 hr), Real.mul_self_sqrt hr.le,
      damp_L L hL]
    interval_cases L <;> norm_num [r, Nat.choose]

  have cg_table (L : ℕ) (hL : L ≤ 3) :
      CG 3 (-3) (2*(L:ℤ)) 0 3 (-3) = (-1:ℝ)^L * Real.sqrt (r 3 L) := by
    interval_cases L <;> norm_num [r, Nat.choose, cg0, cg1, cg2, cg3]

  have kernel_term (L : ℕ) (hL : L ≤ 3) :
      (r 3 L)^(-(1:ℝ)/2) *
        (Real.sqrt ((2*(L:ℝ)+1)/4) * CG 3 (-3) (2*(L:ℤ)) 0 3 (-3)) *
        Real.sqrt (2*(L:ℝ)+1) = (-1:ℝ)^L * (2*(L:ℝ)+1)/2 := by
    have hr : 0 < r 3 L := by interval_cases L <;> norm_num [r, Nat.choose]
    rw [cg_table L hL, show -(1:ℝ)/2 = -((1:ℝ)/2) by ring,
      Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_div (by positivity)]
    norm_num
    have hsr : Real.sqrt (r 3 L) ≠ 0 := by positivity
    have hsL := Real.mul_self_sqrt (show 0 ≤ 2*(L:ℝ)+1 by positivity)
    field_simp
    nlinarith

  have half_four : (4:ℝ)^(-(1:ℝ)/2) = 1/2 := by
    rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring,
      Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num

  have F_value : F 3 1 (Real.log (20/11)) 1 bottom 0 0 =
      ((-760927/256000000:ℝ) : ℂ) := by
    have heq : F 3 1 (Real.log (20/11)) 1 bottom 0 0 =
        ((1/2:ℝ):ℂ) * ∑ L ∈ Finset.range 4,
          (((11/20:ℝ)^(L*(L+1)/2) * ((-1:ℝ)^L * (2*(L:ℝ)+1)/2) : ℝ) : ℂ) := by
      rw [F_north, half_four]
      congr 1
      apply Finset.sum_congr rfl
      intro L hL
      have hb : L ≤ 3 := by simp only [Finset.mem_range] at hL; omega
      rw [damp_L L hb]
      congr 1
      calc
        _ = (11/20:ℝ)^(L*(L+1)/2) *
            ((r 3 L)^(-(1:ℝ)/2) *
              (Real.sqrt ((2*(L:ℝ)+1)/4) * CG 3 (-3) (2*(L:ℤ)) 0 3 (-3)) *
              Real.sqrt (2*(L:ℝ)+1)) := by ring
        _ = _ := by rw [kernel_term L hb]
    rw [heq]
    norm_num [Finset.sum_range_succ]

  intro h
  have hpos := h 3 (by norm_num) 1 (by norm_num [Set.mem_Icc])
    (Real.log (20/11)) (Real.log_pos (by norm_num)) 1 (by norm_num)
    premise bottom bottom_density 0 0
  rw [F_value] at hpos
  norm_num at hpos

end D5.S3.Quantum.Decoherence.DampedSpinKernelPositivityRefutation
