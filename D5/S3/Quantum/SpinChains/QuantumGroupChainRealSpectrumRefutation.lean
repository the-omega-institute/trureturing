/- GID: D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim; result=D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result; claim=D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim
   digest: A positive U_q(sl_2) spin chain can have nonreal eigenvalues. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Quantum.SpinChains.QuantumGroupChainRealSpectrumRefutation

noncomputable section

abbrev Local (n : ℕ) := Fin (n + 1)
abbrev Config (n N : ℕ) := Fin ((n + 1) ^ N)

def digit {n N : ℕ} (x : Config n N) (k : Fin N) : Local n :=
  ⟨x.val / (n + 1) ^ (N - 1 - k.val) % (n + 1), by
    exact Nat.mod_lt _ (by omega)⟩

def qnum (γ t : ℝ) : ℝ := Real.sin (γ * t) / Real.sin γ

def q (γ : ℝ) : ℂ := (Real.cos γ : ℂ) + Complex.I * (Real.sin γ : ℂ)

def γ₀ : ℝ := Real.arccos (4 / 5)

def weight (n : ℕ) (i : Local n) : ℝ := (i.val : ℝ) - (n : ℝ) / 2

def E (n : ℕ) (γ : ℝ) : Matrix (Local n) (Local n) ℂ :=
  fun i j => if i.val = j.val + 1 then
    (Real.sqrt (qnum γ ((n - j.val : ℕ) : ℝ) * qnum γ ((j.val + 1 : ℕ) : ℝ)) : ℂ)
    else 0

def F (n : ℕ) (γ : ℝ) : Matrix (Local n) (Local n) ℂ :=
  fun i j => if j.val = i.val + 1 then
    (Real.sqrt (qnum γ ((j.val : ℝ)) * qnum γ ((n - j.val + 1 : ℕ) : ℝ)) : ℂ)
    else 0

def K (n : ℕ) (γ : ℝ) : Matrix (Local n) (Local n) ℂ :=
  Matrix.diagonal (fun i => q (γ * weight n i))

def Kinv (n : ℕ) (γ : ℝ) : Matrix (Local n) (Local n) ℂ :=
  Matrix.diagonal (fun i => q (-(γ * weight n i)))

def tensorCasimir (n : ℕ) (γ : ℝ) :
    Matrix (Local n × Local n) (Local n × Local n) ℂ :=
  let de := Matrix.kroneckerMap (· * ·) (E n γ) (Kinv n γ) +
    Matrix.kroneckerMap (· * ·) (K n γ) (E n γ)
  let df := Matrix.kroneckerMap (· * ·) (F n γ) (Kinv n γ) +
    Matrix.kroneckerMap (· * ·) (K n γ) (F n γ)
  let dk := Matrix.kroneckerMap (· * ·) (K n γ) (K n γ)
  let dki := Matrix.kroneckerMap (· * ·) (Kinv n γ) (Kinv n γ)
  (1 / 2 : ℂ) • (de * df + df * de) -
    ((Real.cos γ / (4 * Real.sin γ ^ 2) : ℝ) : ℂ) • ((dk - dki) * (dk - dki))

def casimirValue (γ : ℝ) (l : ℕ) : ℝ := qnum γ (l : ℝ) * qnum γ ((l + 1 : ℕ) : ℝ)

def orderedProduct {α : Type} [Monoid α] (f : ℕ → α) : ℕ → α
  | 0 => 1
  | k + 1 => orderedProduct f k * f k

def projector (n s : ℕ) (γ : ℝ) :
    Matrix (Local n × Local n) (Local n × Local n) ℂ :=
  orderedProduct (fun l =>
    if l ≠ s then
      ((qnum γ ((s : ℝ) - l) * qnum γ ((s + l + 1 : ℕ) : ℝ))⁻¹ : ℂ) •
        (tensorCasimir n γ - (casimirValue γ l : ℂ) • 1)
    else 1) (n + 1)

def siteOperator {R : Type} [Zero R] {n N : ℕ} (m : Fin (N - 1))
    (P : Matrix (Local n × Local n) (Local n × Local n) R) :
    Matrix (Config n N) (Config n N) R :=
  fun x y =>
    if (∀ k : Fin N, k ≠ ⟨m.val, by omega⟩ → k ≠ ⟨m.val + 1, by omega⟩ →
        digit x k = digit y k) then
      P (digit x ⟨m.val, by omega⟩, digit x ⟨m.val + 1, by omega⟩)
        (digit y ⟨m.val, by omega⟩, digit y ⟨m.val + 1, by omega⟩)
    else 0

def hamiltonian (n s N : ℕ) (γ : ℝ) (a : Fin (N - 1) → ℝ) :
    Matrix (Config n N) (Config n N) ℂ :=
  ∑ m, (a m : ℂ) • siteOperator m (projector n s γ)

def claim : Prop :=
  ∀ (n s N : ℕ) (γ : ℝ),
    1 ≤ n → s ≤ n → 2 ≤ N → 0 < |γ| → n * |γ| < Real.pi →
    (∀ l : ℕ, l ≤ n → l ≠ s →
      qnum γ ((s : ℝ) - l) * qnum γ ((s + l + 1 : ℕ) : ℝ) ≠ 0) →
    ∀ (a : Fin (N - 1) → ℝ), (∀ m, 0 < a m) →
    ∀ (v : Config n N → ℂ) (z : ℂ), v ≠ 0 →
      hamiltonian n s N γ a *ᵥ v = z • v → z.im = 0

private theorem sin_γ₀ : Real.sin γ₀ = 3 / 5 := by
  rw [γ₀, Real.sin_arccos]
  norm_num

private theorem cos_γ₀ : Real.cos γ₀ = 4 / 5 := by
  rw [γ₀, Real.cos_arccos] <;> norm_num

private theorem sin_two_γ₀ : Real.sin (2 * γ₀) = 24 / 25 := by
  rw [Real.sin_two_mul, sin_γ₀, cos_γ₀]
  norm_num

private theorem sin_three_γ₀ : Real.sin (3 * γ₀) = 117 / 125 := by
  rw [Real.sin_three_mul, sin_γ₀]
  norm_num

private theorem sin_four_γ₀ : Real.sin (4 * γ₀) = 336 / 625 := by
  rw [show (4 : ℝ) * γ₀ = 2 * (2 * γ₀) by ring, Real.sin_two_mul,
    sin_two_γ₀]
  rw [show Real.cos (2 * γ₀) = 2 * Real.cos γ₀ ^ 2 - 1 by
    exact Real.cos_two_mul γ₀, cos_γ₀]
  norm_num

private theorem qnum_γ₀ (t : ℝ) :
    (t = 0 → qnum γ₀ t = 0) ∧
    (t = 1 → qnum γ₀ t = 1) ∧
    (t = 2 → qnum γ₀ t = 8 / 5) ∧
    (t = 3 → qnum γ₀ t = 39 / 25) ∧
    (t = 4 → qnum γ₀ t = 112 / 125) ∧
    (t = -1 → qnum γ₀ t = -1) := by
  constructor
  · intro h; subst t; simp [qnum, sin_γ₀]
  constructor
  · intro h; subst t; simp [qnum, sin_γ₀]
  constructor
  · intro h; subst t; rw [qnum, show γ₀ * 2 = 2 * γ₀ by ring, sin_two_γ₀, sin_γ₀]; norm_num
  constructor
  · intro h; subst t; rw [qnum, show γ₀ * 3 = 3 * γ₀ by ring, sin_three_γ₀, sin_γ₀]; norm_num
  constructor
  · intro h; subst t; rw [qnum, show γ₀ * 4 = 4 * γ₀ by ring, sin_four_γ₀, sin_γ₀]; norm_num
  · intro h; subst t
    rw [qnum, show γ₀ * (-1 : ℝ) = -(γ₀ * 1) by ring, Real.sin_neg,
      show γ₀ * 1 = γ₀ by ring, sin_γ₀]
    norm_num

private theorem qnum0 : qnum γ₀ 0 = 0 := (qnum_γ₀ 0).1 rfl
private theorem qnum1 : qnum γ₀ 1 = 1 := (qnum_γ₀ 1).2.1 rfl
private theorem qnum2 : qnum γ₀ 2 = 8 / 5 := (qnum_γ₀ 2).2.2.1 rfl
private theorem qnum3 : qnum γ₀ 3 = 39 / 25 := (qnum_γ₀ 3).2.2.2.1 rfl
private theorem qnum4 : qnum γ₀ 4 = 112 / 125 := (qnum_γ₀ 4).2.2.2.2.1 rfl
private theorem qnumNeg1 : qnum γ₀ (-1) = -1 := (qnum_γ₀ (-1)).2.2.2.2.2 rfl

private theorem q_γ₀ : q γ₀ = (4 / 5 : ℂ) + Complex.I * (3 / 5 : ℂ) := by
  simp [q, sin_γ₀, cos_γ₀]


private def flatten (i : Local 2 × Local 2) : Fin 9 :=
  ⟨3 * i.1.val + i.2.val, by omega⟩

private def c125G : Matrix (Local 2 × Local 2) (Local 2 × Local 2) GaussianInt :=
  fun i j => (!![312, 0, 0, 0, 0, 0, 0, 0, 0;
    0, ⟨256, -192⟩, 0, 200, 0, 0, 0, 0, 0;
    0, 0, ⟨56, -192⟩, 0, ⟨160, -120⟩, 0, 0, 0, 0;
    0, 200, 0, ⟨256, 192⟩, 0, 0, 0, 0, 0;
    0, 0, ⟨160, -120⟩, 0, 400, 0, ⟨160, 120⟩, 0, 0;
    0, 0, 0, 0, 0, ⟨256, -192⟩, 0, 200, 0;
    0, 0, 0, 0, ⟨160, 120⟩, 0, ⟨56, 192⟩, 0, 0;
    0, 0, 0, 0, 0, 200, 0, ⟨256, 192⟩, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 312]) (flatten i) (flatten j)

private def p14G : Matrix (Local 2 × Local 2) (Local 2 × Local 2) GaussianInt :=
  fun i j => (!![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, ⟨7, 24⟩, 0, (-25), 0, 0, 0, 0, 0;
    0, 0, 25, 0, ⟨0, 30⟩, 0, (-25), 0, 0;
    0, (-25), 0, ⟨7, -24⟩, 0, 0, 0, 0, 0;
    0, 0, ⟨0, 30⟩, 0, (-36), 0, ⟨0, -30⟩, 0, 0;
    0, 0, 0, 0, 0, ⟨7, 24⟩, 0, (-25), 0;
    0, 0, (-25), 0, ⟨0, -30⟩, 0, 25, 0, 0;
    0, 0, 0, 0, 0, (-25), 0, ⟨7, -24⟩, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]) (flatten i) (flatten j)

private def wG : Matrix (Config 2 4) (Fin 2) GaussianInt :=
  fun x j => match x.val, j.val with
    | 26, 1 => 4900
    | 44, 0 => ⟨-5500, -4125⟩
    | 44, 1 => ⟨3080, 8190⟩
    | 50, 0 => ⟨5500, -4125⟩
    | 50, 1 => ⟨-7000, 5250⟩
    | 62, 0 => ⟨8800, -6600⟩
    | 62, 1 => ⟨-9828, 3696⟩
    | 68, 0 => ⟨7920, 10560⟩
    | 68, 1 => ⟨-10080, -13440⟩
    | 70, 0 => ⟨-5500, 4125⟩
    | 70, 1 => ⟨7000, -5250⟩
    | 74, 0 => ⟨-8800, 6600⟩
    | 74, 1 => ⟨6300, -8400⟩
    | 76, 0 => ⟨-2420, -6435⟩
    | 76, 1 => ⟨7000, 5250⟩
    | 78, 1 => ⟨-1372, 4704⟩
    | _, _ => 0

private def a196G : Matrix (Fin 2) (Fin 2) GaussianInt := !![-154, 196; -275, 350]

private def bG : Matrix (Fin 2) (Fin 2) GaussianInt := !![1, 0; 0, 0]

end
end D5.S3.Quantum.SpinChains.QuantumGroupChainRealSpectrumRefutation
