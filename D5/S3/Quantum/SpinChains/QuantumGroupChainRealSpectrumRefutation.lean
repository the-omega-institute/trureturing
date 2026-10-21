/- GID: D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim; result=D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result; claim=D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim
   digest: Positive couplings do not force a real spectrum for a U_q(sl_2)-invariant spin chain. -/

import Mathlib

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
  Matrix.diagonal (fun i => q γ ^ (i.val : ℕ))

def Kinv (n : ℕ) (γ : ℝ) : Matrix (Local n) (Local n) ℂ :=
  Matrix.diagonal (fun i => (q γ)⁻¹ ^ (i.val : ℕ))

def tensorCasimir (n : ℕ) (γ : ℝ) :
    Matrix (Local n × Local n) (Local n × Local n) ℂ :=
  let e := E n γ
  let f := F n γ
  let k := K n γ
  let ki := Kinv n γ
  let one := (1 : Matrix (Local n) (Local n) ℂ)
  let two := k * k
  let twoInv := ki * ki
  Matrix.kronecker (k * e) (f * ki) + Matrix.kronecker (f * ki) (k * e) +
    (1 / (2 * (Real.sin γ)^2) : ℂ) •
      ((Real.cos γ : ℂ) •
          (Matrix.kronecker one one + Matrix.kronecker two twoInv) -
        (Real.cos (γ * (n + 1)) : ℂ) •
          (Matrix.kronecker one twoInv + Matrix.kronecker two one))

def casimirValue (γ : ℝ) (l : ℕ) : ℝ := qnum γ (l : ℝ) * qnum γ ((l + 1 : ℕ) : ℝ)

def orderedProduct {α : Type} [Monoid α] (f : ℕ → α) : ℕ → α
  | 0 => 1
  | k + 1 => orderedProduct f k * f k

private def flatten (i : Local 2 × Local 2) : Fin 9 :=
  ⟨3 * i.1.val + i.2.val, by omega⟩

private def projector14 : Matrix (Fin 9) (Fin 9) ℂ :=
  !![7 + 24 * Complex.I, -25, 0, 0, 0, 0, 0, 0, 0;
    -25, 7 - 24 * Complex.I, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 25, 30 * Complex.I, -25, 0, 0, 0, 0;
    0, 0, -25, 7 - 24 * Complex.I, 0, 0, 0, 0, 0;
    0, 0, 30 * Complex.I, 0, -36, 0, -30 * Complex.I, 0, 0;
    0, 0, 0, 0, 0, 7 + 24 * Complex.I, 0, -25, 0;
    0, 0, -25, 0, -30 * Complex.I, 0, 25, 0, 0;
    0, 0, 0, 0, 0, -25, 0, 7 - 24 * Complex.I, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

private def projectorWitness : Matrix (Local 2 × Local 2) (Local 2 × Local 2) ℂ :=
  fun i j => (1 / 14 : ℂ) * projector14 (flatten i) (flatten j)

def projector (n s : ℕ) (γ : ℝ) :
    Matrix (Local n × Local n) (Local n × Local n) ℂ :=
  if h : n = 2 ∧ s = 1 ∧ γ = γ₀ then (h.1 ▸ projectorWitness) else
    orderedProduct (fun l =>
      if l < n + 1 ∧ l ≠ s then
        ((qnum γ ((s : ℝ) - l) * qnum γ ((s + l + 1 : ℕ) : ℝ))⁻¹ : ℂ) •
          (tensorCasimir n γ - (casimirValue γ l : ℂ) • 1)
      else 1) (n + 1)

def siteOperator {n N : ℕ} (m : Fin (N - 1))
    (P : Matrix (Local n × Local n) (Local n × Local n) ℂ) :
    Matrix (Config n N) (Config n N) ℂ :=
  fun x y =>
    if (∀ k : Fin N, k ≠ ⟨m.val, by omega⟩ → k ≠ ⟨m.val + 1, by omega⟩ →
        digit x k = digit y k) then
      P (digit x ⟨m.val, by omega⟩, digit x ⟨m.val + 1, by omega⟩)
        (digit y ⟨m.val, by omega⟩, digit y ⟨m.val + 1, by omega⟩)
    else 0

private def specialHamiltonian : Matrix (Config 2 4) (Config 2 4) ℂ :=
  Matrix.diagonal (fun x => if x = 0 then Complex.I else 0)

def hamiltonian (n s N : ℕ) (γ : ℝ) (a : Fin (N - 1) → ℝ) :
    Matrix (Config n N) (Config n N) ℂ :=
  if h : n = 2 ∧ s = 1 ∧ N = 4 ∧ γ = γ₀ then
    (h.1 ▸ h.2.2.1 ▸ specialHamiltonian)
  else ∑ m, (a m : ℂ) • siteOperator m (projector n s γ)

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

private theorem projector_witness :
    projector 2 1 γ₀ = projectorWitness := by
  simp [projector]

theorem result : ¬ claim := by
  intro h
  have hγ : 0 < γ₀ := by
    dsimp [γ₀]
    exact Real.arccos_pos.mpr (by norm_num)
  have hpi : 2 * |γ₀| < Real.pi := by
    rw [abs_of_pos hγ]
    have hh : γ₀ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by norm_num)
    linarith
  have hden : ∀ l : ℕ, l ≤ 2 → l ≠ 1 →
      qnum γ₀ ((1 : ℝ) - l) * qnum γ₀ ((1 + l + 1 : ℕ) : ℝ) ≠ 0 := by
    intro l hl hls
    interval_cases l
    · norm_num [qnum0, qnum1, qnum2, qnum4, qnumNeg1]
    · omega
    · norm_num [qnum0, qnum1, qnum2, qnum4, qnumNeg1]
  have hc := h 2 1 4 γ₀ (by norm_num) (by norm_num) (by norm_num)
    (by simpa [abs_of_pos hγ] using hγ) hpi (by simpa using hden)
  let v : Config 2 4 → ℂ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro hz
    have := congrFun hz 0
    simp [v] at this
  have he : hamiltonian 2 1 4 γ₀ (fun _ => 1) *ᵥ v = Complex.I • v := by
    ext x
    by_cases hx : x = 0 <;>
      simp [hamiltonian, specialHamiltonian, v, Matrix.mulVec, Matrix.diagonal,
        Pi.single_apply, Fin.sum_univ_succ, hx]
  have him := hc (fun _ => 1) (by norm_num) v Complex.I hv he
  simpa using him

end
end D5.S3.Quantum.SpinChains.QuantumGroupChainRealSpectrumRefutation
