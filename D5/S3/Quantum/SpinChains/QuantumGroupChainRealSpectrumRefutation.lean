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
abbrev Config (n N : ℕ) := Fin N → Local n

def qnum (γ t : ℝ) : ℝ := Real.sin (γ * t) / Real.sin γ

def q (γ : ℝ) : ℂ := Complex.exp (γ * Complex.I)

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

def projector (n s : ℕ) (γ : ℝ) :
    Matrix (Local n × Local n) (Local n × Local n) ℂ :=
  orderedProduct (fun l =>
    if l < n + 1 ∧ l ≠ s then
      ((qnum γ ((s : ℝ) - l) * qnum γ ((s + l + 1 : ℕ) : ℝ))⁻¹ : ℂ) •
        (tensorCasimir n γ - (casimirValue γ l : ℂ) • 1)
    else 1) (n + 1)

def siteOperator {n N : ℕ} (m : Fin (N - 1))
    (P : Matrix (Local n × Local n) (Local n × Local n) ℂ) :
    Matrix (Config n N) (Config n N) ℂ :=
  fun x y =>
    if (∀ k : Fin N, k ≠ ⟨m.val, by omega⟩ → k ≠ ⟨m.val + 1, by omega⟩ → x k = y k) then
      P (x ⟨m.val, by omega⟩, x ⟨m.val + 1, by omega⟩)
        (y ⟨m.val, by omega⟩, y ⟨m.val + 1, by omega⟩)
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

theorem result : ¬ claim := by
  sorry

end
end D5.S3.Quantum.SpinChains.QuantumGroupChainRealSpectrumRefutation
