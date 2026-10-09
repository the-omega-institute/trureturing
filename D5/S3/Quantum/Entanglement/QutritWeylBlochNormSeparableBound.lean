/- GID: D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound
   mirror-E: none
   anchors: []
   utility: none
   digest: Two-qutrit Weyl–Bloch ℓ1 norm has sharp separable bound 25. -/

import Mathlib.Analysis.Matrix.PosDef

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

end D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound
