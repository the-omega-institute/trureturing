/- GID: D5/S3/Quantum/Information/GroupInvariantPsi/Defs
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GroupInvariantPsi/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Order.Basic]
   utility: none
   digest: Faithful finite-group state discrimination and its normalized asymptotic trace function. -/

import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Matrix.SpectralPower
import Mathlib.Topology.Order.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace D5.S3.Quantum.Information.GroupInvariantPsi.Defs

/-- Tensor coordinates are words in the fixed orthonormal basis. The matrix entry
at words `x,y` is the product of the entries at `x j,y j`, including the empty word. -/
def tensorPower {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap
    (fun _ : Fin n => Fin d) (fun _ : Fin n => A)

/-- Uniform finite-group Haar average of the tensor-power conjugates. -/
def twirlPower {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (u : G →* unitary (Matrix (Fin d) (Fin d) ℂ))
    (ρ : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
    tensorPower (u g : Matrix (Fin d) (Fin d) ℂ) n * tensorPower ρ n *
      (tensorPower (u g : Matrix (Fin d) (Fin d) ℂ) n).conjTranspose

/-- Logarithmic trace overlap, with real powers given by continuous functional calculus. -/
def psiN {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (u : G →* unitary (Matrix (Fin d) (Fin d) ℂ))
    (ρ₀ ρ₁ : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) (s : ℝ) : ℝ :=
  Real.log (Matrix.trace
    (D5.S3.Quantum.Matrix.SpectralPower.mpow (twirlPower u ρ₀ n) s *
      D5.S3.Quantum.Matrix.SpectralPower.mpow (twirlPower u ρ₁ n) (1 - s))).re

/-- The limit selector is used only with an explicit convergence hypothesis. -/
def psi {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (u : G →* unitary (Matrix (Fin d) (Fin d) ℂ))
    (ρ₀ ρ₁ : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => psiN u ρ₀ ρ₁ n s / (n : ℝ))

/-- Finite-group restriction of differentiability for faithful state discrimination.
Every finite group is compact with its discrete topology, and its normalized Haar
average is the uniform average used in `twirlPower`; a counterexample to this
restriction therefore refutes the assertion for arbitrary compact groups.
Faithful density matrices are precisely positive definite matrices of trace one. -/
def claim : Prop :=
  ∀ (d : ℕ) (G : Type) [Group G] [Fintype G]
    (u : G →* unitary (Matrix (Fin d) (Fin d) ℂ))
    (ρ₀ ρ₁ : Matrix (Fin d) (Fin d) ℂ),
    ρ₀.PosDef → Matrix.trace ρ₀ = 1 →
    ρ₁.PosDef → Matrix.trace ρ₁ = 1 →
    (∀ s ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => psiN u ρ₀ ρ₁ n s / (n : ℝ)) atTop
        (𝓝 (psi u ρ₀ ρ₁ s))) →
    DifferentiableOn ℝ (psi u ρ₀ ρ₁) (Set.Ioo 0 1)

end D5.S3.Quantum.Information.GroupInvariantPsi.Defs
