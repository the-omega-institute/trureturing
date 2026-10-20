/- GID: D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The qudit CHSH stabilizer-projector orthogonality graph has degree (2p-1)(p-1). -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import D5.S3.Observer.WindowRegister

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix Kronecker

namespace D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity

noncomputable section

/-- The primitive phase used by the qudit Weyl operators. -/
def omega (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))

/-- The cyclic shift matrix, with `shiftX p |x⟩ = |x+1⟩`. -/
def shiftX (p : ℕ) [Fact p.Prime] : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.circulant (fun i => if i = 1 then 1 else 0)

/-- The clock matrix, with `clockZ p |x⟩ = omega p ^ x |x⟩`. -/
def clockZ (p : ℕ) [Fact p.Prime] : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.diagonal (fun i => omega p ^ i.val)

/-- Alice's CHSH measurement operator. -/
def aliceOp (p : ℕ) [Fact p.Prime] (j : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  if p = 2 then
    if j = 0 then shiftX p else Complex.I • (shiftX p * clockZ p)
  else
    omega p ^ (j * (j + 1)).val • (shiftX p * clockZ p ^ j.val)

/-- Bob's CHSH measurement operator. -/
def bobOp (p : ℕ) [Fact p.Prime] (k : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  if p = 2 then
    if k = 0 then shiftX p else Complex.I • (shiftX p * clockZ p)
  else
    let h : ZMod p := (2 : ZMod p)⁻¹
    omega p ^ (h ^ 2 * (k ^ 2 + 2 * k)).val • (shiftX p * clockZ p ^ (h * k).val)

/-- The normalized spectral projector for an eigenvalue indexed by `a`. -/
def eigenProj (p : ℕ) [Fact p.Prime] (M : Matrix (ZMod p) (ZMod p) ℂ) (a : ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  (p : ℂ)⁻¹ • ∑ m : Fin p,
    omega p ^ (-(m : ZMod p) * a).val • M ^ m.val

/-- The rank-one projector selected by the qudit CHSH decomposition. -/
def vertexProj (p : ℕ) [Fact p.Prime] (v : ZMod p × ZMod p × ZMod p) :
    Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ :=
  eigenProj p (aliceOp p v.1) v.2.2 ⊗ₖ
    eigenProj p (bobOp p v.2.1) (-v.1 * v.2.1 - v.2.2)

/-- The all-prime regularity assertion for the CHSH orthogonality graph. -/
def claim : Prop :=
  ∀ (p : ℕ), ∀ [Fact p.Prime],
    Function.Injective (vertexProj p) ∧
      (∀ v, Matrix.trace (vertexProj p v) = 1 ∧
        vertexProj p v * vertexProj p v = vertexProj p v) ∧
      ∀ v,
        (Finset.univ.filter
          (fun w => w ≠ v ∧ vertexProj p v * vertexProj p w = 0)).card =
          (2 * p - 1) * (p - 1)

theorem result : claim := by
  sorry

end

end D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
