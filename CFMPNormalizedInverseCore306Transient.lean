import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
namespace CFMPNormalizedInverseTangent107
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℝ

def normalScale (G : Mat) : Mat :=
  Matrix.diagonal (fun i => (Real.sqrt (G⁻¹ i i))⁻¹)

def normalizedInverse (G : Mat) : Mat :=
  normalScale G * G⁻¹ * normalScale G

end CFMPNormalizedInverseTangent107
