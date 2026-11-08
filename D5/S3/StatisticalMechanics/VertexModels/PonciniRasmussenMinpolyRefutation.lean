/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.FieldTheory.Minpoly.Field]
   utility: none
   digest: Conjecture B.1 for the literal planar diagram algebra at loop fugacity zero. -/
import D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Basic.Complex.Basic

/-! The quantified family uses the full noncrossing diagram basis and literal path concatenation. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation
open D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra

/-- Poncini–Rasmussen Conjecture B.1 with its original quantifier and Hamiltonian. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ((minpoly ℂ (h ℂ n)).natDegree : ℚ) =
      ((3 : ℚ)^((n+1)/2) + (-1 : ℚ)^n * 3^((n-1)/2))/2

end D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation
