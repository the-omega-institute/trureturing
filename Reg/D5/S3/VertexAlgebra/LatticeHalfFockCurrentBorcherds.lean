import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCurrentBorcherds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

abbrev sourceScope := type_of%
  (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.current_borcherds)

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank

abbrev signature : Signature where
  Params := Parameters
  State p := Carrier p.D × ℤ × ℤ × ℤ × ℤ × ActualTensor p.D p.hu
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role param input =>
    let (b, delta, p, q, r, x) := input
    if role = 0 then currentLeftTerm param.D param.hu param.i b delta p q r x
    else if role = 1 then currentRightFirstTerm param.D param.hu param.i b delta p q r x
    else currentRightSecondTerm param.D param.hu param.i b delta p q r x)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ param input,
    Function.HasFiniteSupport (R.readout 0 param input) ∧
    Function.HasFiniteSupport (R.readout 1 param input) ∧
    Function.HasFiniteSupport (R.readout 2 param input) ∧
    (∑ᶠ j : ℕ, R.readout 0 param input j) =
      (∑ᶠ j : ℕ, R.readout 1 param input j) -
      (∑ᶠ j : ℕ, R.readout 2 param input j)

/-- The source bridge retains all three supports and every original parameter. -/
theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h param ⟨b, delta, p, q, r, x⟩
    simpa [arena, actual, realize] using h param.D param.hu param.i b delta p q r x
  · intro h D hu i b delta p q r x
    simpa [arena, actual, realize] using h ⟨D, hu, i⟩ ⟨b, delta, p, q, r, x⟩

theorem actual_law : arena.Law actual := source_bridge.mp
  (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.current_borcherds)

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
