import D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
import Reg.Support.SingleDependentReadout

/-! Faithful source reconstruction preserves every source parameter.
Four-slot registration remains unfinished under issue #20163: whole-family
intervention, sensitivity, observational dependence and the final
sourceSelection/escapeFrom evidence are not supplied. No declared_validated
status is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
open _root_.D5.S3.VertexAlgebra
open NestedResidues.BinaryLaurentEvaluation
open NestedResidues.LatticeHalfFockABLocalResidue
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockChargedTensorCoefficients LatticeGeneratingFieldLocality
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section

namespace Jump
structure Input where
  Q : BinaryPolynomial
  p : ℤ
  n : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ x =>
  (binaryKernel false x.p * binaryExpansion false (algebraMap _ ABField x.Q)).coeff
    (exponents 2 ![-1, -x.n - 1]) -
  (binaryKernel true x.p * binaryExpansion true (algebraMap _ ABField x.Q)).coeff
    (exponents 2 ![-x.n - 1, -1])) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), R.readout () () x =
    ∑ e ∈ x.Q.coeff.support,
      if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = -x.p - x.n - 2 then
        if x.p < 0 then x.Q.coeff e *
          ((Ring.choose (e ⟨0, by decide⟩) (-x.p - 1).toNat : ℤ) : ℂ) else 0 else 0

theorem source_bridge : (type_of% (@binary_laurent_jump)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.Q x.p x.n
  · intro h Q p n
    exact h () ⟨Q, p, n⟩
theorem actual_law : arena.Law actual := source_bridge.mp (@binary_laurent_jump)
end Jump

namespace Residue
structure Input where
  Q : BinaryPolynomial
  p : ℤ
  r : ℤ
  n : ℤ
  ell : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ x =>
  completeOuterResidue x.r x.n (binaryModes false (binaryRational x.Q x.p))
    (binaryModes true (binaryRational x.Q x.p)) x.ell) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), R.readout () () x =
    ∑ e ∈ x.Q.coeff.support,
      if e ⟨0, by decide⟩ + e ⟨2, by decide⟩ = -x.p - x.r - x.n - 2 then
        if x.p + x.r + x.ell < 0 then x.Q.coeff e *
          ((Ring.choose (e ⟨0, by decide⟩) (-x.p - x.r - x.ell - 1).toNat : ℤ) : ℂ)
        else 0 else 0

theorem source_bridge : (type_of% (@binary_complete_residue)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.Q x.p x.r x.n x.ell
  · intro h Q p r n ell
    exact h () ⟨Q, p, r, n, ell⟩
theorem actual_law : arena.Law actual := source_bridge.mp (@binary_complete_residue)
end Residue

namespace Fractional
structure Input where
  Q : BinaryPolynomial
  B : ℕ
  T : ℕ
  s : ℤ
  r : ℤ
  n : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ x =>
  supportedQReadout x.s x.r x.T x.n
    (binaryModes false (binaryRational x.Q (-(x.B : ℤ))))
    (binaryModes true (binaryRational x.Q (-(x.B : ℤ))))) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), x.B ≤ x.T → R.readout () () x =
    binaryTaylor x.Q x.B x.s x.r x.n

theorem source_bridge : (type_of% (@binary_fractional_taylor)) ↔ arena.Law actual := by
  constructor
  · intro h _ x hBT
    exact h x.Q x.B x.T x.s x.r x.n hBT
  · intro h Q B T s r n hBT
    exact h () ⟨Q, B, T, s, r, n⟩ hBT
theorem actual_law : arena.Law actual := source_bridge.mp (@binary_fractional_taylor)
end Fractional

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
