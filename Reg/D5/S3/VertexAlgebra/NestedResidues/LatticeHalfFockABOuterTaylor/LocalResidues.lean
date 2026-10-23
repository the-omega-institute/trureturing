import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues
import Reg.Support.SingleDependentReadout
/-! Faithful finite collision readout; four-slot registration is unfinished under
issue #20510. Variation, sensitivity, observational dependence and lawful final
template/source binding are absent. No declared_validated status is claimed. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues
open _root_.D5.S3.VertexAlgebra
open UniformGradedLocalCorrelator LatticeHalfFockNestedQReadout
open CollisionRationalExpansions.OrderedRationalExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section
structure Input where
  P : LabelledPolynomial ℂ 3
  gamma : ℤ
  d : ℤ
  r : ℤ
  L : ℕ
  M : ℕ
  N : ℕ
  degree : ℕ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ x =>
  ∑ u ∈ Finset.range (x.degree + 1), collisionTaylor x.P x.gamma u (x.degree-u) *
    fusedResidueWeight ((u : ℤ)-x.M) (x.d-x.L)) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input),
    (x.degree : ℤ) = x.L + x.M + x.N - x.d - x.r - 2 →
    R.readout () () x =
      (∑ u ∈ Finset.range (x.degree+1), collisionTaylor x.P x.gamma u (x.degree-u) *
        orderedResidueWeight (x.d-x.L) ((x.degree-u : ℕ)+x.r-x.N)) -
      StateFieldResidueReconstruction.epsilon (x.d-x.L) *
        ∑ u ∈ Finset.range (x.degree+1), collisionTaylor x.P x.gamma u (x.degree-u) *
          orderedResidueWeight (x.d-x.L) ((u : ℤ)-x.M)
theorem source_bridge : (type_of% (@finite_collision_balance)) ↔ arena.Law actual := by
  constructor
  · intro h _ x total
    exact h x.P x.gamma x.d x.r x.L x.M x.N x.degree total
  · intro h P gamma d r L M N degree total
    exact h () ⟨P, gamma, d, r, L, M, N, degree⟩ total
theorem actual_law : arena.Law actual := source_bridge.mp (@finite_collision_balance)
end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues
