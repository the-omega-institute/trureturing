import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open _root_.D5.S3.VertexAlgebra
open UniformGradedLocalCorrelator FieldNormalProductLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u
noncomputable section

abbrev sourceScope : Prop :=
  ∀ {N : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (A : Fin N → VertexOperator ℂ V) (vector : V) (P : Module.End ℂ V)
    (orders : Fin N × Fin N → ℕ)
    (_locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ orders (i, j)) (FieldNormalProductLocality.commutator (A i) (A j)) = 0)
    (l : List (Fin N)) (_nodup : l.Nodup) (_allLabels : ∀ i, i ∈ l),
    (∀ r, l.Perm r →
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l) =
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P r)) ∧
    (∀ i, LowerBoundIn
      (polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l)) i
      (((HahnModule.of ℂ).symm (A i vector)).order)) ∧
    (∀ total : ℤ, {e : Exponent N | totalExponent e = total ∧
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l) e ≠ 0}.Finite)

structure Parameters where
  N : ℕ
  V : Type u
  [addGroup : AddCommGroup V]
  [module : Module ℂ V]
  A : Fin N → VertexOperator ℂ V
  orders : Fin N × Fin N → ℕ
  locality : ∀ i j : Fin N, i < j →
    (deltaEnd ^ orders (i, j)) (FieldNormalProductLocality.commutator (A i) (A j)) = 0
  l : List (Fin N)
  nodup : l.Nodup
  allLabels : ∀ i, i ∈ l

attribute [instance] Parameters.addGroup Parameters.module

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.V × Module.End ℂ p.V × List (Fin p.N)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Distribution p.N p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p input =>
    let (v, P, order) := input
    polynomialAction (weightedClearingPolynomial p.orders)
      (coefficientDistribution p.A v P order))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ p v P,
    (∀ r, p.l.Perm r → R.readout () p (v, P, p.l) = R.readout () p (v, P, r)) ∧
    (∀ i, LowerBoundIn (R.readout () p (v, P, p.l)) i
      (((HahnModule.of ℂ).symm (p.A i v)).order)) ∧
    (∀ total : ℤ, {e : Exponent p.N | totalExponent e = total ∧
      R.readout () p (v, P, p.l) e ≠ 0}.Finite)

set_option maxHeartbeats 2000000 in
-- The dependent field and module instances are reconstructed at their original universe.
theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p v P
    exact h p.A v P p.orders p.locality p.l p.nodup p.allLabels
  · intro h N V addGroup module A v P orders locality l nodup allLabels
    let p : Parameters.{u} := {
      N := N
      V := V
      A := A
      orders := orders
      locality := locality
      l := l
      nodup := nodup
      allLabels := allLabels }
    exact h p v P

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.{u}.mp (@common_cleared_fields.{u})

/- Whole-family variation, sensitivity, observational dependence and enrolled
source-selection evidence are separate from this exact source reconstruction. -/

end
end Reg.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
