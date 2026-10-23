import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue
import Reg.Support.SingleDependentReadout

/-! Full dependent source reconstruction. The typed four-slot registration
remains unfinished under the source-bound exception in issue #20163:
whole-family variation, sensitivity, dependence and final sourceSelection /
escapeFrom evidence are not supplied. No declared_validated status is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue
open _root_.D5.S3.VertexAlgebra
open NestedResidues.LatticeHalfFockABLocalResidue
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockChargedTensorCoefficients LatticeGeneratingFieldLocality
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open LabelledRationalClearing.GlobalRationalCurry
open OrderedCollisionCoordinates.LocalResidueCurrying
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section

namespace RemainingOrders

structure Input where
  D : LatticeData
  a : Carrier D
  b : Carrier D
  K : ℕ
  I : ℕ
  P : LabelledPolynomial ℂ 3
  s : ℤ
  w : ℤ
  k : ℤ
  l : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ABField)

def actual : Realization signature := realize signature (fun _ _ x =>
  completeAB x.s x.w x.I (originalRational x.D x.a x.b x.K x.P)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input),
    (localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ x.w * originalRational x.D x.a x.b x.K x.P) =
      ∑ e ∈ x.P.coeff.support, abMonomialValue x.D x.a x.b x.K e (x.P.coeff e) x.w) ∧
    ((x.K : ℤ) ≤ x.w → localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ x.w * originalRational x.D x.a x.b x.K x.P) = 0) ∧
    lastSourceLocalQ 1 true x.s x.w x.I x.k x.l (originalRational x.D x.a x.b x.K x.P) =
      (coefficientHahn ℂ 2 0 (1 : Fin 3) (finSuccAboveEquiv 1) (R.readout () () x)).coeff
        (SupportedFieldWords.OrderedWords.exponents 2 ![-x.l - 1, -x.k - 1]) ∧
    lastSourceLocalQ 1 false x.s x.w x.I x.k x.l (originalRational x.D x.a x.b x.K x.P) =
      (coefficientHahn ℂ 1 1 (1 : Fin 3) ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1))
        (R.readout () () x)).coeff
        (SupportedFieldWords.OrderedWords.exponents 2 ![-x.k - 1, -x.l - 1])

set_option maxHeartbeats 1000000 in
-- Preserve the complete dependent source telescope in both directions.
theorem source_bridge :
    (type_of% (@ab_complete_remaining_orders)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.D x.a x.b x.K x.I x.P x.s x.w x.k x.l
  · intro h D a b K I P s w k l
    exact h () ⟨D, a, b, K, I, P, s, w, k, l⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@ab_complete_remaining_orders)

end RemainingOrders

namespace PoleBound

structure Input where
  D : LatticeData
  a : Carrier D
  b : Carrier D
  K : ℕ
  I : ℕ
  P : LabelledPolynomial ℂ 3
  s : ℤ
  w : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ABField)

def actual : Realization signature := realize signature (fun _ _ x =>
  completeAB x.s x.w x.I (originalRational x.D x.a x.b x.K x.P)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input),
    HasABPoleBound
      (vectorFrequencyBound x.D x.a + 1 + (vectorFrequencyBound x.D x.b + 1) +
        ((x.K : ℤ) - x.w - 1).toNat) (R.readout () () x)

set_option maxHeartbeats 1000000 in
-- Preserve the complete dependent source telescope in both directions.
theorem source_bridge :
    (type_of% (@ab_complete_pole_bound)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.D x.a x.b x.K x.I x.P x.s x.w
  · intro h D a b K I P s w
    exact h () ⟨D, a, b, K, I, P, s, w⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@ab_complete_pole_bound)

end PoleBound

namespace CutoffCompatibility

structure Input where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  b : Carrier D
  K : ℕ
  K₁ : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor D hu
  phi : ActualTensor D hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3
  P₁ : LabelledPolynomial ℂ 3
  s : ℤ
  w : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ABField)

def actual : Realization signature := realize signature (fun _ _ x =>
  completeAB x.s x.w x.K₁ (originalRational x.D x.a x.b x.K₁ x.P₁)) (fun empty => nomatch empty)

def coefficients (x : Input) (k : ℕ) (Q : LabelledPolynomial ℂ 3) : Prop :=
  ∀ e : Exponent 3, Q.coeff e =
    if totalExponent e =
        (∑ p ∈ labelledPairs 3, (threeOrders x.D x.a x.b k p : ℤ)) - x.d - x.r - x.n - 3
    then x.phi (actualNumerator x.D x.hu x.i x.a x.b x.gamma x.delta k x.x e) else 0

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), coefficients x x.K x.P → coefficients x x.K₁ x.P₁ →
    completeAB x.s x.w x.K (originalRational x.D x.a x.b x.K x.P) = R.readout () () x

set_option maxHeartbeats 1000000 in
-- Preserve the complete dependent source telescope in both directions.
theorem source_bridge :
    (type_of% (@actual_ab_local_cutoff_compat)) ↔ arena.Law actual := by
  constructor
  · intro h _ x hP hP₁
    exact h x.D x.hu x.i x.a x.b x.K x.K₁ x.gamma x.delta x.d x.r x.n x.x x.phi
      x.P x.P₁ hP hP₁ x.s x.w
  · intro h D hu i a b K K₁ gamma delta d r n x phi P P₁ hP hP₁ s w
    exact h () ⟨D, hu, i, a, b, K, K₁, gamma, delta, d, r, n, x, phi, P, P₁, s, w⟩ hP hP₁

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_ab_local_cutoff_compat)

end CutoffCompatibility

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue
