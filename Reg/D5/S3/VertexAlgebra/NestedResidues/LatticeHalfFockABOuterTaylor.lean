import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
import Reg.Support.SingleDependentReadout

/-! Faithful source reconstruction preserves every source parameter.
Four-slot registration remains unfinished under issue #20163: whole-family
intervention, sensitivity, observational dependence and the final
sourceSelection/escapeFrom evidence are not supplied. No declared_validated
status is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
open _root_.D5.S3.VertexAlgebra
open NestedResidues.BinaryLaurentEvaluation NestedResidues.LatticeHalfFockABOuterTaylor
open NestedResidues.LatticeHalfFockABLocalResidue
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockChargedTensorCoefficients LatticeGeneratingFieldLocality
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section
structure Input where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  b : Carrier D
  K : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor D hu
  phi : ActualTensor D hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3
  H : ℕ → ℕ

def coefficients (x : Input) : Prop :=
  ∀ e : Exponent 3, x.P.coeff e =
    if totalExponent e =
      (∑ p ∈ labelledPairs 3, (threeOrders x.D x.a x.b x.K p : ℤ)) - x.d - x.r - x.n - 3
    then x.phi (actualNumerator x.D x.hu x.i x.a x.b x.gamma x.delta x.K x.x e) else 0

def locality (x : Input) : Prop :=
  ∀ j ∈ Finset.range ((x.K : ℤ) - x.r).toNat,
    (FieldNormalProductLocality.deltaEnd ^ x.H j)
      (FieldNormalProductLocality.commutator (targetCurrent x.D x.hu x.i)
        (qField x.gamma (x.r + j) x.K (targetSlice x.D x.hu x.a x.gamma)
          (targetSlice x.D x.hu x.b x.delta))) = 0

namespace FullForward
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ x =>
  ∑ j ∈ Finset.range ((x.K : ℤ) - x.r).toNat, BinomialKernelDelta.chooseSign x.d j *
    x.phi (((qField 1 (x.d - j) (x.H j) (targetCurrent x.D x.hu x.i)
    (qField x.gamma (x.r + j) x.K (targetSlice x.D x.hu x.a x.gamma)
      (targetSlice x.D x.hu x.b x.delta)))[[x.n]]) x.x)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), coefficients x → locality x →
    let degree : ℤ := (vectorFrequencyBound x.D x.a + 1 : ℕ) +
      (vectorFrequencyBound x.D x.b + 1 : ℕ) + x.K - x.d - x.r - 2
    R.readout () () x = ∑ u ∈ Finset.range (degree + 1).toNat,
      collisionTaylor x.P x.gamma u (degree - u).toNat *
        orderedResidueWeight (x.d - (vectorFrequencyBound x.D x.a + 1 : ℕ))
          (degree - u + x.r - x.K)

set_option maxHeartbeats 1600000 in
-- Reconstruct every original input, including the supplied K and independent H(j).
theorem source_bridge : (type_of% (@forward_weighted_identity)) ↔ arena.Law actual := by
  constructor
  · intro h _ x hP hH
    exact h x.D x.hu x.i x.a x.b x.K x.gamma x.delta x.d x.r x.n x.x x.phi x.P hP x.H hH
  · intro h D hu i a b K gamma delta d r n x phi P hP H hH
    exact h () ⟨D, hu, i, a, b, K, gamma, delta, d, r, n, x, phi, P, H⟩ hP hH

theorem actual_law : arena.Law actual := source_bridge.mp (@forward_weighted_identity)
end FullForward

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
