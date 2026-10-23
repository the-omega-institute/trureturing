import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
import Reg.Support.SingleDependentReadout

/-! Exact source reconstruction includes all three original locality orders.
The four-slot audit is unfinished under issue #20163: whole-family intervention,
sensitivity, observational dependence and lawful sourceSelection/escapeFrom
are absent. The source bridge and actual law assert no declared_validated status. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
open _root_.D5.S3.VertexAlgebra
open NestedResidues.LatticeHalfFockFirstOuterTaylor
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
  H₁ : ℕ
  H₂ : ℕ → ℕ
  H₃ : ℕ → ℕ

def coefficients (x : Input) : Prop :=
  ∀ e : Exponent 3, x.P.coeff e =
    if totalExponent e =
      (∑ p ∈ labelledPairs 3, (threeOrders x.D x.a x.b x.K p : ℤ)) - x.d - x.r - x.n - 3
    then x.phi (actualNumerator x.D x.hu x.i x.a x.b x.gamma x.delta x.K x.x e) else 0

def firstLocality (x : Input) : Prop :=
  (FieldNormalProductLocality.deltaEnd ^ x.H₁)
    (FieldNormalProductLocality.commutator
      (targetSlice x.D x.hu (neutralMode x.D x.i x.d x.a) (x.gamma + 1))
      (targetSlice x.D x.hu x.b x.delta)) = 0

def middleLocality (x : Input) : Prop :=
  ∀ j ∈ Finset.range ((x.K : ℤ) - x.r).toNat,
    (FieldNormalProductLocality.deltaEnd ^ x.H₂ j)
      (FieldNormalProductLocality.commutator (targetCurrent x.D x.hu x.i)
        (qField x.gamma (x.r + j) x.K (targetSlice x.D x.hu x.a x.gamma)
          (targetSlice x.D x.hu x.b x.delta))) = 0

def lastLocality (x : Input) : Prop :=
  ∀ j ∈ Finset.range (vectorFrequencyBound x.D x.b + 1),
    (FieldNormalProductLocality.deltaEnd ^ x.H₃ j)
      (FieldNormalProductLocality.commutator (targetSlice x.D x.hu x.a x.gamma)
        (targetSlice x.D x.hu (neutralMode x.D x.i j x.b) (x.delta + 1))) = 0

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ _ x =>
  x.phi (((qField (x.gamma + 1) x.r x.H₁
    (targetSlice x.D x.hu (neutralMode x.D x.i x.d x.a) (x.gamma + 1))
    (targetSlice x.D x.hu x.b x.delta))[[x.n]]) x.x)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input),
    coefficients x → firstLocality x → middleLocality x → lastLocality x →
    let L := vectorFrequencyBound x.D x.a + 1
    let M := vectorFrequencyBound x.D x.b + 1
    let degree : ℤ := L + M + x.K - x.d - x.r - 2
    R.readout () () x = ∑ u ∈ Finset.range (degree + 1).toNat,
      collisionTaylor x.P x.gamma u (degree - u).toNat *
        fusedResidueWeight ((u : ℤ) - M) (x.d - L)

set_option maxHeartbeats 1600000 in
-- Retain every original parameter and the unused independent locality families.
theorem source_bridge : (type_of% (@fused_weighted_identity)) ↔ arena.Law actual := by
  constructor
  · intro h _ x hP h₁ h₂ h₃
    exact h x.D x.hu x.i x.a x.b x.K x.gamma x.delta x.d x.r
      x.n x.x x.phi x.P hP x.H₁ x.H₂ x.H₃ h₁ h₂ h₃
  · intro h D hu i a b K gamma delta d r
    dsimp only
    intro n x phi P hP H₁ H₂ H₃ h₁ h₂ h₃
    exact h () ⟨D, hu, i, a, b, K, gamma, delta, d, r, n, x, phi, P, H₁, H₂, H₃⟩
      hP h₁ h₂ h₃

theorem actual_law : arena.Law actual := source_bridge.mp (@fused_weighted_identity)

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
