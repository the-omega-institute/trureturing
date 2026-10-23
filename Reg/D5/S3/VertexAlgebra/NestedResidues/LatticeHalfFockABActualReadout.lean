import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout
import Reg.Support.SingleDependentReadout

/-! The complete dependent source is reconstructed. Four-slot registration
remains unfinished under issue #20163: whole-family intervention, sensitivity,
observational dependence and sourceSelection/escapeFrom evidence are absent.
No declared_validated status is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout
open _root_.D5.S3.VertexAlgebra
open NestedResidues.LatticeHalfFockABActualReadout NestedResidues.LatticeHalfFockABLocalResidue
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockChargedTensorCoefficients LatticeGeneratingFieldLocality
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
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
  I : ℕ
  H : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  j : ℤ
  x : ActualTensor D hu
  phi : ActualTensor D hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ _ x =>
  x.phi (((qField 1 (x.d - x.j) x.H (targetCurrent x.D x.hu x.i)
    (qField x.gamma (x.r + x.j) x.I (targetSlice x.D x.hu x.a x.gamma)
      (targetSlice x.D x.hu x.b x.delta)))[[x.n]]) x.x)) (fun empty => nomatch empty)

def coefficients (x : Input) : Prop :=
  ∀ e : Exponent 3, x.P.coeff e =
    if totalExponent e =
        (∑ p ∈ labelledPairs 3, (threeOrders x.D x.a x.b x.K p : ℤ)) - x.d - x.r - x.n - 3
    then x.phi (actualNumerator x.D x.hu x.i x.a x.b x.gamma x.delta x.K x.x e) else 0

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), coefficients x →
    NestedRightSupported x.gamma (x.r + x.j) (x.d - x.j) x.n x.I x.H
      (rationalTripleReadout x.D x.a x.b x.K x.P) ∧
    R.readout () () x =
      nestedRightLocalReadout 1 1 x.gamma (x.r + x.j) (x.d - x.j) x.n x.I x.H
        (originalRational x.D x.a x.b x.K x.P) ∧
    R.readout () () x =
      supportedQReadout 1 (x.d - x.j) x.H x.n
        (fun k l =>
          (coefficientHahn ℂ 2 0 (1 : Fin 3) (finSuccAboveEquiv 1)
            (completeAB x.gamma (x.r + x.j) x.I
              (originalRational x.D x.a x.b x.K x.P))).coeff
                (exponents 2 ![-k - 1, -l - 1]))
        (fun k l =>
          (coefficientHahn ℂ 1 1 (1 : Fin 3)
            ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1))
            (completeAB x.gamma (x.r + x.j) x.I
              (originalRational x.D x.a x.b x.K x.P))).coeff
                (exponents 2 ![-k - 1, -l - 1]))

set_option maxHeartbeats 1600000 in
-- Reconstruct every original parameter and both directions of the source.
theorem source_bridge :
    (type_of% (@actual_ab_nested_readout)) ↔ arena.Law actual := by
  constructor
  · intro h _ x hP
    exact h x.D x.hu x.i x.a x.b x.K x.I x.H x.gamma x.delta x.d x.r x.n x.j
      x.x x.phi x.P hP
  · intro h D hu i a b K I H gamma delta d r n j x phi P hP
    exact h () ⟨D, hu, i, a, b, K, I, H, gamma, delta, d, r, n, j, x, phi, P⟩ hP

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_ab_nested_readout)

namespace JointOuterSupport

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

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ _ x =>
  ∑ j ∈ Finset.range ((x.K : ℤ) - x.r).toNat, BinomialKernelDelta.chooseSign x.d j *
    x.phi (((qField 1 (x.d - j) (x.H j) (targetCurrent x.D x.hu x.i)
      (qField x.gamma (x.r + j) x.K (targetSlice x.D x.hu x.a x.gamma)
        (targetSlice x.D x.hu x.b x.delta)))[[x.n]]) x.x)) (fun empty => nomatch empty)

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

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), coefficients x → locality x →
    let N := ((x.K : ℤ) - x.r).toNat
    let B := fun j : ℕ => ((x.H j : ℤ) - (x.d - j)).toNat
    let T := N + ∑ j ∈ Finset.range N, B j
    let f := fun (j : ℕ) k l => lastSourceLocalQ 1 true x.gamma (x.r + j) x.K l k
      (originalRational x.D x.a x.b x.K x.P)
    let g := fun (j : ℕ) k l => lastSourceLocalQ 1 false x.gamma (x.r + j) x.K k l
      (originalRational x.D x.a x.b x.K x.P)
    (∀ j ∈ Finset.range N, OuterQCompletion 1 (x.d - j) x.n (x.H j) (f j) (g j)) ∧
    R.readout () () x =
      ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (t + 1),
        if j < N then BinomialKernelDelta.chooseSign x.d j *
          (Ring.choose (-(1 : ℂ) / 2) (t - j) *
            completeOuterResidue (x.d - j) x.n (f j) (g j) (t - j)) else 0

set_option maxHeartbeats 1600000 in
-- Reconstruct the independent family of genuine locality premises exactly.
theorem source_bridge :
    (type_of% (@actual_ab_joint_outer_support)) ↔ arena.Law actual := by
  constructor
  · intro h _ x hP hH
    exact h x.D x.hu x.i x.a x.b x.K x.gamma x.delta x.d x.r x.n x.x x.phi x.P hP x.H hH
  · intro h D hu i a b K gamma delta d r n x phi P hP H hH
    exact h () ⟨D, hu, i, a, b, K, gamma, delta, d, r, n, x, phi, P, H⟩ hP hH

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_ab_joint_outer_support)

end JointOuterSupport

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout
