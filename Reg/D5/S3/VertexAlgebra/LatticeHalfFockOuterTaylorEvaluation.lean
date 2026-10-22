import D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
open _root_.D5.S3.VertexAlgebra
open LatticeHalfFockOuterTaylorEvaluation LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionLaurentKernels.LaurentCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator RatFunc
noncomputable section

namespace FiniteSignedOuterConvolution

structure Input where
  d : ℤ
  k : ℤ
  t : ℕ
  F : ℕ → ℂ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def observed (x : Input) : ℂ :=
  let d := x.d;
  let k := x.k;
  let t := x.t;
  let F := x.F;
    (∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
      ∑ u ∈ Finset.range (t - j + 1),
        F u * BinomialKernelDelta.chooseSign k (t - j - u))

def actual : Realization signature := realize signature (fun _ _ x =>
  let d := x.d;
  let k := x.k;
  let t := x.t;
  let F := x.F;
    ∑ u ∈ Finset.range (t + 1),
      F u * BinomialKernelDelta.chooseSign (d + k) (t - u)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@finite_signed_outer_convolution)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.d x.k x.t x.F
  · intro h d k t F
    exact h () ⟨d, k, t, F⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@finite_signed_outer_convolution)

end FiniteSignedOuterConvolution

namespace CurrentSourceLocalMonomial

structure Input where
  D : LatticeData
  a : Carrier D
  b : Carrier D
  K : ℕ
  e : Exponent 3
  c : ℂ
  w : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => RatFunc (LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)))

def observed (x : Input) : RatFunc (LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)) :=
  let D := x.D;
  let a := x.a;
  let b := x.b;
  let K := x.K;
  let e := x.e;
  let c := x.c;
  let w := x.w;
    let E := LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)
    let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨1, by decide⟩
    let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨2, by decide⟩
    let C : E := algebraMap _ E
      (AddMonoidAlgebra.single
        (fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) => e j.val) c);
    OrderedCollisionCoordinates.LocalResidueCurrying.localRational ℂ (0 : Fin 3)
      ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e c) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))

def actual : Realization signature := realize signature (fun _ _ x =>
  let D := x.D;
  let a := x.a;
  let b := x.b;
  let K := x.K;
  let e := x.e;
  let c := x.c;
  let w := x.w;
    let E := LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)
    let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨1, by decide⟩
    let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨2, by decide⟩
    let C : E := algebraMap _ E
      (AddMonoidAlgebra.single
        (fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) => e j.val) c);
      RatFunc.C (C * (v - z) ^ (-(K : ℤ))) *
        (RatFunc.X + RatFunc.C v) ^ e 0 *
        RatFunc.X ^ (w - (vectorFrequencyBound D a + 1 : ℕ)) *
        (RatFunc.X + RatFunc.C (v - z)) ^ (-((vectorFrequencyBound D b + 1 : ℕ) : ℤ))) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@current_source_local_monomial)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.D x.a x.b x.K x.e x.c x.w
  · intro h D a b K e c w
    exact h () ⟨D, a, b, K, e, c, w⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@current_source_local_monomial)

end CurrentSourceLocalMonomial

namespace CurrentSourceMonomialResidue

structure Input where
  D : LatticeData
  a : Carrier D
  b : Carrier D
  K : ℕ
  e : Exponent 3
  c : ℂ
  w : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3))

def observed (x : Input) : LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3) :=
  let D := x.D;
  let a := x.a;
  let b := x.b;
  let K := x.K;
  let e := x.e;
  let c := x.c;
  let w := x.w;
    OrderedCollisionCoordinates.LocalResidueCurrying.localResidue ℂ (0 : Fin 3)
      ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e c) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))

def actual : Realization signature := realize signature (fun _ _ x =>
  let D := x.D;
  let a := x.a;
  let b := x.b;
  let K := x.K;
  let e := x.e;
  let c := x.c;
  let w := x.w;
      currentSourceMonomialValue D a b K e c w) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@current_source_monomial_residue)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.D x.a x.b x.K x.e x.c x.w
  · intro h D a b K e c w
    exact h () ⟨D, a, b, K, e, c, w⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@current_source_monomial_residue)

end CurrentSourceMonomialResidue

namespace CurrentSourceLaurentResidue

structure Input where
  D : LatticeData
  a : Carrier D
  b : Carrier D
  K : ℕ
  P : LabelledPolynomial ℂ 3
  w : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3))

def observed (x : Input) : LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3) :=
  let D := x.D;
  let a := x.a;
  let b := x.b;
  let K := x.K;
  let P := x.P;
  let w := x.w;
    OrderedCollisionCoordinates.LocalResidueCurrying.localResidue ℂ (0 : Fin 3)
      ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) P /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))

def actual : Realization signature := realize signature (fun _ _ x =>
  let D := x.D;
  let a := x.a;
  let b := x.b;
  let K := x.K;
  let P := x.P;
  let w := x.w;
      ∑ e ∈ P.coeff.support, currentSourceMonomialValue D a b K e (P.coeff e) w) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@current_source_laurent_residue)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.D x.a x.b x.K x.P x.w
  · intro h D a b K P w
    exact h () ⟨D, a, b, K, P, w⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@current_source_laurent_residue)

end CurrentSourceLaurentResidue

namespace FiniteForwardOuterTaylor

structure Input where
  P : LabelledPolynomial ℂ 3
  gamma : ℤ
  d : ℤ
  degree : ℤ
  L : ℕ
  t : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def observed (x : Input) : ℂ :=
  let P := x.P;
  let gamma := x.gamma;
  let d := x.d;
  let degree := x.degree;
  let L := x.L;
  let t := x.t;
    (∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
      ∑ v ∈ Finset.range (t - j + 1),
        (if (v : ℤ) ≤ degree then collisionTaylor P gamma (degree - v).toNat v else 0) *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - j - v))

def actual : Realization signature := realize signature (fun _ _ x =>
  let P := x.P;
  let gamma := x.gamma;
  let d := x.d;
  let degree := x.degree;
  let L := x.L;
  let t := x.t;
      ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - L) (degree - u - t - 1)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@finite_forward_outer_taylor)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.P x.gamma x.d x.degree x.L x.t
  · intro h P gamma d degree L t
    exact h () ⟨P, gamma, d, degree, L, t⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@finite_forward_outer_taylor)

end FiniteForwardOuterTaylor

namespace FiniteReverseOuterTaylor

structure Input where
  P : LabelledPolynomial ℂ 3
  gamma : ℤ
  d : ℤ
  degree : ℤ
  L : ℕ
  t : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def observed (x : Input) : ℂ :=
  let P := x.P;
  let gamma := x.gamma;
  let d := x.d;
  let degree := x.degree;
  let L := x.L;
  let t := x.t;
    (∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
      ∑ u ∈ Finset.range (t - j + 1),
        (if (u : ℤ) ≤ degree then collisionTaylor P gamma u (degree - u).toNat else 0) *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - j - u))

def actual : Realization signature := realize signature (fun _ _ x =>
  let P := x.P;
  let gamma := x.gamma;
  let d := x.d;
  let degree := x.degree;
  let L := x.L;
  let t := x.t;
      ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - L) (u - t - 1)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@finite_reverse_outer_taylor)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.P x.gamma x.d x.degree x.L x.t
  · intro h P gamma d degree L t
    exact h () ⟨P, gamma, d, degree, L, t⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@finite_reverse_outer_taylor)

end FiniteReverseOuterTaylor

namespace FiniteAssociatedContraction

structure Input where
  M : ℤ
  N : ℕ
  t : ℕ
  F : ℕ → ℂ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def observed (x : Input) : ℂ :=
  let M := x.M;
  let N := x.N;
  let t := x.t;
  let F := x.F;
    (∑ u ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range (N - u + 1),
        if u ≤ t then ((u + j).choose u : ℂ) * F (u + j) *
          ((Ring.choose M (t - u) : ℤ) : ℂ) else 0)

def actual : Realization signature := realize signature (fun _ _ x =>
  let M := x.M;
  let N := x.N;
  let t := x.t;
  let F := x.F;
      ∑ w ∈ Finset.range (N + 1), F w *
        ((Ring.choose ((w : ℤ) + M) t : ℤ) : ℂ)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@finite_associated_contraction)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.M x.N x.t x.F
  · intro h M N t F
    exact h () ⟨M, N, t, F⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@finite_associated_contraction)

end FiniteAssociatedContraction

namespace FiniteLeftOuterTaylor

structure Input where
  P : LabelledPolynomial ℂ 3
  gamma : ℤ
  degree : ℤ
  M : ℕ
  t : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Input) (fun _ => ℂ)

def observed (x : Input) : ℂ :=
  let P := x.P;
  let gamma := x.gamma;
  let degree := x.degree;
  let M := x.M;
  let t := x.t;
    (∑ u ∈ Finset.range (t + 1),
      (if (u : ℤ) ≤ degree then associatedTaylor P gamma u (degree - u).toNat else 0) *
        ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ))

def actual : Realization signature := realize signature (fun _ _ x =>
  let P := x.P;
  let gamma := x.gamma;
  let degree := x.degree;
  let M := x.M;
  let t := x.t;
      ∑ w ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma w (degree - w).toNat *
          fusedResidueWeight ((w : ℤ) - M) (-(t : ℤ) - 1)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (_ : Unit) (x : Input), observed x = R.readout () () x

theorem source_bridge : (type_of% (@finite_left_outer_taylor)) ↔ arena.Law actual := by
  constructor
  · intro h _ x
    exact h x.P x.gamma x.degree x.M x.t
  · intro h P gamma degree M t
    exact h () ⟨P, gamma, degree, M, t⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@finite_left_outer_taylor)

end FiniteLeftOuterTaylor

universe u
namespace LocalLaurentPairResidue
structure Parameters where
  scalar : Type u
  field : Field scalar
structure Input (E : Type u) [Field E] where
  a : E
  b : E
  c : E
  ha : a ≠ 0
  hb : b ≠ 0
  p : ℤ
  q : ℤ
  k : ℤ

def signature : Signature where
  Params := Parameters.{u}
  State p := @Input p.scalar p.field
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.scalar
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (p : Parameters.{u}) (x : @Input p.scalar p.field) : p.scalar :=
  letI := p.field;
  let E := p.scalar;
  let a := x.a;
  let b := x.b;
  let c := x.c;
  let p := x.p;
  let q := x.q;
  let k := x.k;
    ((HahnSeries.single k c : LaurentSeries E) *
      ((HahnSeries.single 1 1 + HahnSeries.C a) ^ p *
       (HahnSeries.single 1 1 + HahnSeries.C b) ^ q)).coeff (-1)

def actual : Realization signature.{u} := realize signature.{u} (fun _ p x =>
  letI := p.field;
  let E := p.scalar;
  let a := x.a;
  let b := x.b;
  let c := x.c;
  let p := x.p;
  let q := x.q;
  let k := x.k;
      if k < 0 then
        c * (a ^ p * b ^ q) *
          ∑ u ∈ Finset.range ((-k - 1).toNat + 1),
            a⁻¹ ^ u * ((Ring.choose p u : ℤ) : E) *
              (b⁻¹ ^ ((-k - 1).toNat - u) *
                ((Ring.choose q ((-k - 1).toNat - u) : ℤ) : E))
      else (0 : E)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (x : @Input p.scalar p.field),
    observed p x = R.readout () p x

theorem source_bridge :
    (type_of% (@local_laurent_pair_residue.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p x
    letI := p.field
    exact h x.a x.b x.c x.ha x.hb x.p x.q x.k
  · intro h E field a b c ha hb p q k
    exact h ⟨E, field⟩ ⟨a, b, c, ha, hb, p, q, k⟩

theorem actual_law : arena.{u}.Law actual :=
  source_bridge.mp (@local_laurent_pair_residue.{u})
end LocalLaurentPairResidue
end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
