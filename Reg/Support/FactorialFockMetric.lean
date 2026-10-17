/- Typed family witnesses for the canonical factorial polynomial metric.
Reuses DependentFamily.realize and its existing Reg.Support.DependentFamily enrollment.
The original theorem telescope, source bridge, positive law, whole-family variation,
sensitivity and observational dependence are preserved. Continuation is unknown.
Native elaboration and current assessment are distinct, externally recorded checks.
-/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.FactorialFockMetric
import Reg.Support.DependentFamily
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit
open scoped BigOperators InnerProductSpace lp Classical
open ComplexConjugate

noncomputable section
universe u
namespace Reg.D5.S3.VertexAlgebra.FactorialFockMetric

abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def natEqual : Realization natSignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def natLess : Realization natSignature :=
  realize _ (fun _ _ x y => x < y) (fun e => nomatch e)
def natFalse : Realization natSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

theorem natEqualDependence : ObservationalDependence natSignature natEqual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

theorem natLessDependence : ObservationalDependence natSignature natLess := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) < 1 := Eq.mp (congrFun he 1) Nat.zero_lt_one
  exact Nat.lt_irrefl 1 h

abbrev complexSignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def complexEqual : Realization complexSignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def complexFalse : Realization complexSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
def complexNotEqual : Realization complexSignature :=
  realize _ (fun _ _ x y => x ≠ y) (fun e => nomatch e)

theorem complexEqualDependence : ObservationalDependence complexSignature complexEqual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

theorem complexNotEqualDependence :
    ObservationalDependence complexSignature complexNotEqual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (0 : ℂ) ≠ 0 := Eq.mpr (congrFun he 0) one_ne_zero
  exact h rfl

abbrev polynomialSignature : Signature where
  Params := Type u
  State σ := Polynomial σ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ σ := Polynomial σ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def polynomialEqual : Realization polynomialSignature.{u} :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def polynomialFalse : Realization polynomialSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

theorem polynomialEqualDependence :
    ObservationalDependence polynomialSignature.{u} polynomialEqual := by
  intro i
  refine ⟨ULift.{u} Empty, 0, 1, ?_⟩
  intro he
  have h : (1 : Polynomial (ULift.{u} Empty)) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

abbrev hilbertSignature : Signature where
  Params := Type u
  State σ := Hilbert σ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ σ := Hilbert σ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def hilbertEqual : Realization hilbertSignature.{u} :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def hilbertFalse : Realization hilbertSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

theorem hilbertEqualDependence :
    ObservationalDependence hilbertSignature.{u} hilbertEqual := by
  intro i
  refine ⟨ULift.{u} Empty, 0, lp.single 2 0 (1 : ℂ), ?_⟩
  intro he
  have h : (lp.single 2 (0 : Occupation (ULift.{u} Empty)) (1 : ℂ) :
      Hilbert (ULift.{u} Empty)) = 0 := Eq.mp (congrFun he 0) rfl
  have hc := congrArg (fun f : Hilbert (ULift.{u} Empty) => f 0) h
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using hc)

abbrev mapSignature : Signature where
  Params := Type u
  State σ := Polynomial σ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ σ := Hilbert σ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientMap : Realization mapSignature.{u} :=
  realize _ (fun _ σ p => coefficientEmbedding σ p) (fun e => nomatch e)
def factorialMap : Realization mapSignature.{u} :=
  realize _ (fun _ σ p => embedding σ p) (fun e => nomatch e)
def zeroMap : Realization mapSignature.{u} :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

theorem coefficientMapDependence : ObservationalDependence mapSignature.{u} coefficientMap := by
  intro i
  refine ⟨ULift.{u} Empty, 0, 1, ?_⟩
  intro he
  exact zero_ne_one (coefficientEmbedding_injective he)

theorem factorialMapDependence : ObservationalDependence mapSignature.{u} factorialMap := by
  intro i
  refine ⟨ULift.{u} Empty, 0, 1, ?_⟩
  intro he
  exact zero_ne_one (embedding_injective he)

namespace WeightPos
abbrev signature := natSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ),
    r.readout () () 0 (weight d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_pos.{u})) ↔
    arena.{u}.Law natLess := Iff.rfl
private theorem actualLaw : arena.{u}.Law natLess :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_pos.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law natFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_pos.{u})) where
  actual := natLess
  bridge := sourceBridge
  variation := ⟨actualLaw, natFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natLessDependence

end WeightPos

namespace WeightEqProd
abbrev signature := natSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ) (s : Finset σ)
      (hs : d.support ⊆ s),
    r.readout () () (weight d) (∏ x ∈ s, (d x).factorial)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_eq_prod.{u})) ↔
    arena.{u}.Law natEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law natEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_eq_prod.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law natFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 ∅ (by simp)

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_eq_prod.{u})) where
  actual := natEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, natFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natEqualDependence

end WeightEqProd

namespace WeightAddSingle
abbrev signature := natSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ) (i : σ),
    r.readout () () (weight (d + Finsupp.single i 1)) ((d i + 1) * weight d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_add_single.{u})) ↔
    arena.{u}.Law natEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law natEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_add_single.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law natFalse := by
  intro h
  exact @h PUnit.{u+1} 0 PUnit.unit

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.weight_add_single.{u})) where
  actual := natEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, natFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natEqualDependence

end WeightAddSingle

namespace ScaleNeZero
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ),
    r.readout () () (scale d) 0

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.scale_ne_zero.{u})) ↔
    arena.{u}.Law complexNotEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexNotEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.scale_ne_zero.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.scale_ne_zero.{u})) where
  actual := complexNotEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexNotEqualDependence

end ScaleNeZero

namespace ConjScale
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ),
    r.readout () () (conj (scale d)) (scale d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.conj_scale.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.conj_scale.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.conj_scale.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end ConjScale

namespace ScaleMulSelf
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ),
    r.readout () () (scale d * scale d) (weight d : ℂ)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.scale_mul_self.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.scale_mul_self.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.scale_mul_self.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end ScaleMulSelf

namespace DiagonalBasis
abbrev signature := polynomialSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ),
    r.readout () σ (diagonal σ (MvPolynomial.monomial d 1))
      (scale d • MvPolynomial.monomial d 1)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_basis.{u})) ↔
    arena.{u}.Law polynomialEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law polynomialEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_basis.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law polynomialFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_basis.{u})) where
  actual := polynomialEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, polynomialFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨polynomialFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := polynomialEqualDependence

end DiagonalBasis

namespace DiagonalMonomial
abbrev signature := polynomialSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ) (a : ℂ),
    r.readout () σ (diagonal σ (MvPolynomial.monomial d a))
      (MvPolynomial.monomial d (scale d * a))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_monomial.{u})) ↔
    arena.{u}.Law polynomialEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law polynomialEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_monomial.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law polynomialFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_monomial.{u})) where
  actual := polynomialEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, polynomialFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨polynomialFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := polynomialEqualDependence

end DiagonalMonomial

namespace DiagonalCoeff
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (p : Polynomial σ) (d : Occupation σ),
    r.readout () () ((diagonal σ p).coeff d)
      (scale d * p.coeff d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_coeff.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_coeff.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.diagonal_coeff.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end DiagonalCoeff

namespace CoefficientEmbeddingBasis
abbrev signature := hilbertSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ),
    r.readout () σ (coefficientEmbedding σ ((MvPolynomial.basisMonomials σ ℂ) d))
      (hilbertBasis σ d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_basis.{u})) ↔
    arena.{u}.Law hilbertEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law hilbertEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_basis.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law hilbertFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_basis.{u})) where
  actual := hilbertEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, hilbertFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hilbertFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := hilbertEqualDependence

end CoefficientEmbeddingBasis

namespace CoefficientEmbeddingInjective
abbrev signature := mapSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u}, Function.Injective (r.readout () σ)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_injective.{u})) ↔
    arena.{u}.Law coefficientMap := Iff.rfl
private theorem actualLaw : arena.{u}.Law coefficientMap :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_injective.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law zeroMap := by
  intro h
  exact zero_ne_one (@h (ULift.{u} Empty) 0 1 rfl)

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_injective.{u})) where
  actual := coefficientMap
  bridge := sourceBridge
  variation := ⟨@actualLaw, zeroMap, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroMap, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := coefficientMapDependence

end CoefficientEmbeddingInjective

namespace CoefficientEmbeddingMonomial
abbrev signature := hilbertSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ) (a : ℂ),
    r.readout () σ (coefficientEmbedding σ (MvPolynomial.monomial d a))
      (a • hilbertBasis σ d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_monomial.{u})) ↔
    arena.{u}.Law hilbertEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law hilbertEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_monomial.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law hilbertFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_monomial.{u})) where
  actual := hilbertEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, hilbertFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hilbertFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := hilbertEqualDependence

end CoefficientEmbeddingMonomial

namespace CoefficientEmbeddingCoeff
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (p : Polynomial σ) (d : Occupation σ),
    r.readout () () (coefficientEmbedding σ p d) (p.coeff d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_coeff.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_coeff.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.coefficientEmbedding_coeff.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end CoefficientEmbeddingCoeff

namespace EmbeddingInjective
abbrev signature := mapSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u}, Function.Injective (r.readout () σ)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_injective.{u})) ↔
    arena.{u}.Law factorialMap := Iff.rfl
private theorem actualLaw : arena.{u}.Law factorialMap :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_injective.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law zeroMap := by
  intro h
  exact zero_ne_one (@h (ULift.{u} Empty) 0 1 rfl)

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_injective.{u})) where
  actual := factorialMap
  bridge := sourceBridge
  variation := ⟨@actualLaw, zeroMap, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroMap, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := factorialMapDependence

end EmbeddingInjective

namespace EmbeddingCoeff
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (p : Polynomial σ) (d : Occupation σ),
    r.readout () () (embedding σ p d) (scale d * p.coeff d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_coeff.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_coeff.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_coeff.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end EmbeddingCoeff

namespace EmbeddingMonomial
abbrev signature := hilbertSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ) (a : ℂ),
    r.readout () σ (embedding σ (MvPolynomial.monomial d a))
      ((scale d * a) • hilbertBasis σ d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_monomial.{u})) ↔
    arena.{u}.Law hilbertEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law hilbertEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_monomial.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law hilbertFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.embedding_monomial.{u})) where
  actual := hilbertEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, hilbertFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hilbertFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := hilbertEqualDependence

end EmbeddingMonomial

namespace InnerAddFirst
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (p q s : Polynomial σ),
    r.readout () () (inner (p + q) s) (inner p s + inner q s)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.inner_add_first.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.inner_add_first.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.inner_add_first.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end InnerAddFirst

namespace InnerMonomialLeft
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (d : Occupation σ) (a : ℂ) (q : Polynomial σ),
    r.readout () () (inner (MvPolynomial.monomial d a) q)
      ((weight d : ℂ) * conj a * q.coeff d)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.inner_monomial_left.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.inner_monomial_left.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Empty) 0 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.inner_monomial_left.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end InnerMonomialLeft

namespace MulXPderivPairing
abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {σ : Type u} (i : σ) (p q : Polynomial σ),
    r.readout () () (inner (MvPolynomial.X i * p) q) (inner p (MvPolynomial.pderiv i q))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.mul_X_pderiv_pairing.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl
private theorem actualLaw : arena.{u}.Law complexEqual :=
  (@D5.S3.VertexAlgebra.FactorialFockMetric.mul_X_pderiv_pairing.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h PUnit.{u+1} PUnit.unit 0 0

def family : Registration arena.{u}
    (type_of% (@D5.S3.VertexAlgebra.FactorialFockMetric.mul_X_pderiv_pairing.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

end MulXPderivPairing

end Reg.D5.S3.VertexAlgebra.FactorialFockMetric
