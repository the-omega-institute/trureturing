import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
import Reg.Support.OddPrimeJetAudit
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Constructions

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
open Reg.Support.OddPrimeJetAudit

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
universe uK
noncomputable section
open Polynomial Finset Module
open scoped BigOperators MonoidAlgebra

namespace derivative_pow_prime
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature End.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    (derivativeEnd (p := p) (K := K)) ^ p = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (0))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedEnd := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK})
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_pow_prime
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK})
  have ht := ha.symm.trans hb
  have hz := congrArg (fun A : Reg.Support.OddPrimeJetAudit.End Reg.Support.OddPrimeJetAudit.testData => A (vectorOne Reg.Support.OddPrimeJetAudit.testData)) (add_left_cancel (ht.symm.trans (add_zero _).symm))
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData hz

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_pow_prime.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual End
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_pow_prime.{uK}, rejectedEnd, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceEnd

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_pow_prime.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature End.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_pow_prime.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_pow_prime.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature End)
    (Reg.Support.OddPrimeJetAudit.actual End).readout
    (Reg.Support.OddPrimeJetAudit.actual End).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end derivative_pow_prime

namespace constant_derivative
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (c : K),
    (derivativeEnd (p := p) (K := K)) (constantLinear c) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (0))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_derivative
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_derivative.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_derivative.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_derivative.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_derivative.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end constant_derivative

namespace polynomial_log_action
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (q : K →ₗ[(ZMod p)] K) (x : K) (v : (Polynomial.degreeLT K p)),
    -(∑ i : (ZMod p), i^(p-2) • originalRepresentation (p := p) q
      (Multiplicative.ofAdd (i • x)) v) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (jetOperator q x v))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.polynomial_log_action
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.polynomial_log_action.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.polynomial_log_action.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.polynomial_log_action.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.polynomial_log_action.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.polynomial_log_action.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end polynomial_log_action

namespace log_intertwining
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (q : K →ₗ[(ZMod p)] K) (φ : (Multiplicative K) ≃* (Multiplicative K)) (P : (Polynomial.degreeLT K p) ≃ₗ[(ZMod p)] (Polynomial.degreeLT K p))
    (hP : ∀ (g : (Multiplicative K)) (v : (Polynomial.degreeLT K p)), P (originalRepresentation (p := p) q g v) =
      ordinaryRepresentation (φ g) (P v)) (x : K) (v : (Polynomial.degreeLT K p)),
    P (jetOperator q x v) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (automorphismLinear (p := p) φ x • (derivativeEnd (p := p) (K := K)) (P v)))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 (MulEquiv.refl _) (LinearEquiv.refl _ _) (by intro g v; rfl) 0 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.log_intertwining
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 (MulEquiv.refl _) (LinearEquiv.refl _ _) (by intro g v; rfl) 0 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.log_intertwining.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.log_intertwining.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.log_intertwining.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.log_intertwining.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.log_intertwining.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end log_intertwining

namespace derivative_kernel
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Poly.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (v : (Polynomial.degreeLT K p)) (hv : (derivativeEnd (p := p) (K := K)) v = 0),
    (v : K[X]) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (C ((v : K[X]).coeff 0)))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedPoly := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 (by simp)
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_kernel
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 (by simp)
  have ht := ha.symm.trans hb
  exact (one_ne_zero : (1 : Polynomial Reg.Support.OddPrimeJetAudit.testK.{uK}) ≠ 0) (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_kernel.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Poly
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_kernel.{uK}, rejectedPoly, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependencePoly

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_kernel.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Poly.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_kernel.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.derivative_kernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Poly)
    (Reg.Support.OddPrimeJetAudit.actual Poly).readout
    (Reg.Support.OddPrimeJetAudit.actual Poly).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end derivative_kernel

namespace dividedMonomial_zero
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (h0 : 0 < p) (s : K),
    dividedMonomial 0 h0 s = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (constantLinear s))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) (by decide) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_zero
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) (by decide) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_zero.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_zero.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_zero.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_zero.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end dividedMonomial_zero

namespace dividedMonomial_succ
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (j : ℕ) (hj : j + 1 < p) (s : K),
    (derivativeEnd (p := p) (K := K)) (dividedMonomial (j+1) hj s) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (dividedMonomial j (by change j < p; omega) s))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 (by decide) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_succ
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 (by decide) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_succ.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_succ.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_succ.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_succ.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_succ.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end dividedMonomial_succ

namespace diagonalScale_derivative
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (c : K) (hc : c ≠ 0) (v : (Polynomial.degreeLT K p)),
    diagonalScale c hc ((derivativeEnd (p := p) (K := K)) v) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (c⁻¹ • (derivativeEnd (p := p) (K := K)) (diagonalScale c hc v)))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 1 one_ne_zero 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.diagonalScale_derivative
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 1 one_ne_zero 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.diagonalScale_derivative.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.diagonalScale_derivative.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.diagonalScale_derivative.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.diagonalScale_derivative.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.diagonalScale_derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end diagonalScale_derivative

namespace constant_image
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (P : (Polynomial.degreeLT K p) ≃ₗ[(ZMod p)] (Polynomial.degreeLT K p))
    (hD : ∀ v : (Polynomial.degreeLT K p), P ((derivativeEnd (p := p) (K := K)) v) = (derivativeEnd (p := p) (K := K)) (P v)) (s : K),
    P (constantLinear s) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (constantLinear (coefficientZero (P (constantLinear s)))))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) (LinearEquiv.refl _ _) (by intro v; rfl) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_image
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) (LinearEquiv.refl _ _) (by intro v; rfl) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_image.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_image.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_image.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_image.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.constant_image.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end constant_image

namespace dividedMonomial_top
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (s : K),
    ((derivativeEnd (p := p) (K := K))^(p-1)) (dividedMonomial (p-1) (by have : 2 < p := Fact.out; omega) s) =
      (f.readout () ⟨p, pp, po, K, kk, ka⟩ (constantLinear s))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_top
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_top.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_top.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_top.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_top.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_top.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end dividedMonomial_top

namespace dividedMonomial_one_top
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (s : K),
    ((derivativeEnd (p := p) (K := K))^(p-1)) (dividedMonomial 1 (by have : 2 < p := Fact.out; omega) s) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (0))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_one_top
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_one_top.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_one_top.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_one_top.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_one_top.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.dividedMonomial_one_top.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Vector)
    (Reg.Support.OddPrimeJetAudit.actual Vector).readout
    (Reg.Support.OddPrimeJetAudit.actual Vector).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end dividedMonomial_one_top

namespace structural_commutator
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Scalar.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (P : (Polynomial.degreeLT K p) ≃ₗ[(ZMod p)] (Polynomial.degreeLT K p))
    (hD : ∀ v : (Polynomial.degreeLT K p), P ((derivativeEnd (p := p) (K := K)) v) = (derivativeEnd (p := p) (K := K)) (P v)) (a b e : K)
    (hL : ∀ v : (Polynomial.degreeLT K p), P (a • (derivativeEnd (p := p) (K := K)) v + b • ((derivativeEnd (p := p) (K := K))^(p-1)) v) = e • (derivativeEnd (p := p) (K := K)) (P v)),
    ∀ s : K, a * constantCommutator P hD s - constantCommutator P hD (a*s) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (b*s))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedScalar := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) (LinearEquiv.refl _ _) (by intro v; rfl) 0 0 0 (by intro v; simp) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.structural_commutator
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) (LinearEquiv.refl _ _) (by intro v; rfl) 0 0 0 (by intro v; simp) 0
  have ht := ha.symm.trans hb
  exact (one_ne_zero : (1 : Reg.Support.OddPrimeJetAudit.testK.{uK}) ≠ 0) (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.structural_commutator.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Scalar
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.structural_commutator.{uK}, rejectedScalar, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceScalar

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.structural_commutator.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Scalar.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.structural_commutator.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.structural_commutator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.OddPrimeJetAudit.signature Scalar)
    (Reg.Support.OddPrimeJetAudit.actual Scalar).readout
    (Reg.Support.OddPrimeJetAudit.actual Scalar).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end structural_commutator

namespace full_family
private def fieldFintype {p : ℕ} [Fact p.Prime] {K : Type uK}
    [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K] : Fintype K := by
  have : Finite K := Module.finite_of_finite (ZMod p)
  exact Fintype.ofFinite K

private def restrictedRepresentation {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {K : Type uK} [Field K] [Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (H : Subgroup (Multiplicative K)) :
    Representation (ZMod p) H (Polynomial.degreeLT K p) :=
  (originalRepresentation q).comp H.subtype

abbrev signature : Signature where
  Params := Reg.Support.OddPrimeJetAudit.Data.{uK}
  State d := d.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := letI := d.field; Polynomial d.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ d c => letI := d.field; C c) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature
    (fun _ d _ => letI := d.field; (0 : Polynomial d.K)) (fun e => nomatch e)

/-- All eight clauses, including their finite-dimensional premises, are retained verbatim. -/
abbrev arena : Arena where
  signature := signature.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] (q : K →ₗ[(ZMod p)] K) (hq1 : q 1 = 0) (hr : 2 ≤ finrank (ZMod p) K),
    Function.Injective (originalRepresentation (p := p) q) ∧
    (∀ H : Subgroup (Multiplicative K), IsCyclic H →
      Module.Projective (ZMod p)[H] (restrictedRepresentation (p := p) q H).asModule) ∧
    (∀ v : (Polynomial.degreeLT K p), (∀ g : (Multiplicative K), originalRepresentation (p := p) q g v = v) ↔
      ∃ c : K, (v : K[X]) = f.readout () ⟨p, pp, po, K, kk, ka⟩ c) ∧
    (letI : Fintype K := fieldFintype (p := p) (K := K)
     (originalRepresentation (p := p) q).norm = 0) ∧
    ¬ Module.Projective (ZMod p)[(Multiplicative K)] (originalRepresentation (p := p) q).asModule ∧
    finrank (ZMod p) (Polynomial.degreeLT K p) = p * finrank (ZMod p) K ∧
    (∀ (x : K) (v : (Polynomial.degreeLT K p)),
      (ordinaryRepresentation (p := p) (Multiplicative.ofAdd x) v : K[X]) =
        (v : K[X]).comp (X + C x)) ∧
    ((∃ a : K, Algebra.trace (ZMod p) K (q a) ≠ 0) →
      ∀ (φ : (Multiplicative K) ≃* (Multiplicative K)) (P : (Polynomial.degreeLT K p) ≃ₗ[(ZMod p)] (Polynomial.degreeLT K p)),
        ¬ ∀ (g : (Multiplicative K)) (v : (Polynomial.degreeLT K p)), P (originalRepresentation (p := p) q g v) =
          ordinaryRepresentation (p := p) (φ g) (P v))

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  let K := ULift.{uK} (GaloisField 3 2)
  have hr : 2 ≤ finrank (ZMod 3) K := by
    rw [finrank_ulift, GaloisField.finrank 3 (by decide : 2 ≠ 0)]
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.full_family
    (p := 3) (K := K) 0 rfl hr
  have hb := hbad (p := 3) (K := K) 0 rfl hr
  let v := constantLinear (p := 3) (K := K) 1
  have hv := (ha.2.2.1 v).mpr ⟨1, rfl⟩
  obtain ⟨c, hc⟩ := (hb.2.2.1 v).mp hv
  have hz := congrArg (fun f : K[X] => f.coeff 0) hc
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa [rejected, realize, v, constantLinear] using hz)

def family : Registration arena.{uK}
    (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.full_family.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.full_family.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
    intro i
    refine ⟨Reg.Support.OddPrimeJetAudit.testData, 0, 1, ?_⟩
    simp [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.full_family.{uK})
    (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.full_family.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.full_family.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "arg", "arg", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end full_family

namespace pow_constant
universe u

abbrev signature : Signature where
  Params := Reg.Support.OddPrimeJetAudit.Data.{u} × ℕ
  State z := Reg.Support.OddPrimeJetAudit.Vector z.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ z := Reg.Support.OddPrimeJetAudit.Vector z.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ z v =>
  let d := z.1
  letI := d.prime; letI := d.odd; letI := d.field; letI := d.algebra
  ((derivativeEnd (p := d.p) (K := d.K))^z.2) v) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature (fun i z v =>
  letI := z.1.field
  actual.readout i z v + Reg.Support.OddPrimeJetAudit.vectorOne z.1)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [kk : Field K] [ka : Algebra (ZMod p) K]
    (j : ℕ) (hj : 0 < j) (c : K),
    r.readout () (⟨p,pp,po,K,kk,ka⟩,j) (constantLinear c) = 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hbad
  let d := Reg.Support.OddPrimeJetAudit.testData.{u}
  letI := d.prime; letI := d.odd; letI := d.field; letI := d.algebra
  have h := hbad (p := d.p) (K := d.K) 1 (by decide) 0
  exact Reg.Support.OddPrimeJetAudit.vectorOne_ne_zero d
    (by simpa [rejected, actual, realize] using h)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let d := Reg.Support.OddPrimeJetAudit.testData.{u}
  letI := d.prime; letI := d.odd; letI := d.field; letI := d.algebra
  let v := dividedMonomial (p := d.p) (K := d.K) 1 (by decide) 1
  have hd : derivativeEnd (p := d.p) (K := d.K) v =
      Reg.Support.OddPrimeJetAudit.vectorOne d := by
    simpa [v, Reg.Support.OddPrimeJetAudit.vectorOne, dividedMonomial_zero] using
      (dividedMonomial_succ (p := d.p) (K := d.K) 0 (by decide) 1)
  refine ⟨(d,1), v, 0, ?_⟩
  simpa only [actual, realize, pow_one, hd, map_zero] using
    Reg.Support.OddPrimeJetAudit.vectorOne_ne_zero d

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.pow_constant.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.pow_constant.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.pow_constant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.pow_constant.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation.pow_constant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
    definition := none
    coordinates := #[0,1,2,3,4,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end pow_constant

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
