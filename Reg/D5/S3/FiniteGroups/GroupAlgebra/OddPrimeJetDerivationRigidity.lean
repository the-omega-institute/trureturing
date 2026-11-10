import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
import Reg.Support.UniverseSingleReadout
import Reg.Support.OddPrimeJetAudit
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
universe uK
noncomputable section

structure Data where
  p : ℕ
  prime : Fact p.Prime
  odd : Fact (2 < p)
  K : Type uK
  field : Field K
  algebra : letI := prime; letI := field; Algebra (ZMod p) K

abbrev signature : Signature where
  Params := Data.{uK}
  State d := letI := d.prime; letI := d.field; letI := d.algebra; d.K →ₗ[ZMod d.p] d.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := letI := d.prime; letI := d.field; letI := d.algebra; d.K →ₗ[ZMod d.p] d.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ _ q => q) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature (fun _ d _ => by
    letI := d.prime
    letI := d.field
    letI := d.algebra
    exact LinearMap.id) (fun e => nomatch e)

/-- All original hypotheses and the arbitrary original-group automorphism remain in the law. -/
abbrev arena : Arena where
  signature := signature.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (hq1 : q 1 = 0),
    (∃ (φ : Multiplicative K ≃* Multiplicative K)
      (P : Polynomial.degreeLT K p ≃ₗ[ZMod p] Polynomial.degreeLT K p),
      ∀ (g : Multiplicative K) (v : Polynomial.degreeLT K p),
      P (originalRepresentation (p := p) q g v) = ordinaryRepresentation (φ g) (P v)) ↔
    ∃ δ : Derivation (ZMod p) K K,
      δ.toLinearMap = f.readout () ⟨p, pp, po, K, kk, ka⟩ q

private instance testPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev testK := ULift.{uK} (ZMod 3)
private abbrev testData : Data.{uK} where
  p := 3
  prime := ⟨by decide⟩
  odd := ⟨by decide⟩
  K := testK.{uK}
  field := inferInstance
  algebra := inferInstance

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hi := (intertwining_iff_derivation (p := 3) (K := testK.{uK}) 0 rfl).mpr ⟨0, rfl⟩
  obtain ⟨δ, hδ⟩ := (hbad (p := 3) (K := testK.{uK}) 0 rfl).mp hi
  have hz := congrArg (fun q : testK.{uK} →ₗ[ZMod 3] testK.{uK} => q 1) hδ
  have hzero : (0 : testK.{uK}) = 1 := by
    simpa [rejected, realize] using hz
  exact zero_ne_one hzero

def family : Registration arena.{uK} (type_of% (@intertwining_iff_derivation.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intertwining_iff_derivation.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    letI := testData.{uK}.prime
    letI := testData.{uK}.field
    letI := testData.{uK}.algebra
    intro i
    refine ⟨testData.{uK}, 0, LinearMap.id, ?_⟩
    intro h
    have hz := congrArg (fun q : testK.{uK} →ₗ[ZMod 3] testK.{uK} => q 1) h
    exact (zero_ne_one : (0 : testK.{uK}) ≠ 1) (by simpa only [actual, realize, LinearMap.zero_apply, LinearMap.id_apply] using hz)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@intertwining_iff_derivation.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.intertwining_iff_derivation.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open Reg.Support.OddPrimeJetAudit
open Polynomial Finset Module
open scoped BigOperators

namespace leibniz_of_commutator
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Scalar.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (q Q : K →ₗ[(ZMod p)] K)
    (h : ∀ a s : K, a * Q s - Q (a*s) = q a * s) (a b : K),
    q (a*b) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (a * q b + b * q a))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedScalar := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 (by intro a s; simp) 0 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.leibniz_of_commutator
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 (by intro a s; simp) 0 0
  have ht := ha.symm.trans hb
  exact (one_ne_zero : (1 : Reg.Support.OddPrimeJetAudit.testK.{uK}) ≠ 0) (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.leibniz_of_commutator.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Scalar
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.leibniz_of_commutator.{uK}, rejectedScalar, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceScalar

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.leibniz_of_commutator.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Scalar.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.leibniz_of_commutator.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.leibniz_of_commutator.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end leibniz_of_commutator

namespace finiteExp_intertwining
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (P : (Polynomial.degreeLT K p) →ₗ[(ZMod p)] (Polynomial.degreeLT K p))
    (A B : Module.End K (Polynomial.degreeLT K p)) (h : ∀ v, P (A v) = B (P v)) (v : (Polynomial.degreeLT K p)),
    P (finiteExp A v) = (f.readout () ⟨p, pp, po, K, kk, ka⟩ (finiteExp B (P v)))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 0 (by intro v; simp) 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.finiteExp_intertwining
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 0 (by intro v; simp) 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.finiteExp_intertwining.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.finiteExp_intertwining.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.finiteExp_intertwining.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.finiteExp_intertwining.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.finiteExp_intertwining.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end finiteExp_intertwining

namespace gauge_pair_operator
abbrev arena : Arena where
  signature := Reg.Support.OddPrimeJetAudit.signature Vector.{uK}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K],
    ∀ (δ : Derivation (ZMod p) K K) (q : K →ₗ[(ZMod p)] K) (a : K) (v : (Polynomial.degreeLT K p)),
    gauge δ (jetOperator q a v) =
      (f.readout () ⟨p, pp, po, K, kk, ka⟩ (jetOperator (q-δ.toLinearMap) a (gauge δ v)))

private theorem rejected_law : ¬ arena.{uK}.Law rejectedVector := by
  intro hbad
  letI := Reg.Support.OddPrimeJetAudit.testData.{uK}.field
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hb := hbad (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 0 0
  have ha := _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.gauge_pair_operator
    (p := 3) (K := Reg.Support.OddPrimeJetAudit.testK.{uK}) 0 0 0 0
  have ht := ha.symm.trans hb
  exact vectorOne_ne_zero Reg.Support.OddPrimeJetAudit.testData (add_left_cancel (ht.symm.trans (add_zero _).symm))

def family : Registration arena.{uK} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.gauge_pair_operator.{uK})) where
  actual := Reg.Support.OddPrimeJetAudit.actual Vector
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.gauge_pair_operator.{uK}, rejectedVector, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependenceVector

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.gauge_pair_operator.{uK}) (Realization (Reg.Support.OddPrimeJetAudit.signature Vector.{uK})) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.gauge_pair_operator.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity.gauge_pair_operator.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end gauge_pair_operator

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
