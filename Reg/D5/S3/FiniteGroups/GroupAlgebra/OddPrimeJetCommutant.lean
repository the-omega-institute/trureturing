import Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
import Reg.Support.OddPrimeJetAudit
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift

/-! Faithful full-telescope audit mirrors of the original-action commutant endpoints. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
open Polynomial Module

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
open Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
universe uK
noncomputable section

namespace unique_toeplitz

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (hq1 : q 1 = 0)
    (X : Polynomial.degreeLT K p →ₗ[ZMod p] Polynomial.degreeLT K p),
    r.readout () ⟨⟨p, pp, po, K, kk, ka⟩, q⟩ X ↔
      ∃! C : (Fin (p - 1) → K) × (K →ₗ[ZMod p] K),
        X = toeplitz C.1 C.2

def rejected : Realization signature.{uK} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro hbad
  let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
  letI := d.prime
  letI := d.odd
  letI := d.field
  letI := d.algebra
  let q : d.K →ₗ[ZMod d.p] d.K := 0
  let X : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p := 0
  have hh := hbad (p := d.p) q rfl X
  have hr : ∃! C : (Fin (d.p - 1) → d.K) × (d.K →ₗ[ZMod d.p] d.K),
      X = toeplitz C.1 C.2 :=
    (actual_commutant_iff_unique_toeplitz (p := d.p) (K := d.K) q rfl X).mp (by
      intro g v
      simp [q, X])
  simpa [rejected, realize] using hh.mpr hr

def family : Registration arena.{uK} (type_of% (@actual_commutant_iff_unique_toeplitz.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_commutant_iff_unique_toeplitz.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := generated_bridge.family.dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_commutant_iff_unique_toeplitz.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.actual_commutant_iff_unique_toeplitz.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.unique_toeplitz.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end unique_toeplitz

namespace multiplication

abbrev signature : Signature where
  Params := Σ d : Reg.Support.OddPrimeJetAudit.Data.{uK},
    letI := d.prime; letI := d.field; letI := d.algebra
    (Fin d.p → d.K) × ((d.K →ₗ[ZMod d.p] d.K) × (d.K →ₗ[ZMod d.p] d.K))
  State z := Fin z.1.p → z.1.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ z := let d := z.1; letI := d.prime; letI := d.field; letI := d.algebra
    Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ z c =>
    let d := z.1
    letI := d.prime; letI := d.odd; letI := d.field; letI := d.algebra
    toeplitzDegree (productFamily c z.2.1)
      (productTop c z.2.1 z.2.2.1 z.2.2.2)) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature (fun _ z _ =>
    let d := z.1; letI := d.prime; letI := d.field; letI := d.algebra
    (0 : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (c d : Fin p → K) (T U : K →ₗ[ZMod p] K),
    toeplitzDegree c T * toeplitzDegree d U =
      r.readout () ⟨⟨p, pp, po, K, kk, ka⟩, (d, (T, U))⟩ c

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
    intro hbad
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    have hnonzero : constantLinear (p := d.p) (K := d.K) 1 ≠
        (0 : Polynomial.degreeLT d.K d.p) := by
      intro h
      have hh := congrArg (fun v : Polynomial.degreeLT d.K d.p =>
        (v : Polynomial d.K).coeff 0) h
      simpa [constantLinear] using hh
    letI : Nontrivial (Polynomial.degreeLT d.K d.p) := ⟨⟨constantLinear 1, 0, hnonzero⟩⟩

    let c : Fin d.p → d.K := 1
    let T : d.K →ₗ[ZMod d.p] d.K := 0
    have hu : IsUnit (toeplitzDegree (p := d.p) c T) :=
      (toeplitzDegree_isUnit_iff c T).mpr (by simp [c])
    exact (hu.mul hu).ne_zero (hbad (p := d.p) (K := d.K) c c T T)

def family : Registration arena.{uK} (type_of% (@toeplitzDegree_mul.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@toeplitzDegree_mul.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    have hnonzero : constantLinear (p := d.p) (K := d.K) 1 ≠
        (0 : Polynomial.degreeLT d.K d.p) := by
      intro h
      have hh := congrArg (fun v : Polynomial.degreeLT d.K d.p =>
        (v : Polynomial d.K).coeff 0) h
      simpa [constantLinear] using hh
    letI : Nontrivial (Polynomial.degreeLT d.K d.p) := ⟨⟨constantLinear 1, 0, hnonzero⟩⟩

    let z : Fin d.p → d.K := 0
    let o : Fin d.p → d.K := 1
    let T : d.K →ₗ[ZMod d.p] d.K := 0
    refine ⟨⟨d, (o, (T, T))⟩, z, o, ?_⟩
    have hz : toeplitzDegree (p := d.p) z T = 0 := by
      simp [z, T, toeplitzDegree, scalarMap, topMap]
    have hu : IsUnit (toeplitzDegree (p := d.p) o T) :=
      (toeplitzDegree_isUnit_iff o T).mpr (by simp [o])
    intro heq
    have he : toeplitzDegree (p := d.p) z T * toeplitzDegree o T =
        toeplitzDegree o T * toeplitzDegree o T := by
      rw [toeplitzDegree_mul z o T T, toeplitzDegree_mul o o T T]
      exact heq
    exact (hu.mul hu).ne_zero (by simpa [hz] using he.symm)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@toeplitzDegree_mul.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.toeplitzDegree_mul.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.multiplication.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 7, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end multiplication

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
