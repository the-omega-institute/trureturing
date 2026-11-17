import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation

namespace Reg.Support.OddPrimeJetAudit
universe uK
noncomputable section

structure Data where
  p : ℕ
  prime : Fact p.Prime
  odd : Fact (2 < p)
  K : Type uK
  field : Field K
  algebra : letI := prime; letI := field; Algebra (ZMod p) K

abbrev Vector (d : Data.{uK}) : Type uK := letI := d.field; Polynomial.degreeLT d.K d.p
abbrev Scalar (d : Data.{uK}) := d.K
abbrev Poly (d : Data.{uK}) := letI := d.field; Polynomial d.K
abbrev End (d : Data.{uK}) := letI := d.field; Module.End d.K (Vector d)

abbrev signature (S : Data.{uK} → Type uK) : Signature where
  Params := Data.{uK}
  State := S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := S
  Anchor := Empty
  finiteAnchor := inferInstance

def actual (S : Data.{uK} → Type uK) : Realization (signature S) :=
  realize (signature S) (fun _ _ x => x) (fun e => nomatch e)

def vectorOne (d : Data.{uK}) : Vector d := by
  letI := d.prime
  letI := d.odd
  letI := d.field
  letI := d.algebra
  exact constantLinear (p := d.p) (K := d.K) 1

def rejectedVector : Realization (signature Vector.{uK}) :=
  realize (signature Vector) (fun _ d x => letI := d.field; x + vectorOne d)
    (fun e => nomatch e)

def rejectedScalar : Realization (signature Scalar.{uK}) :=
  realize (signature Scalar) (fun _ d x => letI := d.field; x + 1)
    (fun e => nomatch e)

def rejectedPoly : Realization (signature Poly.{uK}) :=
  realize (signature Poly) (fun _ d x => letI := d.field; x + 1)
    (fun e => nomatch e)

def rejectedEnd : Realization (signature End.{uK}) :=
  realize (signature End) (fun _ d x => letI := d.field; x + 1)
    (fun e => nomatch e)

private instance testPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev testK := ULift.{uK} (ZMod 3)
abbrev testData : Data.{uK} where
  p := 3
  prime := ⟨by decide⟩
  odd := ⟨by decide⟩
  K := testK.{uK}
  field := inferInstance
  algebra := inferInstance

theorem vectorOne_ne_zero (d : Data.{uK}) : vectorOne d ≠ 0 := by
  letI := d.field
  intro h
  have hz := congrArg (fun v : Vector d => (v : Polynomial d.K).coeff 0) h
  exact (one_ne_zero : (1 : d.K) ≠ 0) (by simpa [vectorOne, constantLinear] using hz)

theorem dependenceVector : ObservationalDependence (signature Vector.{uK}) (actual Vector) := by
  intro i
  refine ⟨testData, 0, vectorOne testData, ?_⟩
  exact (vectorOne_ne_zero testData).symm

theorem dependenceScalar : ObservationalDependence (signature Scalar.{uK}) (actual Scalar) := by
  letI := testData.{uK}.field
  intro i
  exact ⟨testData, 0, 1, zero_ne_one⟩

theorem dependencePoly : ObservationalDependence (signature Poly.{uK}) (actual Poly) := by
  intro i
  exact ⟨testData, 0, 1, zero_ne_one⟩

theorem dependenceEnd : ObservationalDependence (signature End.{uK}) (actual End) := by
  intro i
  refine ⟨testData, 0, 1, ?_⟩
  intro h
  have hz := congrArg (fun A : End testData => A (vectorOne testData)) h
  exact vectorOne_ne_zero testData hz.symm

end
end Reg.Support.OddPrimeJetAudit
