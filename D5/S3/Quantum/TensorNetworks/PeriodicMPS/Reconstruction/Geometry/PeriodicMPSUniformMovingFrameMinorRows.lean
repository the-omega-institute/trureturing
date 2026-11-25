/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorRows
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorRows
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Triplet and singlet rows in the moving frame. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameRows
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw coreCommutator)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open PeriodicMPSUniformVerticalSectionRank (transverseKet tripletReadout tripletReadout_eq_native
  tripletReadout_section tripletRow tripletShear tripletRotation singletTrace singletTrace_eq_native
  sectionTripletMinor sectionSingletMinor TripletIndex SingletIndex)
open private pairedBra liftCore outerEntry trace_kronecker_transfer from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace
open private sectionBra literalOuterColumn endpoint from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private mapCore map_sectionKet map_sectionBra map_mixedRaw
  from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection

noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

def tripletProjector {R : Type*} [CommRing R] (h : R) : Matrix (Fin 3) TwoBits R :=
  Matrix.of (tripletRow h)

def tripletContract {R : Type*} [CommRing R] (h : R) (W : TransferMatrix R) :
    Matrix (Fin 3) (Fin 3) R :=
  tripletProjector h * W * (tripletProjector h)ᵀ

private theorem tripletContract_eq {R : Type*} [CommRing R] (h : R) (W : TransferMatrix R)
    (i j : Fin 3) :
    tripletContract h W i j =
      ∑ q : TwoBits, ∑ p : TwoBits, tripletRow h j q * (tripletRow h i p * W p q) := by
  simp only [tripletContract, tripletProjector, Matrix.mul_apply, Finset.sum_mul,
    Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => mul_comm _ _

private theorem tripletContract_raw {R : Type*} [CommRing R] (h : R)
    (A B : Core R) (m : ℕ) :
    tripletContract h (mixedRaw A B m) = tripletReadout h A B m := by
  apply Matrix.ext
  intro i j
  rw [tripletContract_eq, tripletReadout_eq_native]

def singletContract {R : Type*} [CommRing R] (h : R) (W : TransferMatrix R) : R :=
  h * (W (0,1) (0,1) - W (1,0) (0,1) - W (0,1) (1,0) + W (1,0) (1,0))

def lowerShear {R : Type*} [CommRing R] : BondMatrix R := !![0,0;1,0]
def upperShear {R : Type*} [CommRing R] : BondMatrix R := !![0,1;0,0]
def diagonalShear {R : Type*} [CommRing R] : BondMatrix R := !![1,0;0,-1]

def physicalShear {R : Type*} [CommRing R] (upper : Bool) : BondMatrix R :=
  if upper then upperShear else lowerShear

set_option maxHeartbeats 2000000 in
private theorem tripletConj (upper : Bool) (W : TransferMatrix E) :
    tripletContract (half E) (physicalTangent (physicalShear upper) W) =
      tripletRotation upper (tripletContract (half E) W) := by
  let _ : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  have hh : half E = 1 / 2 := (map_div₀ (algebraMap ℂ E) 1 2).trans (by rw [map_one, map_ofNat])
  apply Matrix.ext
  intro i j
  cases upper <;> fin_cases i <;> fin_cases j <;>
    simp [tripletRotation, tripletContract_eq, tripletRow, tripletShear, physicalTangent,
      physicalShear, lowerShear, upperShear, pairGenerator, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, hh] <;> ring

def diagonalTriplet {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![2,0,0;0,0,0;0,0,-2]

set_option maxHeartbeats 1200000 in
private theorem tripletConj_diag (W : TransferMatrix E) :
    tripletContract (half E) (physicalTangent diagonalShear W) =
      diagonalTriplet * tripletContract (half E) W - tripletContract (half E) W * diagonalTriplet := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalTriplet, tripletContract_eq, tripletRow, physicalTangent, diagonalShear,
      pairGenerator, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

private def sectionRaw (x : Fin 5 → E) (m : ℕ) : TransferMatrix E :=
  mixedRaw (transverseKet 0) (sectionBra x) m

private def parameterTangent (x : Fin 5 → E) (m : ℕ) (j : Fin 5) : TransferMatrix E :=
  jetTangent (mixedRaw (transverseKet 0) (sectionBraJet x (Pi.single j 1)) m)

private def transverseTangent (x : Fin 5 → E) (m : ℕ) : TransferMatrix E :=
  jetTangent (mixedRaw (transverseKet (inr 1 : DualNumber E)) (sectionBraJet x 0) m)

def sectionRawColumns (x : Fin 5 → E) (m : ℕ) : TripletIndex → TransferMatrix E :=
  Sum.elim (fun i => ![parameterTangent x m 0, parameterTangent x m 1, parameterTangent x m 2,
    parameterTangent x m 3, parameterTangent x m 4,
    physicalTangent diagonalShear (sectionRaw x m)] i)
    (fun i => ![physicalTangent lowerShear (sectionRaw x m),
      physicalTangent upperShear (sectionRaw x m), transverseTangent x m] i)

def tripletContractRow (W : TransferMatrix E) (i : TripletIndex) : E :=
  i.elim (outerEntry (tripletContract (half E) W)) (tripletContract (half E) W 1)

def singletContractRow (W : TransferMatrix E) (i : SingletIndex) : E :=
  i.elim (outerEntry (tripletContract (half E) W))
    (Sum.elim (fun j => tripletContract (half E) W 1 (endpoint j)) (fun _ => singletContract (half E) W))

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
