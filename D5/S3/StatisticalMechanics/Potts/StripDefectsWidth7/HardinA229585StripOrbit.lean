/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.sum_count
   digest: Shared enumeration of exact width-seven successor classes. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
nextClasses: proof_shape=bind-only; consumers=sum_count, OrbitChecks
images: proof_shape=bind-only; consumers=OrbitChecks, OrbitTable.table_counts
sum_count: proof_shape=bind-only; consumers=OrbitCertificate.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Data.Multiset.Replicate

set_option profiler true

/-! Successor multisets retain multiplicity before selecting an output class. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
open HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)

def nextClasses (p : Boundary) (d : ℕ) : Multiset (Fin 72) :=
  ∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d then
    {cl (boundary r) (d - (cross p r + bondDefects horizontal r r))} else 0

/- image0: proof_shape=bind-only; consumers=images -/
@[noinline] private def image0 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 0 j).toNat
    (j.castAdd 56)) +
    ↑([16, 17, 20, 21, 22, 23, 26, 27, 28, 28, 28, 28, 28, 29, 29, 30, 30, 31, 31, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 36, 36, 36, 36, 37, 37, 38, 38, 39, 39, 39, 40, 40, 41, 41, 41, 42, 42, 43, 43, 48, 48, 49, 49, 50, 50, 51, 51, 52, 53, 54, 54, 56, 56, 57, 57, 57, 57, 57, 58, 58, 58, 58, 58, 59, 60, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 65, 65, 65, 66, 66, 66, 67, 67, 67, 68, 68, 69, 69] : List (Fin 72))

/- image1: proof_shape=bind-only; consumers=images -/
@[noinline] private def image1 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 1 j).toNat
    (j.castAdd 56)) +
    ↑([16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 28, 28, 28, 29, 30, 31, 31, 31, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 36, 36, 36, 36, 39, 39, 39, 39, 40, 40, 41, 41, 41, 41, 42, 42, 43, 43, 48, 48, 49, 49, 54, 54, 54, 54, 55, 56, 56, 56, 56, 57, 57, 57, 58, 58, 58, 59, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 67, 68, 68, 69, 69, 70, 70, 71, 71] : List (Fin 72))

/- image2: proof_shape=bind-only; consumers=images -/
@[noinline] private def image2 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 2 j).toNat
    (j.castAdd 56)) +
    ↑([20, 21, 24, 24, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27, 28, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 31, 31, 31, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 36, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 39, 39, 39, 39, 40, 40, 40, 41, 41, 41, 41, 42, 42, 43, 43, 44, 44, 45, 45, 46, 46, 47, 47, 50, 50, 51, 51, 54, 54, 54, 54, 55, 55, 56, 56, 56, 56, 57, 57, 58, 58, 59, 59, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 64, 64, 64, 65, 66, 67, 67, 68, 69, 70, 71] : List (Fin 72))

/- image3: proof_shape=bind-only; consumers=images -/
@[noinline] private def image3 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 3 j).toNat
    (j.castAdd 56)) +
    ↑([20, 21, 22, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 28, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 33, 33, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 39, 39, 40, 40, 41, 41, 42, 43, 44, 44, 45, 45, 48, 48, 49, 49, 50, 50, 51, 51, 52, 52, 53, 53, 54, 54, 54, 54, 54, 56, 56, 56, 56, 56, 57, 57, 58, 58, 59, 59, 60, 60, 60, 61, 61, 62, 62, 65, 65, 66, 66, 67, 67, 67, 68, 69] : List (Fin 72))

/- image4: proof_shape=bind-only; consumers=images -/
@[noinline] private def image4 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 4 j).toNat
    (j.castAdd 56)) +
    ↑([16, 17, 18, 19, 20, 21, 22, 23, 28, 28, 28, 28, 29, 30, 31, 31, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 36, 36, 36, 36, 39, 39, 40, 40, 41, 41, 42, 42, 43, 43, 46, 47, 48, 48, 49, 49, 52, 53, 54, 54, 54, 54, 54, 56, 56, 56, 56, 56, 57, 57, 57, 58, 58, 58, 59, 60, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 64, 64, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 67, 68, 68, 69, 69, 70, 70, 71, 71] : List (Fin 72))

/- image5: proof_shape=bind-only; consumers=images -/
@[noinline] private def image5 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 5 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 17, 17, 18, 18, 19, 19, 22, 23, 28, 28, 28, 28, 29, 30, 31, 31, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 36, 36, 36, 36, 39, 39, 40, 40, 41, 41, 42, 42, 43, 43, 44, 45, 46, 47, 48, 48, 49, 49, 50, 50, 51, 51, 54, 54, 54, 55, 56, 56, 56, 57, 57, 57, 57, 57, 57, 58, 58, 58, 58, 58, 58, 59, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 64, 65, 65, 65, 66, 66, 66, 67, 67, 67, 68, 68, 69, 69] : List (Fin 72))

/- image6: proof_shape=bind-only; consumers=images -/
@[noinline] private def image6 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 6 j).toNat
    (j.castAdd 56)) +
    ↑([16, 17, 18, 19, 20, 21, 22, 23, 24, 24, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27, 29, 29, 29, 30, 30, 30, 31, 31, 32, 32, 33, 33, 34, 34, 35, 35, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 40, 40, 41, 41, 41, 41, 42, 42, 43, 43, 44, 44, 44, 45, 45, 45, 46, 46, 47, 47, 48, 49, 50, 50, 50, 51, 51, 51, 52, 53, 54, 54, 54, 54, 55, 55, 55, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 61, 61, 61, 61, 61, 62, 62, 62, 62, 62, 63, 63, 64, 64, 65, 66, 67, 67, 68, 69, 70, 71] : List (Fin 72))

/- image7: proof_shape=bind-only; consumers=images -/
@[noinline] private def image7 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 7 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 17, 17, 18, 18, 19, 19, 22, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 29, 30, 30, 30, 33, 34, 35, 35, 36, 36, 37, 37, 37, 38, 38, 38, 39, 40, 40, 41, 44, 44, 44, 45, 45, 45, 46, 47, 48, 48, 49, 49, 50, 50, 50, 51, 51, 51, 52, 52, 53, 53, 54, 54, 54, 54, 54, 54, 54, 55, 56, 56, 56, 56, 56, 56, 56, 57, 57, 57, 58, 58, 58, 59, 59, 59, 60, 60, 61, 62, 65, 65, 65, 66, 66, 66, 67, 67, 70, 71] : List (Fin 72))

/- image8: proof_shape=bind-only; consumers=images -/
@[noinline] private def image8 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 8 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 22, 22, 23, 23, 24, 25, 26, 27, 28, 29, 29, 29, 29, 30, 30, 30, 30, 33, 33, 33, 34, 34, 34, 35, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 40, 41, 41, 41, 41, 44, 44, 44, 45, 45, 45, 46, 46, 47, 47, 48, 49, 50, 50, 50, 51, 51, 51, 52, 53, 54, 54, 54, 54, 55, 55, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 59, 60, 61, 61, 61, 62, 62, 62, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 67, 70, 70, 71, 71] : List (Fin 72))

/- image9: proof_shape=bind-only; consumers=images -/
@[noinline] private def image9 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 9 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26, 27, 27, 29, 29, 30, 30, 31, 32, 33, 33, 33, 34, 34, 34, 35, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 40, 41, 41, 41, 41, 41, 41, 42, 43, 44, 44, 44, 45, 45, 45, 46, 47, 48, 48, 49, 49, 50, 50, 50, 51, 51, 51, 52, 52, 53, 53, 54, 54, 54, 55, 55, 55, 56, 56, 56, 57, 57, 57, 57, 57, 57, 57, 58, 58, 58, 58, 58, 58, 58, 59, 61, 61, 61, 61, 61, 61, 62, 62, 62, 62, 62, 62, 63, 64, 65, 65, 65, 65, 66, 66, 66, 66, 67, 68, 68, 69, 69, 70, 70, 71, 71] : List (Fin 72))

/- image10: proof_shape=bind-only; consumers=images -/
@[noinline] private def image10 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 10 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 22, 22, 23, 23, 28, 28, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 31, 32, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 35, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 40, 41, 41, 41, 42, 43, 44, 44, 45, 45, 46, 46, 47, 47, 48, 49, 50, 51, 54, 54, 55, 55, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 60, 61, 61, 61, 61, 61, 61, 62, 62, 62, 62, 62, 62, 63, 63, 64, 64, 65, 65, 65, 66, 66, 66, 67, 67, 67, 68, 69] : List (Fin 72))

/- image11: proof_shape=bind-only; consumers=images -/
@[noinline] private def image11 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 11 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22, 23, 23, 28, 28, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 31, 32, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 35, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 40, 41, 41, 41, 42, 43, 46, 46, 47, 47, 48, 49, 52, 52, 53, 53, 54, 54, 54, 54, 54, 54, 56, 56, 56, 56, 56, 56, 57, 58, 59, 59, 60, 60, 60, 61, 61, 61, 62, 62, 62, 63, 64, 65, 65, 65, 66, 66, 66, 67, 67, 68, 69, 70, 71] : List (Fin 72))

/- image12: proof_shape=bind-only; consumers=images -/
@[noinline] private def image12 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 12 j).toNat
    (j.castAdd 56)) +
    ↑([20, 20, 21, 21, 22, 22, 23, 23, 24, 25, 26, 27, 28, 28, 28, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 33, 33, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 40, 41, 41, 41, 41, 41, 41, 42, 42, 43, 43, 44, 45, 48, 49, 50, 51, 52, 53, 54, 54, 54, 56, 56, 56, 57, 57, 57, 57, 57, 58, 58, 58, 58, 58, 59, 60, 60, 60, 61, 61, 62, 62, 65, 65, 66, 66, 67, 67, 67, 68, 68, 69, 69] : List (Fin 72))

/- image13: proof_shape=bind-only; consumers=images -/
@[noinline] private def image13 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 13 j).toNat
    (j.castAdd 56)) +
    ↑([20, 20, 21, 21, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 29, 30, 30, 30, 31, 31, 31, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 35, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 43, 44, 45, 46, 47, 50, 51, 54, 54, 54, 54, 54, 54, 55, 56, 56, 56, 56, 56, 56, 57, 57, 57, 58, 58, 58, 59, 60, 60, 61, 62, 63, 63, 63, 64, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 67, 68, 68, 69, 69, 70, 70, 71, 71] : List (Fin 72))

/- image14: proof_shape=bind-only; consumers=images -/
@[noinline] private def image14 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 14 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 17, 17, 18, 18, 19, 19, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 31, 31, 31, 32, 32, 32, 33, 33, 33, 34, 34, 34, 35, 35, 35, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 40, 41, 41, 41, 41, 41, 41, 41, 42, 43, 48, 49, 54, 55, 55, 56, 57, 58, 59, 59, 60, 61, 61, 61, 61, 61, 61, 62, 62, 62, 62, 62, 62, 63, 63, 63, 64, 64, 64, 65, 65, 65, 66, 66, 66, 67, 67, 68, 69, 70, 71] : List (Fin 72))

/- image15: proof_shape=bind-only; consumers=images -/
@[noinline] private def image15 : Multiset (Fin 72) :=
  (∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 15 j).toNat
    (j.castAdd 56)) +
    ↑([16, 16, 17, 17, 20, 20, 21, 21, 22, 22, 23, 23, 26, 26, 27, 27, 28, 28, 28, 28, 29, 29, 29, 29, 30, 30, 30, 30, 31, 32, 33, 33, 33, 34, 34, 34, 35, 35, 35, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 40, 41, 41, 41, 41, 41, 42, 43, 48, 49, 50, 51, 52, 52, 53, 53, 54, 54, 54, 56, 56, 56, 57, 57, 58, 58, 59, 59, 60, 60, 60, 61, 61, 61, 62, 62, 62, 65, 65, 65, 66, 66, 66, 67, 67, 67, 68, 69] : List (Fin 72))

/- image16: proof_shape=bind-only; consumers=images -/
@[noinline] private def image16 : Multiset (Fin 72) :=
  ↑([29, 29, 29, 30, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 39, 41, 57, 58, 61, 61, 62, 62, 65, 65, 66, 66] : List (Fin 72))

/- image17: proof_shape=bind-only; consumers=images -/
@[noinline] private def image17 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 39, 41, 54, 56, 57, 58, 61, 62, 65, 66] : List (Fin 72))

/- image18: proof_shape=bind-only; consumers=images -/
@[noinline] private def image18 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 39, 41, 57, 58, 61, 61, 62, 62, 65, 65, 66, 66] : List (Fin 72))

/- image19: proof_shape=bind-only; consumers=images -/
@[noinline] private def image19 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 37, 38, 39, 39, 41, 41, 54, 56, 57, 58, 61, 62, 65, 66] : List (Fin 72))

/- image20: proof_shape=bind-only; consumers=images -/
@[noinline] private def image20 : Multiset (Fin 72) :=
  ↑([33, 34, 39, 41, 54, 54, 56, 56, 57, 58, 65, 66] : List (Fin 72))

/- image21: proof_shape=bind-only; consumers=images -/
@[noinline] private def image21 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 37, 38, 39, 41, 54, 56, 57, 57, 58, 58, 61, 62, 65, 66] : List (Fin 72))

/- image22: proof_shape=bind-only; consumers=images -/
@[noinline] private def image22 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 34, 37, 37, 38, 38, 39, 41, 57, 58, 61, 61, 62, 62, 65, 66] : List (Fin 72))

/- image23: proof_shape=bind-only; consumers=images -/
@[noinline] private def image23 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 34, 37, 37, 38, 38, 39, 41, 54, 56, 57, 58, 61, 62, 65, 65, 66, 66] : List (Fin 72))

/- image24: proof_shape=bind-only; consumers=images -/
@[noinline] private def image24 : Multiset (Fin 72) :=
  ↑([37, 38, 39, 41, 54, 54, 54, 54, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 65, 65, 66, 66] : List (Fin 72))

/- image25: proof_shape=bind-only; consumers=images -/
@[noinline] private def image25 : Multiset (Fin 72) :=
  ↑([39, 41, 54, 54, 56, 56, 57, 57, 58, 58, 61, 61, 62, 62, 65, 65, 66, 66] : List (Fin 72))

/- image26: proof_shape=bind-only; consumers=images -/
@[noinline] private def image26 : Multiset (Fin 72) :=
  ↑([29, 30, 37, 38, 39, 41, 54, 54, 54, 54, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 65, 65, 66, 66] : List (Fin 72))

/- image27: proof_shape=bind-only; consumers=images -/
@[noinline] private def image27 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 37, 38, 54, 54, 56, 56, 57, 57, 58, 58, 61, 61, 62, 62, 65, 65, 66, 66] : List (Fin 72))

/- image28: proof_shape=bind-only; consumers=images -/
@[noinline] private def image28 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 33, 33, 33, 34, 34, 34, 34, 39, 39, 39, 39, 41, 41, 41, 41, 54, 56, 61, 62, 65, 65, 66, 66] : List (Fin 72))

/- image29: proof_shape=bind-only; consumers=images -/
@[noinline] private def image29 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 0 j).toNat
    (zeroBudgetClass j)

/- image30: proof_shape=bind-only; consumers=images -/
@[noinline] private def image30 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 1 j).toNat
    (zeroBudgetClass j)

/- image31: proof_shape=bind-only; consumers=images -/
@[noinline] private def image31 : Multiset (Fin 72) :=
  ↑([33, 33, 34, 34, 37, 38, 39, 39, 39, 41, 41, 41, 54, 54, 54, 56, 56, 56, 57, 57, 58, 58] : List (Fin 72))

/- image32: proof_shape=bind-only; consumers=images -/
@[noinline] private def image32 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 39, 39, 39, 41, 41, 41, 54, 54, 54, 56, 56, 56, 57, 58] : List (Fin 72))

/- image33: proof_shape=bind-only; consumers=images -/
@[noinline] private def image33 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 2 j).toNat
    (zeroBudgetClass j)

/- image34: proof_shape=bind-only; consumers=images -/
@[noinline] private def image34 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 3 j).toNat
    (zeroBudgetClass j)

/- image35: proof_shape=bind-only; consumers=images -/
@[noinline] private def image35 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 34, 37, 37, 38, 38, 39, 41, 54, 54, 56, 56, 61, 61, 62, 62, 65, 66] : List (Fin 72))

/- image36: proof_shape=bind-only; consumers=images -/
@[noinline] private def image36 : Multiset (Fin 72) :=
  ↑([33, 33, 33, 33, 34, 34, 34, 34, 39, 39, 39, 39, 41, 41, 41, 41, 54, 56, 61, 62, 65, 65, 66, 66] : List (Fin 72))

/- image37: proof_shape=bind-only; consumers=images -/
@[noinline] private def image37 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 4 j).toNat
    (zeroBudgetClass j)

/- image38: proof_shape=bind-only; consumers=images -/
@[noinline] private def image38 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 5 j).toNat
    (zeroBudgetClass j)

/- image39: proof_shape=bind-only; consumers=images -/
@[noinline] private def image39 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 6 j).toNat
    (zeroBudgetClass j)

/- image40: proof_shape=bind-only; consumers=images -/
@[noinline] private def image40 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 37, 37, 38, 38, 54, 54, 56, 56, 57, 58, 61, 61, 62, 62] : List (Fin 72))

/- image41: proof_shape=bind-only; consumers=images -/
@[noinline] private def image41 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 7 j).toNat
    (zeroBudgetClass j)

/- image42: proof_shape=bind-only; consumers=images -/
@[noinline] private def image42 : Multiset (Fin 72) :=
  ↑([33, 33, 34, 34, 39, 39, 41, 41, 54, 54, 56, 56, 57, 57, 58, 58, 61, 62] : List (Fin 72))

/- image43: proof_shape=bind-only; consumers=images -/
@[noinline] private def image43 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 39, 39, 41, 41, 54, 54, 56, 56, 61, 62, 65, 66] : List (Fin 72))

/- image44: proof_shape=bind-only; consumers=images -/
@[noinline] private def image44 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 54, 54, 56, 56, 57, 57, 57, 58, 58, 58, 61, 62, 65, 65, 65, 66, 66, 66] : List (Fin 72))

/- image45: proof_shape=bind-only; consumers=images -/
@[noinline] private def image45 : Multiset (Fin 72) :=
  ↑([33, 34, 54, 56, 57, 57, 57, 58, 58, 58, 61, 61, 62, 62, 65, 65, 65, 66, 66, 66] : List (Fin 72))

/- image46: proof_shape=bind-only; consumers=images -/
@[noinline] private def image46 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 37, 38, 54, 54, 56, 56, 57, 57, 58, 58, 61, 62, 65, 66] : List (Fin 72))

/- image47: proof_shape=bind-only; consumers=images -/
@[noinline] private def image47 : Multiset (Fin 72) :=
  ↑([29, 30, 37, 38, 39, 41, 54, 54, 56, 56, 61, 62] : List (Fin 72))

/- image48: proof_shape=bind-only; consumers=images -/
@[noinline] private def image48 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 37, 37, 38, 38, 39, 39, 41, 41, 54, 56, 61, 61, 62, 62] : List (Fin 72))

/- image49: proof_shape=bind-only; consumers=images -/
@[noinline] private def image49 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 54, 56, 57, 58, 61, 61, 62, 62, 65, 65, 66, 66] : List (Fin 72))

/- image50: proof_shape=bind-only; consumers=images -/
@[noinline] private def image50 : Multiset (Fin 72) :=
  ↑([33, 33, 34, 34, 54, 54, 56, 56, 57, 57, 57, 58, 58, 58, 61, 62, 65, 65, 65, 66, 66, 66] : List (Fin 72))

/- image51: proof_shape=bind-only; consumers=images -/
@[noinline] private def image51 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 54, 56, 57, 57, 57, 58, 58, 58, 61, 61, 62, 62, 65, 65, 65, 66, 66, 66] : List (Fin 72))

/- image52: proof_shape=bind-only; consumers=images -/
@[noinline] private def image52 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 37, 38, 39, 41, 54, 56, 61, 61, 62, 62, 65, 65, 66, 66] : List (Fin 72))

/- image53: proof_shape=bind-only; consumers=images -/
@[noinline] private def image53 : Multiset (Fin 72) :=
  ↑([33, 34, 39, 41, 54, 56, 57, 58, 61, 61, 62, 62] : List (Fin 72))

/- image54: proof_shape=bind-only; consumers=images -/
@[noinline] private def image54 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 8 j).toNat
    (zeroBudgetClass j)

/- image55: proof_shape=bind-only; consumers=images -/
@[noinline] private def image55 : Multiset (Fin 72) :=
  ↑([29, 30, 37, 38, 54, 56, 57, 57, 58, 58, 61, 62] : List (Fin 72))

/- image56: proof_shape=bind-only; consumers=images -/
@[noinline] private def image56 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 9 j).toNat
    (zeroBudgetClass j)

/- image57: proof_shape=bind-only; consumers=images -/
@[noinline] private def image57 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 10 j).toNat
    (zeroBudgetClass j)

/- image58: proof_shape=bind-only; consumers=images -/
@[noinline] private def image58 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 11 j).toNat
    (zeroBudgetClass j)

/- image59: proof_shape=bind-only; consumers=images -/
@[noinline] private def image59 : Multiset (Fin 72) :=
  ↑([33, 33, 34, 34, 39, 39, 41, 41, 54, 54, 56, 56, 61, 61, 62, 62, 65, 66] : List (Fin 72))

/- image60: proof_shape=bind-only; consumers=images -/
@[noinline] private def image60 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 33, 34, 34, 37, 38, 39, 39, 41, 41, 54, 56, 61, 62, 65, 65, 66, 66] : List (Fin 72))

/- image61: proof_shape=bind-only; consumers=images -/
@[noinline] private def image61 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 12 j).toNat
    (zeroBudgetClass j)

/- image62: proof_shape=bind-only; consumers=images -/
@[noinline] private def image62 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 13 j).toNat
    (zeroBudgetClass j)

/- image63: proof_shape=bind-only; consumers=images -/
@[noinline] private def image63 : Multiset (Fin 72) :=
  ↑([29, 30, 33, 34, 37, 38, 39, 39, 39, 41, 41, 41, 54, 54, 54, 56, 56, 56, 57, 57, 58, 58] : List (Fin 72))

/- image64: proof_shape=bind-only; consumers=images -/
@[noinline] private def image64 : Multiset (Fin 72) :=
  ↑([33, 34, 37, 37, 38, 38, 39, 39, 39, 41, 41, 41, 54, 54, 54, 56, 56, 56, 57, 58] : List (Fin 72))

/- image65: proof_shape=bind-only; consumers=images -/
@[noinline] private def image65 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 14 j).toNat
    (zeroBudgetClass j)

/- image66: proof_shape=bind-only; consumers=images -/
@[noinline] private def image66 : Multiset (Fin 72) :=
  ∑ j : Fin 16, Multiset.replicate (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 15 j).toNat
    (zeroBudgetClass j)

/- image67: proof_shape=bind-only; consumers=images -/
@[noinline] private def image67 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 39, 39, 41, 41, 54, 54, 56, 56, 61, 61, 62, 62, 65, 66] : List (Fin 72))

/- image68: proof_shape=bind-only; consumers=images -/
@[noinline] private def image68 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 33, 33, 34, 34, 37, 37, 38, 38, 54, 56, 57, 58, 61, 62, 65, 66] : List (Fin 72))

/- image69: proof_shape=bind-only; consumers=images -/
@[noinline] private def image69 : Multiset (Fin 72) :=
  ↑([29, 29, 30, 30, 37, 37, 38, 38, 39, 39, 41, 41, 54, 54, 56, 56, 57, 57, 58, 58, 65, 66] : List (Fin 72))

/- image70: proof_shape=bind-only; consumers=images -/
@[noinline] private def image70 : Multiset (Fin 72) :=
  ↑([39, 39, 41, 41, 54, 56, 57, 58, 61, 62, 65, 66] : List (Fin 72))

/- image71: proof_shape=bind-only; consumers=images -/
@[noinline] private def image71 : Multiset (Fin 72) :=
  ↑([37, 37, 38, 38, 39, 39, 41, 41, 54, 54, 56, 56, 57, 57, 58, 58, 65, 66] : List (Fin 72))

def images : Fin 72 → Multiset (Fin 72) :=
  ![image0, image1, image2, image3, image4, image5, image6, image7, image8, image9, image10, image11, image12, image13, image14, image15, image16, image17, image18, image19, image20, image21, image22, image23, image24, image25, image26, image27, image28, image29, image30, image31, image32, image33, image34, image35, image36, image37, image38, image39, image40, image41, image42, image43, image44, image45, image46, image47, image48, image49, image50, image51, image52, image53, image54, image55, image56, image57, image58, image59, image60, image61, image62, image63, image64, image65, image66, image67, image68, image69, image70, image71]

theorem sum_count (p : Boundary) (d : ℕ) (s : Fin 72) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = ((nextClasses p d).count s : ℤ) := by
  unfold nextClasses
  rw [Multiset.count_sum', Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : cross p r + bondDefects horizontal r r ≤ d
  · simp only [h, ite_true, true_and, Multiset.count_singleton]
    split_ifs with hs hs' <;> simp_all
  · simp only [h, ite_false, false_and, Multiset.count_zero, Nat.cast_zero]

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
