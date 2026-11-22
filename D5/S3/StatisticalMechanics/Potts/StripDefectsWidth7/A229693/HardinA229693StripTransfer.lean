/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts
   digest: Exact successor multiplicities into the exhausted budget. -/

/-
admission_basis: escape-witness
escape_witness: exactExits_active and exactExits_new compute the multiplicities of transitions reaching budget zero
Valid: proof_shape=bind-only; consumers=decidableValid, exhaustedClass, valid_shift, cl_relabel, next_valid, initial_valid, leading_counts, old_exhausted_counts, exactExits_active, exactExits_new, class_counts_canonical, class_counts, transition_counts, count_transfer
decidableValid: proof_shape=bind-only; consumers=exhaustedClass, exactExits_active, exactExits_new
patternCode: proof_shape=content; consumers=pattern_relabel, exhaustedClass, exactExits_new
pattern_relabel: proof_shape=content; consumers=cl_relabel
newPatterns: proof_shape=content; consumers=exhaustedClass, exactExits_new
oldZeroImage: proof_shape=bind-only; consumers=exhaustedClass, initialExhausted, old_exhausted_counts
exhaustedClass: proof_shape=content; consumers=cl, cl_relabel, exhausted_relabel, exhausted_cut, old_exhausted_counts, exactExits, exactExits_count, class_counts_canonical, class_counts, initialExits, initial_counts
cl: proof_shape=content; consumers=cl_relabel, exhausted_relabel, active_cut, exhausted_cut, terminal_eq, leading_counts, old_exhausted_counts, class_counts_canonical, class_counts, transition_counts, count_transfer
exitRead: proof_shape=content; consumers=activeWeight, exhaustedWeight
activeExits: proof_shape=content; consumers=activeWeight
exhaustedExits: proof_shape=content; consumers=exhaustedWeight
activeWeight: proof_shape=content; consumers=T, exactExits_active
exhaustedWeight: proof_shape=content; consumers=T, exactExits_new
exitsFromWeights: proof_shape=bind-only; consumers=exitsFromWeights_count, exactExits_active, exactExits_new
exitsFromWeights_count: proof_shape=bind-only; consumers=class_counts_canonical
pushOld: proof_shape=bind-only; consumers=T
T: proof_shape=content; consumers=leading_counts, old_exhausted_counts, class_counts_canonical, class_counts, transition_counts, count_transfer, HardinA229693Strip.leading_action
initialExhausted: proof_shape=content; consumers=initial, initialExits_eq, initialExits_count
initial: proof_shape=content; consumers=initial_counts, count_transfer, HardinA229693Strip.forward_table
terminal: proof_shape=bind-only; consumers=terminal_eq, count_transfer, HardinA229693Strip.result
valid_shift: proof_shape=bind-only; consumers=old_valid, leading_counts
old_valid: proof_shape=bind-only; consumers=old_exhausted_counts
cl_relabel: proof_shape=content; consumers=exhausted_relabel, class_counts
exhausted_relabel: proof_shape=content; consumers=class_counts
blocks_disjoint: proof_shape=bind-only; consumers=active_cut, exhausted_cut, old_exhausted_counts
active_cut: proof_shape=bind-only; consumers=leading_counts, initial_counts
exhausted_cut: proof_shape=bind-only; consumers=transition_counts, initial_counts
next_valid: proof_shape=bind-only; consumers=count_transfer
initial_valid: proof_shape=bind-only; consumers=count_transfer
terminal_eq: proof_shape=bind-only; consumers=count_transfer
leading_counts: proof_shape=bind-only; consumers=transition_counts
old_exhausted_counts: proof_shape=bind-only; consumers=class_counts_canonical
horizontalCost: proof_shape=bind-only; consumers=horizontalCost_eq, rowCost, initialExits, initial_counts
horizontalCost_eq: proof_shape=bind-only; consumers=rowCost_eq, initial_counts
rowCost: proof_shape=bind-only; consumers=rowCost_eq, exactExits, exactExits_count
rowCost_eq: proof_shape=bind-only; consumers=exactExits_count
exactExits: proof_shape=content; consumers=exactExits_count, exactExits_active, exactExits_new
exactExits_count: proof_shape=content; consumers=class_counts_canonical
exactExits_active: proof_shape=content; consumers=class_counts_canonical
exactExits_new: proof_shape=content; consumers=class_counts_canonical
class_counts_canonical: proof_shape=content; consumers=class_counts
class_counts: proof_shape=content; consumers=transition_counts
transition_counts: proof_shape=content; consumers=count_transfer
initialExits: proof_shape=content; consumers=initialExits_eq, initialExits_count
initialExits_eq: proof_shape=content; consumers=initialExits_count
initialExits_count: proof_shape=content; consumers=initial_counts
initial_counts: proof_shape=content; consumers=count_transfer
count_transfer: proof_shape=content; consumers=HardinA229693Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Data.Matrix.Block

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
  (Canonical canonical_exists_unique)
open HardinA229585StripData (Boundary Row horizontal antidiagonal boundary cross)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true

def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 2 ∧ (Finset.univ.filter fun j : Fin 5 => p j.castSucc = p j.succ).card ≤ 2 - d

private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def patternCode (p : Boundary) : Fin 729 :=
  let b := (List.finRange 6).find? (fun j => p j != p 0)
  finFunctionFinEquiv (fun j => if p j = p 0 then 0
    else if b.any (fun i => p j == p i) then 1 else (2 : Fin 3))

private theorem pattern_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    patternCode (e ∘ p) = patternCode p := by
  have h (x y : Fin 3) : (e x == e y) = (x == y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, e.injective.eq_iff]
  simp only [patternCode, Function.comp_apply, bne, h, e.injective.eq_iff]

private def newPatterns : List (Fin 729) :=
  [270, 513, 189, 432, 252, 495, 333, 657, 279, 522, 198, 441, 63, 387, 225, 468, 246, 489, 327,
   651, 354, 705, 255, 498, 336, 660, 282, 525, 201, 444, 66, 390, 228, 471, 21, 372, 75, 399, 237,
   480]

private def oldZeroImage (i : Fin 72) : Fin 96 :=
  if h : 16 ≤ i.val then (Fin.subNat 16 i h).castAdd 40 else 0

def exhaustedClass (p : Boundary) : Fin 96 :=
  if Valid p 1 then oldZeroImage (HardinA229585StripData.cl p 0)
  else (Fin.ofNat 40 (newPatterns.idxOf (patternCode p))).natAdd 56

def cl (p : Boundary) (d : ℕ) : Fin 168 :=
  if d = 0 then (exhaustedClass p).natAdd 72 else
    (HardinA229585StripData.cl p (d - 1)).castAdd 96

private def exitRead : Fin 96 → Fin 108 :=
  ![72, 72, 73, 73, 74, 74, 75, 75, 76, 76, 77, 77, 29, 78, 78, 79, 79, 80, 80, 33, 37, 81, 81,
    82, 39, 82, 83, 83, 84, 84, 85, 85, 86, 86, 87, 87, 88, 88, 89, 54, 89, 90, 90, 57, 61, 91,
    91, 92, 92, 93, 93, 65, 94, 94, 95, 95, 96, 96, 97, 97, 98, 98, 16, 18, 99, 99, 100, 100,
    20, 22, 101, 101, 102, 102, 24, 26, 31, 42, 103, 103, 44, 46, 104, 104, 105, 105, 48, 50,
    106, 106, 52, 63, 68, 70, 107, 107]

private def activeExits : Fin 72 → List (Fin 36) :=
  ![
    [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7,
     8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 12, 12, 12, 12, 13, 13, 14, 14, 14, 15,
     16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 19, 19, 20, 20, 20, 20,
     20, 20, 21, 21, 21, 21, 21, 22, 22, 22, 23, 23, 23, 23, 24, 25, 26, 30, 32, 32, 35, 35],
    [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7,
     7, 7, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 13, 13, 13, 13,
     13, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 19,
     19, 19, 19, 19, 20, 20, 21, 21, 22, 22, 23, 25, 29, 32, 32, 33, 33, 34, 34],
    [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9,
     9, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 13, 13, 14, 14, 14, 14, 14, 15, 15, 16,
     16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 20, 20, 21, 21, 21, 21, 21, 21,
     21, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 24, 24, 25, 27, 28, 29, 34, 34],
    [0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7,
     8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 13, 13, 13,
     13, 13, 14, 14, 15, 15, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19,
     19, 19, 20, 20, 20, 21, 21, 21, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 24, 24, 25, 27, 30,
     30, 30, 30, 31, 31, 35],
    [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7,
     8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14,
     15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18,
     19, 19, 19, 20, 20, 21, 21, 22, 22, 22, 22, 23, 26, 26, 27, 28, 31, 32, 32, 32, 33, 33, 33,
     34, 34],
    [0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6,
     7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 12, 12, 12, 12, 12, 13, 13, 13,
     14, 14, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19,
     19, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 22, 22, 23, 23, 23, 23, 23, 23, 28, 29,
     32, 32, 33, 35, 35],
    [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 8, 8,
     8, 8, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14,
     14, 14, 14, 15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19,
     19, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 26, 26, 27,
     28, 31, 34, 34],
    [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7,
     7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11,
     11, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 14, 15, 15, 16, 16, 16, 17, 17, 18, 18, 18, 18,
     18, 18, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22,
     22, 22, 22, 23, 23, 23, 23, 28, 29, 30, 30, 30, 30, 31, 31, 34, 35],
    [0, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 8, 8, 8, 8, 8,
     8, 8, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13,
     14, 14, 14, 14, 15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 19, 19, 19, 19,
     19, 19, 19, 20, 20, 20, 20, 20, 21, 21, 22, 22, 22, 22, 22, 23, 28, 28, 29, 29, 30, 30, 31,
     34, 34, 35, 35],
    [0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7,
     7, 7, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 12, 12, 12, 13, 13,
     13, 13, 13, 13, 13, 14, 15, 15, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 19, 19, 19, 19,
     20, 20, 20, 20, 20, 21, 21, 21, 21, 22, 23, 23, 23, 26, 26, 26, 26, 27, 27, 28, 28, 31, 31,
     34],
    [0, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9,
     10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 12, 12, 12, 13, 13, 14, 14, 14, 15, 15, 15, 15, 15,
     15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 21, 21, 21,
     21, 21, 21, 22, 22, 22, 23, 23, 23, 23, 23, 23, 28, 28, 29, 29, 32, 33, 33, 35],
    [0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 5, 5, 5, 6, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 10,
     10, 10, 10, 10, 10, 11, 11, 11, 12, 12, 12, 12, 13, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15,
     15, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20,
     20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 26, 26,
     26, 26, 27, 27, 28, 28, 31, 31, 32, 32, 32, 33, 33, 33, 34],
    [0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 8, 8,
     8, 8, 9, 9, 9, 10, 10, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15,
     15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19,
     19, 20, 20, 20, 21, 21, 21, 22, 22, 23, 23, 23, 23, 24, 24, 24, 24, 25, 25, 27, 27, 30, 30,
     31, 35, 35],
    [0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7,
     7, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12,
     13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 18,
     18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 20, 20, 21, 21, 21, 21, 22, 23, 23, 23, 24,
     24, 24, 24, 25, 25, 27, 27, 28, 28, 29, 29, 34],
    [0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4, 4, 5, 5, 5, 6, 7, 7, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9,
     10, 10, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 14, 14, 14, 15,
     15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 19, 19,
     19, 19, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 23, 23, 23, 23, 25, 25, 29, 29, 32,
     33, 34],
    [0, 0, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4, 4, 4, 4, 5, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 10,
     10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 14, 14, 14, 14, 14, 15, 15, 15,
     15, 16, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20,
     20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26, 30, 30, 32, 35],
    [0, 2, 3, 5, 6, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 14,
     15, 16, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 21, 21, 21, 21, 21, 21, 22],
    [0, 1, 3, 4, 5, 6, 6, 6, 6, 6, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 14,
     17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 21, 21, 21, 21, 21, 21, 22, 23],
    [2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 12, 14, 15,
     16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 21, 21, 21, 21, 22],
    [2, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 12, 13,
     15, 17, 17, 17, 17, 17, 17, 18, 18, 18, 19, 19, 19, 20, 20, 21, 21, 21, 22, 23],
    [0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 12, 12,
     13, 14, 15, 15, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 21, 21,
     21, 22, 23],
    [0, 0, 1, 1, 3, 4, 5, 6, 6, 6, 6, 6, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 12, 12, 13, 14,
     15, 15, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 21, 21, 21, 21, 21, 21,
     23],
    [0, 1, 2, 3, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 13, 14, 16, 17,
     17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 21, 21, 21, 21, 21, 21, 22, 23],
    [0, 0, 1, 1, 3, 6, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 12, 13,
     14, 15, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 21, 21, 21, 21, 21,
     21, 22],
    [0, 2, 3, 4, 6, 6, 6, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 13, 13, 13,
     13, 14, 15, 15, 15, 17, 18, 19, 19, 19, 20, 20, 21, 21, 21, 23, 23],
    [0, 1, 3, 4, 5, 6, 6, 6, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 12, 12, 12, 13, 13,
     13, 14, 14, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 21, 22, 22,
     23, 23],
    [2, 3, 6, 6, 6, 7, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 12, 12, 12, 12, 13, 13, 13,
     13, 14, 15, 15, 15, 19, 19, 19, 19, 20, 20, 21, 21, 21, 23, 23],
    [2, 6, 6, 6, 6, 6, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 12, 12, 13, 13, 14, 14,
     14, 15, 15, 16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 19, 19, 21, 22, 22, 23, 23],
    [1, 2, 4, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 9, 9, 9, 9, 9, 9, 10, 11, 11, 11, 11, 15, 15,
     16, 17, 17, 17, 17, 17, 18, 18, 18, 19, 19, 19, 19, 19, 20, 20, 20, 21, 21, 21, 23, 23],
    [0, 2, 3, 5, 6, 6, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 10, 11, 11, 14, 14, 15, 15, 16, 17, 17,
     18, 18, 18, 18, 18, 19, 19, 19, 19, 21, 21, 21, 22, 22],
    [0, 1, 3, 4, 5, 6, 7, 7, 7, 8, 8, 8, 8, 10, 10, 10, 10, 11, 11, 14, 14, 17, 17, 17, 17, 18,
     18, 18, 19, 19, 19, 19, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 22, 23, 23],
    [1, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11,
     12, 12, 13, 13, 16, 17, 17, 17, 17, 18, 18, 18, 19, 19, 21, 21, 21, 21, 22, 23, 23, 23],
    [0, 1, 4, 4, 4, 5, 5, 5, 6, 6, 8, 8, 9, 9, 9, 10, 10, 11, 13, 13, 16, 16, 17, 17, 18, 18, 18,
     18, 18, 18, 19, 19, 19, 19, 19, 21, 21, 21, 21, 22, 22, 23, 23, 23],
    [2, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10,
     10, 11, 11, 12, 12, 13, 13, 15, 15, 17, 17, 17, 17, 18, 18, 19, 19, 19, 19, 20, 20, 20, 21,
     22, 23],
    [2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 9, 10, 10, 11, 12, 12, 14, 14, 15, 15,
     16, 16, 17, 17, 17, 17, 17, 18, 18, 19, 19, 21, 21, 22],
    [3, 4, 4, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10,
     11, 11, 11, 13, 13, 14, 14, 16, 16, 17, 18, 18, 18, 18, 18, 18, 19, 20, 20, 20, 21, 21, 21,
     21, 23],
    [0, 1, 2, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 9, 9, 9, 9, 11, 11, 11, 11, 12, 15, 15, 16, 17, 17,
     17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 20, 20, 21, 21, 21, 23, 23],
    [0, 1, 2, 3, 6, 7, 7, 8, 8, 8, 8, 10, 10, 11, 11, 13, 14, 14, 16, 17, 17, 17, 17, 17, 18, 18,
     18, 19, 19, 19, 19, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 22, 23, 23],
    [0, 0, 1, 1, 3, 6, 7, 7, 8, 8, 8, 8, 10, 10, 11, 11, 12, 13, 14, 14, 15, 15, 17, 17, 17, 18,
     18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 21, 21, 21, 22, 22],
    [0, 1, 2, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11,
     12, 12, 12, 13, 13, 14, 15, 15, 15, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19,
     20, 20, 21, 22, 23],
    [0, 1, 2, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 13, 13,
     13, 14, 14, 14, 16, 16, 16, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 20, 20, 21, 21, 21, 21,
     22],
    [0, 0, 1, 1, 3, 4, 4, 5, 5, 6, 6, 6, 8, 9, 9, 9, 10, 12, 12, 12, 13, 14, 14, 15, 15, 15, 16,
     16, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 19, 21, 21, 21, 23],
    [2, 2, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11,
     12, 12, 13, 13, 14, 15, 17, 17, 17, 17, 18, 18, 19, 19, 19, 20, 21, 21, 21, 21, 21, 21, 22,
     23, 23, 23],
    [2, 2, 3, 4, 4, 5, 5, 6, 6, 6, 8, 9, 9, 9, 10, 13, 13, 14, 16, 16, 17, 18, 18, 18, 18, 18,
     18, 19, 19, 19, 19, 19, 19, 19, 21, 21, 21, 21, 22, 22, 22, 23, 23],
    [0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 3, 3, 3, 5, 6, 6, 6, 6, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 12,
     12, 13, 13, 16, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 20, 21, 21, 21],
    [0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 5, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 9, 9, 10, 10, 10,
     13, 13, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 19, 19, 20, 21, 21],
    [0, 0, 0, 0, 1, 1, 1, 1, 2, 3, 3, 3, 6, 6, 6, 6, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11,
     12, 12, 13, 13, 15, 15, 17, 17, 18, 18, 18, 18, 19, 19, 19, 21, 21, 21, 21, 21, 21, 21, 22,
     23, 23],
    [0, 0, 1, 1, 2, 2, 2, 3, 3, 6, 6, 6, 7, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 12, 12,
     14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 21, 21, 21,
     21, 22, 22, 22, 23, 23, 23],
    [0, 1, 2, 2, 2, 3, 6, 6, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 10, 10, 12, 14, 15, 16, 17, 17, 17,
     17, 17, 18, 18, 18, 19, 19, 20, 20, 21, 21, 21, 21, 22, 22, 22, 23, 23, 23],
    [0, 0, 1, 1, 2, 2, 3, 3, 3, 6, 6, 6, 8, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 12, 13, 15,
     17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 21, 21, 21, 22, 22, 23],
    [0, 0, 0, 1, 1, 1, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 10, 10,
     10, 13, 16, 17, 17, 18, 18, 19, 19, 19, 19, 19, 20, 20, 21, 21],
    [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 3, 5, 5, 6, 6, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 12, 13, 16,
     16, 17, 17, 17, 17, 17, 18, 18, 18, 19, 19, 20, 21, 21, 21],
    [2, 2, 2, 2, 3, 3, 4, 5, 6, 6, 6, 6, 6, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 13, 14, 14,
     16, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 21, 22, 22, 22, 23],
    [2, 2, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 6, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11,
     12, 13, 14, 14, 15, 15, 17, 17, 17, 17, 17, 17, 18, 18, 18, 19, 19, 20, 20, 21, 21, 21, 21,
     21, 21, 22, 22, 23, 23, 23],
    [0, 0, 0, 0, 1, 1, 1, 1, 3, 3, 4, 5, 6, 6, 6, 6, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 12, 12,
     12, 13, 13, 14, 15, 15, 15, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 21, 21, 21, 21,
     21, 21, 21, 23, 23],
    [0, 0, 1, 1, 2, 2, 4, 5, 6, 6, 6, 7, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 11, 13, 13, 13, 14,
     14, 14, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 19, 19, 19, 19, 19, 19, 20, 21, 21, 21,
     21, 22, 22],
    [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10,
     11, 12, 12, 12, 13, 14, 14, 15, 15, 15, 16, 16, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 19,
     19, 19, 19, 19, 19, 20, 21, 21, 21, 21, 22, 22, 23, 23],
    [0, 0, 0, 0, 1, 1, 1, 1, 3, 3, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10,
     11, 12, 12, 13, 13, 14, 15, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 21, 21,
     21, 22],
    [0, 0, 1, 1, 2, 2, 3, 3, 6, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11,
     13, 13, 14, 16, 16, 17, 17, 17, 17, 17, 17, 18, 19, 19, 19, 20, 21, 21, 21, 22, 23],
    [0, 0, 1, 1, 2, 2, 6, 6, 6, 6, 6, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 10, 10, 11, 11, 12, 12, 15,
     16, 16, 17, 17, 18, 18, 18, 18, 18, 19, 19, 20, 20, 20, 21, 21, 21, 21, 21, 23],
    [3, 3, 4, 5, 6, 6, 6, 6, 6, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11,
     13, 14, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 21, 23, 23],
    [2, 2, 3, 3, 4, 5, 6, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 12,
     14, 15, 16, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 21, 21, 22, 22],
    [2, 2, 4, 4, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 11, 12, 13,
     15, 17, 17, 17, 17, 17, 17, 18, 18, 18, 19, 20, 20, 20, 21, 21, 21, 21, 22, 22, 23, 23],
    [0, 0, 1, 1, 4, 4, 4, 5, 5, 5, 6, 6, 6, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 11, 11, 13,
     16, 17, 17, 18, 18, 19, 19, 19, 21, 21, 21, 21, 22, 23, 23, 23],
    [1, 1, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 9, 10, 10, 10, 11, 12, 13, 16, 16,
     17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 21, 21, 22, 22, 23, 23, 23],
    [0, 0, 1, 1, 3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10,
     10, 10, 10, 10, 11, 14, 17, 18, 19, 19, 19, 19, 19, 19, 20, 20, 20, 21, 21, 21, 22, 23],
    [0, 0, 2, 2, 3, 3, 5, 5, 6, 6, 6, 6, 7, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10,
     11, 14, 15, 16, 16, 17, 17, 17, 18, 18, 19, 19, 19, 21, 21, 21, 22],
    [1, 1, 2, 2, 4, 4, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10,
     10, 11, 11, 15, 16, 16, 17, 17, 18, 18, 18, 19, 19, 20, 20, 20, 21, 21, 21, 21, 21, 23],
    [2, 2, 6, 6, 6, 8, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 12, 13, 14, 14, 14, 15, 16, 16,
     17, 17, 17, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 21, 21, 21, 21, 22, 23],
    [2, 2, 3, 3, 6, 6, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 10, 10, 12, 12, 13, 13, 14, 14, 15, 15, 15,
     17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 21, 21, 21, 21, 21, 23],
    [0, 0, 1, 1, 3, 3, 4, 4, 5, 5, 6, 6, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 11, 11, 12, 12, 12,
     13, 13, 13, 14, 15, 15, 15, 16, 16, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18,
     19, 19, 19, 21, 21, 21, 21, 22, 23],
    [0, 0, 2, 2, 3, 3, 4, 4, 6, 6, 6, 6, 6, 8, 8, 8, 9, 10, 10, 12, 12, 12, 12, 13, 13, 14, 14,
     15, 15, 15, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 20, 21, 21, 21, 21,
     21, 23]]

private def exhaustedExits : Fin 40 → List (Fin 36) :=
  ![
    [6, 8, 17, 18, 18, 19, 21, 21],
    [8, 17, 18, 18, 19, 21, 21],
    [6, 9, 10, 17, 19],
    [6, 8, 9, 17, 18, 19, 21],
    [8, 9, 10, 10, 17, 17, 18],
    [6, 8, 9, 10, 10, 17, 17, 18],
    [6, 8, 8, 10, 10, 17, 19, 21],
    [6, 8, 9, 10, 17, 19, 21],
    [9, 10, 17, 17, 18, 18, 21],
    [10, 17, 18, 19, 21],
    [6, 8, 9, 17, 18, 19, 21],
    [6, 9, 10, 17, 17, 18, 18, 21],
    [6, 9, 17, 18, 19],
    [8, 8, 10, 10, 17, 19, 21],
    [6, 8, 9, 10, 17, 19, 21],
    [8, 10, 17, 18, 19],
    [6, 8, 19, 19, 19, 19, 21, 21],
    [8, 19, 19, 19, 19, 21, 21],
    [9, 17, 17, 18, 18, 19, 19],
    [8, 10, 17, 17, 18, 18, 19, 19],
    [6, 6, 9, 9, 9, 18, 18, 18],
    [6, 6, 9, 9, 18, 18, 21],
    [9, 10, 17, 19, 19],
    [10, 17, 18, 19, 19, 21, 21],
    [6, 17, 17, 17, 19, 19, 19],
    [8, 10, 18, 18, 21],
    [6, 6, 9, 9, 9, 10, 10, 10],
    [6, 6, 8, 8, 9, 9, 10],
    [6, 8, 9, 10, 10],
    [6, 9, 9, 9, 10, 10, 10],
    [8, 8, 10, 10, 18, 21, 21],
    [6, 6, 17, 17, 17, 19, 19, 19],
    [10, 10, 17, 17, 18, 18, 19, 21],
    [9, 9, 10, 10, 17, 17, 19],
    [6, 9, 18, 21, 21],
    [6, 9, 9, 9, 18, 18, 18],
    [8, 8, 10, 10, 17, 18, 19],
    [9, 9, 17, 18, 19],
    [8, 8, 19, 19, 21],
    [6, 6, 8, 8, 19, 19, 21]]

private def activeWeight (i : Fin 72) : Fin 96 → ℕ :=
  fun j => Fin.append (fun k => (HardinA229585StripData.T i k).toNat)
    (fun k => (activeExits i).count k) (exitRead j)

private def exhaustedWeight (i : Fin 40) : Fin 96 → ℕ :=
  fun j => Fin.append (0 : Fin 72 → ℕ) (fun k => (exhaustedExits i).count k) (exitRead j)

private def exitsFromWeights (v : Fin 96 → ℕ) : List (Fin 96) :=
  (List.ofFn (fun j : Fin 96 => j)).flatMap fun j => List.replicate (v j) j

private theorem exitsFromWeights_count (v : Fin 96 → ℕ) (j : Fin 96) :
    (exitsFromWeights v).count j = v j := by
  rw [exitsFromWeights, List.count_flatMap, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, List.count_replicate, beq_iff_eq]
  simp

private def pushOld (i : Fin 56) (j : Fin 96) : ℤ :=
  Fin.append (fun k : Fin 56 => HardinA229585StripData.T (i.natAdd 16) (k.natAdd 16))
    (0 : Fin 40 → ℤ) j

def T : Matrix (Fin 168) (Fin 168) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 72 ⊕ Fin 96 ≃ Fin 168) finSumFinEquiv
    (Matrix.fromBlocks HardinA229585StripData.T
      (fun i j => (activeWeight i j : ℤ)) 0
      (Fin.append pushOld fun i j => (exhaustedWeight i j : ℤ)))

private def initialExhausted : Fin 96 → ℤ :=
  Fin.addCases (fun j : Fin 56 =>
    if j.castAdd 40 ∈ Finset.univ.image (oldZeroImage ∘ HardinA229585StripData.zeroBudgetClass)
      then 0 else 6)
    (fun _ : Fin 40 => 12)

def initial : Fin 168 → ℤ :=
  Fin.append HardinA229585StripData.initial initialExhausted

def terminal : Fin 168 → ℤ :=
  Fin.append (0 : Fin 72 → ℤ) (1 : Fin 96 → ℤ)

private theorem valid_shift (p : Boundary) (d : ℕ) (h : 0 < d) :
    Valid p d ↔ HardinA229585StripData.Valid p (d - 1) := by
  unfold Valid HardinA229585StripData.Valid
  have hsub : 1 - (d - 1) = 2 - d := by omega
  rw [hsub]
  exact and_congr_left (fun _ => by omega)

private theorem old_valid (p : Boundary) :
    Valid p 1 ↔ HardinA229585StripData.Valid p 0 :=
  valid_shift p 1 Nat.one_pos

private theorem cl_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  have hv : Valid (e ∘ p) 1 ↔ Valid p 1 := by
    simp only [Valid, Function.comp_apply, e.injective.eq_iff]
  simp only [cl, exhaustedClass, hv, pattern_relabel, HardinA229585Strip.class_relabel]

private theorem exhausted_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    exhaustedClass (e ∘ p) = exhaustedClass p := by
  simpa only [cl, if_pos rfl, Fin.natAdd_inj] using cl_relabel e p 0

private theorem blocks_disjoint {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≠ j.natAdd m :=
  finSumFinEquiv.injective.ne Sum.inl_ne_inr

private theorem active_cut (p : Boundary) (d c : ℕ) (j : Fin 72) :
    (c ≤ d ∧ cl p (d - c) = j.castAdd 96) ↔
      (0 < d ∧ c ≤ d - 1 ∧ HardinA229585StripData.cl p (d - 1 - c) = j) := by
  by_cases h : c < d
  · have hn : d - c ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt h)
    simp only [cl, hn, if_false, Fin.castAdd_inj, Nat.sub_right_comm d c 1]
    have hd : 0 < d := Nat.zero_lt_of_lt h
    have hc : c ≤ d - 1 := by omega
    simp [h.le, hd, hc]
  · have he : d - c = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
    have hb := (blocks_disjoint j (exhaustedClass p)).symm
    simp only [cl, he, if_pos rfl, hb, and_false, false_iff, not_and]
    omega

private theorem exhausted_cut (p : Boundary) (d c : ℕ) (j : Fin 96) :
    (c ≤ d ∧ cl p (d - c) = j.natAdd 72) ↔ (c = d ∧ exhaustedClass p = j) := by
  by_cases h : c < d
  · have hn : d - c ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt h)
    simp [cl, hn, blocks_disjoint, h.ne]
  · simp only [cl, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h), if_pos rfl, Fin.natAdd_inj]
    exact and_congr_left (fun _ => ⟨fun hc => hc.antisymm (Nat.le_of_not_gt h), Eq.le⟩)

private theorem next_valid (p : Boundary) (d : ℕ) (hp : Valid p d) (r : Row)
    (hr : cross p r + bondDefects horizontal r r ≤ d) :
    Valid (boundary r) (d - (cross p r + bondDefects horizontal r r)) := by
  refine ⟨(Nat.sub_le _ _).trans hp.1, ?_⟩
  have ht := HardinA229585StripCertificate.tail_bound r
  have hd := hp.1
  change _ ≤ 2 - (d - (cross p r + bondDefects horizontal r r))
  omega

private theorem initial_valid (r : Row) (hr : bondDefects horizontal r r ≤ 2) :
    Valid (boundary r) (2 - bondDefects horizontal r r) :=
  ⟨Nat.sub_le _ _, by
    rw [Nat.sub_sub_self hr]
    exact HardinA229585StripCertificate.tail_bound r⟩

private theorem terminal_eq (p : Boundary) (d : ℕ) :
    terminal (cl p d) = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0 <;> simp [cl, terminal, hd]

private theorem leading_counts (p : Boundary) (d : ℕ) (hp : Valid p d)
    (j : Fin 72) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = j.castAdd 96
      then (1 : ℤ) else 0) = T (cl p d) (j.castAdd 96) := by
  simp_rw [active_cut]
  by_cases hd : d = 0
  · simp [hd, T, cl, Matrix.reindex_apply, Matrix.fromBlocks_apply₂₁]
  · have hp' := (valid_shift p d (Nat.pos_of_ne_zero hd)).mp hp
    have h := HardinA229585Strip.finite_certificate.2.2.1 p
      ⟨d - 1, Nat.lt_succ_of_le hp'.1⟩ hp' j
    simpa [show 0 < d from Nat.pos_of_ne_zero hd, T, cl, hd, Matrix.reindex_apply,
      Matrix.fromBlocks_apply₁₁] using h

private theorem old_exhausted_counts (p : Boundary) (hp : Valid p 1) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = 0 ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p 0) (j.natAdd 72) := by
  have hp' := (old_valid p).mp hp
  have hcl : ∀ q, HardinA229585StripData.Valid q 0 →
      16 ≤ (HardinA229585StripData.cl q 0).val := by
    unfold HardinA229585StripData.Valid
    decide +kernel
  have he (r : Row) (h : cross p r + bondDefects horizontal r r = 0) :
      exhaustedClass (boundary r) =
        oldZeroImage (HardinA229585StripData.cl (boundary r) 0) := by
    have hv := HardinA229585Strip.finite_certificate.2.1 p 0 hp' r (Nat.le_of_eq h)
    simp only [Fin.val_zero, Nat.zero_sub] at hv
    simp [exhaustedClass, (old_valid _).mpr hv]
  have hinge (q : Boundary) (hq : HardinA229585StripData.Valid q 0) :
      oldZeroImage (HardinA229585StripData.cl q 0) =
        (Fin.subNat 16 (HardinA229585StripData.cl q 0) (hcl q hq)).castAdd 40 := by
    simp [oldZeroImage, hcl q hq]
  have hs (r : Row) (h : cross p r + bondDefects horizontal r r = 0) :
      HardinA229585StripData.Valid (boundary r) 0 := by
    simpa only [Fin.val_zero, Nat.zero_sub] using
      HardinA229585Strip.finite_certificate.2.1 p 0 hp' r (Nat.le_of_eq h)
  have hsource : (Fin.subNat 16 (HardinA229585StripData.cl p 0)
      (hcl p hp')).natAdd 16 = HardinA229585StripData.cl p 0 := by simp
  induction j using Fin.addCases (m := 56) (n := 40) with
  | left j =>
    conv_rhs =>
      simp only [T, cl, if_pos rfl, exhaustedClass, hp, oldZeroImage, hcl p hp',
        dif_pos, finSumFinEquiv_symm_apply_natAdd, Matrix.reindex_apply,
        Matrix.fromBlocks_apply₂₂, Fin.append_left, pushOld, hsource]
    have h := HardinA229585Strip.finite_certificate.2.2.1 p 0 hp' (j.natAdd 16)
    simp only [Fin.val_zero, Nat.le_zero, Nat.zero_sub] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : cross p r + bondDefects horizontal r r = 0
    · have heq : exhaustedClass (boundary r) = j.castAdd 40 ↔
          HardinA229585StripData.cl (boundary r) 0 = j.natAdd 16 := by
        rw [he r hr, hinge _ (hs r hr), Fin.castAdd_inj]
        constructor
        · intro hh
          simpa using congrArg (Fin.natAdd 16) hh
        · intro hh
          exact (Fin.natAdd_injective 56 16) (by simpa using hh)
      simp only [hr, true_and, heq]
    · simp [hr]
  | right j =>
    conv_rhs =>
      simp only [T, cl, if_pos rfl, exhaustedClass, hp, oldZeroImage, hcl p hp',
        dif_pos, finSumFinEquiv_symm_apply_natAdd, Matrix.reindex_apply,
        Matrix.fromBlocks_apply₂₂, Fin.append_left, pushOld, Fin.append_right, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : cross p r + bondDefects horizontal r r = 0
    · simp [hr, he r hr, hinge _ (hs r hr), blocks_disjoint]
    · simp [hr]

private def horizontalCost (r : Row) : ℕ :=
  (List.ofFn fun j : Fin 6 => if r j.castSucc = r j.succ then 1 else 0).sum

private theorem horizontalCost_eq (r : Row) :
    horizontalCost r = bondDefects horizontal r r := by
  simp only [horizontalCost, List.sum_ofFn, Finset.sum_boole, bondDefects, horizontal,
    Finset.filter_image]
  exact (Finset.card_image_of_injective _ fun i j h =>
    Fin.castSucc_injective 6 (congrArg Prod.fst h)).symm

private def rowCost (p : Boundary) (r : Row) : ℕ :=
  (List.ofFn fun j : Fin 6 => if p j = r j.castSucc then 1 else 0).sum + horizontalCost r

private theorem rowCost_eq (p : Boundary) (r : Row) :
    rowCost p r = cross p r + bondDefects horizontal r r := by
  simp only [rowCost, horizontalCost_eq, add_left_inj, List.sum_ofFn, Finset.sum_boole,
    cross, bondDefects, antidiagonal, Finset.filter_image, Fin.cons_succ]
  exact (Finset.card_image_of_injective _ fun i j h =>
    Fin.castSucc_injective 6 (congrArg Prod.snd h)).symm

private def exactExits (p : Boundary) (d : ℕ) : List (Fin 96) :=
  (((List.ofFn fun i : Fin 2187 => (finFunctionFinEquiv.symm i : Row)).filterMap
    fun r => if rowCost p r = d then some (exhaustedClass (boundary r)) else none)
    .insertionSort (· ≤ ·))

private theorem exactExits_count (p : Boundary) (d : ℕ) (j : Fin 96) :
    ((exactExits p d).count j : ℤ) =
      ∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
        exhaustedClass (boundary r) = j then 1 else 0 := by
  have h := D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge.count_successors
    (fun r : Row => rowCost p r = d) (fun r => exhaustedClass (boundary r)) j
  have h := congrArg (fun n : ℕ => (n : ℤ)) h
  simpa only [exactExits, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, rowCost_eq] using h

private theorem exactExits_active (p : Boundary) (d : Fin 3)
    (hp : Valid p d.val) (hn : Canonical p) (hd : d ≠ 0) :
    exactExits p d.val = exitsFromWeights
      (activeWeight (HardinA229585StripData.cl p (d.val - 1))) := by
  revert p d
  unfold Canonical
  decide +kernel

private theorem exactExits_new (p : Boundary)
    (hp : Valid p 0) (hn : Canonical p) (hnv : ¬ Valid p 1) :
    exactExits p 0 = exitsFromWeights
      (exhaustedWeight (Fin.ofNat 40 (newPatterns.idxOf (patternCode p)))) := by
  revert p
  unfold Canonical
  decide +kernel

private theorem class_counts_canonical (p : Boundary) (d : ℕ) (hp : Valid p d)
    (hn : Canonical p) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p d) (j.natAdd 72) := by
  by_cases hd : d = 0
  · subst d
    by_cases h : Valid p 1
    · exact old_exhausted_counts p h j
    · rw [← exactExits_count, exactExits_new p hp hn h, exitsFromWeights_count]
      simp only [T, cl, if_pos rfl, exhaustedClass, if_neg h,
        Matrix.reindex_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂,
        Fin.append_right]
  · rw [← exactExits_count]
    have he := exactExits_active p ⟨d, Nat.lt_succ_of_le hp.1⟩ hp hn
      (fun h => hd (congrArg Fin.val h))
    rw [he, exitsFromWeights_count]
    simp only [T, cl, if_neg hd, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]

private theorem class_counts (p : Boundary) (d : ℕ) (hp : Valid p d)
    (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p d) (j.natAdd 72) := by
  obtain ⟨q, ⟨hn, e, rfl⟩, _⟩ := canonical_exists_unique p
  have hv : Valid (e ∘ p) d := by
    simpa only [Valid, Function.comp_apply, e.injective.eq_iff] using hp
  have h := class_counts_canonical (e ∘ p) d hv hn j
  rw [← (Equiv.piCongrRight fun _ : Fin 7 => e).sum_comp] at h
  change (∑ r : Row, if cross (e ∘ p) (e ∘ r) + bondDefects horizontal (e ∘ r) (e ∘ r) = d ∧
    exhaustedClass (boundary (e ∘ r)) = j then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d) (j.natAdd 72) at h
  simpa only [HardinA229585Strip.cross_relabel, HardinA229585Strip.horizontal_relabel,
    show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
    exhausted_relabel, cl_relabel] using h

/-- Transfer multiplicities for both the positive and exhausted budgets. -/
theorem transition_counts (p : Boundary) (d : ℕ) (hp : Valid p d) (s : Fin 168) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  induction s using Fin.addCases (m := 72) (n := 96) with
  | left j => exact leading_counts p d hp j
  | right j =>
    simp_rw [exhausted_cut]
    exact class_counts p d hp j

private def initialExits : List (Fin 96) :=
  (((List.ofFn fun i : Fin 2187 => (finFunctionFinEquiv.symm i : Row)).filterMap
    fun r => if horizontalCost r = 2 then some (exhaustedClass (boundary r)) else none)
    .insertionSort (· ≤ ·))

private theorem initialExits_eq :
    initialExits = (List.finRange 96).flatMap fun j =>
      List.replicate (initialExhausted j).toNat j := by
  decide +kernel

private theorem initialExits_count (j : Fin 96) :
    (initialExits.count j : ℤ) = initialExhausted j := by
  rw [initialExits_eq]
  revert j
  decide +kernel

private theorem initial_counts (s : Fin 168) :
    (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s
      then (1 : ℤ) else 0) = initial s := by
  induction s using Fin.addCases (m := 72) (n := 96) with
  | left j =>
    simp_rw [active_cut]
    simpa only [show 0 < (2 : ℕ) by decide, true_and, Nat.reduceSub, initial,
      Fin.append_left] using HardinA229585Strip.finite_certificate.2.2.2.2.1 j
  | right j =>
    simp_rw [exhausted_cut]
    have h := D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge.count_successors
      (fun r : Row => horizontalCost r = 2) (fun r => exhaustedClass (boundary r)) j
    have h := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [← horizontalCost_eq, initial, Fin.append_right, ← initialExits_count j]
    simpa only [initialExits, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h.symm

/-- The exact two-defect labelled count as a matrix coefficient. -/
theorem count_transfer (n : ℕ) :
    (D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.literalCount
      (q := 3) horizontal antidiagonal 2 (n + 1) : ℤ) =
      dotProduct initial ((T ^ n).mulVec terminal) := by
  exact D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.lumped_count
    horizontal antidiagonal boundary cross Valid cl T initial terminal 2
    HardinA229585Strip.edge (fun p d _ => terminal_eq p d) next_valid
    transition_counts initial_valid initial_counts n

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
