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
Valid: proof_shape=bind-only; consumers=activeCover, activeCover._proof_1_1, cl_relabel, class_counts, class_counts_canonical, count_transfer, decidableValid, decidableValid._proof_1, exactExits_active, exactExits_new, exhaustedClass, exhaustedClass.eq_1, exhaustedCover, exhaustedCover._proof_1_1, initial_valid, leading_counts, next_valid, old_exhausted_counts, old_valid, transition_counts, valid_shift
decidableValid: proof_shape=bind-only; consumers=activeCover, activeCover._proof_1_1, cl_relabel, class_counts_canonical, exactExits_active, exactExits_new, exhaustedClass, exhaustedClass.eq_1, exhaustedCover, exhaustedCover._proof_1_1, old_exhausted_counts
patternCode: proof_shape=content; consumers=cl_relabel, class_counts_canonical, exactExits_new, exhaustedClass, exhaustedClass.eq_1, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1, old_exhausted_counts, pattern_relabel
pattern_relabel: proof_shape=content; consumers=cl_relabel
newPatterns: proof_shape=content; consumers=cl_relabel, class_counts_canonical, exactExits_new, exhaustedClass, exhaustedClass.eq_1, exhaustedCover, exhaustedCover._proof_1_1, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1, old_exhausted_counts
oldZeroImage: proof_shape=bind-only; consumers=cl_relabel, class_counts_canonical, exhaustedClass, exhaustedClass.eq_1, initialExhausted, initialExhausted.eq_1, initialExits_count, old_exhausted_counts
exhaustedClass: proof_shape=content; consumers=active_cut, cl, cl.eq_1, cl_relabel, class_counts, class_counts_canonical, exactExits_count, exhausted_cut, exhausted_relabel, exitCodes_bound, exitCodes_eq, initial_counts, initial_counts._simp_1_3, leading_counts, old_exhausted_counts, packedClass_all, packedClass_all._proof_1_1, packedClass_eq, terminal_eq, transition_counts, transition_counts._simp_1_1
cl: proof_shape=content; consumers=active_cut, cl_relabel, class_counts, class_counts_canonical, count_transfer, exhausted_cut, initial_counts, initial_counts._simp_1_1, initial_counts._simp_1_3, leading_counts, leading_counts._simp_1_1, old_exhausted_counts, terminal_eq, transition_counts, transition_counts._simp_1_1
exitRead: proof_shape=content; consumers=activeWeight, exhaustedWeight
activeExits: proof_shape=content; consumers=activeWeight
exhaustedExits: proof_shape=content; consumers=exhaustedWeight
activeWeight: proof_shape=content; consumers=T, T.eq_1, activeProfileCheck, activeProfileCheck.eq_1, class_counts_canonical, exactExits_active, leading_counts, old_exhausted_counts
exhaustedWeight: proof_shape=content; consumers=T, T.eq_1, class_counts_canonical, exactExits_new, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1, leading_counts, old_exhausted_counts
weightPack: proof_shape=bind-only; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, classPack_count, weightPack_injective, weightPack_injective._proof_1_2, weightPack_sum
weightPack_sum: proof_shape=bind-only; consumers=classPack_count
weightPack_injective: proof_shape=bind-only; consumers=checkHistogram_count
classPack: proof_shape=content; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, classPack_count
classPack_count: proof_shape=content; consumers=checkHistogram_count
pushOld: proof_shape=bind-only; consumers=T, T.eq_1, class_counts_canonical, leading_counts, old_exhausted_counts
T: proof_shape=content; consumers=class_counts, class_counts_canonical, count_transfer, leading_counts, old_exhausted_counts, transition_counts
initialExhausted: proof_shape=content; consumers=initial, initial.eq_1, initialExits_count, initialHistogram, initialHistogram._proof_1_1, initial_counts
initial: proof_shape=content; consumers=count_transfer, initial_counts
terminal: proof_shape=bind-only; consumers=count_transfer, terminal_eq
valid_shift: proof_shape=bind-only; consumers=leading_counts, old_valid
old_valid: proof_shape=bind-only; consumers=old_exhausted_counts
cl_relabel: proof_shape=content; consumers=class_counts, exhausted_relabel
exhausted_relabel: proof_shape=content; consumers=class_counts
blocks_disjoint: proof_shape=bind-only; consumers=active_cut, exhausted_cut, old_exhausted_counts
active_cut: proof_shape=bind-only; consumers=initial_counts._simp_1_1, leading_counts._simp_1_1
exhausted_cut: proof_shape=bind-only; consumers=initial_counts._simp_1_3, transition_counts._simp_1_1
next_valid: proof_shape=bind-only; consumers=count_transfer
initial_valid: proof_shape=bind-only; consumers=count_transfer
terminal_eq: proof_shape=bind-only; consumers=count_transfer
leading_counts: proof_shape=bind-only; consumers=transition_counts
old_exhausted_counts: proof_shape=bind-only; consumers=class_counts_canonical
horizontalCost: proof_shape=bind-only; consumers=completionCost_initial, completionCost_row, horizontalCost_eq, initial_counts, initial_counts._simp_1_4, rowCost, rowCost.eq_1, rowCost_eq
horizontalCost_eq: proof_shape=bind-only; consumers=initial_counts._simp_1_4, rowCost_eq
rowCost: proof_shape=bind-only; consumers=completionCost_row, exactExits_count, rowCost_eq
rowCost_eq: proof_shape=bind-only; consumers=exactExits_count
matchCost: proof_shape=content; consumers=completionCodes._f, completionCodes._sunfold, completionCodes._unsafe_rec, completionCodes.eq_1, completionCodes.eq_2, completionCodes.eq_def, completionCodes_eq, completionCost._f, completionCost._sunfold, completionCost._unsafe_rec, completionCost.eq_1, completionCost.eq_2, completionCost.eq_def, completionCost_initial, completionCost_row, completionRows._f, completionRows._sunfold, completionRows._unsafe_rec, completionRows.eq_1, completionRows.eq_2, completionRows.eq_def, completionRows_count, completionRows_count._proof_1_9
completionCost: proof_shape=content; consumers=completionCost_initial, completionCost_row, completionRows_count, completionRows_length_le, exactExits_count, initial_counts
completionRows: proof_shape=content; consumers=completionCodes_eq, completionRows_count, completionRows_length_le, exactExits_count, exitCodes_bound, exitCodes_eq, initial_counts
completionRows_count: proof_shape=content; consumers=completionRows_length_le, exactExits_count, initial_counts
completionCost_row: proof_shape=content; consumers=exactExits_count
completionCost_initial: proof_shape=content; consumers=initial_counts
completionCodes: proof_shape=content; consumers=completionCodes_eq, exitCodes, exitCodes.eq_1, exitCodes_eq
rowCode_cons: proof_shape=content; consumers=completionCodes_eq, rowCode_tail
completionCodes_eq: proof_shape=content; consumers=exitCodes_eq
rowCode_tail: proof_shape=content; consumers=exitCodes_eq
packedClass: proof_shape=content; consumers=exitCodes, exitCodes.eq_1, exitCodes_eq, packedClass_all, packedClass_all._proof_1_1, packedClass_eq
packedClass_all: proof_shape=content; consumers=packedClass_eq
packedClass_eq: proof_shape=content; consumers=exitCodes_eq
exitCodes: proof_shape=content; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, class_counts_canonical, exactExits_active, exactExits_count, exactExits_new, exitCodes_bound, exitCodes_eq, initialExits_count, initial_counts
exitCodes_eq: proof_shape=content; consumers=exactExits_count, exitCodes_bound, initial_counts
completionRows_length_le: proof_shape=content; consumers=exitCodes_bound
exitCodes_bound: proof_shape=content; consumers=checkHistogram_count
checkHistogram: proof_shape=content; consumers=activeProfileCheck, activeProfileCheck.eq_1, checkHistogram_count, exactExits_active, exactExits_new, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1, initialHistogram, initialHistogram._proof_1_1
checkHistogram_count: proof_shape=content; consumers=exactExits_active, exactExits_new, initialExits_count
exactExits_count: proof_shape=content; consumers=class_counts_canonical
activeGroups: proof_shape=content; consumers=activeBudgetOne, activeBudgetTwo, activeOneGroups, activeProfiles, activeTwoGroups
activeProfiles: proof_shape=content; consumers=activeBudgetOne, activeBudgetTwo, activeCheck, activeCover, activeCover._proof_1_1, exactExits_active
activeCover: proof_shape=content; consumers=exactExits_active
activeProfileCheck: proof_shape=content; consumers=activeBudgetOne, activeBudgetTwo, activeCheck, activeOneGroups, activeTwoGroups, exactExits_active
activeCheck: proof_shape=content; consumers=activeBudgetOne, activeBudgetTwo, activeMultiplicities
activeOneGroups: proof_shape=content; consumers=activeBudgetOne
activeBudgetOne: proof_shape=content; consumers=activeMultiplicities
activeTwoGroups: proof_shape=content; consumers=activeBudgetTwo
activeBudgetTwo: proof_shape=content; consumers=activeMultiplicities
activeMultiplicities: proof_shape=bind-only; consumers=exactExits_active
exhaustedCover: proof_shape=content; consumers=exactExits_new
exhaustedMultiplicities: proof_shape=content; consumers=exactExits_new
exactExits_active: proof_shape=content; consumers=class_counts_canonical
exactExits_new: proof_shape=content; consumers=class_counts_canonical
class_counts_canonical: proof_shape=content; consumers=class_counts
class_counts: proof_shape=content; consumers=transition_counts
transition_counts: proof_shape=content; consumers=count_transfer
initialHistogram: proof_shape=content; consumers=initialExits_count
initialExits_count: proof_shape=content; consumers=initial_counts
initial_counts: proof_shape=content; consumers=count_transfer
count_transfer: proof_shape=content; consumers=HardinA229693Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Data.Matrix.Block
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
  (Canonical canonical_exists_unique)
open HardinA229585StripData (Boundary Row horizontal antidiagonal boundary cross)

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

private def exitRead (i : Fin 96) : Fin 108 :=
  (#[72, 72, 73, 73, 74, 74, 75, 75, 76, 76, 77, 77, 29, 78, 78, 79, 79, 80, 80, 33, 37, 81, 81,
    82, 39, 82, 83, 83, 84, 84, 85, 85, 86, 86, 87, 87, 88, 88, 89, 54, 89, 90, 90, 57, 61, 91,
    91, 92, 92, 93, 93, 65, 94, 94, 95, 95, 96, 96, 97, 97, 98, 98, 16, 18, 99, 99, 100, 100,
    20, 22, 101, 101, 102, 102, 24, 26, 31, 42, 103, 103, 44, 46, 104, 104, 105, 105, 48, 50,
    106, 106, 52, 63, 68, 70, 107, 107] : Array (Fin 108))[i.val]

private def activeExits (i : Fin 72) (j : Fin 36) : ℕ :=
  let table : Array (Array ℕ) := #[
    #[4, 4, 4, 5, 4, 4, 3, 3, 2, 6, 4, 3, 4, 2, 3, 1, 4, 10, 3, 2, 6, 5, 3, 4, 1, 1, 1, 0, 0, 0, 1, 0, 2, 0, 0, 2],
    #[4, 4, 4, 3, 5, 5, 5, 4, 3, 4, 5, 4, 2, 5, 2, 5, 4, 3, 7, 5, 2, 2, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 2, 2, 2, 0],
    #[3, 4, 4, 5, 1, 0, 4, 4, 5, 5, 3, 4, 3, 2, 5, 2, 4, 5, 4, 3, 2, 7, 3, 7, 2, 1, 0, 1, 1, 1, 0, 0, 0, 0, 2, 0],
    #[5, 2, 5, 5, 2, 3, 3, 6, 4, 3, 8, 6, 1, 5, 2, 2, 3, 4, 8, 4, 3, 3, 6, 4, 2, 1, 0, 1, 0, 0, 4, 2, 0, 0, 0, 1],
    #[4, 4, 5, 3, 3, 4, 5, 3, 5, 4, 4, 2, 2, 4, 4, 5, 5, 6, 7, 3, 2, 2, 4, 1, 0, 0, 2, 1, 1, 0, 0, 1, 3, 3, 2, 0],
    #[5, 4, 4, 6, 3, 4, 5, 3, 5, 4, 4, 2, 5, 3, 2, 2, 4, 7, 4, 5, 6, 6, 2, 6, 0, 0, 0, 0, 1, 1, 0, 0, 2, 1, 0, 2],
    #[5, 5, 4, 4, 1, 0, 7, 3, 4, 7, 5, 2, 4, 4, 4, 2, 5, 3, 5, 6, 2, 7, 3, 7, 0, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 0],
    #[6, 4, 4, 6, 3, 3, 4, 4, 7, 5, 7, 6, 3, 7, 1, 2, 3, 2, 6, 7, 4, 7, 6, 4, 0, 0, 0, 0, 1, 1, 4, 2, 0, 0, 1, 1],
    #[1, 0, 4, 4, 5, 5, 5, 2, 7, 7, 3, 5, 4, 4, 4, 2, 5, 5, 3, 7, 5, 2, 5, 1, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 2, 2],
    #[3, 3, 3, 1, 6, 4, 10, 4, 6, 6, 4, 3, 3, 7, 1, 2, 3, 6, 2, 4, 5, 4, 1, 3, 0, 0, 4, 2, 2, 0, 0, 2, 0, 0, 1, 0],
    #[1, 0, 4, 4, 3, 4, 4, 5, 4, 2, 7, 3, 3, 2, 3, 6, 4, 4, 5, 4, 2, 6, 3, 6, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 0, 1],
    #[3, 3, 3, 1, 2, 4, 1, 4, 4, 4, 6, 3, 4, 1, 7, 4, 3, 4, 7, 6, 5, 7, 7, 4, 0, 0, 4, 2, 2, 0, 0, 2, 3, 3, 1, 0],
    #[5, 2, 3, 2, 3, 5, 3, 6, 4, 3, 2, 2, 3, 3, 6, 5, 5, 9, 4, 4, 3, 3, 2, 4, 4, 2, 0, 2, 0, 0, 2, 1, 0, 0, 0, 2],
    #[2, 4, 3, 6, 6, 4, 4, 3, 2, 5, 6, 7, 4, 3, 6, 5, 4, 4, 6, 7, 2, 4, 1, 3, 4, 2, 0, 2, 2, 2, 0, 0, 0, 0, 1, 0],
    #[3, 3, 4, 1, 3, 3, 1, 3, 6, 4, 2, 7, 4, 6, 3, 4, 4, 7, 7, 4, 2, 7, 3, 4, 0, 2, 0, 0, 0, 2, 0, 0, 1, 1, 1, 0],
    #[2, 6, 1, 2, 5, 1, 3, 5, 4, 0, 4, 5, 4, 3, 5, 4, 1, 7, 6, 4, 5, 4, 5, 2, 2, 2, 2, 0, 0, 0, 2, 0, 1, 0, 0, 1],
    #[1, 0, 1, 1, 0, 1, 6, 1, 5, 6, 4, 1, 0, 0, 1, 1, 1, 3, 5, 5, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 0, 1, 1, 1, 5, 2, 5, 4, 5, 1, 0, 0, 1, 0, 0, 3, 4, 6, 2, 6, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 1, 1, 1, 6, 0, 4, 6, 4, 1, 1, 0, 1, 1, 1, 4, 5, 4, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 0, 2, 2, 4, 2, 5, 4, 5, 1, 1, 1, 0, 1, 0, 6, 3, 3, 2, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 6, 1, 2, 1, 1, 2, 1, 5, 5, 5, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 1, 1, 1, 5, 0, 4, 5, 3, 0, 2, 1, 1, 2, 1, 5, 5, 4, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 1, 0, 0, 5, 1, 6, 4, 3, 1, 0, 1, 1, 0, 1, 5, 4, 5, 1, 6, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 1, 0, 0, 6, 1, 6, 4, 3, 1, 1, 1, 1, 1, 0, 3, 6, 6, 1, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 0, 1, 1, 1, 0, 3, 0, 3, 3, 5, 0, 5, 4, 1, 3, 0, 1, 1, 3, 2, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 0, 1, 1, 1, 3, 0, 5, 4, 4, 1, 3, 3, 2, 3, 4, 4, 4, 2, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 1, 0, 0, 3, 1, 4, 4, 5, 0, 4, 4, 1, 3, 0, 0, 0, 4, 2, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 0, 0, 0, 5, 0, 4, 5, 5, 1, 2, 2, 3, 2, 4, 2, 2, 4, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 1, 1, 0, 1, 0, 6, 5, 1, 6, 1, 4, 0, 0, 0, 2, 1, 5, 3, 5, 3, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 0, 1, 1, 0, 1, 2, 2, 4, 2, 3, 2, 0, 0, 2, 2, 1, 2, 5, 4, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 0, 1, 1, 1, 1, 3, 4, 0, 4, 2, 0, 0, 2, 0, 0, 4, 3, 4, 3, 7, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 1, 0, 0, 5, 4, 4, 2, 3, 4, 4, 2, 2, 2, 0, 0, 1, 4, 3, 2, 0, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 0, 0, 3, 3, 2, 0, 2, 3, 2, 1, 0, 2, 0, 0, 2, 2, 6, 5, 0, 4, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 0, 4, 4, 5, 3, 4, 5, 4, 2, 2, 2, 0, 2, 0, 4, 2, 4, 3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 1, 2, 2, 5, 0, 2, 5, 2, 1, 2, 0, 2, 2, 2, 5, 2, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 1, 2, 2, 3, 3, 7, 3, 7, 3, 0, 2, 2, 0, 2, 1, 6, 1, 3, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 0, 0, 0, 6, 4, 0, 4, 0, 4, 1, 0, 0, 2, 1, 5, 4, 5, 3, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 1, 0, 0, 1, 2, 4, 0, 2, 2, 0, 1, 2, 0, 1, 5, 3, 4, 2, 7, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 1, 0, 0, 1, 2, 4, 0, 2, 2, 1, 1, 2, 2, 0, 3, 6, 4, 1, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 1, 4, 4, 3, 2, 2, 4, 4, 2, 3, 2, 1, 3, 1, 4, 4, 5, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 0, 2, 2, 2, 2, 5, 3, 5, 2, 0, 3, 3, 0, 3, 2, 6, 2, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 1, 2, 2, 3, 0, 1, 3, 1, 0, 3, 1, 2, 3, 2, 7, 3, 1, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 1, 4, 4, 3, 2, 2, 4, 4, 2, 2, 2, 1, 1, 0, 4, 2, 3, 1, 6, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 1, 2, 2, 3, 0, 1, 3, 1, 0, 0, 2, 1, 0, 2, 1, 6, 7, 0, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[5, 4, 1, 3, 0, 1, 4, 0, 5, 4, 2, 0, 2, 2, 0, 0, 1, 3, 4, 5, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[3, 3, 2, 3, 1, 1, 5, 1, 5, 2, 3, 0, 0, 2, 0, 0, 2, 6, 2, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[4, 4, 1, 3, 0, 0, 4, 0, 3, 4, 5, 1, 2, 2, 0, 2, 0, 2, 4, 3, 0, 7, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 3, 2, 0, 0, 3, 1, 3, 5, 5, 0, 2, 0, 2, 2, 2, 2, 5, 6, 1, 4, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 3, 1, 0, 0, 2, 2, 5, 3, 2, 0, 1, 0, 1, 1, 1, 5, 3, 2, 2, 4, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 2, 3, 0, 0, 3, 0, 1, 3, 6, 2, 1, 1, 0, 1, 0, 3, 6, 1, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[3, 3, 1, 3, 2, 2, 5, 2, 2, 2, 5, 0, 0, 1, 0, 0, 1, 2, 2, 5, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[4, 2, 2, 3, 0, 2, 2, 0, 2, 6, 3, 0, 1, 1, 0, 0, 2, 5, 3, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 4, 2, 1, 1, 5, 0, 4, 5, 3, 0, 0, 1, 2, 0, 1, 3, 5, 4, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 4, 2, 2, 2, 3, 1, 3, 4, 6, 1, 1, 1, 2, 2, 0, 6, 3, 2, 2, 6, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[4, 4, 0, 2, 1, 1, 4, 0, 3, 4, 4, 0, 3, 2, 1, 3, 1, 4, 4, 3, 0, 7, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 2, 0, 1, 1, 3, 1, 3, 5, 3, 1, 0, 3, 3, 0, 3, 6, 2, 6, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 2, 2, 2, 2, 2, 1, 3, 4, 6, 1, 3, 1, 2, 3, 2, 3, 7, 6, 1, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[4, 4, 0, 2, 0, 0, 5, 1, 6, 4, 3, 1, 2, 2, 1, 1, 0, 2, 4, 6, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 2, 2, 0, 0, 6, 1, 6, 4, 3, 1, 0, 2, 1, 0, 2, 6, 1, 3, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 2, 0, 0, 0, 5, 2, 4, 2, 4, 2, 2, 0, 0, 1, 2, 2, 5, 2, 3, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 2, 1, 1, 5, 3, 4, 5, 4, 3, 0, 1, 1, 0, 1, 4, 5, 4, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 2, 1, 1, 5, 0, 2, 5, 6, 2, 1, 0, 1, 1, 1, 3, 5, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 0, 2, 2, 3, 3, 7, 3, 3, 1, 1, 1, 0, 1, 0, 6, 3, 1, 3, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 0, 3, 3, 3, 0, 6, 5, 2, 2, 0, 1, 0, 0, 1, 2, 2, 3, 0, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 2, 0, 0, 4, 2, 5, 1, 5, 1, 3, 1, 1, 1, 0, 0, 2, 3, 5, 3, 0, 2, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 2, 2, 2, 6, 3, 3, 4, 7, 1, 0, 0, 1, 0, 0, 1, 1, 6, 3, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 0, 2, 2, 0, 2, 4, 1, 3, 8, 5, 1, 0, 0, 1, 1, 2, 3, 2, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 2, 2, 0, 2, 0, 2, 4, 6, 6, 6, 2, 0, 0, 0, 1, 2, 2, 3, 2, 3, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 0, 0, 0, 3, 0, 1, 3, 6, 2, 1, 1, 3, 1, 2, 3, 3, 7, 0, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 2, 0, 0, 2, 2, 5, 3, 2, 0, 2, 2, 2, 3, 0, 4, 4, 5, 1, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 2, 2, 2, 2, 0, 6, 4, 1, 2, 3, 3, 1, 3, 2, 7, 7, 3, 0, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 0, 2, 2, 2, 0, 5, 0, 3, 1, 2, 0, 4, 2, 2, 3, 0, 6, 6, 3, 1, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  let row := table[i.val]!
  row[j.val]!


private def exhaustedExits (i : Fin 40) (j : Fin 36) : ℕ :=
  let table : Array (Array ℕ) := #[
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  let row := table[i.val]!
  row[j.val]!


private def activeWeight (i : Fin 72) : Fin 96 → ℕ :=
  fun j => Fin.append (fun k => (HardinA229585StripData.T i k).toNat)
    (activeExits i) (exitRead j)

private def exhaustedWeight (i : Fin 40) : Fin 96 → ℕ :=
  fun j => Fin.append (0 : Fin 72 → ℕ) (exhaustedExits i) (exitRead j)

private def weightPack {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  (List.ofFn f).foldr (fun a b => a + 4096 * b) 0

private theorem weightPack_sum {n : ℕ} (f : Fin n → ℕ) :
    weightPack f = ∑ i, f i * 4096 ^ i.val := by
  induction n with
  | zero => simp [weightPack]
  | succ n ih =>
    rw [weightPack, List.ofFn_succ, List.foldr_cons, ← weightPack, ih,
      Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ', Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl

private theorem weightPack_injective {n : ℕ} (f g : Fin n → ℕ)
    (hf : ∀ j, f j < 4096) (hg : ∀ j, g j < 4096) (h : weightPack f = weightPack g) :
    f = g := by
  induction n with
  | zero => exact funext fun j => j.elim0
  | succ n ih =>
    simp only [weightPack, List.ofFn_succ, List.foldr_cons] at h
    change f 0 + 4096 * weightPack (Fin.tail f) =
      g 0 + 4096 * weightPack (Fin.tail g) at h
    have h0 := congrArg (· % 4096) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0),
      Nat.mod_eq_of_lt (hg 0)] at h0
    have ht := ih (Fin.tail f) (Fin.tail g) (fun j => hf j.succ) (fun j => hg j.succ)
      (by omega)
    funext j
    refine Fin.cases h0 (fun k => congrFun ht k) j

private def classPack {n : ℕ} (xs : List (Fin n)) : ℕ :=
  (xs.map fun j => 4096 ^ j.val).sum

private theorem classPack_count {n : ℕ} (xs : List (Fin n)) :
    classPack xs = weightPack (fun j => xs.count j) := by
  induction xs with
  | nil => simp [classPack, weightPack_sum]
  | cons x xs ih =>
    change 4096 ^ x.val + classPack xs = _
    rw [ih]
    simp only [weightPack_sum, List.count_cons, beq_iff_eq, Nat.add_mul,
      Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    simp [eq_comm, Nat.add_comm]

private def pushOld (i : Fin 56) (j : Fin 96) : ℤ :=
  Fin.append (fun k : Fin 56 => HardinA229585StripData.T (i.natAdd 16) (k.natAdd 16))
    (0 : Fin 40 → ℤ) j

def T : Matrix (Fin 168) (Fin 168) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 72 ⊕ Fin 96 ≃ Fin 168) finSumFinEquiv
    (Matrix.fromBlocks HardinA229585StripData.T
      (Matrix.of fun i j => (activeWeight i j : ℤ)) 0
      (Matrix.of (Fin.append pushOld fun i j => (exhaustedWeight i j : ℤ))))

private def initialExhausted (i : Fin 96) : ℤ :=
  Fin.addCases (fun j : Fin 56 =>
    if j.castAdd 40 ∈ Finset.univ.image (oldZeroImage ∘ HardinA229585StripData.zeroBudgetClass)
      then 0 else 6)
    (fun _ : Fin 40 => 12) i

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
    exhaustedClass (e ∘ p) = exhaustedClass p :=
  Fin.natAdd_injective 96 72 (cl_relabel e p 0)

private theorem blocks_disjoint {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≠ j.natAdd m :=
  finSumFinEquiv.injective.ne Sum.inl_ne_inr

private theorem active_cut (p : Boundary) (d c : ℕ) (j : Fin 72) :
    (c ≤ d ∧ cl p (d - c) = j.castAdd 96) ↔
      (0 < d ∧ c ≤ d - 1 ∧ HardinA229585StripData.cl p (d - 1 - c) = j) := by
  by_cases h : c < d
  · have hn : d - c ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt h)
    simp only [cl, hn, ↓reduceIte, Nat.sub_right_comm d c 1]
    have hd : 0 < d := Nat.zero_lt_of_lt h
    have hc : c ≤ d - 1 := by omega
    simp only [h.le, hd, hc, true_and]
    exact Fin.castAdd_inj
  · have he : d - c = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
    have hb := (blocks_disjoint j (exhaustedClass p)).symm
    simp only [cl, he, ↓reduceIte, hb, and_false, false_iff, not_and]
    omega

private theorem exhausted_cut (p : Boundary) (d c : ℕ) (j : Fin 96) :
    (c ≤ d ∧ cl p (d - c) = j.natAdd 72) ↔ (c = d ∧ exhaustedClass p = j) := by
  by_cases h : c < d
  · have hn : d - c ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt h)
    simp [cl, hn, blocks_disjoint (HardinA229585StripData.cl p (d - c - 1)) j, h.ne]
  · simp only [cl, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h), ↓reduceIte]
    rw [Fin.natAdd_inj 72]
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
  · subst d
    simp only [Nat.lt_irrefl, false_and, ite_false, Finset.sum_const_zero]
    change 0 = T ((exhaustedClass p).natAdd 72) (j.castAdd 96)
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have hd' := Nat.pos_of_ne_zero hd
    have hp' := (valid_shift p d hd').mp hp
    simp only [hd', true_and]
    simp only [cl, ite_eq_right hd, T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
    exact HardinA229585Strip.finite_certificate.2.2.1 p
      ⟨d - 1, Nat.lt_succ_of_le hp'.1⟩ hp' j

private theorem old_exhausted_counts (p : Boundary) (hp : Valid p 1) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = 0 ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p 0) (j.natAdd 72) := by
  have hp' := (old_valid p).mp hp
  have ht : ∀ i : Fin 72, HardinA229585StripData.terminal i =
      (if i.val < 16 then 0 else 1) := by
    decide +kernel
  have hcl (q : Boundary) (hq : HardinA229585StripData.Valid q 0) :
      16 ≤ (HardinA229585StripData.cl q 0).val := by
    have hz := HardinA229585Strip.finite_certificate.1 q (0 : Fin 2) hq
    change HardinA229585StripData.terminal (HardinA229585StripData.cl q 0) = 1 at hz
    by_contra h
    have hh := ht (HardinA229585StripData.cl q 0)
    rw [ite_eq_left (Nat.lt_of_not_ge h)] at hh
    exact zero_ne_one (hh.symm.trans hz)
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
      (hcl p hp')).natAdd 16 = HardinA229585StripData.cl p 0 :=
    Fin.natAdd_subNat_cast (n := 16) (m := 56) (hcl p hp')
  induction j using Fin.addCases (m := 56) (n := 40) with
  | left j =>
    conv_rhs =>
      simp only [T, cl, ↓reduceIte, exhaustedClass, hp, oldZeroImage, hcl p hp',
        dite_eq_left, finSumFinEquiv_symm_apply_natAdd, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Fin.append_left, pushOld, hsource]
    have h := HardinA229585Strip.finite_certificate.2.2.1 p 0 hp' (j.natAdd 16)
    simp only [Fin.val_zero, Nat.le_zero, Nat.zero_sub] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : cross p r + bondDefects horizontal r r = 0
    · have heq : exhaustedClass (boundary r) = j.castAdd 40 ↔
          HardinA229585StripData.cl (boundary r) 0 = j.natAdd 16 := by
        rw [he r hr, hinge _ (hs r hr), Fin.castAdd_inj]
        have hi : (Fin.subNat 16 (HardinA229585StripData.cl (boundary r) 0)
            (hcl _ (hs r hr))).natAdd 16 = HardinA229585StripData.cl (boundary r) 0 :=
          Fin.natAdd_subNat_cast (n := 16) (m := 56) (hcl _ (hs r hr))
        rw [← Fin.natAdd_inj 16, hi]
      simp only [hr, true_and, heq]
    · simp only [hr, false_and, ite_false]
  | right j =>
    conv_rhs =>
      simp only [T, cl, ↓reduceIte, exhaustedClass, hp, oldZeroImage, hcl p hp',
        dite_eq_left, finSumFinEquiv_symm_apply_natAdd, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Fin.append_left, pushOld, Fin.append_right, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : cross p r + bondDefects horizontal r r = 0
    · have hb := blocks_disjoint
        (Fin.subNat 16 (HardinA229585StripData.cl (boundary r) 0) (hcl _ (hs r hr))) j
      simp only [hr, true_and, he r hr, hinge _ (hs r hr), hb, ite_false]
    · simp only [hr, false_and, ite_false]

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

private def matchCost : Option (Fin 3) → Fin 3 → ℕ
  | none, _ => 0
  | some p, x => if p = x then 1 else 0

private def completionCost : {k : ℕ} → (Fin k → Option (Fin 3)) → Option (Fin 3) →
    (Fin (k + 1) → Fin 3) → ℕ
  | 0, _, prev, r => matchCost prev (r 0)
  | _k + 1, p, prev, r =>
    matchCost prev (r 0) + matchCost (p 0) (r 0) +
      completionCost (Fin.tail p) (some (r 0)) (Fin.tail r)

private def completionRows : {k : ℕ} → (Fin k → Option (Fin 3)) → Option (Fin 3) →
    ℕ → List (Fin (k + 1) → Fin 3)
  | 0, _, prev, d =>
    ((List.finRange 3).filter fun x => matchCost prev x == d).map fun x _ => x
  | _k + 1, p, prev, d => (List.finRange 3).flatMap fun x =>
    let c := matchCost prev x + matchCost (p 0) x
    if c ≤ d then (completionRows (Fin.tail p) (some x) (d - c)).map (Fin.cons x) else []

private theorem completionRows_count {k : ℕ} (p : Fin k → Option (Fin 3))
    (prev : Option (Fin 3)) (d : ℕ) (f : (Fin (k + 1) → Fin 3) → Bool) :
    (completionRows p prev d).countP f =
      ∑ r, if completionCost p prev r = d ∧ f r = true then 1 else 0 := by
  induction k generalizing prev d with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) (Fin 3)).symm.sum_comp]
    simp only [completionCost, completionRows, List.countP_map, List.countP_filter,
      Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply, Fin.sum_univ_three]
    change ([(0 : Fin 3), 1, 2].countP
      (fun x => f (fun _ => x) && (matchCost prev x == d))) =
      (if matchCost prev 0 = d ∧ f (fun _ => 0) = true then 1 else 0) +
      (if matchCost prev 1 = d ∧ f (fun _ => 1) = true then 1 else 0) +
      (if matchCost prev 2 = d ∧ f (fun _ => 2) = true then 1 else 0)
    simp only [List.countP_cons, List.countP_nil, Bool.and_eq_true, beq_iff_eq, and_comm]
    omega
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin 3)).sum_comp, Fintype.sum_prod_type]
    simp only [completionRows, List.countP_flatMap, ← List.ofFn_id,
      List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]
    apply Finset.sum_congr rfl
    intro x _
    let c := matchCost prev x + matchCost (p 0) x
    change (if c ≤ d then (completionRows (Fin.tail p) (some x) (d - c)).map (Fin.cons x)
      else []).countP f = _
    split_ifs with hc
    · rw [List.countP_map, ih]
      apply Finset.sum_congr rfl
      intro r _
      change (if completionCost (Fin.tail p) (some x) r = d - c ∧ f (Fin.cons x r) = true
        then 1 else 0) = (if c + completionCost (Fin.tail p) (some x) r = d ∧
        f (Fin.cons x r) = true then 1 else 0)
      have he : completionCost (Fin.tail p) (some x) r = d - c ↔
          c + completionCost (Fin.tail p) (some x) r = d :=
        eq_comm.trans ((Nat.sub_eq_iff_eq_add' hc).trans eq_comm)
      simp only [he]
    · simp only [List.countP_nil]
      symm
      apply Finset.sum_eq_zero
      intro r _
      change (if c + completionCost (Fin.tail p) (some x) r = d ∧ f (Fin.cons x r) = true
        then 1 else 0) = 0
      apply ite_eq_right
      intro h
      exact hc (h.1 ▸ Nat.le_add_right c _)

private theorem completionCost_row (p : Boundary) (r : Row) :
    completionCost (some ∘ p) none r = rowCost p r := by
  simp only [completionCost, matchCost, Fin.tail, Function.comp_apply, zero_add, Fin.castSucc_zero, Fin.castSucc_succ, rowCost, horizontalCost, List.ofFn_succ, List.ofFn_zero,
    List.sum_cons, List.sum_nil]
  ac_rfl

private theorem completionCost_initial (r : Row) :
    completionCost (fun _ : Fin 6 => none) none r = horizontalCost r := by
  simp only [completionCost, matchCost, Fin.tail, add_zero, zero_add, Fin.castSucc_zero, Fin.castSucc_succ,
    horizontalCost, List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil]
  rfl

private def completionCodes : List (Option (Fin 3)) → Option (Fin 3) → ℕ → List ℕ
  | [], prev, d =>
    ((List.finRange 3).filter fun x => matchCost prev x == d).map Fin.val
  | a :: as, prev, d => (List.finRange 3).flatMap fun x =>
    let c := matchCost prev x + matchCost a x
    if c ≤ d then (completionCodes as (some x) (d - c)).map (fun r => x.val + 3 * r)
    else []

private theorem rowCode_cons {k : ℕ} (x : Fin 3) (r : Fin k → Fin 3) :
    (finFunctionFinEquiv (Fin.cons x r)).val = x.val + 3 * (finFunctionFinEquiv r).val := by
  simp only [finFunctionFinEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

private theorem completionCodes_eq {k : ℕ} (p : Fin k → Option (Fin 3))
    (prev : Option (Fin 3)) (d : ℕ) :
    completionCodes (List.ofFn p) prev d =
      (completionRows p prev d).map (fun r => (finFunctionFinEquiv r).val) := by
  induction k generalizing prev d with
  | zero =>
    simp only [List.ofFn_zero, completionCodes, completionRows, List.map_map]
    apply List.map_congr_left
    intro x _
    change x.val = (finFunctionFinEquiv (fun _ : Fin 1 => x)).val
    simp only [finFunctionFinEquiv_apply, Fin.sum_univ_one, Fin.val_zero, pow_zero, mul_one]
  | succ k ih =>
    simp only [List.ofFn_succ, completionCodes, completionRows, List.map_flatMap]
    apply List.flatMap_congr
    intro x _
    split_ifs
    · simp only [show (fun i => p i.succ) = Fin.tail p from rfl, ih, List.map_map]
      apply List.map_congr_left
      intro r _
      exact (rowCode_cons x r).symm
    · rfl

private theorem rowCode_tail (r : Row) :
    (finFunctionFinEquiv (boundary r)).val = (finFunctionFinEquiv r).val / 3 := by
  have h := rowCode_cons (r 0) (boundary r)
  rw [show Fin.cons (r 0) (boundary r) = r from Fin.cons_self_tail r] at h
  have hb := (r 0).isLt
  omega

private def packedClass (i : ℕ) : Fin 96 :=
  Fin.ofNat 96 ((631614627661551089507037924218425714181766582700302798335294774353035012103669334343882498299797517482778717833240785354081841445867758355654705238740956489384272353271925295040101201519626782324308261045702564636867222402643809756911723775426193733058666040802422222883400075404366663632442620079012971170961285382545873962737476626297879390944083601786736677734027780386166316420955515047640886042463979085669706615501372613396788312422325379924603492404172148376952083974087938285673937238627488927937971419895343525287584306247862132598410739904614597120703652442692949138388165144657052550217565074527064894897706351856002807565685973836632258139348908379307605636465526259608721022366832792165479652712969423720395860924969949797959571905273079510397410289147760792853287994033429179151168731035746442502610220164877666819421544299336998862895946880122242076871683973281681379347106525709827939713289232160210887407831946516103156420731249239151304833073813004719029008720575744857113722837226419707976404869235531456443785022671936056343393190662211330799582932738636512871880281000226456190879720927118747493412034056543193234357534181099348594802434827546508548940164773917712386255123898264309585209278611823616361638142422055803311502805331264790481728463137283432021167833288760992048882347322060907904523686844769641993174873016262741733720910168515464793360097529033560099291578211344211954648872547568265373137702578720632703059280249225823855484263234905503166072969885683406834163968560745262221749469043350066281978936 >>> (7 * i)) % 128)

-- Check the packed readout at every boundary code.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem packedClass_all :
    (List.finRange 729).all (fun i =>
      packedClass i.val == exhaustedClass ((finFunctionFinEquiv (m := 3) (n := 6)).symm i)) = true := by
  decide +kernel

private theorem packedClass_eq (p : Boundary) :
    packedClass (finFunctionFinEquiv p).val = exhaustedClass p := by
  have h := List.all_eq_true.mp packedClass_all (finFunctionFinEquiv p) (List.mem_finRange _)
  simpa only [beq_iff_eq, Equiv.symm_apply_apply] using h

private def exitCodes {k : ℕ} (p : Fin k → Option (Fin 3)) (d : ℕ) :
    List (Fin 96) :=
  ((completionCodes (List.ofFn p) none d).map fun r => packedClass (r / 3))

private theorem exitCodes_eq (p : Fin 6 → Option (Fin 3)) (d : ℕ) :
    exitCodes p d =
      (completionRows p none d).map (fun r => exhaustedClass (boundary r)) := by
  rw [exitCodes, completionCodes_eq, List.map_map]
  apply List.map_congr_left
  intro r _
  change packedClass ((finFunctionFinEquiv r).val / 3) = exhaustedClass (boundary r)
  rw [← rowCode_tail r, packedClass_eq]

private theorem completionRows_length_le (p : Fin 6 → Option (Fin 3)) (d : ℕ) :
    (completionRows p none d).length ≤ 2187 := by
  rw [← List.countP_true]
  have h := completionRows_count p none d (fun _ => true)
  rw [h]
  calc
    _ ≤ ∑ _ : Row, (1 : ℕ) := Finset.sum_le_sum fun i _ => by split_ifs <;> decide
    _ = 2187 := by simp [Row, Fintype.card_fun]

private theorem exitCodes_bound (p : Fin 6 → Option (Fin 3)) (d : ℕ)
    (j : Fin 96) : (exitCodes p d).count j < 4096 := by
  apply lt_of_le_of_lt List.count_le_length
  rw [exitCodes_eq, List.length_map]
  exact (completionRows_length_le p d).trans_lt (by decide)

private def checkHistogram (p : Fin 6 → Option (Fin 3)) (d : ℕ)
    (weights : Fin 96 → ℕ) : Bool :=
  (classPack (exitCodes p d) == weightPack weights) &&
    (List.finRange 96).all (fun i => weights i < 4096)

private theorem checkHistogram_count (p : Fin 6 → Option (Fin 3)) (d : ℕ)
    (weights : Fin 96 → ℕ) (h : checkHistogram p d weights = true) (j : Fin 96) :
    (exitCodes p d).count j = weights j := by
  simp only [checkHistogram, Bool.and_eq_true, beq_iff_eq, classPack_count] at h
  exact congrFun (weightPack_injective _ _ (exitCodes_bound p d) (fun i =>
    of_decide_eq_true (List.all_eq_true.mp h.2 i (List.mem_finRange i))) h.1) j

private theorem exactExits_count (p : Boundary) (d : ℕ) (j : Fin 96) :
    ((exitCodes (some ∘ p) d).count j : ℤ) =
      ∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
        exhaustedClass (boundary r) = j then 1 else 0 := by
  rw [exitCodes_eq, List.count_eq_countP, List.countP_map]
  change ((completionRows (some ∘ p) none d).countP
    (fun r => exhaustedClass (boundary r) == j) : ℤ) = _
  exact_mod_cast (by
    simpa only [completionCost_row, rowCost_eq, beq_iff_eq] using
      completionRows_count (some ∘ p) none d (fun r => exhaustedClass (boundary r) == j) :
    _ = ∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℕ) else 0)

private def activeGroups : Fin 3 → List (List (Fin 729 × Fin 72)) :=
  ![[],
    [[(90, 16), (576, 17), (171, 18), (414, 19)],
      [(306, 20), (549, 21), (144, 22), (630, 23)],
      [(84, 24), (570, 25), (165, 26), (408, 27)],
      [(30, 28), (273, 29), (516, 30), (111, 31)],
      [(597, 32), (192, 33), (435, 34), (678, 35)],
      [(57, 36), (300, 37), (543, 38), (138, 39)],
      [(381, 40), (624, 41), (219, 42), (462, 43)],
      [(93, 44), (579, 45), (174, 46), (417, 47)],
      [(309, 48), (552, 49), (147, 50), (633, 51)],
      [(264, 52), (507, 53), (102, 54), (345, 55)],
      [(588, 56), (183, 57), (426, 58), (669, 59)],
      [(48, 60), (291, 61), (534, 62), (129, 63)],
      [(615, 64), (210, 65), (453, 66), (696, 67)],
      [(318, 68), (561, 69), (156, 70), (642, 71)]],
    [[(273, 0), (516, 1), (192, 2), (435, 3)],
      [(300, 4), (543, 5), (138, 6), (624, 7)],
      [(102, 8), (588, 9), (183, 10), (426, 11)],
      [(291, 12), (534, 13), (210, 14), (453, 15)]]]

private def activeProfiles (d : Fin 3) : List (Fin 729 × Fin 72) :=
  (activeGroups d).flatten

-- Cover every valid canonical input by its boundary code and its inherited class.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem activeCover :
    (List.finRange 3).all (fun d => (List.finRange 729).all fun i =>
      let p : Boundary := (finFunctionFinEquiv (m := 3) (n := 6)).symm i
      letI : Decidable (Canonical p) := by unfold Canonical; infer_instance
      if Valid p d.val ∧ Canonical p ∧ d ≠ 0 then
        (activeProfiles d).contains (i, HardinA229585StripData.cl p (d.val - 1))
      else true) = true := by
  decide +kernel

private def activeProfileCheck (d : Fin 3) (entry : Fin 729 × Fin 72) : Bool :=
  checkHistogram (some ∘ (finFunctionFinEquiv (m := 3) (n := 6)).symm entry.1)
    d.val (activeWeight entry.2)

private def activeCheck (d : Fin 3) : Bool :=
  (activeProfiles d).all (activeProfileCheck d)

-- Each case normalizes at most four profiles with the same finite kernel check.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem activeOneGroups (i : Fin 14) :
    ((activeGroups 1)[i.val]!).all (activeProfileCheck 1) = true := by
  fin_cases i <;> decide +kernel

private theorem activeBudgetOne : activeCheck 1 = true := by
  unfold activeCheck activeProfiles
  rw [List.all_flatten]
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  have hlt : i < 14 := hi
  simpa only [getElem!_pos (activeGroups 1) i hi] using activeOneGroups ⟨i, hlt⟩

-- Each case normalizes at most four profiles with the same finite kernel check.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem activeTwoGroups (i : Fin 4) :
    ((activeGroups 2)[i.val]!).all (activeProfileCheck 2) = true := by
  fin_cases i <;> decide +kernel

private theorem activeBudgetTwo : activeCheck 2 = true := by
  unfold activeCheck activeProfiles
  rw [List.all_flatten]
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  have hlt : i < 4 := hi
  simpa only [getElem!_pos (activeGroups 2) i hi] using activeTwoGroups ⟨i, hlt⟩

private theorem activeMultiplicities (d : Fin 3) : activeCheck d = true := by
  fin_cases d
  · rfl
  · exact activeBudgetOne
  · exact activeBudgetTwo

-- Exhausted sources outside the inherited sectors have one of the new codes.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem exhaustedCover :
    (List.finRange 729).all (fun i =>
      let p : Boundary := (finFunctionFinEquiv (m := 3) (n := 6)).symm i
      letI : Decidable (Canonical p) := by unfold Canonical; infer_instance
      if Valid p 0 ∧ Canonical p ∧ ¬ Valid p 1 then
        newPatterns.contains i
      else true) = true := by
  decide +kernel

-- The finite calculation generates exactly the zero-cost successors of each new code.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem exhaustedMultiplicities :
    newPatterns.all (fun i =>
      let p : Boundary := (finFunctionFinEquiv (m := 3) (n := 6)).symm i
      checkHistogram (some ∘ p) 0
        (exhaustedWeight (Fin.ofNat 40 (newPatterns.idxOf (patternCode p))))) =
        true := by
  decide +kernel

private theorem exactExits_active (p : Boundary) (d : Fin 3)
    (hp : Valid p d.val) (hn : Canonical p) (hd : d ≠ 0) (j : Fin 96) :
    (exitCodes (some ∘ p) d.val).count j =
      activeWeight (HardinA229585StripData.cl p (d.val - 1)) j := by
  let i : Fin 729 := finFunctionFinEquiv p
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp activeCover d (List.mem_finRange d)) i (List.mem_finRange i)
  have he : (finFunctionFinEquiv (m := 3) (n := 6)).symm i = p := finFunctionFinEquiv.symm_apply_apply p
  have hv : Valid ((finFunctionFinEquiv (m := 3) (n := 6)).symm i) d.val ∧
      Canonical ((finFunctionFinEquiv (m := 3) (n := 6)).symm i) ∧ d ≠ 0 := by rw [he]; exact ⟨hp, hn, hd⟩
  dsimp only at h
  rw [ite_eq_left hv] at h
  have hm : (i, HardinA229585StripData.cl p (d.val - 1)) ∈ activeProfiles d := by
    simpa only [List.contains_iff_mem, he] using h
  have hs := List.all_eq_true.mp
    (activeMultiplicities d) _ hm
  exact checkHistogram_count _ _ _ (by simpa only [activeProfileCheck, Prod.fst, Prod.snd, he] using hs) j

private theorem exactExits_new (p : Boundary)
    (hp : Valid p 0) (hn : Canonical p) (hnv : ¬ Valid p 1) (j : Fin 96) :
    (exitCodes (some ∘ p) 0).count j =
      exhaustedWeight (Fin.ofNat 40 (newPatterns.idxOf (patternCode p))) j := by
  let i : Fin 729 := finFunctionFinEquiv p
  have h := List.all_eq_true.mp exhaustedCover i (List.mem_finRange i)
  have he : (finFunctionFinEquiv (m := 3) (n := 6)).symm i = p := finFunctionFinEquiv.symm_apply_apply p
  have hv : Valid ((finFunctionFinEquiv (m := 3) (n := 6)).symm i) 0 ∧
      Canonical ((finFunctionFinEquiv (m := 3) (n := 6)).symm i) ∧ ¬ Valid ((finFunctionFinEquiv (m := 3) (n := 6)).symm i) 1 :=
    by rw [he]; exact ⟨hp, hn, hnv⟩
  dsimp only at h
  rw [ite_eq_left hv] at h
  have hm : i ∈ newPatterns := List.contains_iff_mem.mp h
  have hs := List.all_eq_true.mp exhaustedMultiplicities i hm
  exact checkHistogram_count _ _ _ (by simpa only [he] using hs) j

private theorem class_counts_canonical (p : Boundary) (d : ℕ) (hp : Valid p d)
    (hn : Canonical p) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p d) (j.natAdd 72) := by
  by_cases hd : d = 0
  · subst d
    by_cases h : Valid p 1
    · exact old_exhausted_counts p h j
    · rw [← exactExits_count, exactExits_new p hp hn h j]
      simp only [T, cl, ↓reduceIte, exhaustedClass, ite_eq_right h,
        Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
        Fin.append_right]
  · rw [← exactExits_count]
    have he := exactExits_active p ⟨d, Nat.lt_succ_of_le hp.1⟩ hp hn
      (fun h => hd (congrArg Fin.val h)) j
    rw [he]
    simp only [T, cl, ite_eq_right hd, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]

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

-- The histogram compares the first rows with exactly two horizontal defects.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem initialHistogram :
    checkHistogram (fun _ : Fin 6 => none) 2 (fun j => (initialExhausted j).toNat) = true := by
  decide +kernel

private theorem initialExits_count (j : Fin 96) :
    ((exitCodes (fun _ : Fin 6 => none) 2).count j : ℤ) = initialExhausted j := by
  rw [checkHistogram_count _ _ _ initialHistogram, Int.toNat_of_nonneg]
  induction j using Fin.addCases (m := 56) (n := 40) with
  | left j => simp only [initialExhausted, Fin.addCases_left]; split_ifs <;> norm_num
  | right j => simp [initialExhausted]

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
    simp only [← horizontalCost_eq, initial, Fin.append_right, ← initialExits_count j]
    symm
    rw [exitCodes_eq, List.count_eq_countP, List.countP_map]
    simp only [Function.comp_def]
    exact_mod_cast (by
      simpa only [completionCost_initial, Function.comp_apply, beq_iff_eq] using
        completionRows_count (fun _ : Fin 6 => none) none 2
          (fun r => exhaustedClass (boundary r) == j) :
      _ = ∑ r : Row, if horizontalCost r = 2 ∧ exhaustedClass (boundary r) = j
        then (1 : ℕ) else 0)

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
