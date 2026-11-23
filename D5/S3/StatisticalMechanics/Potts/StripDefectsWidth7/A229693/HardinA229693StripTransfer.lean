/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts,D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.initial_counts
   digest: Exact successor multiplicities into the exhausted budget. -/

/-
admission_basis: escape-witness
escape_witness: exactExits_active and exactExits_new compute the multiplicities of transitions reaching budget zero
Valid: proof_shape=bind-only; consumers=activeCover, activeCover._proof_1_1, cl_relabel, class_counts, class_counts_canonical, count_transfer, decidableValid, decidableValid._proof_1, exactExits_active, exactExits_new, exhaustedClass, exhaustedClass.eq_1, exhaustedCover, exhaustedCover._proof_1_1, initial_valid, leading_counts, next_valid, old_exhausted_counts, old_valid, transition_counts, valid_shift
tailCost_eq: proof_shape=bind-only; consumers=valid_shift, next_valid, initial_valid
valid_parts: proof_shape=bind-only; consumers=class_counts_canonical
valid_relabel: proof_shape=bind-only; consumers=class_counts, cl_relabel
fresh_relabel: proof_shape=bind-only; consumers=cl_relabel
rep_partition: proof_shape=bind-only; consumers=exactExits_active, exactExits_new
decidableValid: proof_shape=bind-only; consumers=activeCover, activeCover._proof_1_1, cl_relabel, class_counts_canonical, exactExits_active, exactExits_new, exhaustedClass, exhaustedClass.eq_1, exhaustedCover, exhaustedCover._proof_1_1, old_exhausted_counts
oldZeroImage: proof_shape=bind-only; consumers=cl_relabel, class_counts_canonical, exhaustedClass, exhaustedClass.eq_1, initialExhausted, initialExhausted.eq_1, initialExits_count, old_exhausted_counts
exhaustedClass: proof_shape=content; consumers=active_cut, cl, cl.eq_1, cl_relabel, class_counts, class_counts_canonical, exactExits_count, exhausted_cut, exhausted_relabel, exitCodes_bound, exitCodes_eq, initial_counts, initial_counts._simp_1_3, leading_counts, old_exhausted_counts, packedClass_all, packedClass_all._proof_1_1, packedClass_eq, terminal_eq, transition_counts, transition_counts._simp_1_1
cl: proof_shape=content; consumers=active_cut, cl_relabel, class_counts, class_counts_canonical, count_transfer, exhausted_cut, initial_counts, initial_counts._simp_1_1, initial_counts._simp_1_3, leading_counts, leading_counts._simp_1_1, old_exhausted_counts, terminal_eq, transition_counts, transition_counts._simp_1_1
exitRead: proof_shape=content; consumers=activeWeight, exhaustedWeight
oldExits: proof_shape=bind-only; consumers=activeWeight, T, old_exhausted_row
oldTerminal: proof_shape=bind-only; consumers=oldDestination
oldDestination: proof_shape=bind-only; consumers=old_exhausted_row, old_exhausted_counts, class_counts_canonical
old_exhausted_row: proof_shape=bind-only; consumers=old_exhausted_counts, class_counts_canonical
activeExits: proof_shape=content; consumers=activeWeight
exhaustedExits: proof_shape=content; consumers=exhaustedWeight
activeWeight: proof_shape=content; consumers=T, T.eq_1, activeProfileCheck, activeProfileCheck.eq_1, class_counts_canonical, exactExits_active, leading_counts, old_exhausted_counts
exhaustedWeight: proof_shape=content; consumers=T, T.eq_1, class_counts_canonical, exactExits_new, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1, leading_counts, old_exhausted_counts
weightPack: proof_shape=bind-only; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, classPack_count, weightPack_injective, weightPack_injective._proof_1_2, weightPack_sum
weightPack_sum: proof_shape=bind-only; consumers=classPack_count
weightPack_injective: proof_shape=bind-only; consumers=checkHistogram_count
classPack: proof_shape=bind-only; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, classPack_count
classPack_count: proof_shape=bind-only; consumers=checkHistogram_count
T: proof_shape=content; consumers=class_counts, class_counts_canonical, count_transfer, leading_counts, old_exhausted_counts, transition_counts
initialExhausted: proof_shape=content; consumers=initial, initial.eq_1, initialExits_count, initialHistogram, initialHistogram._proof_1_1, initial_counts
initial: proof_shape=content; consumers=count_transfer, initial_counts
terminal: proof_shape=bind-only; consumers=count_transfer, terminal_eq
valid_shift: proof_shape=bind-only; consumers=leading_counts, old_valid
old_valid: proof_shape=bind-only; consumers=old_exhausted_counts
cl_relabel: proof_shape=bind-only; consumers=class_counts, exhausted_relabel
exhausted_relabel: proof_shape=bind-only; consumers=class_counts
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
matchCost: proof_shape=bind-only; consumers=completionCodes._f, completionCodes._sunfold, completionCodes._unsafe_rec, completionCodes.eq_1, completionCodes.eq_2, completionCodes.eq_def, completionCodes_eq, completionCost._f, completionCost._sunfold, completionCost._unsafe_rec, completionCost.eq_1, completionCost.eq_2, completionCost.eq_def, completionCost_initial, completionCost_row, completionRows._f, completionRows._sunfold, completionRows._unsafe_rec, completionRows.eq_1, completionRows.eq_2, completionRows.eq_def, completionRows_count, completionRows_count._proof_1_9
completionCost: proof_shape=content; consumers=completionCost_initial, completionCost_row, completionRows_count, completionRows_length_le, exactExits_count, initial_counts
completionRows: proof_shape=content; consumers=completionCodes_eq, completionRows_count, completionRows_length_le, exactExits_count, exitCodes_bound, exitCodes_eq, initial_counts
completionRows_count: proof_shape=content; consumers=completionRows_length_le, exactExits_count, initial_counts
completionCost_row: proof_shape=bind-only; consumers=exactExits_count
completionCodes: proof_shape=content; consumers=completionCodes_eq, exitCodes, exitCodes.eq_1, exitCodes_eq
rowCode_cons: proof_shape=bind-only; consumers=completionCodes_eq, rowCode_tail
completionCodes_eq: proof_shape=content; consumers=exitCodes_eq
rowCode_tail: proof_shape=bind-only; consumers=exitCodes_eq
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
inheritedSource: proof_shape=bind-only; consumers=T
newSources: proof_shape=bind-only; consumers=activeWeight
activeGroups: proof_shape=content; consumers=activeMultiplicities
activeMultiplicities: proof_shape=content; consumers=exactExits_active
inheritedActiveCheck: proof_shape=bind-only; consumers=inheritedActiveCheck_all
inheritedActiveCheck_all: proof_shape=bind-only; consumers=inherited_active_spec
inherited_active_spec: proof_shape=bind-only; consumers=class_counts_canonical
activeProfileCheck: proof_shape=content; consumers=activeBudgetOne, activeCheck, activeOneGroups, exactExits_active
exhaustedMultiplicities: proof_shape=content; consumers=exactExits_new
exactExits_active: proof_shape=content; consumers=class_counts_canonical
exactExits_new: proof_shape=content; consumers=class_counts_canonical
class_counts_canonical: proof_shape=content; consumers=class_counts
class_counts: proof_shape=content; consumers=transition_counts
transition_counts: proof_shape=content; consumers=count_transfer
horizontal_cons: proof_shape=bind-only; consumers=head_weight_eq
headWeight: proof_shape=bind-only; consumers=head_weight_eq
head_weight_eq: proof_shape=bind-only; consumers=initial_exhausted_count
fresh_start_count: proof_shape=bind-only; consumers=initial_exhausted_count
rep_weight: proof_shape=bind-only; consumers=initial_exhausted_count
initial_from_starts: proof_shape=bind-only; consumers=initial_exhausted_count
initial_exhausted_count: proof_shape=bind-only; consumers=initial_counts
initial_counts: proof_shape=content; consumers=count_transfer
count_transfer: proof_shape=content; consumers=HardinA229693Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Starts
import Mathlib.Tactic.Eval
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
  (Canonical canonical_exists_unique)
open HardinA229585StripData (Boundary Row horizontal antidiagonal boundary cross)
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (relabel_defects)

def Valid (p : Boundary) (d : ℕ) : Prop :=
  HardinA229635State.Valid p d

private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (HardinA229635State.h p + d ≤ 2))

private theorem valid_parts (p : Boundary) (d : ℕ) :
    Valid p d ↔ d ≤ 2 ∧ HardinA229635State.h p ≤ 2 - d := by
  change HardinA229635State.h p + d ≤ 2 ↔ _
  omega

private theorem tailCost_eq (p : Boundary) :
    HardinA229635State.h p =
      (Finset.univ.filter fun j : Fin 5 => p j.castSucc = p j.succ).card := by
  simp only [HardinA229635State.h, bondDefects,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.horizontal,
    Finset.filter_image]
  exact Finset.card_image_of_injective _ fun i j h =>
    Fin.castSucc_injective 5 (congrArg Prod.fst h)

private theorem valid_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    Valid (e ∘ p) d ↔ Valid p d := by
  simp only [Valid, HardinA229635State.Valid, HardinA229635State.h_relabel]

private theorem fresh_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    HardinA229635State.fresh (e ∘ p) = HardinA229635State.fresh p := by
  apply Fin.natAdd_injective 96 31
  simpa only [HardinA229635State.cl, show ∀ n : ℕ, ¬ n + 3 ≤ 1 from fun _ => by omega,
    ite_false] using HardinA229635State.cl_relabel e p 3

private def oldZeroImage (i : Fin 72) : Fin 96 :=
  if h : 16 ≤ i.val then (Fin.subNat 16 i h).castAdd 40 else 0

def exhaustedClass (p : Boundary) : Fin 96 :=
  if Valid p 1 then oldZeroImage (HardinA229585StripData.cl p 0)
  else (Fin.ofNat 40 (HardinA229635State.fresh p).val).natAdd 56

def cl (p : Boundary) (d : ℕ) : Fin 168 :=
  if d = 0 then (exhaustedClass p).natAdd 72 else
    (HardinA229585StripData.cl p (d - 1)).castAdd 96

def exitRead (i : Fin 96) : Fin 108 :=
  (#[72, 72, 73, 73, 74, 74, 75, 75, 76, 76, 77, 77, 29, 78, 78, 79, 79, 80, 80, 33, 37, 81, 81,
    82, 39, 82, 83, 83, 84, 84, 85, 85, 86, 86, 87, 87, 88, 88, 89, 54, 89, 90, 90, 57, 61, 91,
    91, 92, 92, 93, 93, 65, 94, 94, 95, 95, 96, 96, 97, 97, 98, 98, 16, 18, 99, 99, 100, 100,
    20, 22, 101, 101, 102, 102, 24, 26, 31, 42, 103, 103, 44, 46, 104, 104, 105, 105, 48, 50,
    106, 106, 52, 63, 68, 70, 107, 107] : Array (Fin 108))[i.val]

private def inheritedSource (i : Fin 72) : Option (Fin 16) :=
  (List.finRange 16).find? fun k => HardinA229585StripData.zeroBudgetClass k == i

private def newSources : List (Fin 72) :=
  (List.finRange 72).filter fun i => (inheritedSource i).isNone

private def activeExits (i : ℕ) (j : Fin 36) : ℕ :=
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
    #[0, 1, 0, 0, 5, 4, 4, 2, 3, 4, 4, 2, 2, 2, 0, 0, 1, 4, 3, 2, 0, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 0, 0, 3, 3, 2, 0, 2, 3, 2, 1, 0, 2, 0, 0, 2, 2, 6, 5, 0, 4, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 1, 2, 2, 3, 3, 7, 3, 7, 3, 0, 2, 2, 0, 2, 1, 6, 1, 3, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 0, 0, 0, 6, 4, 0, 4, 0, 4, 1, 0, 0, 2, 1, 5, 4, 5, 3, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 0, 2, 2, 2, 2, 5, 3, 5, 2, 0, 3, 3, 0, 3, 2, 6, 2, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
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
    #[2, 2, 2, 0, 1, 1, 3, 1, 3, 5, 3, 1, 0, 3, 3, 0, 3, 6, 2, 6, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 2, 0, 0, 0, 5, 2, 4, 2, 4, 2, 2, 0, 0, 1, 2, 2, 5, 2, 3, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 2, 1, 1, 5, 3, 4, 5, 4, 3, 0, 1, 1, 0, 1, 4, 5, 4, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 0, 3, 3, 3, 0, 6, 5, 2, 2, 0, 1, 0, 0, 1, 2, 2, 3, 0, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 2, 0, 0, 4, 2, 5, 1, 5, 1, 3, 1, 1, 1, 0, 0, 2, 3, 5, 3, 0, 2, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 2, 2, 0, 2, 0, 2, 4, 6, 6, 6, 2, 0, 0, 0, 1, 2, 2, 3, 2, 3, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 0, 0, 0, 3, 0, 1, 3, 6, 2, 1, 1, 3, 1, 2, 3, 3, 7, 0, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 2, 2, 0, 0, 2, 2, 5, 3, 2, 0, 2, 2, 2, 3, 0, 4, 4, 5, 1, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 2, 2, 2, 2, 0, 6, 4, 1, 2, 3, 3, 1, 3, 2, 7, 7, 3, 0, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 0, 2, 2, 2, 0, 5, 0, 3, 1, 2, 0, 4, 2, 2, 3, 0, 6, 6, 3, 1, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  let row := table[i]!
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


private def oldExits (i : Fin 72) (j : Fin 96) : ℤ :=
  Fin.append (fun k : Fin 56 => HardinA229585StripData.T i (k.natAdd 16))
    (0 : Fin 40 → ℤ) j

private def activeWeight (i : Fin 72) : Fin 96 → ℕ :=
  fun j => Fin.append (fun k => (HardinA229585StripData.T i k).toNat)
    (activeExits (newSources.idxOf i)) (exitRead j)

private def exhaustedWeight (i : Fin 40) : Fin 96 → ℕ :=
  fun j => Fin.append (0 : Fin 72 → ℕ) (exhaustedExits i) (exitRead j)

private def weightPack {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  Nat.ofDigits 4096 (List.ofFn f)

private theorem weightPack_sum {n : ℕ} (f : Fin n → ℕ) :
    weightPack f = ∑ i, f i * 4096 ^ i.val := by
  simp only [weightPack, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
    List.sum_ofFn, List.get_ofFn, List.length_ofFn, Fin.cast_refl, Nat.cast_id]
  rfl

private theorem weightPack_injective {n : ℕ} (f g : Fin n → ℕ)
    (hf : ∀ j, f j < 4096) (hg : ∀ j, g j < 4096) (h : weightPack f = weightPack g) :
    f = g := by
  change Nat.ofDigits 4096 (List.ofFn f) = Nat.ofDigits 4096 (List.ofFn g) at h
  apply List.ofFn_inj.mp
  exact Nat.ofDigits_inj_of_len_eq (by decide) (by simp) (by simpa using hf)
    (by simpa using hg) h

private def classPack {n : ℕ} (xs : List (Fin n)) : ℕ :=
  (xs.map fun j => 4096 ^ j.val).sum

private theorem classPack_count {n : ℕ} (xs : List (Fin n)) :
    classPack xs = weightPack (fun j => xs.count j) := by
  rw [classPack, weightPack_sum, Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    simp only [List.count_eq_zero_of_not_mem (fun hm => hi (List.mem_toFinset.mpr hm)),
      Nat.cast_zero, zero_mul]

def T : Matrix (Fin 168) (Fin 168) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 72 ⊕ Fin 96 ≃ Fin 168) finSumFinEquiv
    (Matrix.fromBlocks HardinA229585StripData.T
      (Matrix.of fun i j => match inheritedSource i with
        | some k => oldExits (k.castAdd 56) j
        | none => (activeWeight i j : ℤ)) 0
      (Matrix.of (Fin.append (fun i : Fin 56 => oldExits (i.natAdd 16)) fun i j => (exhaustedWeight i j : ℤ))))

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
  rw [valid_parts]
  unfold HardinA229585StripData.Valid
  rw [tailCost_eq]
  omega

private theorem old_valid (p : Boundary) :
    Valid p 1 ↔ HardinA229585StripData.Valid p 0 :=
  valid_shift p 1 Nat.one_pos

private theorem cl_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, exhaustedClass, valid_relabel, fresh_relabel, HardinA229585Strip.class_relabel]

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
  have hd := ((valid_parts p d).mp hp).1
  have ht := HardinA229585StripCertificate.tail_bound r
  rw [← tailCost_eq] at ht
  change HardinA229635State.h (boundary r) + (d - (cross p r + bondDefects horizontal r r)) ≤ 2
  omega

private theorem initial_valid (r : Row) (hr : bondDefects horizontal r r ≤ 2) :
    Valid (boundary r) (2 - bondDefects horizontal r r) := by
  have ht := HardinA229585StripCertificate.tail_bound r
  rw [← tailCost_eq] at ht
  change HardinA229635State.h (boundary r) + (2 - bondDefects horizontal r r) ≤ 2
  omega

private theorem terminal_eq (p : Boundary) (d : ℕ) :
    terminal (cl p d) = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0 <;> simp [cl, terminal, hd]

private theorem leading_counts (p : Boundary) (d : ℕ) (j : Fin 72)
    (hp : Valid p d ∨ d = 0) :
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
    have hp' := (valid_shift p d hd').mp (hp.resolve_right hd)
    simp only [hd', true_and]
    simp only [cl, ite_eq_right hd, T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
    exact HardinA229585Strip.finite_certificate.2.2.1 p
      ⟨d - 1, Nat.lt_succ_of_le hp'.1⟩ hp' j

private theorem oldTerminal (i : Fin 72) :
    HardinA229585StripData.terminal i = (if i.val < 16 then 0 else 1) := by
  revert i
  decide +kernel

private theorem oldDestination (p : Boundary) (d : Fin 2)
    (hp : HardinA229585StripData.Valid p d.val) :
    (HardinA229585StripData.cl p d.val).val < 16 ↔ d.val ≠ 0 := by
  have h := HardinA229585Strip.finite_certificate.1 p d hp
  rw [oldTerminal] at h
  split_ifs at h with hi hd hd <;> simp_all

private theorem old_exhausted_row (p : Boundary) (d : Fin 2)
    (hp : HardinA229585StripData.Valid p d.val) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = d.val ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    oldExits (HardinA229585StripData.cl p d.val) j := by
  let cost (r : Row) := cross p r + bondDefects horizontal r r
  have valid (r : Row) (hr : cost r ≤ d.val) :=
    HardinA229585Strip.finite_certificate.2.1 p d hp r hr
  have class_eq (r : Row) (hr : cost r = d.val) :
      ∃ k : Fin 56, exhaustedClass (boundary r) = k.castAdd 40 ∧
        HardinA229585StripData.cl (boundary r) 0 = k.natAdd 16 := by
    have hv := valid r hr.le
    change HardinA229585StripData.Valid (boundary r) (d.val - cost r) at hv
    rw [hr, Nat.sub_self] at hv
    have hh : 16 ≤ (HardinA229585StripData.cl (boundary r) 0).val :=
      Nat.le_of_not_gt fun h => (oldDestination _ 0 hv).mp h rfl
    refine ⟨Fin.subNat 16 _ hh, ?_, (Fin.natAdd_subNat_cast (n := 16) (m := 56) hh).symm⟩
    simp only [exhaustedClass, (old_valid _).mpr hv, ite_true, oldZeroImage, hh, dite_true]
  induction j using Fin.addCases (m := 56) (n := 40) with
  | left j =>
    rw [oldExits, Fin.append_left, ← HardinA229585Strip.finite_certificate.2.2.1 p d hp (j.natAdd 16)]
    apply Finset.sum_congr rfl
    intro r _
    change (if cost r = d.val ∧ _ then (1 : ℤ) else 0) =
      (if cost r ≤ d.val ∧ _ then (1 : ℤ) else 0)
    by_cases hr : cost r = d.val
    · obtain ⟨k, hk, hk'⟩ := class_eq r hr
      have hz : d.val - (cross p r + bondDefects horizontal r r) = 0 := Nat.sub_eq_zero_of_le hr.ge
      simp only [hr, le_refl, hz, true_and, hk, hk']
      by_cases h : k = j
      · subst j
        simp
      · simp only [(Fin.castAdd_injective 56 40).ne h,
          (Fin.natAdd_injective 56 16).ne h, ite_false]
    · by_cases hl : cost r ≤ d.val
      · have hn := Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne hl hr))
        let b : Fin 2 := ⟨d.val - cost r, (Nat.sub_le _ _).trans_lt d.isLt⟩
        have hboundary : (HardinA229585StripData.cl (boundary r) b.val).val < 16 :=
          (oldDestination _ b (valid r hl)).mpr hn
        have hne : HardinA229585StripData.cl (boundary r) (d.val - cost r) ≠ j.natAdd 16 := by
          intro he
          change (HardinA229585StripData.cl (boundary r) (d.val - cost r)).val < 16 at hboundary
          rw [he, Fin.val_natAdd] at hboundary
          omega
        change HardinA229585StripData.cl (boundary r)
          (d.val - (cross p r + bondDefects horizontal r r)) ≠ j.natAdd 16 at hne
        simp only [hr, false_and, hl, hne, and_false, ite_false]
      · simp only [hr, hl, false_and, ite_false]
  | right j =>
    simp only [oldExits, Fin.append_right, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro r _
    change (if cost r = d.val ∧ _ then (1 : ℤ) else 0) = 0
    by_cases hr : cost r = d.val
    · obtain ⟨k, hk, _⟩ := class_eq r hr
      simp only [hr, hk, blocks_disjoint k j, and_false, ite_false]
    · simp only [hr, false_and, ite_false]

private theorem old_exhausted_counts (p : Boundary) (hp : Valid p 1) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = 0 ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p 0) (j.natAdd 72) := by
  have hv := (old_valid p).mp hp
  have hh : 16 ≤ (HardinA229585StripData.cl p 0).val :=
    Nat.le_of_not_gt fun h => (oldDestination p 0 hv).mp h rfl
  conv_rhs =>
    simp only [T, cl, ↓reduceIte, exhaustedClass, hp, oldZeroImage, hh, dite_true,
      finSumFinEquiv_symm_apply_natAdd, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Fin.append_left]
  have h : (Fin.subNat 16 (HardinA229585StripData.cl p 0) hh).natAdd 16 =
      HardinA229585StripData.cl p 0 := Fin.ext (Nat.add_sub_of_le hh)
  rw [h]
  exact old_exhausted_row p 0 hv j

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
  let packed : ℕ := eval% Nat.ofDigits 128
    (List.ofFn fun i => (exhaustedClass (HardinA229635State.rowEquiv i)).val)
  Fin.ofNat 96 ((packed >>> (7 * i)) % 128)

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

private theorem rep_partition (i : Fin 96) :
    HardinA229635State.h (HardinA229635State.rep i) ≤ 1 ↔ 40 ≤ i.val := by
  revert i
  decide +kernel

private def activeProfileCheck (d : Fin 2) (i : Fin 96) : Bool :=
  let p := HardinA229635State.rep i
  let k := HardinA229585StripData.cl p d.val
  if (inheritedSource k).isNone && decide (Valid p (d.val + 1)) then
    checkHistogram (some ∘ p) (d.val + 1) (activeWeight k)
  else true

-- Partition the 56 inherited representatives into 14 groups of four.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem activeGroups (d : Fin 2) (g : Fin 14) :
    (List.finRange 4).all (fun i => activeProfileCheck d
      ⟨40 + 4 * g.val + i.val, by omega⟩) = true := by
  fin_cases d <;> fin_cases g <;> decide +kernel

private theorem activeMultiplicities (d : Fin 2) (i : Fin 96) (hi : 40 ≤ i.val) :
    activeProfileCheck d i = true := by
  let g : Fin 14 := ⟨(i.val - 40) / 4, by omega⟩
  let j : Fin 4 := ⟨(i.val - 40) % 4, Nat.mod_lt _ (by decide)⟩
  have h := List.all_eq_true.mp (activeGroups d g) j (List.mem_finRange j)
  rwa [show (⟨40 + 4 * g.val + j.val, by omega⟩ : Fin 96) = i from Fin.ext (by
    dsimp [g, j]
    omega)] at h

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem exhaustedMultiplicities :
    (List.finRange 40).all (fun i =>
      let p := HardinA229635State.rep (i.castAdd 56)
      checkHistogram (some ∘ p) 0
        (exhaustedWeight (Fin.ofNat 40 (HardinA229635State.fresh p).val))) = true := by
  decide +kernel

private theorem exactExits_active (p : Boundary) (d : Fin 2)
    (hp : Valid p (d.val + 1)) (hn : Canonical p)
    (hd : inheritedSource (HardinA229585StripData.cl p d.val) = none) (j : Fin 96) :
    (exitCodes (some ∘ p) (d.val + 1)).count j =
      activeWeight (HardinA229585StripData.cl p d.val) j := by
  let i := HardinA229635State.fresh p
  have h : HardinA229635State.h p ≤ 1 := by
    have := ((valid_parts p (d.val + 1)).mp hp).2
    omega
  have he : HardinA229635State.rep i = p :=
    HardinA229635Laws.representatives_complete p hn (h.trans (by decide))
  have hi := (rep_partition i).mp (show HardinA229635State.h (HardinA229635State.rep i) ≤ 1 by
    rw [he]
    exact h)
  have hc := activeMultiplicities d i hi
  unfold activeProfileCheck at hc
  simp only [he, hd, Option.isNone_none, decide_eq_true hp, Bool.true_and, ite_true] at hc
  exact checkHistogram_count _ _ _ hc j

private def inheritedActiveCheck (i : Fin 96) (d : Fin 2) : Bool :=
  let p := HardinA229635State.rep i
  match inheritedSource (HardinA229585StripData.cl p d.val) with
  | some k => !decide (Valid p (d.val + 1)) ||
      decide (Valid p 2 ∧ d = 0 ∧ HardinA229585StripData.cl p 1 = k.castAdd 56)
  | none => true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem inheritedActiveCheck_all (i : Fin 96) (d : Fin 2) :
    inheritedActiveCheck i d = true := by
  revert i d
  decide +kernel

private theorem inherited_active_spec (i : Fin 96) (d : Fin 2) (k : Fin 16) :
    let p := HardinA229635State.rep i
    Valid p (d.val + 1) →
      inheritedSource (HardinA229585StripData.cl p d.val) = some k →
        HardinA229585StripData.Valid p 1 ∧ d = 0 ∧
          HardinA229585StripData.cl p 1 = k.castAdd 56 := by
  intro p hp hk
  have h := inheritedActiveCheck_all i d
  unfold inheritedActiveCheck at h
  change inheritedSource (HardinA229585StripData.cl (HardinA229635State.rep i) d.val) = some k at hk
  change Valid (HardinA229635State.rep i) (d.val + 1) at hp
  rw [hk] at h
  simp only [decide_eq_true hp, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact ⟨(valid_shift p 2 (by decide)).mp h.1, h.2⟩

private theorem exactExits_new (p : Boundary)
    (hp : Valid p 0) (hn : Canonical p) (hnv : ¬ Valid p 1) (j : Fin 96) :
    (exitCodes (some ∘ p) 0).count j =
      exhaustedWeight (Fin.ofNat 40 (HardinA229635State.fresh p).val) j := by
  let i := HardinA229635State.fresh p
  have he := HardinA229635Laws.representatives_complete p hn ((valid_parts p 0).mp hp).2
  have hi : i.val < 40 := Nat.lt_of_not_ge fun hi =>
    hnv ((valid_parts p 1).mpr ⟨by decide, he ▸ (rep_partition i).mpr hi⟩)
  let k : Fin 40 := ⟨i.val, hi⟩
  have hk : k.castAdd 56 = i := Fin.ext rfl
  have hs := List.all_eq_true.mp exhaustedMultiplicities k (List.mem_finRange k)
  dsimp only at hs
  rw [hk, he] at hs
  exact checkHistogram_count _ _ _ hs j

set_option maxRecDepth 6000 in
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
  · have hv := (valid_shift p d (Nat.pos_of_ne_zero hd)).mp hp
    let b : Fin 2 := ⟨d - 1, Nat.lt_succ_of_le hv.1⟩
    have hb : b.val + 1 = d := Nat.sub_add_cancel (Nat.pos_of_ne_zero hd)
    have ht : T (cl p d) (j.natAdd 72) =
        match inheritedSource (HardinA229585StripData.cl p b.val) with
        | some k => oldExits (k.castAdd 56) j
        | none => (activeWeight (HardinA229585StripData.cl p b.val) j : ℤ) := by
      simp only [cl, hd, ite_false, T, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₁₂, Matrix.of_apply, b]
    rw [ht]
    cases hs : inheritedSource (HardinA229585StripData.cl p b.val) with
    | none =>
      dsimp only
      have he := exactExits_active p b (hb.symm ▸ hp) hn hs j
      rw [← exactExits_count, ← hb]
      exact_mod_cast he
    | some k =>
      dsimp only
      have hh := ((valid_parts p d).mp hp).2
      have hrep := HardinA229635Laws.representatives_complete p hn
        (hh.trans (Nat.sub_le _ _))
      have hi := inherited_active_spec (HardinA229635State.fresh p) b k
      dsimp only at hi
      rw [hrep] at hi
      specialize hi (hb.symm ▸ hp) hs
      have hd₁ : d = 1 := by
        have h := congrArg Fin.val hi.2.1
        omega
      rw [← hi.2.2, hd₁]
      exact old_exhausted_row p 1 hi.1 j

private theorem class_counts (p : Boundary) (d : ℕ) (hp : Valid p d)
    (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p d) (j.natAdd 72) := by
  obtain ⟨q, ⟨hn, e, rfl⟩, _⟩ := canonical_exists_unique p
  have hv := (valid_relabel e p d).mpr hp
  have h := class_counts_canonical (e ∘ p) d hv hn j
  rw [← (Equiv.piCongrRight fun _ : Fin 7 => e).sum_comp] at h
  change (∑ r : Row, if cross (e ∘ p) (e ∘ r) + bondDefects horizontal (e ∘ r) (e ∘ r) = d ∧
    exhaustedClass (boundary (e ∘ r)) = j then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d) (j.natAdd 72) at h
  have horizontal_eq (r : Row) :
      bondDefects horizontal (e ∘ r) (e ∘ r) = bondDefects horizontal r r :=
    relabel_defects horizontal antidiagonal e [r]
  simpa only [HardinA229585Strip.cross_relabel, horizontal_eq,
    show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
    exhausted_relabel, cl_relabel] using h

/-- Transfer multiplicities for both the positive and exhausted budgets. -/
theorem transition_counts (p : Boundary) (d : ℕ) (s : Fin 168)
    (hp : Valid p d ∨ (d = 0 ∧ s.val < 72)) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  induction s using Fin.addCases (m := 72) (n := 96) with
  | left j => exact leading_counts p d j (hp.imp_right And.left)
  | right j =>
    simp_rw [exhausted_cut]
    apply class_counts p d (hp.resolve_right ?_) j
    simp only [Fin.val_natAdd, not_and]
    omega

private theorem horizontal_cons (x : Fin 3) (p : Boundary) :
    bondDefects horizontal (Fin.cons x p) (Fin.cons x p) =
      (if x = p 0 then 1 else 0) + HardinA229635State.h p := by
  rw [tailCost_eq]
  simp only [bondDefects, horizontal, Finset.filter_image]
  rw [Finset.card_image_of_injective _ (fun i j h =>
    Fin.castSucc_injective 6 (congrArg Prod.fst h))]
  let r : Row := Fin.cons x p
  have h : (∑ j : Fin 6, if r j.castSucc = r j.succ then (1 : ℕ) else 0) =
      (Finset.univ.filter fun j : Fin 6 => r j.castSucc = r j.succ).card := by
    simpa using (Finset.sum_boole (R := ℕ) (fun j : Fin 6 => r j.castSucc = r j.succ) Finset.univ)
  change (Finset.univ.filter fun j : Fin 6 => r j.castSucc = r j.succ).card = _
  rw [← h, Fin.sum_univ_succ]
  simp only [r, Fin.castSucc_zero, Fin.castSucc_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_boole, Nat.cast_id]

private def headWeight (p : Boundary) : ℤ :=
  if HardinA229635State.h p = 1 then 1 else
  if HardinA229635State.h p = 2 then 2 else 0

private theorem head_weight_eq (p : Boundary) :
    (∑ x : Fin 3, if bondDefects horizontal (Fin.cons x p) (Fin.cons x p) = 2
      then (1 : ℤ) else 0) = headWeight p := by
  simp_rw [horizontal_cons]
  unfold headWeight
  by_cases h₁ : HardinA229635State.h p = 1
  · simp only [h₁, ite_true]
    have h (x : Fin 3) :
        ((if x = p 0 then (1 : ℕ) else 0) + 1 = 2) ↔ x = p 0 := by
      split_ifs <;> simp_all
    simp [h, Finset.sum_ite_eq']
  · by_cases h₂ : HardinA229635State.h p = 2
    · simp only [h₁, h₂, ite_false, ite_true]
      have h (x : Fin 3) :
          ((if x = p 0 then (1 : ℕ) else 0) + 2 = 2) ↔ x ≠ p 0 := by
        split_ifs <;> simp_all
      simp_rw [h]
      rw [show (fun x : Fin 3 => if x ≠ p 0 then (1 : ℤ) else 0) =
          fun x => 1 - (if x = p 0 then 1 else 0) by
        funext x
        by_cases hx : x = p 0 <;> simp [hx], Finset.sum_sub_distrib]
      simp
    · simp only [h₁, h₂, ite_false]
      apply Finset.sum_eq_zero
      intro x _
      split_ifs with hx <;> omega

private theorem fresh_start_count (i : Fin 96) :
    (∑ p : Boundary, if HardinA229635State.h p ≤ 2 ∧ HardinA229635State.fresh p = i
      then (1 : ℤ) else 0) = 6 := by
  have h := HardinA229635State.start_count (i.natAdd 31)
  rw [HardinA229635Starts.checked_starts, HardinA229635Starts.start_tallies] at h
  simp only [Fin.val_natAdd, show ¬ 31 + i.val < 31 by omega, ite_false] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : HardinA229635State.h p ≤ 2
  · have hn : ¬ HardinA229635State.h p + (2 - HardinA229635State.h p) ≤ 1 := by omega
    simp only [hp, true_and, HardinA229635State.cl, hn, ite_false]
    by_cases he : HardinA229635State.fresh p = i
    · simp only [he, ite_true]
    · simp only [he, (Fin.natAdd_injective 96 31).ne he, ite_false]
  · simp [hp]

private theorem rep_weight (p : Boundary) (hp : HardinA229635State.h p ≤ 2)
    (j : Fin 96) :
    (if exhaustedClass p = j then headWeight p else 0) =
      (let q := HardinA229635State.rep (HardinA229635State.fresh p)
       if exhaustedClass q = j then headWeight q else 0) := by
  obtain ⟨q, ⟨hn, e, rfl⟩, _⟩ := canonical_exists_unique p
  have hp' := (HardinA229635State.h_relabel e p).symm ▸ hp
  have h := HardinA229635Laws.representatives_complete (e ∘ p) hn hp'
  rw [fresh_relabel] at h
  rw [h]
  simp only [headWeight, HardinA229635State.h_relabel, exhausted_relabel]

-- Only the reindexing and head weights are checked here. The 96 fibre sizes
-- come from the frozen start certificate.
set_option maxRecDepth 14000 in
set_option maxHeartbeats 4000000 in
private theorem initial_from_starts (j : Fin 96) :
    (∑ i : Fin 96, if exhaustedClass (HardinA229635State.rep i) = j
      then headWeight (HardinA229635State.rep i) * 6 else 0) = initialExhausted j := by
  revert j
  decide +kernel

private theorem initial_exhausted_count (j : Fin 96) :
    (∑ r : Row, if bondDefects horizontal r r = 2 ∧ exhaustedClass (boundary r) = j
      then (1 : ℤ) else 0) = initialExhausted j := by
  rw [← (Fin.consEquiv (fun _ : Fin 7 => Fin 3)).sum_comp, Fintype.sum_prod_type_right]
  change (∑ p : Boundary, ∑ x : Fin 3,
    if bondDefects horizontal (Fin.cons x p) (Fin.cons x p) = 2 ∧ exhaustedClass p = j
    then (1 : ℤ) else 0) = _
  calc
    _ = ∑ p : Boundary, if exhaustedClass p = j then headWeight p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : exhaustedClass p = j
      · simp only [hp, and_true, ite_true, head_weight_eq]
      · simp only [hp, and_false, ite_false, Finset.sum_const_zero]
    _ = ∑ p : Boundary, ∑ i : Fin 96,
        (if exhaustedClass (HardinA229635State.rep i) = j
          then headWeight (HardinA229635State.rep i) else 0) *
        (if HardinA229635State.h p ≤ 2 ∧ HardinA229635State.fresh p = i then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : HardinA229635State.h p ≤ 2
      · simp only [hp, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        exact rep_weight p hp j
      · have h₁ : HardinA229635State.h p ≠ 1 := by omega
        have h₂ : HardinA229635State.h p ≠ 2 := by omega
        simp [headWeight, hp, h₁, h₂]
    _ = _ := by
      rw [Finset.sum_comm, ← initial_from_starts j]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, fresh_start_count]
      split_ifs <;> simp

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
    simpa only [initial, Fin.append_right] using initial_exhausted_count j

/-- The exact two-defect labelled count as a matrix coefficient. -/
theorem count_transfer (n : ℕ) :
    (D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.literalCount
      (q := 3) horizontal antidiagonal 2 (n + 1) : ℤ) =
      dotProduct initial ((T ^ n).mulVec terminal) := by
  exact D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.lumped_count
    horizontal antidiagonal boundary cross Valid cl T initial terminal 2
    HardinA229585Strip.edge (fun p d _ => terminal_eq p d) next_valid
    (fun p d hp s => transition_counts p d s (Or.inl hp)) initial_valid initial_counts n

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
