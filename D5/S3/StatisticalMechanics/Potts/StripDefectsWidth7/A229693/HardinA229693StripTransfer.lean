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
tailCost_eq: proof_shape=bind-only; consumers=horizontal_cons, valid_shift
decidableBudget: proof_shape=bind-only; consumers=activeProfileCheck, exhaustedClass, inheritedActiveCheck
valid_parts: proof_shape=bind-only; consumers=class_counts_canonical, exactExits_active, exactExits_new, next_valid, valid_shift
valid_relabel: proof_shape=bind-only; consumers=class_counts
fresh_relabel: proof_shape=bind-only; consumers=cl_relabel, rep_weight
alternating: proof_shape=bind-only; consumers=properRows, proper_iff, zeroExitCodes_count
proper_iff: proof_shape=bind-only; consumers=zeroExitCodes_count._simp_1_2
properRows: proof_shape=bind-only; consumers=zeroExitCodes, zeroExitCodes_count, exactExits_new
zeroExitCodes: proof_shape=bind-only; consumers=zeroExitCodes_count, exhaustedMultiplicities, exactExits_new
zeroExitCodes_count: proof_shape=bind-only; consumers=class_counts_canonical
rep_partition: proof_shape=bind-only; consumers=exactExits_active, exactExits_new
oldZeroImage: proof_shape=bind-only; consumers=cl_relabel, class_counts_canonical, exhaustedClass, exhaustedClass.eq_1, initialExhausted, old_exhausted_counts, old_exhausted_row
exhaustedClass: proof_shape=bind-only; consumers=active_cut, cl, cl.eq_1, cl_relabel, class_counts, class_counts_canonical, exactExits_count, exhausted_cut, exhausted_relabel, exitCodes_bound, exitCodes_eq, initial_counts, initial_counts._simp_1_3, initial_exhausted_count, initial_from_starts, leading_counts, old_exhausted_counts, old_exhausted_row, packedClass_all, packedClass_all._proof_1_1, packedClass_eq, rep_weight, terminal_eq, transition_counts, transition_counts._simp_1_1
cl: proof_shape=bind-only; consumers=active_cut, cl_relabel, class_counts, class_counts_canonical, count_transfer, exhausted_cut, initial_counts, initial_counts._simp_1_1, initial_counts._simp_1_3, leading_counts, leading_counts._simp_1_1, old_exhausted_counts, terminal_eq, transition_counts, transition_counts._simp_1_1
exitRead: proof_shape=content; consumers=HardinA229693Strip.w, HardinA229693Strip.w_leading, activeWeight, exhaustedWeight
oldExits: proof_shape=bind-only; consumers=HardinA229693Strip.leading_action, T, class_counts_canonical, leading_counts, old_exhausted_counts, old_exhausted_row
oldTerminal: proof_shape=bind-only; consumers=oldDestination
oldDestination: proof_shape=bind-only; consumers=old_exhausted_counts, old_exhausted_row
old_exhausted_row: proof_shape=bind-only; consumers=class_counts_canonical, old_exhausted_counts
activeExits: proof_shape=content; consumers=activeWeight
exhaustedExits: proof_shape=content; consumers=exhaustedWeight
activeWeight: proof_shape=content; consumers=HardinA229693Strip.leading_action, T, T.eq_1, activeProfileCheck, class_counts_canonical, exactExits_active, leading_counts, old_exhausted_counts
exhaustedWeight: proof_shape=content; consumers=HardinA229693Strip.leading_action, T, T.eq_1, class_counts_canonical, exactExits_new, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1, leading_counts, old_exhausted_counts
weightPack: proof_shape=bind-only; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, classPack_count, weightPack_injective, weightPack_sum
weightPack_sum: proof_shape=bind-only; consumers=classPack_count
weightPack_injective: proof_shape=bind-only; consumers=checkHistogram_count
classPack: proof_shape=bind-only; consumers=checkHistogram, checkHistogram.eq_1, checkHistogram_count, classPack_count
classPack_count: proof_shape=bind-only; consumers=checkHistogram_count
T: proof_shape=content; consumers=HardinA229693Strip.exhausted_step, HardinA229693Strip.forward_step, HardinA229693Strip.forward_table, HardinA229693Strip.leading_action, HardinA229693Strip.polynomial_relation, HardinA229693Strip.result, HardinA229693Strip.rightColumn_eq, class_counts, class_counts_canonical, count_transfer, leading_counts, old_exhausted_counts, transition_counts
initialExhausted: proof_shape=content; consumers=HardinA229693Strip.w_leading, initial, initial.eq_1, initial_counts, initial_exhausted_count, initial_from_starts
initial: proof_shape=content; consumers=HardinA229693Strip.forward_table, HardinA229693Strip.polynomial_relation, HardinA229693Strip.result, HardinA229693Strip.w, HardinA229693Strip.w_leading, count_transfer, initial_counts
terminal: proof_shape=bind-only; consumers=HardinA229693Strip.result, count_transfer, terminal_eq
valid_shift: proof_shape=bind-only; consumers=class_counts_canonical, inherited_active_spec, leading_counts, old_valid
old_valid: proof_shape=bind-only; consumers=old_exhausted_counts, old_exhausted_row
cl_relabel: proof_shape=bind-only; consumers=class_counts, exhausted_relabel
exhausted_relabel: proof_shape=bind-only; consumers=class_counts, rep_weight
blocks_disjoint: proof_shape=bind-only; consumers=active_cut, exhausted_cut, old_exhausted_row
active_cut: proof_shape=bind-only; consumers=initial_counts._simp_1_1, leading_counts._simp_1_1
exhausted_cut: proof_shape=bind-only; consumers=initial_counts._simp_1_3, transition_counts._simp_1_1
next_valid: proof_shape=bind-only; consumers=count_transfer
initial_valid: proof_shape=bind-only; consumers=count_transfer
terminal_eq: proof_shape=bind-only; consumers=count_transfer
leading_counts: proof_shape=bind-only; consumers=transition_counts
old_exhausted_counts: proof_shape=bind-only; consumers=class_counts_canonical
horizontalCost: proof_shape=bind-only; consumers=completionCost_row, horizontalCost_eq, rowCost, rowCost.eq_1, rowCost_eq
horizontalCost_eq: proof_shape=bind-only; consumers=rowCost_eq
rowCost: proof_shape=bind-only; consumers=completionCost_row, exactExits_count, rowCost_eq
rowCost_eq: proof_shape=bind-only; consumers=exactExits_count
completionCost_row: proof_shape=bind-only; consumers=exactExits_count
rowCode_tail: proof_shape=bind-only; consumers=exitCodes_eq
packedClass: proof_shape=bind-only; consumers=exitCodes, exitCodes.eq_1, exitCodes_eq, packedClass_all, packedClass_all._proof_1_1, packedClass_eq
packedClass_all: proof_shape=bind-only; consumers=packedClass_eq
packedClass_eq: proof_shape=bind-only; consumers=exitCodes_eq
exitCodes: proof_shape=content; consumers=class_counts_canonical, exactExits_active, exactExits_count, exitCodes_bound, exitCodes_eq, activeProfileCheck
exitCodes_eq: proof_shape=content; consumers=exactExits_count, exitCodes_bound
completionRows_length_le: proof_shape=content; consumers=exitCodes_bound
exitCodes_bound: proof_shape=content; consumers=checkHistogram_count
checkHistogram: proof_shape=content; consumers=activeProfileCheck, checkHistogram_count, exactExits_active, exactExits_new, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1
checkHistogram_count: proof_shape=content; consumers=exactExits_active, exactExits_new
exactExits_count: proof_shape=content; consumers=class_counts_canonical
inheritedSource: proof_shape=bind-only; consumers=HardinA229693Strip.leading_action, T, activeProfileCheck, class_counts_canonical, exactExits_active, inheritedActiveCheck, inherited_active_spec, leading_counts, old_exhausted_counts
sourceCode: proof_shape=bind-only; consumers=activeWeight, inheritedSource
activeGroups: proof_shape=content; consumers=activeMultiplicities
activeMultiplicities: proof_shape=content; consumers=exactExits_active
inheritedActiveCheck: proof_shape=bind-only; consumers=inheritedActiveCheck_all, inherited_active_spec
inheritedActiveCheck_all: proof_shape=bind-only; consumers=inherited_active_spec
inherited_active_spec: proof_shape=bind-only; consumers=class_counts_canonical
activeProfileCheck: proof_shape=content; consumers=activeGroups, activeMultiplicities, exactExits_active
exhaustedMultiplicities: proof_shape=content; consumers=exactExits_new
exactExits_active: proof_shape=content; consumers=class_counts_canonical
exactExits_new: proof_shape=content; consumers=class_counts_canonical
class_counts_canonical: proof_shape=content; consumers=class_counts
class_counts: proof_shape=content; consumers=transition_counts
old_exhausted_index: proof_shape=bind-only; consumers=budget_one_leading
old_lower_left: proof_shape=bind-only; consumers=budget_one_leading
budget_one_leading: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=content; consumers=count_transfer
horizontal_cons: proof_shape=bind-only; consumers=head_weight_eq, next_valid, initial_valid
headWeight: proof_shape=bind-only; consumers=head_weight_eq, initial_exhausted_count, initial_from_starts, rep_weight
head_weight_eq: proof_shape=bind-only; consumers=initial_exhausted_count
fresh_start_count: proof_shape=bind-only; consumers=initial_exhausted_count
rep_weight: proof_shape=bind-only; consumers=initial_exhausted_count
initial_from_starts: proof_shape=content; consumers=initial_exhausted_count
initial_exhausted_count: proof_shape=content; consumers=initial_counts
initial_counts: proof_shape=content; consumers=count_transfer
count_transfer: proof_shape=content; consumers=HardinA229693Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Starts
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripCompletion
import Mathlib.Data.Fin.Rev
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
open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA229693StripCompletion
open HardinA229585StripData (Boundary Row horizontal antidiagonal boundary cross)
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (relabel_defects defects tailDefects)

private instance decidableBudget (p : Boundary) (d : ℕ) :
    Decidable (HardinA229635State.Valid p d) :=
  inferInstanceAs (Decidable (HardinA229635State.h p + d ≤ 2))

private theorem valid_parts (p : Boundary) (d : ℕ) :
    HardinA229635State.Valid p d ↔ d ≤ 2 ∧ HardinA229635State.h p ≤ 2 - d := by
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
    HardinA229635State.Valid (e ∘ p) d ↔ HardinA229635State.Valid p d := by
  simp only [HardinA229635State.Valid, HardinA229635State.h_relabel]

private theorem fresh_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    HardinA229635State.fresh (e ∘ p) = HardinA229635State.fresh p := by
  apply Fin.natAdd_injective 96 31
  simpa only [HardinA229635State.cl, show ∀ n : ℕ, ¬ n + 3 ≤ 1 from fun _ => by omega,
    ite_false] using HardinA229635State.cl_relabel e p 3

private def oldZeroImage (i : Fin 72) : Fin 96 :=
  if h : 16 ≤ i.val then (Fin.subNat 16 i h).castAdd 40 else 0

def exhaustedClass (p : Boundary) : Fin 96 :=
  if HardinA229635State.Valid p 1 then oldZeroImage (HardinA229585StripData.cl p 0)
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

-- Precompute indices for the inherited row slice and the 56 stored rows.
private def sourceCode (i : Fin 72) : ℕ :=
  let packed : ℕ := eval% (
    let old := List.ofFn HardinA229585StripData.zeroBudgetClass
    let new := (List.finRange 72).filter fun i => !old.contains i
    Nat.ofDigits 128 (List.ofFn fun i : Fin 72 =>
      if old.contains i then old.idxOf i else 16 + new.idxOf i))
  (packed >>> (7 * i.val)) % 128

private def inheritedSource (i : Fin 72) : Option (Fin 16) :=
  if h : sourceCode i < 16 then some ⟨sourceCode i, h⟩ else none

-- Each radix-16 digit is one multiplicity in a stored profile.
private def activeExits (i : ℕ) (j : Fin 36) : ℕ :=
  let table : Array ℕ := #[
    2788275043799815682532746590457228291232836, 185794255416855400453938519237118859228228, 174224660458547477809789119302022232888387, 1393844427441978589848243499947228753188133,
    191600245781807376049677704021765741819204, 2793718320689981833366592376332016687473733, 174245845068869012419384152290811552285781, 1480956801316840849800070374472505992897606,
    2961841824321872249115168527719522922480641, 87154832342401075250539838829869247370035, 1405026069554678863642220569047189894153217, 104509233055375803759967330408923421348659,
    2787617076572161830334784728496471675183909, 87112463121758003111215415028492395766594, 92897252325471848491076004523318269121587, 1394139515774346566067879968349375092302178,
    425944194770854524146946305, 5380193019449183310779060241, 387183305827647125999128832, 5321934070679385020993503488,
    5320885429844288518370758929, 5068144375681084288591269922, 5378909144512898604325671185, 427233382378717705528152098,
    9964198299919589047799976193, 10542004410228803935260446737, 9964268840268645511431459072, 10542145489841831844706779392,
    9965568983993651333653659920, 15242303215576119883396874256, 15552028494238442204282683409, 5032862411312900810819637248,
    9965573706360414436761534737, 389454209708026711739859217, 15282268585898880711463801344, 10909904167569851720765936128,
    60843873665324765353619781, 40056920297630211295490611, 10348651171569581851737600324, 15862793267818144743213245218,
    15863691383221597439399039761, 5628863394789800678841659938, 41491320665556379100131635, 59404160625820105407738404,
    5899884747045790436954285056, 15592892277558586358292947968, 698014816290330384801006114, 5052276356072224196313219618,
    9926816947258021680090521600, 15242373460772483901814931490, 15513187325060523402377560096, 5052266911338697990047138336,
    5339160415274857483449926144, 5050081011518940108688466432, 5338878256048798585116041250, 5049939930820827181475832322]
  (table[i]! >>> (4 * j.val)) % 16

private def exhaustedExits (i : Fin 40) (j : Fin 36) : ℕ :=
  let table : Array ℕ := #[
    38770923972264970869014528, 38770923972264970852237312, 75853011632261924126720, 19423388491948103147978752,
    5312662295500388564992, 5312662295500405342208, 19418666125467368101511168, 19418666125466333014392832,
    19352848142611333022482432, 19423388491949129628385280, 19352848142611333039259648, 80575378114032057712640,
    19418666125467368084733952, 80575378115067128053760, 38987857682571795196018688, 38987857682571795179241472,
    161150756227995362394112, 161150756229030449512448, 14167099448815127625728, 19352257846799943558234112,
    151410875358176230768640, 38841759469509110747103232, 227559034893281045512192, 19352257846800909892321280,
    3504726867968, 1245574070272, 2272054476800, 3504710090752,
    38690348594153210849001472, 227559034893281062289408, 19428406006338278138052608, 76148159538609491279872,
    38690348594151071972065280, 14167099448815110848512, 80575378116170934648832, 80575378114100760412160,
    19493928841285904032071680, 19493928841285904065626112]
  let index : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 3, 10, 11, 12, 7, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
  (table[index[i.val]!]! >>> (4 * j.val)) % 16

private def oldExits (i : Fin 72) (j : Fin 96) : ℤ :=
  Fin.append (fun k : Fin 56 => HardinA229585StripData.T i (k.natAdd 16))
    (0 : Fin 40 → ℤ) j

private def activeWeight (i : Fin 72) : Fin 96 → ℕ :=
  fun j => Fin.append (fun k => (HardinA229585StripData.T i k).toNat)
    (activeExits (sourceCode i - 16)) (exitRead j)

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
    HardinA229635State.Valid p d ↔ HardinA229585StripData.Valid p (d - 1) := by
  rw [valid_parts]
  unfold HardinA229585StripData.Valid
  rw [tailCost_eq]
  omega

private theorem old_valid (p : Boundary) :
    HardinA229635State.Valid p 1 ↔ HardinA229585StripData.Valid p 0 :=
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

private theorem next_valid (p : Boundary) (d : ℕ) (hp : HardinA229635State.Valid p d) (r : Row)
    (hr : cross p r + bondDefects horizontal r r ≤ d) :
    HardinA229635State.Valid (boundary r) (d - (cross p r + bondDefects horizontal r r)) := by
  have hd := ((valid_parts p d).mp hp).1
  have ht := horizontal_cons (r 0) (boundary r)
  rw [show Fin.cons (r 0) (boundary r) = r from Fin.cons_self_tail r] at ht
  change HardinA229635State.h (boundary r) + (d - (cross p r + bondDefects horizontal r r)) ≤ 2
  omega

private theorem initial_valid (r : Row) (hr : bondDefects horizontal r r ≤ 2) :
    HardinA229635State.Valid (boundary r) (2 - bondDefects horizontal r r) := by
  have ht := horizontal_cons (r 0) (boundary r)
  rw [show Fin.cons (r 0) (boundary r) = r from Fin.cons_self_tail r] at ht
  change HardinA229635State.h (boundary r) + (2 - bondDefects horizontal r r) ≤ 2
  omega

private theorem terminal_eq (p : Boundary) (d : ℕ) :
    terminal (cl p d) = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0 <;> simp [cl, terminal, hd]

private theorem leading_counts (p : Boundary) (d : ℕ) (j : Fin 72)
    (hp : HardinA229635State.Valid p d ∨ d = 0) :
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

private theorem old_exhausted_counts (p : Boundary) (hp : HardinA229635State.Valid p 1) (j : Fin 96) :
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

private theorem completionCost_row (p : Boundary) (r : Row) :
    completionCost (some ∘ p) none r = rowCost p r := by
  simp only [completionCost, matchCost, Fin.tail, Function.comp_apply, zero_add, Fin.castSucc_zero, Fin.castSucc_succ, rowCost, horizontalCost, List.ofFn_succ, List.ofFn_zero,
    List.sum_cons, List.sum_nil]
  ac_rfl

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

private def checkHistogram (xs : List (Fin 96)) (weights : Fin 96 → ℕ) : Bool :=
  (classPack xs == weightPack weights) &&
    (List.finRange 96).all (fun i => weights i < 4096)

private theorem checkHistogram_count (xs : List (Fin 96)) (weights : Fin 96 → ℕ)
    (h : checkHistogram xs weights = true) (bound : ∀ j, xs.count j < 4096) (j : Fin 96) :
    xs.count j = weights j := by
  simp only [checkHistogram, Bool.and_eq_true, beq_iff_eq, classPack_count] at h
  exact congrFun (weightPack_injective _ _ bound (fun i =>
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

private def alternating : Row ≃ Row :=
  Equiv.piCongrRight (fun i : Fin 7 => (Fin.revPerm (n := 3)) ^ i.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem proper_iff (r : Row) :
    HardinA233155RowTransfer.rowLegal r ↔
      bondDefects horizontal (alternating r) (alternating r) = 0 := by
  have h : ∀ c : Fin 2187,
      HardinA233155RowTransfer.rowLegal (HardinA233155RowTransfer.decode 7 c) ↔
      bondDefects horizontal (alternating (HardinA233155RowTransfer.decode 7 c))
        (alternating (HardinA233155RowTransfer.decode 7 c)) = 0 := by
    decide +kernel
  simpa only [HardinA233155RowTransfer.decode, Equiv.symm_apply_apply] using
    h (finFunctionFinEquiv r)

private def properRows : List Row :=
  HardinA233154Rows.codes.map (alternating ∘ HardinA233155RowTransfer.decode 7)

private def zeroExitCodes (p : Boundary) : List (Fin 96) :=
  ((properRows.filter fun r => cross p r == 0).map fun r => exhaustedClass (boundary r))

private theorem zeroExitCodes_count (p : Boundary) (j : Fin 96) :
    ((zeroExitCodes p).count j : ℤ) =
      ∑ r : Row, if cross p r + bondDefects horizontal r r = 0 ∧
        exhaustedClass (boundary r) = j then 1 else 0 := by
  rw [← alternating.sum_comp]
  simp only [Nat.add_eq_zero]
  simp_rw [← proper_iff]
  have h := HardinA233155RowTransfer.row_sum 7 (fun r =>
    if cross p (alternating r) = 0 ∧ exhaustedClass (boundary (alternating r)) = j
      then 1 else 0)
  rw [HardinA233154Column.codes_table] at h
  change _ = (HardinA233154Rows.codes.map
    ((fun r : Row => if cross p r = 0 ∧ exhaustedClass (boundary r) = j
        then (1 : ℤ) else 0) ∘ (alternating ∘ HardinA233155RowTransfer.decode 7))).sum at h
  rw [← List.map_map] at h
  simp_rw [show ∀ r : Row, ((if
      (cross p (alternating r) = 0 ∧ HardinA233155RowTransfer.rowLegal r) ∧
        exhaustedClass (boundary (alternating r)) = j then 1 else 0) : ℤ) =
      if HardinA233155RowTransfer.rowLegal r then
        (if cross p (alternating r) = 0 ∧ exhaustedClass (boundary (alternating r)) = j
          then 1 else 0) else 0 from fun r => by
            by_cases hr : HardinA233155RowTransfer.rowLegal r <;> simp [hr]]
  rw [h]
  change ((zeroExitCodes p).count j : ℤ) = (properRows.map fun r =>
    if cross p r = 0 ∧ exhaustedClass (boundary r) = j then 1 else 0).sum
  simp only [zeroExitCodes, List.count_eq_countP, List.countP_map, List.countP_filter]
  generalize properRows = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih,
      Function.comp_apply, Bool.and_eq_true, beq_iff_eq, and_comm]
    split_ifs <;> simp_all [add_comm]

private theorem rep_partition (i : Fin 96) :
    HardinA229635State.h (HardinA229635State.rep i) ≤ 1 ↔ 40 ≤ i.val := by
  revert i
  decide +kernel

private def activeProfileCheck (d : Fin 2) (i : Fin 96) : Bool :=
  let p := HardinA229635State.rep i
  let k := HardinA229585StripData.cl p d.val
  if (inheritedSource k).isNone && decide (HardinA229635State.Valid p (d.val + 1)) then
    checkHistogram (exitCodes (some ∘ p) (d.val + 1)) (activeWeight k)
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
      checkHistogram (zeroExitCodes p)
        (exhaustedWeight (Fin.ofNat 40 (HardinA229635State.fresh p).val))) = true := by
  decide +kernel

private theorem exactExits_active (p : Boundary) (d : Fin 2)
    (hp : HardinA229635State.Valid p (d.val + 1)) (hn : Canonical p)
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
  exact checkHistogram_count _ _ hc (exitCodes_bound _ _) j

private def inheritedActiveCheck (i : Fin 96) (d : Fin 2) : Bool :=
  let p := HardinA229635State.rep i
  match inheritedSource (HardinA229585StripData.cl p d.val) with
  | some k => !decide (HardinA229635State.Valid p (d.val + 1)) ||
      decide (HardinA229635State.Valid p 2 ∧ d = 0 ∧ HardinA229585StripData.cl p 1 = k.castAdd 56)
  | none => true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem inheritedActiveCheck_all (i : Fin 96) (d : Fin 2) :
    inheritedActiveCheck i d = true := by
  revert i d
  decide +kernel

private theorem inherited_active_spec (i : Fin 96) (d : Fin 2) (k : Fin 16) :
    let p := HardinA229635State.rep i
    HardinA229635State.Valid p (d.val + 1) →
      inheritedSource (HardinA229585StripData.cl p d.val) = some k →
        HardinA229585StripData.Valid p 1 ∧ d = 0 ∧
          HardinA229585StripData.cl p 1 = k.castAdd 56 := by
  intro p hp hk
  have h := inheritedActiveCheck_all i d
  dsimp only [inheritedActiveCheck] at h
  change inheritedSource (HardinA229585StripData.cl (HardinA229635State.rep i) d.val) = some k at hk
  change HardinA229635State.Valid (HardinA229635State.rep i) (d.val + 1) at hp
  rw [hk] at h
  simp only [decide_eq_true hp, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact ⟨(valid_shift p 2 (by decide)).mp h.1, h.2⟩

private theorem exactExits_new (p : Boundary)
    (hp : HardinA229635State.Valid p 0) (hn : Canonical p) (hnv : ¬ HardinA229635State.Valid p 1) (j : Fin 96) :
    (zeroExitCodes p).count j =
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
  apply checkHistogram_count _ _ hs _ j
  intro k
  apply List.count_le_length.trans_lt
  unfold zeroExitCodes
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans_lt (by decide +kernel)

set_option maxRecDepth 6000 in
private theorem class_counts_canonical (p : Boundary) (d : ℕ) (hp : HardinA229635State.Valid p d)
    (hn : Canonical p) (j : Fin 96) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℤ) else 0) =
    T (cl p d) (j.natAdd 72) := by
  by_cases hd : d = 0
  · subst d
    by_cases h : HardinA229635State.Valid p 1
    · exact old_exhausted_counts p h j
    · rw [← zeroExitCodes_count, exactExits_new p hp hn h j]
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

private theorem class_counts (p : Boundary) (d : ℕ) (hp : HardinA229635State.Valid p d)
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
  have cross_eq (r : Row) : cross (e ∘ p) (e ∘ r) = cross p r := by
    have hc := relabel_defects ∅ antidiagonal e [Fin.cons 0 p, r]
    have hempty (x : Row) : bondDefects ∅ x x = 0 := by simp [bondDefects]
    simp only [List.map_cons, List.map_nil, defects, tailDefects, hempty, Nat.zero_add,
      Nat.add_zero, HardinA229585Strip.edge] at hc
    exact hc
  simpa only [cross_eq, horizontal_eq,
    show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
    exhausted_relabel, cl_relabel] using h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem old_exhausted_index : ∀ p : Boundary, 16 ≤ (HardinA229585StripData.cl p 0).val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem old_lower_left : ∀ i : Fin 56, ∀ j : Fin 16,
    HardinA229585StripData.T (i.natAdd 16) (j.castAdd 56) = 0 := by
  decide +kernel

private theorem budget_one_leading (p : Boundary) (s : Fin 168) (hs : s.val < 16) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 1) s := by
  have he (q : Boundary) (k : ℕ) (hk : k ≤ 1) : 16 ≤ (cl q k).val := by
    have cases : k = 0 ∨ k = 1 := by omega
    rcases cases with rfl | rfl
    · simp [cl, Fin.val_natAdd] <;> omega
    · simpa [cl] using old_exhausted_index q
  have hsum : (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [ite_eq_right]
    rintro ⟨_, hr⟩
    have h := he (boundary r) (1 - (cross p r + bondDefects horizontal r r)) (by omega)
    rw [hr] at h
    omega
  rw [hsum]
  let j : Fin 16 := ⟨s.val, hs⟩
  have hj : ((j.castAdd 56).castAdd 96 : Fin 168) = s := Fin.ext rfl
  let i := HardinA229585StripData.cl p 0
  let k : Fin 56 := Fin.subNat 16 i (old_exhausted_index p)
  have hi : k.natAdd 16 = i := Fin.natAdd_subNat_cast (old_exhausted_index p)
  have ht : T (cl p 1) ((j.castAdd 56).castAdd 96) =
      HardinA229585StripData.T i (j.castAdd 56) := by
    simp only [cl, Nat.one_ne_zero, ite_false, Nat.sub_self, T, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, i]
  rw [← hj, ht, ← hi]
  exact (old_lower_left k j).symm

/-- Transfer multiplicities for both the positive and exhausted budgets. -/
theorem transition_counts (p : Boundary) (d : ℕ) (s : Fin 168)
    (hp : HardinA229635State.Valid p d ∨ (d = 0 ∧ s.val < 72) ∨ (d = 1 ∧ s.val < 16)) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  rcases hp with hv | hz | ho
  · induction s using Fin.addCases (m := 72) (n := 96) with
    | left j => exact leading_counts p d j (Or.inl hv)
    | right j =>
      simp_rw [exhausted_cut]
      exact class_counts p d hv j
  · obtain ⟨rfl, hs⟩ := hz
    let j : Fin 72 := ⟨s.val, hs⟩
    have hj : j.castAdd 96 = s := Fin.ext rfl
    rw [← hj]
    exact leading_counts p 0 j (Or.inr rfl)
  · obtain ⟨rfl, hs⟩ := ho
    exact budget_one_leading p s hs

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
    horizontal antidiagonal boundary cross HardinA229635State.Valid cl T initial terminal 2
    HardinA229585Strip.edge (fun p d _ => terminal_eq p d) next_valid
    (fun p d hp s => transition_counts p d s (Or.inl hp)) initial_valid initial_counts n

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
