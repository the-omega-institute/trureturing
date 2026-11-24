/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts,D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.initial_counts
   digest: Exact successor multiplicities into the exhausted budget. -/

/-
admission_basis: escape-witness
escape_witness: exactExits_active and exactExits_new compute the multiplicities of transitions reaching budget zero
completionCodes: proof_shape=content; consumers=completionCodes_eq, exitCodes, exitCodes.eq_1, exitCodes_eq
completionCodes_eq: proof_shape=content; consumers=exitCodes_eq
completionCost: proof_shape=content; consumers=completionCost_row, completionRows_count, completionRows_length_le, exactExits_count
completionRows: proof_shape=content; consumers=completionCodes_eq, completionRows_count, completionRows_length_le, exactExits_count, exitCodes_bound, exitCodes_eq
completionRows_count: proof_shape=content; consumers=completionRows_length_le, exactExits_count
matchCost: proof_shape=bind-only; consumers=completionCodes._f, completionCodes._sunfold, completionCodes._unsafe_rec, completionCodes.eq_1, completionCodes.eq_2, completionCodes.eq_def, completionCodes_eq, completionCost._f, completionCost._sunfold, completionCost._unsafe_rec, completionCost.eq_1, completionCost.eq_2, completionCost.eq_def, completionCost_row, completionRows._f, completionRows._sunfold, completionRows._unsafe_rec, completionRows.eq_1, completionRows.eq_2, completionRows.eq_def, completionRows_count
rowCode_cons: proof_shape=bind-only; consumers=completionCodes_eq, rowCode_tail
tailCost_eq: proof_shape=bind-only; consumers=horizontal_cons, valid_shift
decidableBudget: proof_shape=bind-only; consumers=activeProfileCheck, exhaustedClass, inheritedActiveCheck
valid_parts: proof_shape=bind-only; consumers=class_counts_canonical, exactExits_active, exactExits_new, HardinA229693Strip.next_valid, valid_shift
valid_relabel: proof_shape=bind-only; consumers=class_counts
fresh_relabel: proof_shape=bind-only; consumers=cl_relabel, HardinA229693Strip.rep_weight
alternating: proof_shape=bind-only; consumers=properRows, proper_iff, zeroExitCodes_count
proper_iff: proof_shape=bind-only; consumers=zeroExitCodes_count._simp_1_2
properRows: proof_shape=bind-only; consumers=zeroExitCodes, zeroExitCodes_count, exactExits_new
zeroExitCodes: proof_shape=bind-only; consumers=zeroExitCodes_count, exhaustedMultiplicities, exactExits_new
zeroExitCodes_count: proof_shape=bind-only; consumers=class_counts_canonical
rep_partition: proof_shape=bind-only; consumers=exactExits_active, exactExits_new
oldZeroImage: proof_shape=bind-only; consumers=cl_relabel, class_counts_canonical, exhaustedClass, exhaustedClass.eq_1, old_exhausted_counts, old_exhausted_row
exhaustedClass: proof_shape=bind-only; consumers=active_cut, cl, cl.eq_1, cl_relabel, class_counts, class_counts_canonical, exactExits_count, exhausted_cut, exhausted_relabel, exitCodes_bound, exitCodes_eq, HardinA229693Strip.initial_counts, HardinA229693Strip.initial_counts._simp_2, HardinA229693Strip.initial_exhausted_count, HardinA229693Strip.initial_from_starts, leading_counts, old_exhausted_counts, old_exhausted_row, packedClass_all, packedClass_all._proof_1_1, packedClass_eq, HardinA229693Strip.rep_weight, HardinA229693Strip.terminal_eq, transition_counts, transition_counts._simp_1_6
cl: proof_shape=bind-only; consumers=active_cut, cl_relabel, class_counts, class_counts_canonical, HardinA229693Strip.count_transfer, exhausted_cut, HardinA229693Strip.initial_counts, HardinA229693Strip.initial_counts._simp_1, HardinA229693Strip.initial_counts._simp_2, leading_counts, leading_counts._simp_1_1, old_exhausted_counts, HardinA229693Strip.terminal_eq, transition_counts, transition_counts._simp_1_4, transition_counts._simp_1_6
exitRead: proof_shape=content; consumers=HardinA229693Strip.w, HardinA229693Strip.w_leading, HardinA229693Strip.w_copied, HardinA229693Strip.polynomialCoordinates, HardinA229693Strip.polynomial_relation, activeWeight, exhaustedWeight
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
T: proof_shape=content; consumers=HardinA229693Strip.exhausted_step, HardinA229693Strip.forward_step, HardinA229693Strip.forward_table, HardinA229693Strip.leading_action, HardinA229693Strip.polynomial_relation, HardinA229693Strip.result, HardinA229693Strip.rightColumn_eq, class_counts, class_counts_canonical, HardinA229693Strip.count_transfer, leading_counts, old_exhausted_counts, transition_counts
valid_shift: proof_shape=bind-only; consumers=class_counts_canonical, inherited_active_spec, leading_counts, old_valid
old_valid: proof_shape=bind-only; consumers=old_exhausted_counts, old_exhausted_row
cl_relabel: proof_shape=bind-only; consumers=class_counts, exhausted_relabel
exhausted_relabel: proof_shape=bind-only; consumers=class_counts, HardinA229693Strip.rep_weight
blocks_disjoint: proof_shape=bind-only; consumers=active_cut, exhausted_cut, old_exhausted_row
active_cut: proof_shape=bind-only; consumers=HardinA229693Strip.initial_counts._simp_1, leading_counts._simp_1_1, transition_counts._simp_1_4
exhausted_cut: proof_shape=bind-only; consumers=HardinA229693Strip.initial_counts._simp_2, transition_counts._simp_1_6
leading_counts: proof_shape=bind-only; consumers=transition_counts
old_exhausted_counts: proof_shape=bind-only; consumers=class_counts_canonical
completionCost_row: proof_shape=bind-only; consumers=exactExits_count
rowCode_tail: proof_shape=bind-only; consumers=exitCodes_eq
packedClass: proof_shape=bind-only; consumers=exitCodes, exitCodes.eq_1, exitCodes_eq, packedClass_all, packedClass_all._proof_1_1, packedClass_eq
packedClass_all: proof_shape=bind-only; consumers=packedClass_eq
packedClass_eq: proof_shape=bind-only; consumers=exitCodes_eq
exitCodes: proof_shape=content; consumers=class_counts_canonical, exactExits_active, exactExits_count, exitCodes_bound, exitCodes_eq, activeProfileCheck
exitCodes_eq: proof_shape=content; consumers=exactExits_count, exitCodes_bound
completionRows_length_le: proof_shape=content; consumers=exitCodes_bound
exitCodes_bound: proof_shape=content; consumers=exactExits_active
checkHistogram: proof_shape=bind-only; consumers=activeProfileCheck, checkHistogram_count, exactExits_active, exactExits_new, exhaustedMultiplicities, exhaustedMultiplicities._proof_1_1
checkHistogram_count: proof_shape=bind-only; consumers=exactExits_active, exactExits_new
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
transition_counts: proof_shape=content; consumers=HardinA229693Strip.count_transfer, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer.Transition.family._proof_3
horizontal_cons: proof_shape=bind-only; consumers=HardinA229693Strip.head_weight_eq, HardinA229693Strip.next_valid, HardinA229693Strip.initial_valid
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Logic.Equiv.Prod
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
open HardinA229585StripData (Boundary Row horizontal antidiagonal boundary cross)
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (relabel_defects defects tailDefects)

private instance decidableBudget (p : Boundary) (d : ℕ) :
    Decidable (HardinA229635State.Valid p d) :=
  inferInstanceAs (Decidable (HardinA229635State.h p + d ≤ 2))
theorem valid_parts (p : Boundary) (d : ℕ) :
    HardinA229635State.Valid p d ↔ d ≤ 2 ∧ HardinA229635State.h p ≤ 2 - d := by
  change HardinA229635State.h p + d ≤ 2 ↔ _
  omega

private theorem bond_eq_adjacent {k : ℕ} (r : Fin (k + 1) → Fin 3) :
    bondDefects (Finset.univ.image fun j : Fin k => (j.castSucc, j.succ)) r r =
      (Finset.univ.filter fun j : Fin k => r j.castSucc = r j.succ).card := by
  have he : HardinA229637RowColumn.horiz (k + 1) =
      Finset.univ.image (fun j : Fin k => (j.castSucc, j.succ)) := by
    ext e
    simp only [HardinA229637RowColumn.horiz, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      have hi : e.1.val < k := by have := e.2.isLt; omega
      exact ⟨e.1.castLT hi, Prod.ext (Fin.ext rfl) (Fin.ext h.symm)⟩
    · rintro ⟨j, rfl⟩
      rfl
  rw [← he, HardinA229637RowColumn.bond_row, ← Finset.card_map (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))]
  change (Finset.univ.filter fun i : Fin (k + 1) =>
    ∃ j : Fin (k + 1), j.val = i.val + 1 ∧ r i = r j).card = _
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨j, hj, h⟩
    have hi : i.val < k := by have := j.isLt; omega
    let x : Fin k := i.castLT hi
    have hx : x.castSucc = i := Fin.castSucc_castLT i hi
    have hy : x.succ = j := Fin.ext hj.symm
    refine ⟨x, ?_, hx⟩
    simpa only [hx, hy] using h
  · rintro ⟨j, h, rfl⟩
    exact ⟨j.succ, rfl, h⟩

private theorem tailCost_eq (p : Boundary) :
    HardinA229635State.h p =
      (Finset.univ.filter fun j : Fin 5 => p j.castSucc = p j.succ).card :=
  bond_eq_adjacent p

private theorem valid_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    HardinA229635State.Valid (e ∘ p) d ↔ HardinA229635State.Valid p d := by
  simp only [HardinA229635State.Valid, HardinA229635State.h_relabel]
theorem fresh_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    HardinA229635State.fresh (e ∘ p) = HardinA229635State.fresh p := by
  apply Fin.natAdd_injective 96 31
  simpa only [HardinA229635State.cl, show ∀ n : ℕ, ¬ n + 3 ≤ 1 from fun _ => by omega,
    ite_false] using HardinA229635State.cl_relabel e p 3

def oldZeroImage (i : Fin 72) : Fin 96 :=
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
theorem exhausted_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) :
    exhaustedClass (e ∘ p) = exhaustedClass p :=
  Fin.natAdd_injective 96 72 (cl_relabel e p 0)
private theorem blocks_disjoint {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≠ j.natAdd m :=
  finSumFinEquiv.injective.ne Sum.inl_ne_inr
theorem active_cut (p : Boundary) (d c : ℕ) (j : Fin 72) :
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
theorem exhausted_cut (p : Boundary) (d c : ℕ) (j : Fin 96) :
    (c ≤ d ∧ cl p (d - c) = j.natAdd 72) ↔ (c = d ∧ exhaustedClass p = j) := by
  by_cases h : c < d
  · have hn : d - c ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt h)
    simp [cl, hn, blocks_disjoint (HardinA229585StripData.cl p (d - c - 1)) j, h.ne]
  · simp only [cl, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h), ↓reduceIte]
    rw [Fin.natAdd_inj 72]
    exact and_congr_left (fun _ => ⟨fun hc => hc.antisymm (Nat.le_of_not_gt h), Eq.le⟩)
theorem horizontal_cons (x : Fin 3) (p : Boundary) :
    bondDefects horizontal (Fin.cons x p) (Fin.cons x p) =
      (if x = p 0 then 1 else 0) + HardinA229635State.h p := by
  rw [tailCost_eq]
  rw [horizontal, bond_eq_adjacent]
  let r : Row := Fin.cons x p
  have h : (∑ j : Fin 6, if r j.castSucc = r j.succ then (1 : ℕ) else 0) =
      (Finset.univ.filter fun j : Fin 6 => r j.castSucc = r j.succ).card := by
    simpa using (Finset.sum_boole (R := ℕ) (fun j : Fin 6 => r j.castSucc = r j.succ) Finset.univ)
  change (Finset.univ.filter fun j : Fin 6 => r j.castSucc = r j.succ).card = _
  rw [← h, Fin.sum_univ_succ]
  simp only [r, Fin.castSucc_zero, Fin.castSucc_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_boole, Nat.cast_id]
private theorem leading_counts (p : Boundary) (d : ℕ) (j : Fin 72)
    (hp : HardinA229635State.Valid p d) (hd : 0 < d) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = j.castAdd 96
      then (1 : ℤ) else 0) = T (cl p d) (j.castAdd 96) := by
  simp_rw [active_cut]
  have hp' := (valid_shift p d hd).mp hp
  simp only [hd, true_and, cl, Nat.ne_of_gt hd, ite_false, T, Matrix.reindex_apply,
    Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
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
private def matchCost {m : ℕ} : Option (Fin m) → Fin m → ℕ
  | none, _ => 0
  | some p, x => if p = x then 1 else 0

private def completionCost {m : ℕ} : {k : ℕ} → (Fin k → Option (Fin m)) → Option (Fin m) →
    (Fin (k + 1) → Fin m) → ℕ
  | 0, _, prev, r => matchCost prev (r 0)
  | _k + 1, p, prev, r =>
    matchCost prev (r 0) + matchCost (p 0) (r 0) +
      completionCost (Fin.tail p) (some (r 0)) (Fin.tail r)

private def completionRows {m : ℕ} : {k : ℕ} → (Fin k → Option (Fin m)) → Option (Fin m) →
    ℕ → List (Fin (k + 1) → Fin m)
  | 0, _, prev, d =>
    ((List.finRange m).filter fun x => matchCost prev x == d).map fun x _ => x
  | _k + 1, p, prev, d => (List.finRange m).flatMap fun x =>
    let c := matchCost prev x + matchCost (p 0) x
    if c ≤ d then (completionRows (Fin.tail p) (some x) (d - c)).map (Fin.cons x) else []
private theorem completionRows_count {k m : ℕ} (p : Fin k → Option (Fin m))
    (prev : Option (Fin m)) (d : ℕ) (f : (Fin (k + 1) → Fin m) → Bool) :
    (completionRows p prev d).countP f =
      ∑ r, if completionCost p prev r = d ∧ f r = true then 1 else 0 := by
  induction k generalizing prev d with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) (Fin m)).symm.sum_comp]
    simp only [completionCost, completionRows, List.countP_map, List.countP_filter,
      Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply]
    let accepted (x : Fin m) := matchCost prev x = d ∧ f (fun _ : Fin 1 => x) = true
    have h : (List.finRange m).countP (fun x => f (fun _ : Fin 1 => x) &&
        (matchCost prev x == d)) = (List.finRange m).countP (fun x => decide (accepted x)) := by
      congr 1
      funext x
      rw [Bool.eq_iff_iff]
      simp [accepted, Bool.and_eq_true, beq_iff_eq, and_comm]
    rw [h, ← Finset.sum_filter_count_eq_countP accepted]
    rw [List.toFinset_finRange, Finset.sum_filter]
    simp only [List.count_finRange, accepted]
    rfl
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin m)).sum_comp, Fintype.sum_prod_type]
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

private def completionCodes {m : ℕ} : List (Option (Fin m)) → Option (Fin m) → ℕ → List ℕ
  | [], prev, d =>
    ((List.finRange m).filter fun x => matchCost prev x == d).map Fin.val
  | a :: as, prev, d => (List.finRange m).flatMap fun x =>
    let c := matchCost prev x + matchCost a x
    if c ≤ d then (completionCodes as (some x) (d - c)).map (fun r => x.val + m * r)
    else []
private theorem rowCode_cons {k m : ℕ} (x : Fin m) (r : Fin k → Fin m) :
    (finFunctionFinEquiv (Fin.cons x r)).val = x.val + m * (finFunctionFinEquiv r).val := by
  simp only [finFunctionFinEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl
private theorem completionCodes_eq {k m : ℕ} (p : Fin k → Option (Fin m))
    (prev : Option (Fin m)) (d : ℕ) :
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
private theorem completionCost_row (p : Boundary) (r : Row) :
    completionCost (m := 3) (some ∘ p) none r = cross p r + bondDefects horizontal r r := by
  calc
    _ = (List.ofFn fun j : Fin 6 => if p j = r j.castSucc then 1 else 0).sum +
        (List.ofFn fun j : Fin 6 => if r j.castSucc = r j.succ then 1 else 0).sum := by
      simp only [completionCost, matchCost, Fin.tail, Function.comp_apply, zero_add,
        Fin.castSucc_zero, Fin.castSucc_succ, List.ofFn_succ, List.ofFn_zero,
        List.sum_cons, List.sum_nil]
      ac_rfl
    _ = _ := by
      rw [horizontal, bond_eq_adjacent]
      simp only [List.sum_ofFn, Finset.sum_boole, cross, bondDefects, antidiagonal,
        Finset.filter_image, Fin.cons_succ]
      rw [Finset.card_image_of_injective _ (fun i j h => Fin.castSucc_injective 6 (congrArg Prod.snd h))]
      simp only [Nat.cast_id]
private theorem rowCode_tail (r : Row) :
    (finFunctionFinEquiv (boundary r)).val = (finFunctionFinEquiv r).val / 3 := by
  have h := rowCode_cons (r 0) (boundary r)
  rw [show Fin.cons (r 0) (boundary r) = r from Fin.cons_self_tail r] at h
  have hb := (r 0).isLt
  omega

private def classDigits : List ℕ :=
  List.ofFn fun i => (exhaustedClass (HardinA229635State.rowEquiv i)).val

private def packedClassWord : ℕ := eval% Nat.ofDigits 128 classDigits

private def packedClass (i : ℕ) : Fin 96 :=
  Fin.ofNat 96 ((packedClassWord >>> (7 * i)) % 128)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem packedClassWord_eq : packedClassWord = Nat.ofDigits 128 classDigits := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem packedClass_eq (p : Boundary) :
    packedClass (finFunctionFinEquiv p).val = exhaustedClass p := by
  let j : Fin 729 := finFunctionFinEquiv p
  have hj : j.val < classDigits.length := by simpa only [classDigits, List.length_ofFn] using j.isLt
  have hd (a : ℕ) (ha : a ∈ classDigits) : a < 128 := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (exhaustedClass (HardinA229635State.rowEquiv i)).isLt.trans (by decide)
  have hread : ((packedClassWord >>> (7 * j.val)) % 128) = (exhaustedClass p).val := by
    rw [packedClassWord_eq, Nat.shiftRight_eq_div_pow, pow_mul]
    change (Nat.ofDigits 128 classDigits / 128 ^ j.val) % 128 = _
    rw [Nat.ofDigits_div_pow_eq_ofDigits_drop _ (by decide) classDigits hd,
      Nat.ofDigits_mod_eq_head!, List.drop_eq_getElem_cons hj]
    have hp : HardinA229635State.rowEquiv j = p := Equiv.symm_apply_apply _ _
    simpa only [List.head!_cons, classDigits, List.getElem_ofFn, hp] using
      Nat.mod_eq_of_lt ((exhaustedClass p).isLt.trans (show 96 < 128 by decide))
  change Fin.ofNat 96 ((packedClassWord >>> (7 * j.val)) % 128) = _
  rw [hread]
  exact Fin.ext (Nat.mod_eq_of_lt (exhaustedClass p).isLt)
private def exitCodes {k : ℕ} (p : Fin k → Option (Fin 3)) (d : ℕ) :
    List (Fin 96) :=
  ((completionCodes (m := 3) (List.ofFn p) none d).map fun r => packedClass (r / 3))
private theorem exitCodes_eq (p : Fin 6 → Option (Fin 3)) (d : ℕ) :
    exitCodes p d =
      (completionRows (m := 3) p none d).map (fun r => exhaustedClass (boundary r)) := by
  rw [exitCodes, completionCodes_eq, List.map_map]
  apply List.map_congr_left
  intro r _
  change packedClass ((finFunctionFinEquiv r).val / 3) = exhaustedClass (boundary r)
  rw [← rowCode_tail r, packedClass_eq]
private theorem completionRows_length_le (p : Fin 6 → Option (Fin 3)) (d : ℕ) :
    (completionRows (m := 3) p none d).length ≤ 2187 := by
  rw [← List.countP_true]
  have h := completionRows_count (m := 3) p none d (fun _ => true)
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
  change ((completionRows (m := 3) (some ∘ p) none d).countP
    (fun r => exhaustedClass (boundary r) == j) : ℤ) = _
  exact_mod_cast (by
    simpa only [completionCost_row, beq_iff_eq] using
      completionRows_count (m := 3) (some ∘ p) none d (fun r => exhaustedClass (boundary r) == j) :
    _ = ∑ r : Row, if cross p r + bondDefects horizontal r r = d ∧
      exhaustedClass (boundary r) = j then (1 : ℕ) else 0)
private def alternating : Row ≃ Row :=
  let e := (Equiv.curry (Fin 1) (Fin 7) (Fin 3)).trans (Equiv.funUnique (Fin 1) Row)
  e.symm.trans ((HardinA233155ColumnTransfer.alternatingEquiv 1 7).trans e)
private theorem proper_iff (r : Row) :
    HardinA233155RowTransfer.rowLegal r ↔
      bondDefects horizontal (alternating r) (alternating r) = 0 := by
  have h := HardinA233155ColumnTransfer.alternating_legal 1 7 (fun p => r p.2)
  have hl : HardinA233155RowTransfer.Legal (fun p : Fin 1 × Fin 7 => r p.2) ↔
      HardinA233155RowTransfer.rowLegal r := by
    constructor
    · exact fun h => h.1 0
    · exact fun h => ⟨fun _ => h, fun i hi => by omega⟩
  rw [← hl, h, bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro hp e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    exact hp j.castSucc j.succ.isLt 0 0 (Or.inl rfl)
  · intro hp j hj a b _
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst a
    subst b
    exact hp (Finset.mem_image.mpr
      ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩)
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
  classical
  let accepted (r : Row) := cross p r = 0 ∧ exhaustedClass (boundary r) = j
  have hcount : (zeroExitCodes p).count j = properRows.countP (fun r => decide (accepted r)) := by
    simp only [zeroExitCodes, List.count_eq_countP, List.countP_map, List.countP_filter]
    congr 1
    funext r
    rw [Bool.eq_iff_iff]
    simp [accepted, Bool.and_eq_true, beq_iff_eq, and_comm]
  rw [hcount, Finset.sum_list_map_count]
  change _ = ∑ m ∈ properRows.toFinset, properRows.count m •
    (if accepted m then (1 : ℤ) else 0)
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Nat.cast_sum]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (Finset.sum_filter_count_eq_countP accepted properRows).symm
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
  simpa only [HardinA229585Strip.cross_relabel,
    show ∀ r : Row, bondDefects horizontal (e ∘ r) (e ∘ r) = bondDefects horizontal r r from
      fun r => relabel_defects horizontal antidiagonal e [r],
    show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
    exhausted_relabel, cl_relabel] using h

-- The inherited slice needs a finite index check. The other two row
-- families read their columns directly through exitRead.
private def exitRepresentative (key : Fin 108) : Fin 96 :=
  Fin.ofNat 96 ((List.ofFn exitRead).idxOf key)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem oldExits_representative (j : Fin 96) (hj : 72 ≤ (exitRead j).val) :
    (List.finRange 72).all (fun i => oldExits i (exitRepresentative (exitRead j)) ==
      oldExits i j) = true := by
  fin_cases j <;> revert hj <;> decide +kernel

private theorem inheritedSource_index (i : Fin 72) (k : Fin 16)
    (h : inheritedSource i = some k) : i = HardinA229585StripData.zeroBudgetClass k := by
  have hc : (inheritedSource i).all (fun l => decide (i = HardinA229585StripData.zeroBudgetClass l)) = true := by
    fin_cases i <;> decide +kernel
  simpa only [h, Option.all_some, decide_eq_true_eq] using hc

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem oldExits_copied_check (j : Fin 96) (hj : (exitRead j).val < 72) :
    let k := Fin.ofNat 72 (exitRead j).val
    ((List.finRange 16).all (fun i =>
        oldExits (i.castAdd 56) j == HardinA229585StripData.T (HardinA229585StripData.zeroBudgetClass i) k) &&
      (List.finRange 56).all (fun i => oldExits (i.natAdd 16) j == 0) &&
      (List.finRange 72).all (fun i => decide (0 ≤ HardinA229585StripData.T i k))) = true := by
  fin_cases j <;> revert hj <;> decide +kernel

set_option maxRecDepth 4000 in
theorem copied_column (j : Fin 96) (hj : (exitRead j).val < 72) (i : Fin 168) :
    T i (j.natAdd 72) = T i (Fin.castAdd 96 (⟨(exitRead j).val, hj⟩ : Fin 72)) := by
  let r : Fin 72 := ⟨(exitRead j).val, hj⟩
  change T i (j.natAdd 72) = T i (r.castAdd 96)
  have hk : Fin.ofNat 72 (exitRead j).val = r := Fin.ext (Nat.mod_eq_of_lt hj)
  have hread : exitRead j = r.castAdd 36 := Fin.ext rfl
  have hc := oldExits_copied_check j hj
  dsimp only at hc
  rw [hk, Bool.and_eq_true, Bool.and_eq_true] at hc
  induction i using Fin.addCases (m := 72) (n := 96) with
  | left i =>
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.of_apply]
    cases hi : inheritedSource i with
    | none =>
      simp only [activeWeight, hread,
        Fin.append_left]
      exact Int.toNat_of_nonneg
        (of_decide_eq_true (List.all_eq_true.mp hc.2 i (List.mem_finRange i)))
    | some k =>
      rw [inheritedSource_index i k hi]
      exact beq_iff_eq.mp (List.all_eq_true.mp hc.1.1 k (List.mem_finRange k))
  | right i =>
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply, Matrix.zero_apply]
    induction i using Fin.addCases (m := 56) (n := 40) with
    | left i =>
      rw [Fin.append_left]
      exact beq_iff_eq.mp (List.all_eq_true.mp hc.1.2 i (List.mem_finRange i))
    | right i =>
      simp only [Fin.append_right, exhaustedWeight,
        hread, Fin.append_left,
        Pi.zero_apply, Nat.cast_zero]

theorem new_column_congr (j k : Fin 96) (hj : 72 ≤ (exitRead j).val)
    (h : exitRead j = exitRead k) (i : Fin 168) :
    T i (j.natAdd 72) = T i (k.natAdd 72) := by
  have hk : 72 ≤ (exitRead k).val := h ▸ hj
  have hold (r : Fin 72) : oldExits r j = oldExits r k := by
    have hrep (l : Fin 96) (hl : 72 ≤ (exitRead l).val) :=
      beq_iff_eq.mp (List.all_eq_true.mp (oldExits_representative l hl) r (List.mem_finRange r))
    rw [← hrep j hj, h, hrep k hk]
  induction i using Fin.addCases (m := 72) (n := 96) with
  | left i =>
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    cases inheritedSource i with
    | none => rw [activeWeight, activeWeight, h]
    | some l => exact hold (l.castAdd 56)
  | right i =>
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    induction i using Fin.addCases (m := 56) (n := 40) with
    | left i => simpa only [Fin.append_left] using hold (i.natAdd 16)
    | right i => simp only [Fin.append_right, exhaustedWeight, h]

/-- Transfer multiplicities for both the positive and exhausted budgets. -/
theorem transition_counts (p : Boundary) (d : ℕ) (s : Fin 168)
    (hp : HardinA229635State.Valid p d) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  induction s using Fin.addCases (m := 72) (n := 96) with
  | left j =>
    by_cases hd : d = 0
    · subst d
      have hzero : T (cl p 0) (j.castAdd 96) = 0 := by
        simp only [T, cl, ↓reduceIte, Matrix.reindex_apply, Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [hzero]
      simp only [active_cut, Nat.lt_irrefl, false_and, ite_false, Finset.sum_const_zero]
    · exact leading_counts p d j hp (Nat.pos_of_ne_zero hd)
  | right j =>
    simp_rw [exhausted_cut]
    exact class_counts p d hp j
end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
