/- GID: D5/S3/ConceptDynamics/InformationEscape/CountingReflection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CountingReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One strict list fold reflects every finite information-escape census. -/
import D5.S3.ConceptDynamics.InformationEscape.RoleHistogram
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import Mathlib.Tactic.FinCases
/- Library-search audit trail (2026-09-05):
   * Repository searches found the frozen `escapeNumerator`, `uniqueCaptureCount`,
     `roleHistogram`, `mem_without_iff`, and Boolean agreement reflection APIs.
   * Pinned Mathlib supplies `List.Nodup.card_eq_countP`, product-list nodup,
     `List.all_eq_true`, `List.finRange`, and finite extensionality.
   * No existing strict one-pass list census or named state enumeration was found.
The 5-prime escape witness is `foldPairs_value`: its live fold invariant classifies
every ordered list pair once, before enumeration completeness transports the count to
the frozen finset definitions. `uniqueCaptureCount_pos_of_list` is bind-only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT
universe u v w
attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq
namespace Arena
/-- An ordered, duplicate-free list containing every state of an arena. -/
structure StateEnumeration (arena : Arena.{u}) where
  states : List arena.State
  nodup : states.Nodup
  complete : states.toFinset = Finset.univ
end Arena
namespace Catalog
/-- An ordered, duplicate-free list containing every index of a catalog. -/
structure IndexEnumeration (Index : Type w) [DecidableEq Index] where
  indices : List Index
  nodup : indices.Nodup
  complete : forall index, index ∈ indices
/-- The canonical ascending enumeration of `Fin n`. -/
def finIndexEnumeration (n : Nat) : IndexEnumeration (Fin n) where
  indices := List.finRange n
  nodup := List.nodup_finRange n
  complete := by intro index; simp
/-- Strict one-pass counts for full escape, leave-one-out escape, and role masks.
Mask bits are high-first in CUT, FLOW, ADMIT, ANCHOR order. -/
structure ListUniqueCaptureSummary where
  fullEscapeCount : Nat
  withoutEscapeCount : Nat
  uniqueCaptureCount : Nat
  bucket01 : Nat
  bucket02 : Nat
  bucket03 : Nat
  bucket04 : Nat
  bucket05 : Nat
  bucket06 : Nat
  bucket07 : Nat
  bucket08 : Nat
  bucket09 : Nat
  bucket10 : Nat
  bucket11 : Nat
  bucket12 : Nat
  bucket13 : Nat
  bucket14 : Nat
  bucket15 : Nat
/-- Select mask bucket one through fifteen by its zero-based finite index. -/
def ListUniqueCaptureSummary.bucket
    (summary : ListUniqueCaptureSummary) (bucket : Fin 15) : Nat :=
  match bucket.1 with
  | 0 => summary.bucket01
  | 1 => summary.bucket02
  | 2 => summary.bucket03
  | 3 => summary.bucket04
  | 4 => summary.bucket05
  | 5 => summary.bucket06
  | 6 => summary.bucket07
  | 7 => summary.bucket08
  | 8 => summary.bucket09
  | 9 => summary.bucket10
  | 10 => summary.bucket11
  | 11 => summary.bucket12
  | 12 => summary.bucket13
  | 13 => summary.bucket14
  | _ => summary.bucket15
private def ListUniqueCaptureSummary.zero : ListUniqueCaptureSummary :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
private def maskSignature (mask : Fin 16) : Fin 4 -> Bool := fun coordinate =>
  match coordinate.1 with
  | 0 => mask.1.testBit 3
  | 1 => mask.1.testBit 2
  | 2 => mask.1.testBit 1
  | _ => mask.1.testBit 0
private def bucketMask (bucket : Fin 15) : Fin 16 :=
  ⟨bucket.1 + 1, by omega⟩
/-- The nonzero high-first role signature belonging to one reflected bucket. -/
def roleSignatureOfBucket (bucket : Fin 15) : Fin 4 -> Bool :=
  maskSignature (bucketMask bucket)
private theorem maskSignature_injective : Function.Injective maskSignature := by
  decide
private theorem roleSignatureOfBucket_ne_zero (bucket : Fin 15) :
    roleSignatureOfBucket bucket ≠ fun _ => false := by
  fin_cases bucket <;> decide
private def selectedMask {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State) : Fin 16 :=
  let cut := bundle.separatesOnAxis .cut left right
  let flow := bundle.separatesOnAxis .flow left right
  let admit := bundle.separatesOnAxis .admit left right
  let anchor := bundle.separatesOnAxis .anchor left right
  ⟨(if cut then 8 else 0) + (if flow then 4 else 0) +
      (if admit then 2 else 0) + (if anchor then 1 else 0), by
    cases cut <;> cases flow <;> cases admit <;> cases anchor <;> decide⟩
set_option linter.flexible false in
private theorem maskSignature_selectedMask {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State) :
    maskSignature (selectedMask bundle left right) = bundle.roleSignature left right := by
  funext coordinate
  cases hcut : bundle.separatesOnAxis .cut left right <;>
    cases hflow : bundle.separatesOnAxis .flow left right <;>
    cases hadmit : bundle.separatesOnAxis .admit left right <;>
    cases hanchor : bundle.separatesOnAxis .anchor left right <;>
    fin_cases coordinate <;>
    simp [maskSignature, selectedMask, PrimitiveBundle.roleSignature,
      axisOfOrdinal, hcut, hflow, hadmit, hanchor] <;> decide
private def ListUniqueCaptureSummary.value
    (summary : ListUniqueCaptureSummary) (slot : Fin 18) : Nat :=
  match slot.1 with
  | 0 => summary.fullEscapeCount
  | 1 => summary.withoutEscapeCount
  | 2 => summary.uniqueCaptureCount
  | 3 => summary.bucket01
  | 4 => summary.bucket02
  | 5 => summary.bucket03
  | 6 => summary.bucket04
  | 7 => summary.bucket05
  | 8 => summary.bucket06
  | 9 => summary.bucket07
  | 10 => summary.bucket08
  | 11 => summary.bucket09
  | 12 => summary.bucket10
  | 13 => summary.bucket11
  | 14 => summary.bucket12
  | 15 => summary.bucket13
  | 16 => summary.bucket14
  | _ => summary.bucket15
private def pairClass (diagonal othersAgree : Bool) (mask : Fin 16)
    (slot : Fin 18) : Bool :=
  if diagonal || !othersAgree then false
  else
    match slot.1 with
    | 0 => mask == 0
    | 1 => true
    | 2 => mask != 0
    | n + 3 => mask.1 == n + 1
private def pairStep (diagonal othersAgree : Bool) (mask : Fin 16)
    (summary : ListUniqueCaptureSummary) : ListUniqueCaptureSummary :=
  match summary with
  | ⟨full, without, unique, b01, b02, b03, b04, b05, b06, b07, b08,
      b09, b10, b11, b12, b13, b14, b15⟩ =>
    if diagonal || !othersAgree then
      ⟨full, without, unique, b01, b02, b03, b04, b05, b06, b07, b08,
        b09, b10, b11, b12, b13, b14, b15⟩
    else
      match mask.1 with
      | 0 =>
          ⟨full + 1, without + 1, unique, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 1 =>
          ⟨full, without + 1, unique + 1, b01 + 1, b02, b03, b04, b05,
            b06, b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 2 =>
          ⟨full, without + 1, unique + 1, b01, b02 + 1, b03, b04, b05,
            b06, b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 3 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03 + 1, b04, b05,
            b06, b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 4 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04 + 1, b05,
            b06, b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 5 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05 + 1,
            b06, b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 6 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05,
            b06 + 1, b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 7 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07 + 1, b08, b09, b10, b11, b12, b13, b14, b15⟩
      | 8 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08 + 1, b09, b10, b11, b12, b13, b14, b15⟩
      | 9 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09 + 1, b10, b11, b12, b13, b14, b15⟩
      | 10 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10 + 1, b11, b12, b13, b14, b15⟩
      | 11 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10, b11 + 1, b12, b13, b14, b15⟩
      | 12 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10, b11, b12 + 1, b13, b14, b15⟩
      | 13 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10, b11, b12, b13 + 1, b14, b15⟩
      | 14 =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10, b11, b12, b13, b14 + 1, b15⟩
      | _ =>
          ⟨full, without + 1, unique + 1, b01, b02, b03, b04, b05, b06,
            b07, b08, b09, b10, b11, b12, b13, b14, b15 + 1⟩
set_option maxHeartbeats 800000 in
-- Exhaustively checks 18 projections against all 16 masks in the strict constructor.
private theorem pairStep_value (diagonal othersAgree : Bool) (mask : Fin 16)
    (summary : ListUniqueCaptureSummary) (slot : Fin 18) :
    (pairStep diagonal othersAgree mask summary).value slot =
      summary.value slot + (pairClass diagonal othersAgree mask slot).toNat := by
  rcases summary with ⟨full, without, unique, b01, b02, b03, b04, b05, b06,
    b07, b08, b09, b10, b11, b12, b13, b14, b15⟩
  cases diagonal <;> cases othersAgree <;> fin_cases mask <;> fin_cases slot <;>
    simp [pairStep, pairClass, ListUniqueCaptureSummary.value]
private def pairDiagonal {arena : Arena.{u}} (left right : arena.State) : Bool :=
  left == right
private def pairOthersAgree {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) : Bool :=
  indices.indices.all fun candidate =>
    candidate == index || (catalog.theoremAt candidate).primitives.agreesB left right
private def reflectedPairStep {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (summary : ListUniqueCaptureSummary)
    (left right : arena.State) : ListUniqueCaptureSummary :=
  pairStep (pairDiagonal left right)
    (pairOthersAgree catalog indices index left right)
    (selectedMask (catalog.theoremAt index).primitives left right) summary
/-- Compute every leave-one-out count in one strict nested fold over ordered states. -/
def listUniqueCaptureSummary {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    ListUniqueCaptureSummary :=
  states.states.foldl (fun summary left =>
    states.states.foldl (fun summary right =>
      reflectedPairStep catalog indices index summary left right) summary)
    ListUniqueCaptureSummary.zero
private def reflectedPairClass {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (slot : Fin 18) (pair : arena.State × arena.State) : Bool :=
  pairClass (pairDiagonal pair.1 pair.2)
    (pairOthersAgree catalog indices index pair.1 pair.2)
    (selectedMask (catalog.theoremAt index).primitives pair.1 pair.2) slot
private theorem boolToNat_eq_indicator (value : Bool) :
    value.toNat = if value = true then 1 else 0 := by
  cases value <;> rfl
private theorem foldPairs_value {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (slot : Fin 18) (pairs : List (arena.State × arena.State))
    (summary : ListUniqueCaptureSummary) :
    (pairs.foldl (fun summary pair =>
      reflectedPairStep catalog indices index summary pair.1 pair.2) summary).value slot =
      summary.value slot + pairs.countP (reflectedPairClass catalog indices index slot) := by
  induction pairs generalizing summary with
  | nil => simp
  | cons pair pairs inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      simp only [reflectedPairStep, pairStep_value, List.countP_cons]
      change summary.value slot +
          (reflectedPairClass catalog indices index slot pair).toNat + _ =
        summary.value slot + (_ + if
          reflectedPairClass catalog indices index slot pair = true then 1 else 0)
      rw [← boolToNat_eq_indicator]
      omega
private theorem product_foldl {alpha beta gamma : Type*}
    (step : gamma -> alpha -> beta -> gamma) (lefts : List alpha) (rights : List beta)
    (initial : gamma) :
    (lefts ×ˢ rights).foldl (fun state pair => step state pair.1 pair.2) initial =
      lefts.foldl (fun state left => rights.foldl (fun state right =>
        step state left right) state) initial := by
  induction lefts generalizing initial with
  | nil => rfl
  | cons left lefts inductionHypothesis =>
      simp only [List.product_cons, List.foldl_append, List.foldl_map]
      exact inductionHypothesis _
private theorem ListUniqueCaptureSummary.zero_value (slot : Fin 18) :
    ListUniqueCaptureSummary.zero.value slot = 0 := by
  fin_cases slot <;> rfl
private def bucketSlot (bucket : Fin 15) : Fin 18 :=
  ⟨bucket.1 + 3, by omega⟩
private theorem ListUniqueCaptureSummary.bucket_eq_value
    (summary : ListUniqueCaptureSummary) (bucket : Fin 15) :
    summary.bucket bucket = summary.value (bucketSlot bucket) := by
  fin_cases bucket <;> rfl
private theorem listSummary_value {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) (slot : Fin 18) :
    (catalog.listUniqueCaptureSummary states indices index).value slot =
      (states.states ×ˢ states.states).countP
        (reflectedPairClass catalog indices index slot) := by
  rw [listUniqueCaptureSummary, ← product_foldl,
    foldPairs_value, ListUniqueCaptureSummary.zero_value, Nat.zero_add]
private theorem statePairs_nodup {arena : Arena.{u}}
    (states : Arena.StateEnumeration arena) :
    (states.states ×ˢ states.states).Nodup :=
  states.nodup.product states.nodup
private theorem statePairs_toFinset {arena : Arena.{u}}
    (states : Arena.StateEnumeration arena) :
    (states.states ×ˢ states.states).toFinset = Finset.univ := by
  ext pair
  rcases pair with ⟨left, right⟩
  simp only [List.mem_toFinset, List.mem_product, Finset.mem_univ, iff_true]
  constructor
  · rw [← List.mem_toFinset, states.complete]
    exact Finset.mem_univ left
  · rw [← List.mem_toFinset, states.complete]
    exact Finset.mem_univ right
private theorem statePairs_countP_eq_card {arena : Arena.{u}}
    (states : Arena.StateEnumeration arena) (predicate : arena.State × arena.State -> Bool) :
    (states.states ×ˢ states.states).countP predicate =
      (Finset.univ.filter fun pair => predicate pair = true).card := by
  have countAsPredicate := (statePairs_nodup states).card_eq_countP
    (P := fun pair => predicate pair = true)
  rw [statePairs_toFinset states] at countAsPredicate
  have samePredicate : (fun pair => decide (predicate pair = true)) = predicate := by
    funext pair
    cases predicate pair <;> rfl
  rw [samePredicate] at countAsPredicate
  exact countAsPredicate.symm
private theorem pairOthersAgree_eq_true_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    pairOthersAgree catalog indices index left right = true ↔
      catalog.indistinguishable (catalog.without index) left right := by
  rw [catalog.indistinguishable_iff_forall]
  constructor
  · intro allAgree candidate candidateMem
    have candidateResult := List.all_eq_true.mp allAgree candidate
      (indices.complete candidate)
    simp only [Bool.or_eq_true, beq_iff_eq,
      PrimitiveBundle.agreesB_eq_true_iff] at candidateResult
    rcases candidateResult with same | agrees
    · exact False.elim (((catalog.mem_without_iff index candidate).1 candidateMem) same)
    · exact agrees
  · intro allAgree
    apply List.all_eq_true.mpr
    intro candidate candidateMem
    by_cases same : candidate = index
    · simp [same]
    · simp only [Bool.or_eq_true, beq_iff_eq,
        PrimitiveBundle.agreesB_eq_true_iff]
      exact Or.inr (allAgree candidate (catalog.mem_without_iff index candidate |>.2 same))
private theorem selectedMask_eq_zero_iff {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State) :
    selectedMask bundle left right = 0 ↔ bundle.agrees left right := by
  rw [bundle.agrees_iff_roleSignature_zero]
  constructor
  · intro maskZero
    rw [← maskSignature_selectedMask bundle left right, maskZero]
    decide
  · intro signatureZero
    apply maskSignature_injective
    rw [maskSignature_selectedMask bundle left right, signatureZero]
    decide
private theorem selectedMask_eq_bucketMask_iff {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State)
    (bucket : Fin 15) :
    selectedMask bundle left right = bucketMask bucket ↔
      bundle.roleSignature left right = roleSignatureOfBucket bucket := by
  rw [← maskSignature_selectedMask bundle left right]
  exact maskSignature_injective.eq_iff.symm
private theorem residualSignature_eq_bucket_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (index : catalog.Index)
    (left right : arena.State) (bucket : Fin 15) :
    (catalog.theoremAt index).primitives.residualRoleSignature
        (catalog.withoutKernel index) left right = roleSignatureOfBucket bucket ↔
      catalog.indistinguishable (catalog.without index) left right ∧
        (catalog.theoremAt index).primitives.roleSignature left right =
          roleSignatureOfBucket bucket := by
  by_cases current : catalog.indistinguishable (catalog.without index) left right
  · unfold PrimitiveBundle.residualRoleSignature withoutKernel
    have currentDecision :
        @decide (catalog.indistinguishable (catalog.without index) left right)
          (catalog.indistinguishableDecidable
            (catalog.without index) left right) = true :=
      decide_eq_true current
    constructor
    · intro equality
      refine ⟨current, ?_⟩
      funext coordinate
      have atCoordinate := congrFun equality coordinate
      change (catalog.theoremAt index).primitives.separatesOnAxis
        (axisOfOrdinal coordinate) left right = roleSignatureOfBucket bucket coordinate
      simpa only [currentDecision, Bool.true_and] using atCoordinate
    · rintro ⟨_, equality⟩
      funext coordinate
      simp only [currentDecision, Bool.true_and]
      have atCoordinate := congrFun equality coordinate
      change (catalog.theoremAt index).primitives.separatesOnAxis
        (axisOfOrdinal coordinate) left right =
          roleSignatureOfBucket bucket coordinate at atCoordinate
      exact atCoordinate
  · have nonzero := roleSignatureOfBucket_ne_zero bucket
    unfold PrimitiveBundle.residualRoleSignature withoutKernel
    constructor
    · intro equality
      exact False.elim (nonzero (by
        funext coordinate
        have atCoordinate := congrFun equality coordinate
        simpa [current] using atCoordinate.symm))
    · rintro ⟨agreement, _⟩
      exact False.elim (current agreement)
private theorem fullAgreement_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (index : catalog.Index)
    (left right : arena.State) :
    catalog.indistinguishable catalog.fullIndexSet left right ↔
      catalog.indistinguishable (catalog.without index) left right ∧
        (catalog.theoremAt index).primitives.agrees left right := by
  simp only [catalog.indistinguishable_iff_forall]
  constructor
  · intro fullAgreement
    constructor
    · intro candidate candidateMem
      exact fullAgreement candidate (Finset.mem_univ candidate)
    · exact fullAgreement index (Finset.mem_univ index)
  · rintro ⟨withoutAgreement, selectedAgreement⟩ candidate _
    by_cases same : candidate = index
    · simpa [same] using selectedAgreement
    · exact withoutAgreement candidate (catalog.mem_without_iff index candidate |>.2 same)
private theorem pairClass_full_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    reflectedPairClass catalog indices index 0 (left, right) = true ↔
      left ≠ right ∧ catalog.indistinguishable catalog.fullIndexSet left right := by
  by_cases diagonal : left = right
  · subst right
    simp [reflectedPairClass, pairClass, pairDiagonal]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    rw [fullAgreement_iff catalog index left right,
      ← pairOthersAgree_eq_true_iff catalog indices index left right,
      ← selectedMask_eq_zero_iff (catalog.theoremAt index).primitives left right]
    simp [reflectedPairClass, pairClass, pairDiagonal, diagonal, diagonalB]
private theorem pairClass_without_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    reflectedPairClass catalog indices index 1 (left, right) = true ↔
      left ≠ right ∧ catalog.indistinguishable (catalog.without index) left right := by
  by_cases diagonal : left = right
  · subst right
    simp [reflectedPairClass, pairClass, pairDiagonal]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    rw [← pairOthersAgree_eq_true_iff catalog indices index left right]
    simp [reflectedPairClass, pairClass, pairDiagonal, diagonal, diagonalB]
private theorem pairClass_unique_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    reflectedPairClass catalog indices index 2 (left, right) = true ↔
      left ≠ right ∧ catalog.indistinguishable (catalog.without index) left right ∧
        ¬(catalog.theoremAt index).primitives.agrees left right := by
  by_cases diagonal : left = right
  · subst right
    simp [reflectedPairClass, pairClass, pairDiagonal]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    rw [← pairOthersAgree_eq_true_iff catalog indices index left right,
      ← selectedMask_eq_zero_iff (catalog.theoremAt index).primitives left right]
    simp [reflectedPairClass, pairClass, pairDiagonal, diagonal, diagonalB]
private theorem pairClass_bucket_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) (bucket : Fin 15) :
    reflectedPairClass catalog indices index (bucketSlot bucket) (left, right) = true ↔
      left ≠ right ∧ catalog.indistinguishable (catalog.without index) left right ∧
        (catalog.theoremAt index).primitives.roleSignature left right =
          roleSignatureOfBucket bucket := by
  by_cases diagonal : left = right
  · subst right
    simp [reflectedPairClass, pairClass, pairDiagonal]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    rw [← pairOthersAgree_eq_true_iff catalog indices index left right,
      ← selectedMask_eq_bucketMask_iff
        (catalog.theoremAt index).primitives left right bucket]
    fin_cases bucket <;>
      simp [reflectedPairClass, pairClass, pairDiagonal, bucketSlot, bucketMask,
        diagonal, diagonalB, Fin.ext_iff]
/-- The list fold's full-catalog field equals the frozen escape numerator. -/
theorem listFullEscapeCount_eq_escapeNumerator {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    (catalog.listUniqueCaptureSummary states indices index).fullEscapeCount =
      catalog.escapeNumerator catalog.fullIndexSet := by
  change (catalog.listUniqueCaptureSummary states indices index).value 0 = _
  rw [listSummary_value, statePairs_countP_eq_card states]
  unfold escapeNumerator escapePairs offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pairClass_full_iff catalog indices index pair.1 pair.2
/-- The list fold's leave-one-out field equals the frozen escape numerator. -/
theorem listWithoutEscapeCount_eq_escapeNumerator {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    (catalog.listUniqueCaptureSummary states indices index).withoutEscapeCount =
      catalog.escapeNumerator (catalog.without index) := by
  change (catalog.listUniqueCaptureSummary states indices index).value 1 = _
  rw [listSummary_value, statePairs_countP_eq_card states]
  unfold escapeNumerator escapePairs offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pairClass_without_iff catalog indices index pair.1 pair.2
/-- The list fold's unique field equals the frozen unique-capture count. -/
theorem listUniqueCaptureCount_eq_uniqueCaptureCount {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    (catalog.listUniqueCaptureSummary states indices index).uniqueCaptureCount =
      catalog.uniqueCaptureCount index := by
  change (catalog.listUniqueCaptureSummary states indices index).value 2 = _
  rw [listSummary_value, statePairs_countP_eq_card states]
  unfold uniqueCaptureCount uniqueCapturePairs escapePairs offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
  exact pairClass_unique_iff catalog indices index pair.1 pair.2
/-- Every reflected nonzero role bucket equals the frozen residual histogram. -/
theorem listBucket_eq_roleHistogram {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index)
    (bucket : Fin 15) :
    (catalog.listUniqueCaptureSummary states indices index).bucket bucket =
      catalog.roleHistogram index (roleSignatureOfBucket bucket) := by
  rw [ListUniqueCaptureSummary.bucket_eq_value, listSummary_value,
    statePairs_countP_eq_card states]
  unfold roleHistogram PrimitiveBundle.residualSignatureHistogram offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pairClass_bucket_iff catalog indices index pair.1 pair.2 bucket,
    residualSignature_eq_bucket_iff catalog index pair.1 pair.2 bucket]
/-- A positive reflected unique count transports to the frozen census. -/
theorem uniqueCaptureCount_pos_of_list {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    0 < (catalog.listUniqueCaptureSummary states indices index).uniqueCaptureCount ->
      0 < catalog.uniqueCaptureCount index := by
  rw [catalog.listUniqueCaptureCount_eq_uniqueCaptureCount states indices index]
  exact id
end Catalog
end D5.S3.ConceptDynamics.InformationEscape
namespace D5.S3.ConceptDynamics.InformationEscape.CountingReflection
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
private def boolStates : List Bool := [false, true]
private def agendaStates : List Agenda :=
  (List.finRange 3).flatMap fun first =>
    (List.finRange 3).flatMap fun second =>
      (List.finRange 3).map fun final => ⟨first, second, final⟩
private def residueStates : List ResidueState :=
  [zeroState, tenState, fifteenState, twentyOneState]
private def spectrumStates : List SpectrumAtom :=
  [.t1, .t2, .t3, .t4, .t5]
private def contextStates : List BinaryInterpretationContext :=
  boolStates.flatMap fun admission =>
    boolStates.flatMap fun background =>
      boolStates.map fun goal =>
        { text := ()
          readerAdmission := admission
          background := background
          evaluationGoal := goal
          interpretationRule := () }
private abbrev InterventionModel :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM
private def interventionStates : List InterventionModel :=
  boolStates.flatMap fun ff =>
    boolStates.flatMap fun ft =>
      boolStates.flatMap fun tf =>
        boolStates.map fun tt =>
          ⟨fun exogenous treatment =>
            if exogenous then (if treatment then tt else tf)
            else if treatment then ft else ff⟩
private def unaryBoolTables : List (Bool -> Bool) :=
  [fun _ => false, fun bit => bit, fun bit => !bit, fun _ => true]
private abbrev ObservationModel :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM
private def observationStates : List ObservationModel :=
  [.xCausesY, .yCausesX].flatMap fun direction =>
    unaryBoolTables.flatMap fun root =>
      unaryBoolTables.map fun child => ⟨direction, root, child⟩
private def staticStates : List (Fin 3) := List.finRange 3
private def completionStates : List FourState := [.a, .b, .c, .d]
private def gluingStates : List (Bool × Bool × Bool) :=
  boolStates.flatMap fun first =>
    boolStates.flatMap fun second =>
      boolStates.map fun third => (first, second, third)
private def triggerOptions : List (Option Mechanism) :=
  [none, some .shooterA, some .shooterB]
private def preemptionStates : List PreemptionTrace :=
  triggerOptions.flatMap fun first =>
    triggerOptions.map fun second => fun time =>
      if time = 0 then first else second
end D5.S3.ConceptDynamics.InformationEscape.CountingReflection
section
set_option linter.style.nameCheck false
set_option linter.style.haveILetI false
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.CountingReflection
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
namespace D5.S3.ConceptDynamics.InformationEscapeArenas
namespace FirstThreeArenas.agendaPowerArena
/-- Deterministic enumeration companion for the agenda-power arena. -/
def __state_enumeration : Arena.StateEnumeration
    FirstThreeArenas.agendaPowerArena.toArena where
  states := agendaStates
  nodup := by change agendaStates.Nodup; decide
  complete := by
    letI := FirstThreeArenas.agendaFintype
    change agendaStates.toFinset = (Finset.univ : Finset Agenda); decide
end FirstThreeArenas.agendaPowerArena
namespace FirstThreeArenas.residueArena
/-- Deterministic enumeration companion for the adaptive-residue arena. -/
def __state_enumeration : Arena.StateEnumeration FirstThreeArenas.residueArena.toArena where
  states := residueStates
  nodup := by change residueStates.Nodup; decide
  complete := by change residueStates.toFinset = (Finset.univ : Finset ResidueState); decide
end FirstThreeArenas.residueArena
namespace FirstThreeArenas.spectrumArena
/-- Deterministic enumeration companion for the five-atom spectrum arena. -/
def __state_enumeration : Arena.StateEnumeration FirstThreeArenas.spectrumArena.toArena where
  states := spectrumStates
  nodup := by change spectrumStates.Nodup; decide
  complete := by change spectrumStates.toFinset = (Finset.univ : Finset SpectrumAtom); decide
end FirstThreeArenas.spectrumArena
namespace FourthFifthArenas.contextArena
/-- Deterministic enumeration companion for the interpretation-context arena. -/
def __state_enumeration : Arena.StateEnumeration FourthFifthArenas.contextArena.toArena where
  states := contextStates
  nodup := by
    letI := FourthFifthArenas.contextDecidableEq
    change contextStates.Nodup; decide
  complete := by
    letI := FourthFifthArenas.contextFintype
    letI := FourthFifthArenas.contextDecidableEq
    change contextStates.toFinset = (Finset.univ : Finset BinaryInterpretationContext); decide
end FourthFifthArenas.contextArena
namespace FourthFifthArenas.interventionArena
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
set_option maxHeartbeats 2000000 in
-- The explicit sixteen-table certificate needs the acceptance heartbeat cap.
/-- Deterministic enumeration companion for the counterfactual-intervention arena. -/
def __state_enumeration : Arena.StateEnumeration
    FourthFifthArenas.interventionArena.toArena where
  states := interventionStates
  nodup := by
    letI := FourthFifthArenas.modelDecidableEq
    change interventionStates.Nodup; decide
  complete := by
    letI := FourthFifthArenas.modelFintype
    letI := FourthFifthArenas.modelDecidableEq
    change interventionStates.toFinset = (Finset.univ : Finset DeterministicBoolSCM); decide
end FourthFifthArenas.interventionArena
namespace ObservationIntervention.observationInterventionArena
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
/-- Deterministic enumeration companion for the observation-intervention arena. -/
def __state_enumeration : Arena.StateEnumeration
    ObservationIntervention.observationInterventionArena.toArena where
  states := observationStates
  nodup := by change observationStates.Nodup; decide
  complete := by
    change observationStates.toFinset = (Finset.univ : Finset DeterministicBoolSCM); decide
end ObservationIntervention.observationInterventionArena
namespace StaticExactExperimentDesign.staticExactExperimentArena
/-- Deterministic enumeration companion for the static exact-experiment arena. -/
def __state_enumeration : Arena.StateEnumeration
    StaticExactExperimentDesign.staticExactExperimentArena.toArena where
  states := staticStates
  nodup := List.nodup_finRange 3
  complete := by change staticStates.toFinset = (Finset.univ : Finset (Fin 3)); decide
end StaticExactExperimentDesign.staticExactExperimentArena
namespace CommutingCompletionExchange.commutingCompletionArena
/-- Deterministic enumeration companion for the commuting-completion arena. -/
def __state_enumeration : Arena.StateEnumeration
    CommutingCompletionExchange.commutingCompletionArena.toArena where
  states := completionStates
  nodup := by change completionStates.Nodup; decide
  complete := by change completionStates.toFinset = (Finset.univ : Finset FourState); decide
end CommutingCompletionExchange.commutingCompletionArena
namespace LocalLawGluingObstruction.localLawGluingArena
/-- Deterministic enumeration companion for the local-law-gluing arena. -/
def __state_enumeration : Arena.StateEnumeration
    LocalLawGluingObstruction.localLawGluingArena.toArena where
  states := gluingStates
  nodup := by change gluingStates.Nodup; decide
  complete := by
    change gluingStates.toFinset = (Finset.univ : Finset (Bool × Bool × Bool)); decide
end LocalLawGluingObstruction.localLawGluingArena
namespace EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
/-- Deterministic enumeration companion for the preemption-trace arena. -/
def __state_enumeration : Arena.StateEnumeration
    EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.toArena where
  states := preemptionStates
  nodup := by change preemptionStates.Nodup; decide
  complete := by change preemptionStates.toFinset = (Finset.univ : Finset PreemptionTrace); decide
end EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
end D5.S3.ConceptDynamics.InformationEscapeArenas
namespace D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
/-- Deterministic enumeration companion for the two-stage system arena. -/
def __state_enumeration : Arena.StateEnumeration SystemUnit.arena.toArena where
  states := [false, true]
  nodup := by decide
  complete := by decide
end D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
end
namespace D5.S3.ConceptDynamics.InformationEscape.CountingReflection
universe u v w
open D5.S3.ConceptDynamics.InformationEscape.Catalog
open D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
set_option linter.style.haveILetI false in
private def singletonCatalog {arena : PrimitiveLawArena.{u, v, w}}
    (realization : PrimitiveRealization arena.signature) :
    Catalog.{u, v, 0} arena.toArena := by
  letI := arena.toArena.stateDecidableEq
  exact
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      theoremAt := fun _ =>
        { primitives := realization.toPrimitiveBundle
          Statement := True
          proof := True.intro } }
private def singletonSummary {arena : PrimitiveLawArena.{u, v, w}}
    (realization : PrimitiveRealization arena.signature)
  (states : Arena.StateEnumeration arena.toArena) : ListUniqueCaptureSummary :=
  (singletonCatalog realization).listUniqueCaptureSummary states
    (finIndexEnumeration 1) (0 : Fin 1)
set_option linter.style.setOption false in
-- The executable censuses share the acceptance resource envelope.
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
example : (singletonSummary agendaPowerRealization
    agendaPowerArena.__state_enumeration).uniqueCaptureCount = 570 := by decide
example : (singletonSummary residueRealization
    residueArena.__state_enumeration).uniqueCaptureCount = 12 := by decide
example : (singletonSummary spectrumRealization
    spectrumArena.__state_enumeration).uniqueCaptureCount = 20 := by decide
example : (singletonSummary contextRealization
    contextArena.__state_enumeration).uniqueCaptureCount = 56 := by decide
example : (singletonSummary interventionRealization
    interventionArena.__state_enumeration).uniqueCaptureCount = 240 := by decide
example : (singletonSummary observationInterventionRealization
    observationInterventionArena.__state_enumeration).uniqueCaptureCount = 968 := by decide
example : (singletonSummary staticExactExperimentRealization
    staticExactExperimentArena.__state_enumeration).uniqueCaptureCount = 6 := by decide
example : (singletonSummary commutingCompletionRealization
    commutingCompletionArena.__state_enumeration).uniqueCaptureCount = 12 := by decide
example : (singletonSummary localLawGluingRealization
    localLawGluingArena.__state_enumeration).uniqueCaptureCount = 48 := by decide
example : (singletonSummary endStateOmitsPreemptingCauseRealization
    endStateOmitsPreemptingCauseArena.__state_enumeration).uniqueCaptureCount = 60 := by decide
example : (singletonSummary SystemUnit.systemRealization
    SystemUnit.arena.__state_enumeration).uniqueCaptureCount = 2 := by decide
end
end D5.S3.ConceptDynamics.InformationEscape.CountingReflection
