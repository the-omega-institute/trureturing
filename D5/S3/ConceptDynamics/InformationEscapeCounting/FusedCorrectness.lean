/- GID: D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The catalog-wide fused fold equals every frozen escape-count field. -/
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-09-05):
   * Attempt 1 supplied the state-pair transport and role-mask reflection pattern.
   * Repository search found the frozen leave-one-out and role-histogram sum theorems.
   * Pinned Mathlib supplies list count/card transport and finite sum reindexing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

private theorem maskSignature_injective : Function.Injective maskSignature := by
  decide

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

private theorem bucketMask_bucketOfMask (mask : Fin 16) (nonzero : mask ≠ 0) :
    bucketMask (bucketOfMask mask) = mask := by
  rcases mask with ⟨value, bound⟩
  cases value with
  | zero => exact False.elim (nonzero rfl)
  | succ value => simp [bucketOfMask, bucketMask]

private theorem bucketOfMask_eq_iff (mask : Fin 16) (nonzero : mask ≠ 0)
    (bucket : Fin 15) :
    bucketOfMask mask = bucket ↔ mask = bucketMask bucket := by
  constructor
  · intro equality
    rw [← bucketMask_bucketOfMask mask nonzero, equality]
  · intro equality
    subst mask
    apply Fin.ext
    simp [bucketOfMask, bucketMask]

private theorem scanAfterOne_ne_none {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : arena.State)
    (first : catalog.Index) (mask : Fin 16) (indices : List catalog.Index) :
    scanAfterOne catalog left right first mask indices ≠ .none := by
  induction indices with
  | nil => simp [scanAfterOne]
  | cons candidate rest inductionHypothesis =>
      cases agreement : (catalog.theoremAt candidate).primitives.agreesB left right <;>
        simp [scanAfterOne, agreement, inductionHypothesis]

private theorem scanAfterOne_eq_one_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : arena.State)
    (first index : catalog.Index) (firstMask mask : Fin 16)
    (indices : List catalog.Index) :
    scanAfterOne catalog left right first firstMask indices = .one index mask ↔
      index = first ∧ mask = firstMask ∧
        ∀ candidate ∈ indices,
          (catalog.theoremAt candidate).primitives.agreesB left right = true := by
  induction indices generalizing index mask with
  | nil =>
      constructor
      · intro equality
        have parts := PairScan.one.inj equality
        exact ⟨parts.1.symm, parts.2.symm, by simp⟩
      · rintro ⟨rfl, rfl, _⟩
        rfl
  | cons candidate rest inductionHypothesis =>
      cases agreement : (catalog.theoremAt candidate).primitives.agreesB left right <;>
        simp [scanAfterOne, agreement, inductionHypothesis]

private theorem scanIndices_eq_none_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : arena.State)
    (indices : List catalog.Index) :
    scanIndices catalog left right indices = .none ↔
      ∀ candidate ∈ indices,
        (catalog.theoremAt candidate).primitives.agreesB left right = true := by
  induction indices with
  | nil => simp [scanIndices]
  | cons candidate rest inductionHypothesis =>
      cases agreement : (catalog.theoremAt candidate).primitives.agreesB left right <;>
        simp [scanIndices, agreement, inductionHypothesis,
          scanAfterOne_ne_none]

private theorem scanIndices_eq_one_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : arena.State)
    (indices : List catalog.Index) (nodup : indices.Nodup)
    (index : catalog.Index) (mask : Fin 16) :
    scanIndices catalog left right indices = .one index mask ↔
      index ∈ indices ∧
        mask = selectedMask (catalog.theoremAt index).primitives left right ∧
        (catalog.theoremAt index).primitives.agreesB left right = false ∧
        ∀ candidate ∈ indices, candidate ≠ index ->
          (catalog.theoremAt candidate).primitives.agreesB left right = true := by
  induction indices generalizing index mask with
  | nil => simp [scanIndices]
  | cons candidate rest inductionHypothesis =>
      have candidateNotMem := (List.nodup_cons.mp nodup).1
      have restNodup := (List.nodup_cons.mp nodup).2
      cases agreement : (catalog.theoremAt candidate).primitives.agreesB left right
      · simp only [scanIndices, agreement, Bool.false_eq_true, ↓reduceIte]
        rw [scanAfterOne_eq_one_iff]
        constructor
        · rintro ⟨indexEq, maskEq, allRest⟩
          subst index
          refine ⟨by simp, maskEq, agreement, ?_⟩
          intro other otherMem otherNe
          simp only [List.mem_cons] at otherMem
          rcases otherMem with rfl | otherRest
          · exact False.elim (otherNe rfl)
          · exact allRest other otherRest
        · rintro ⟨indexMem, maskEq, indexDisagrees, othersAgree⟩
          have indexEq : index = candidate := by
            by_contra indexNe
            have agrees := othersAgree candidate (by simp) (Ne.symm indexNe)
            rw [agreement] at agrees
            contradiction
          subst index
          refine ⟨rfl, maskEq, ?_⟩
          intro other otherRest
          exact othersAgree other (by simp [otherRest]) (by
            intro same
            subst other
            exact candidateNotMem otherRest)
      · simp only [scanIndices, agreement, ↓reduceIte]
        rw [inductionHypothesis restNodup]
        constructor
        · rintro ⟨indexMem, maskEq, indexDisagrees, othersAgree⟩
          refine ⟨by simp [indexMem], maskEq, indexDisagrees, ?_⟩
          intro other otherMem otherNe
          simp only [List.mem_cons] at otherMem
          rcases otherMem with rfl | otherRest
          · exact agreement
          · exact othersAgree other otherRest otherNe
        · rintro ⟨indexMem, maskEq, indexDisagrees, othersAgree⟩
          have indexNe : index ≠ candidate := by
            intro same
            subst index
            rw [agreement] at indexDisagrees
            contradiction
          refine ⟨?_, maskEq, indexDisagrees, ?_⟩
          · simpa [indexNe, Ne.symm indexNe] using indexMem
          · intro other otherRest otherNe
            exact othersAgree other (by simp [otherRest]) otherNe

private theorem otherAgreement_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    (∀ candidate ∈ indices.indices, candidate ≠ index ->
        (catalog.theoremAt candidate).primitives.agreesB left right = true) ↔
      catalog.indistinguishable (catalog.without index) left right := by
  rw [catalog.indistinguishable_iff_forall]
  constructor
  · intro allAgree candidate candidateMem
    exact ((catalog.theoremAt candidate).primitives.agreesB_eq_true_iff
      left right).mp
      (allAgree candidate (indices.complete candidate)
        ((catalog.mem_without_iff index candidate).1 candidateMem))
  · intro allAgree candidate candidateMem candidateNe
    exact ((catalog.theoremAt candidate).primitives.agreesB_eq_true_iff
      left right).mpr
      (allAgree candidate (catalog.mem_without_iff index candidate |>.2 candidateNe))

private theorem agreesB_eq_false_iff {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State) :
    bundle.agreesB left right = false ↔ ¬bundle.agrees left right := by
  constructor
  · intro booleanFalse agreement
    have booleanTrue := (bundle.agreesB_eq_true_iff left right).mpr agreement
    rw [booleanFalse] at booleanTrue
    contradiction
  · intro disagreement
    cases booleanValue : bundle.agreesB left right
    · rfl
    · exact False.elim
        (disagreement ((bundle.agreesB_eq_true_iff left right).mp booleanValue))

private theorem pairScan_eq_none_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (left right : arena.State) :
    catalog.pairScan indices left right = .none ↔
      catalog.indistinguishable catalog.fullIndexSet left right := by
  rw [pairScan, scanIndices_eq_none_iff, catalog.indistinguishable_iff_forall]
  constructor
  · intro allAgree candidate _
    exact ((catalog.theoremAt candidate).primitives.agreesB_eq_true_iff
      left right).mp
      (allAgree candidate (indices.complete candidate))
  · intro allAgree candidate candidateMem
    exact ((catalog.theoremAt candidate).primitives.agreesB_eq_true_iff
      left right).mpr
      (allAgree candidate (Finset.mem_univ candidate))

private theorem pairScan_eq_one_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (mask : Fin 16) (left right : arena.State) :
    catalog.pairScan indices left right = .one index mask ↔
      mask = selectedMask (catalog.theoremAt index).primitives left right ∧
        catalog.indistinguishable (catalog.without index) left right ∧
        ¬(catalog.theoremAt index).primitives.agrees left right := by
  rw [pairScan, scanIndices_eq_one_iff catalog left right indices.indices
    indices.nodup index mask]
  simp only [indices.complete index, true_and]
  rw [otherAgreement_iff, agreesB_eq_false_iff]
  tauto

/-- The saturated scan classifies empty and singleton disagreement sets exactly. -/
theorem fusedPairClassification {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (left right : arena.State) :
    (catalog.pairScan indices left right = .none ↔
      catalog.indistinguishable catalog.fullIndexSet left right) ∧
    (∀ index mask, catalog.pairScan indices left right = .one index mask ↔
      mask = selectedMask (catalog.theoremAt index).primitives left right ∧
        catalog.indistinguishable (catalog.without index) left right ∧
        ¬(catalog.theoremAt index).primitives.agrees left right) := by
  exact ⟨pairScan_eq_none_iff catalog indices left right,
    fun index mask => pairScan_eq_one_iff catalog indices index mask left right⟩

private inductive FusedSlot (Index : Type w) where
  | full
  | unique (index : Index)
  | role (index : Index) (bucket : Fin 15)

private def FusedCounts.value {Index : Type w}
    (counts : FusedCounts Index) : FusedSlot Index -> Nat
  | .full => counts.full
  | .unique index => counts.unique index
  | .role index bucket => counts.roleBins index bucket

private def pairClass {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (slot : FusedSlot catalog.Index) (pair : arena.State × arena.State) : Bool :=
  if pair.1 == pair.2 then
    false
  else
    match slot with
    | .full =>
        match catalog.pairScan indices pair.1 pair.2 with
        | .none => true
        | _ => false
    | .unique index =>
        match catalog.pairScan indices pair.1 pair.2 with
        | .one found _ => found == index
        | _ => false
    | .role index bucket =>
        match catalog.pairScan indices pair.1 pair.2 with
        | .one found mask => found == index && bucketOfMask mask == bucket
        | _ => false

private theorem pairStep_value {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (counts : FusedCounts catalog.Index) (left right : arena.State)
    (slot : FusedSlot catalog.Index) :
    (pairStep catalog indices counts left right).value slot =
      counts.value slot + (pairClass catalog indices slot (left, right)).toNat := by
  cases diagonal : (left == right)
  · cases scan : catalog.pairScan indices left right with
    | none => cases slot <;>
        simp [pairStep, pairClass, diagonal, scan, FusedCounts.value]
    | many => cases slot <;>
        simp [pairStep, pairClass, diagonal, scan, FusedCounts.value]
    | one found mask =>
        cases slot with
        | full =>
            simp [pairStep, pairClass, diagonal, scan, FusedCounts.value,
              FusedCounts.bump]
        | unique index =>
            by_cases same : found = index
            · subst found
              simp [pairStep, pairClass, diagonal, scan, FusedCounts.value,
                FusedCounts.bump]
            · simp [pairStep, pairClass, diagonal, scan, FusedCounts.value,
                FusedCounts.bump, same, Ne.symm same]
        | role index bucket =>
            by_cases same : found = index
            · subst found
              by_cases sameBucket : bucketOfMask mask = bucket
              · subst bucket
                simp [pairStep, pairClass, diagonal, scan, FusedCounts.value,
                  FusedCounts.bump]
              · simp [pairStep, pairClass, diagonal, scan, FusedCounts.value,
                  FusedCounts.bump, sameBucket, Ne.symm sameBucket]
            · simp [pairStep, pairClass, diagonal, scan, FusedCounts.value,
                FusedCounts.bump, same, Ne.symm same]
  · cases slot <;> simp [pairStep, pairClass, diagonal, FusedCounts.value]

private theorem boolToNat_eq_indicator (value : Bool) :
    value.toNat = if value = true then 1 else 0 := by
  cases value <;> rfl

private theorem foldPairs_value {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (slot : FusedSlot catalog.Index) (pairs : List (arena.State × arena.State))
    (counts : FusedCounts catalog.Index) :
    (pairs.foldl (fun counts pair =>
      pairStep catalog indices counts pair.1 pair.2) counts).value slot =
      counts.value slot + pairs.countP (pairClass catalog indices slot) := by
  induction pairs generalizing counts with
  | nil => simp
  | cons pair pairs inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      simp only [pairStep_value, List.countP_cons]
      change counts.value slot + (pairClass catalog indices slot pair).toNat + _ =
        counts.value slot +
          (_ + if pairClass catalog indices slot pair = true then 1 else 0)
      rw [← boolToNat_eq_indicator]
      omega

private theorem product_foldl {alpha beta gamma : Type*}
    (step : gamma -> alpha -> beta -> gamma) (lefts : List alpha)
    (rights : List beta) (initial : gamma) :
    (lefts ×ˢ rights).foldl (fun state pair => step state pair.1 pair.2) initial =
      lefts.foldl (fun state left => rights.foldl (fun state right =>
        step state left right) state) initial := by
  induction lefts generalizing initial with
  | nil => rfl
  | cons left lefts inductionHypothesis =>
      simp only [List.product_cons, List.foldl_append, List.foldl_map]
      exact inductionHypothesis _

private theorem FusedCounts.zero_value {Index : Type w} (slot : FusedSlot Index) :
    (FusedCounts.zero : FusedCounts Index).value slot = 0 := by
  cases slot <;> rfl

private theorem fusedCounts_value {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (slot : FusedSlot catalog.Index) :
    (catalog.fusedCounts states indices).value slot =
      (states.states ×ˢ states.states).countP
        (pairClass catalog indices slot) := by
  rw [fusedCounts, ← product_foldl, foldPairs_value,
    FusedCounts.zero_value, Nat.zero_add]

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
    (states : Arena.StateEnumeration arena)
    (predicate : arena.State × arena.State -> Bool) :
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

private theorem pairScan_unique_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    (∃ mask, catalog.pairScan indices left right = .one index mask) ↔
      catalog.indistinguishable (catalog.without index) left right ∧
        ¬(catalog.theoremAt index).primitives.agrees left right := by
  constructor
  · rintro ⟨mask, scan⟩
    exact (pairScan_eq_one_iff catalog indices index mask left right).mp scan |>.2
  · rintro ⟨otherAgreement, disagreement⟩
    refine ⟨selectedMask (catalog.theoremAt index).primitives left right, ?_⟩
    exact (pairScan_eq_one_iff catalog indices index _ left right).mpr
      ⟨rfl, otherAgreement, disagreement⟩

private theorem pairClass_full_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (left right : arena.State) :
    pairClass catalog indices .full (left, right) = true ↔
      left ≠ right ∧
        catalog.indistinguishable catalog.fullIndexSet left right := by
  by_cases diagonal : left = right
  · subst right
    simp [pairClass]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    have scanFull :
        (match catalog.pairScan indices left right with
          | .none => true
          | _ => false) = true ↔
        catalog.pairScan indices left right = .none := by
      cases scan : catalog.pairScan indices left right <;> simp
    simp only [pairClass, diagonalB, Bool.false_eq_true, ↓reduceIte]
    rw [scanFull, pairScan_eq_none_iff]
    simp [diagonal]

private theorem pairClass_unique_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (left right : arena.State) :
    pairClass catalog indices (.unique index) (left, right) = true ↔
      left ≠ right ∧
        catalog.indistinguishable (catalog.without index) left right ∧
        ¬(catalog.theoremAt index).primitives.agrees left right := by
  by_cases diagonal : left = right
  · subst right
    simp [pairClass]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    have scanUnique :
        (match catalog.pairScan indices left right with
          | .one found _ => found == index
          | _ => false) = true ↔
        ∃ mask, catalog.pairScan indices left right = .one index mask := by
      cases scan : catalog.pairScan indices left right <;> simp
    simp only [pairClass, diagonalB, Bool.false_eq_true, ↓reduceIte]
    rw [scanUnique, pairScan_unique_iff]
    simp [diagonal]

private theorem pairScan_role_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (bucket : Fin 15) (left right : arena.State) :
    (∃ mask, catalog.pairScan indices left right = .one index mask ∧
        bucketOfMask mask = bucket) ↔
      catalog.indistinguishable (catalog.without index) left right ∧
        (catalog.theoremAt index).primitives.roleSignature left right =
          roleSignatureOfBucket bucket := by
  constructor
  · rintro ⟨mask, scan, maskBucket⟩
    have classification :=
      (pairScan_eq_one_iff catalog indices index mask left right).mp scan
    have maskNonzero : mask ≠ 0 := by
      intro maskZero
      have agrees := (selectedMask_eq_zero_iff
        (catalog.theoremAt index).primitives left right).mp
        (classification.1 ▸ maskZero)
      exact classification.2.2 agrees
    have maskEq := (bucketOfMask_eq_iff mask maskNonzero bucket).mp maskBucket
    refine ⟨classification.2.1, ?_⟩
    exact (selectedMask_eq_bucketMask_iff
      (catalog.theoremAt index).primitives left right bucket).mp
      (classification.1.symm.trans maskEq)
  · rintro ⟨otherAgreement, signatureEq⟩
    have maskEq := (selectedMask_eq_bucketMask_iff
      (catalog.theoremAt index).primitives left right bucket).mpr signatureEq
    have maskNonzero :
        selectedMask (catalog.theoremAt index).primitives left right ≠ 0 := by
      rw [maskEq]
      intro impossible
      have values := congrArg Fin.val impossible
      simp [bucketMask] at values
    have disagreement :
        ¬(catalog.theoremAt index).primitives.agrees left right := by
      intro agreement
      exact maskNonzero ((selectedMask_eq_zero_iff
        (catalog.theoremAt index).primitives left right).mpr agreement)
    refine ⟨selectedMask (catalog.theoremAt index).primitives left right,
      (pairScan_eq_one_iff catalog indices index _ left right).mpr
        ⟨rfl, otherAgreement, disagreement⟩, ?_⟩
    exact (bucketOfMask_eq_iff _ maskNonzero bucket).mpr maskEq

private theorem pairClass_role_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (index : catalog.Index) (bucket : Fin 15) (left right : arena.State) :
    pairClass catalog indices (.role index bucket) (left, right) = true ↔
      left ≠ right ∧
        catalog.indistinguishable (catalog.without index) left right ∧
        (catalog.theoremAt index).primitives.roleSignature left right =
          roleSignatureOfBucket bucket := by
  by_cases diagonal : left = right
  · subst right
    simp [pairClass]
  · have diagonalB : (left == right) = false := beq_eq_false_iff_ne.mpr diagonal
    have scanRole :
        (match catalog.pairScan indices left right with
          | .one found mask => found == index && bucketOfMask mask == bucket
          | _ => false) = true ↔
        ∃ mask, catalog.pairScan indices left right = .one index mask ∧
          bucketOfMask mask = bucket := by
      cases scan : catalog.pairScan indices left right <;> simp
    simp only [pairClass, diagonalB, Bool.false_eq_true, ↓reduceIte]
    rw [scanRole, pairScan_role_iff]
    simp [diagonal]

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
      exact congrFun equality coordinate
  · have nonzero : roleSignatureOfBucket bucket ≠ fun _ => false := by
      fin_cases bucket <;> decide
    unfold PrimitiveBundle.residualRoleSignature withoutKernel
    constructor
    · intro equality
      exact False.elim (nonzero (by
        funext coordinate
        have atCoordinate := congrFun equality coordinate
        simpa [current] using atCoordinate.symm))
    · rintro ⟨agreement, _⟩
      exact False.elim (current agreement)

/-- The fused full field is the frozen full-catalog escape numerator. -/
theorem fusedFull_eq_escapeNumerator {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) :
    (catalog.fusedCounts states indices).full =
      catalog.escapeNumerator catalog.fullIndexSet := by
  change (catalog.fusedCounts states indices).value .full = _
  rw [fusedCounts_value, statePairs_countP_eq_card states]
  unfold escapeNumerator escapePairs offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pairClass_full_iff catalog indices pair.1 pair.2

/-- Every fused unique field is the frozen unique-capture count. -/
theorem fusedUnique_eq_uniqueCaptureCount {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    (catalog.fusedCounts states indices).unique index =
      catalog.uniqueCaptureCount index := by
  change (catalog.fusedCounts states indices).value (.unique index) = _
  rw [fusedCounts_value, statePairs_countP_eq_card states]
  unfold uniqueCaptureCount uniqueCapturePairs escapePairs offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
  exact pairClass_unique_iff catalog indices index pair.1 pair.2

/-- Leave-one-out escape is derived as full plus unique, without rescanning. -/
theorem fusedWithout_eq_escapeNumerator_without {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    (catalog.fusedCounts states indices).without index =
      catalog.escapeNumerator (catalog.without index) := by
  rw [FusedCounts.without, catalog.fusedFull_eq_escapeNumerator states indices,
    catalog.fusedUnique_eq_uniqueCaptureCount states indices index,
    catalog.escapeNumerator_without_eq]

/-- Every fused role bin is the corresponding frozen residual histogram. -/
theorem fusedRoleBins_eq_roleHistogram {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index)
    (bucket : Fin 15) :
    (catalog.fusedCounts states indices).roleBins index bucket =
      catalog.roleHistogram index (roleSignatureOfBucket bucket) := by
  change (catalog.fusedCounts states indices).value (.role index bucket) = _
  rw [fusedCounts_value, statePairs_countP_eq_card states]
  unfold roleHistogram PrimitiveBundle.residualSignatureHistogram offDiagonalPairs
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pairClass_role_iff, residualSignature_eq_bucket_iff]

private theorem roleSignatureOfBucket_injective :
    Function.Injective roleSignatureOfBucket := by
  intro left right equality
  have maskEquality : bucketMask left = bucketMask right :=
    maskSignature_injective (by
      simpa only [roleSignatureOfBucket] using equality)
  apply Fin.ext
  have valueEquality := congrArg Fin.val maskEquality
  simpa only [bucketMask, Fin.mk.injEq] using Nat.add_right_cancel valueEquality

private theorem roleSignatureOfBucket_nonzero (bucket : Fin 15) :
    roleSignatureOfBucket bucket ≠ fun _ => false := by
  fin_cases bucket <;> decide

private theorem roleSignatureOfBucket_surjective_nonzero
    (signature : Fin 4 -> Bool) (nonzero : signature ≠ fun _ => false) :
    ∃ bucket, roleSignatureOfBucket bucket = signature := by
  have maskSurjective : Function.Surjective maskSignature :=
    ((Fintype.bijective_iff_injective_and_card maskSignature).2
      ⟨maskSignature_injective, by simp⟩).2
  obtain ⟨mask, rfl⟩ := maskSurjective signature
  have maskNonzero : mask ≠ 0 := by
    intro maskZero
    subst mask
    apply nonzero
    funext coordinate
    fin_cases coordinate <;> decide
  exact ⟨bucketOfMask mask, by
    rw [roleSignatureOfBucket, bucketMask_bucketOfMask mask maskNonzero]⟩

/-- For every theorem, the fifteen fused role bins sum to its fused unique count. -/
theorem fusedRoleBins_sum_eq_unique {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    (∑ bucket : Fin 15,
        (catalog.fusedCounts states indices).roleBins index bucket) =
      (catalog.fusedCounts states indices).unique index := by
  calc
    (∑ bucket : Fin 15,
        (catalog.fusedCounts states indices).roleBins index bucket) =
        ∑ bucket : Fin 15,
          catalog.roleHistogram index (roleSignatureOfBucket bucket) := by
      apply Finset.sum_congr rfl
      intro bucket _
      exact catalog.fusedRoleBins_eq_roleHistogram states indices index bucket
    _ = ∑ signature with signature ≠ fun _ => false,
        catalog.roleHistogram index signature := by
      apply Finset.sum_bij (fun bucket _ => roleSignatureOfBucket bucket)
      · intro bucket _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact roleSignatureOfBucket_nonzero bucket
      · intro left _ right _ equality
        exact roleSignatureOfBucket_injective equality
      · intro signature signatureMem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at signatureMem
        obtain ⟨bucket, equality⟩ :=
          roleSignatureOfBucket_surjective_nonzero signature signatureMem
        exact ⟨bucket, Finset.mem_univ bucket, equality⟩
      · simp
    _ = catalog.uniqueCaptureCount index :=
      catalog.roleHistogram_sum_eq_uniqueCaptureCount index
    _ = (catalog.fusedCounts states indices).unique index :=
      (catalog.fusedUnique_eq_uniqueCaptureCount states indices index).symm

/-- Positivity of a fused unique field transports to the frozen count. -/
theorem uniqueCaptureCount_pos_of_fused {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) (index : catalog.Index) :
    0 < (catalog.fusedCounts states indices).unique index ->
      0 < catalog.uniqueCaptureCount index := by
  rw [catalog.fusedUnique_eq_uniqueCaptureCount states indices index]
  exact id

#print axioms fusedPairClassification
#print axioms fusedFull_eq_escapeNumerator
#print axioms fusedUnique_eq_uniqueCaptureCount
#print axioms fusedWithout_eq_escapeNumerator_without
#print axioms fusedRoleBins_eq_roleHistogram
#print axioms fusedRoleBins_sum_eq_unique
#print axioms uniqueCaptureCount_pos_of_fused

end Catalog
end D5.S3.ConceptDynamics.InformationEscape
