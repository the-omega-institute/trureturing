/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount
   mirror-E: none(waiver:weighted-terminal-counting)
   anchors: []
   utility: none
   digest: Counts terminal constructions with arbitrary weights on every finite alphabet. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTerminal
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoCount

open NonnestingOneThreeTwoTwoTypeI NonnestingOneThreeTwoTwoTypeII
open D5.S3.Combinatorics ArrowThirtyTwoOneThreeCatalan NonnestingBasicOrders

open Classical in
theorem weighted_decomposition {Weight : Type*} [AddCommMonoid Weight]
    (alphabet : List ℕ) (distinct : alphabet.Nodup)
    (nonempty : alphabet ≠ []) (weight : ℕ → Weight) :
    let words := fun labels : List ℕ =>
      ((labels.flatMap fun letter => [letter, letter]).permutations.toFinset).filter
        fun word => ¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
          ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word
    ∑ word ∈ words alphabet,
        weight (word.length - word.toFinset.sup (fun letter => word.idxOf letter) - 1) =
      ∑ pivot ∈ alphabet.toFinset,
        ((∑ _upper ∈ words (alphabet.filter fun letter => decide (pivot < letter)),
          ∑ lower ∈ words (alphabet.filter fun letter => decide (letter < pivot)),
            ∑ cut ∈ (Finset.range (lower.length + 1)).filter
              (fun cut => ∀ letter ∈ lower, lower.idxOf letter < cut),
                weight (lower.length - cut + 1)) +
        catalan (alphabet.filter fun letter => decide (letter < pivot)).length •
          (∑ upper ∈ words (alphabet.filter fun letter => decide (pivot < letter)),
            ∑ cut ∈ (Finset.range upper.length).filter
              (fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut),
                weight (upper.length - cut +
                  (alphabet.filter fun letter => decide (letter < pivot)).length + 1))) := by
  classical
  intro words
  let cuts := fun upper lower : List ℕ =>
    ((Finset.range (lower.length + 1)).filter
      fun cut => ∀ letter ∈ lower, lower.idxOf letter < cut).map
        (Function.Embedding.inl : ℕ ↪ ℕ ⊕ ℕ) ∪
    (if lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower then
      ((Finset.range upper.length).filter
        fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut).map
          (Function.Embedding.inr : ℕ ↪ ℕ ⊕ ℕ) else ∅)
  have doubledCount (labels : List ℕ) (letter : ℕ) :
      (labels.flatMap fun entry => [entry, entry]).count letter = 2 * labels.count letter := by
    induction labels with
    | nil => simp
    | cons entry labels inductionHypothesis =>
      by_cases equal : entry = letter
      · simp [equal, inductionHypothesis]; omega
      · simp [equal, inductionHypothesis]
  have mountainCount (labels : List ℕ) (labelsDistinct : labels.Nodup) :
      {word : List ℕ |
        word.Perm (labels.flatMap fun letter => [letter, letter]) ∧
        ¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
        ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word ∧
        word.take (word.length / 2) ++ word.take (word.length / 2) = word}.ncard =
          catalan labels.length := by
    have double (order : List ℕ) (orderDistinct : order.Nodup) :
        ∀ letter ∈ order ++ order, (order ++ order).count letter = 2 := by
      intro letter present
      have member : letter ∈ order := by simpa using present
      simp [List.count_eq_one_of_mem orderDistinct member]
    have secondIndex (order : List ℕ) (orderDistinct : order.Nodup)
        (letter : ℕ) (present : letter ∈ order) :
        secondPos letter (order ++ order) = order.length + order.idxOf letter := by
      obtain ⟨initial, ending, orderEq⟩ := List.append_of_mem present
      have countEq := List.count_eq_one_of_mem orderDistinct present
      rw [orderEq] at countEq
      simp only [List.count_append, List.count_cons, beq_self_eq_true,
        ↓reduceIte] at countEq
      have absentInitial : letter ∉ initial := List.count_eq_zero.mp (by omega)
      have absentEnding : letter ∉ ending := List.count_eq_zero.mp (by omega)
      have firstIndex : order.idxOf letter = initial.length := by
        simp [orderEq, List.idxOf_append, absentInitial]
      have fullEq : order ++ order =
          initial ++ [letter] ++ (ending ++ initial) ++ [letter] ++ ending := by
        simp [orderEq, List.append_assoc]
      have dropInitial : initial.drop (initial.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      unfold secondPos
      rw [List.idxOf_append_of_mem present, firstIndex, fullEq]
      simp [List.drop_append, dropInitial, List.idxOf_append, absentInitial,
        absentEnding, List.length_append, orderEq, Nat.add_assoc]
      omega
    have occurrence (order : List ℕ) (orderDistinct : order.Nodup) :
        NonnestingDefs.Occurs [1, 3, 2, 2] (order ++ order) ↔ Has132 order := by
      constructor
      · rintro ⟨labels, increasing, _, sub, _⟩
        have lower := increasing 1 (by omega) (by simp [NonnestingDefs.letters])
        have upper := increasing 2 (by omega) (by simp [NonnestingDefs.letters])
        have sub' : [labels 1, labels 3, labels 2, labels 2].Sublist (order ++ order) := by
          simpa using sub
        obtain ⟨embedding, getEq⟩ :=
          List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sub'
        have values (index : Fin 4) : (order ++ order)[(embedding index).val]? =
            [labels 1, labels 3, labels 2, labels 2][index.val]? := by
          rw [List.getElem?_eq_getElem (embedding index).isLt,
            List.getElem?_eq_getElem index.isLt]
          exact congrArg some (getEq index).symm
        have before := embedding.strictMono (by change (0 : Fin 4) < 1; decide)
        have after := embedding.strictMono (by change (1 : Fin 4) < 2; decide)
        have copies := embedding.strictMono (by change (2 : Fin 4) < 3; decide)
        have thirdBound : (embedding 2).val < order.length := by
          by_contra outside
          have fourthOutside : ¬ (embedding 3).val < order.length := by omega
          have thirdValue : order[(embedding 2).val - order.length]? = some (labels 2) := by
            simpa [List.getElem?_append, outside] using values 2
          have fourthValue : order[(embedding 3).val - order.length]? = some (labels 2) := by
            simpa [List.getElem?_append, fourthOutside] using values 3
          have equal := orderDistinct.getElem_inj_iff.mp
            ((List.getElem?_eq_some_iff.mp thirdValue).2.trans
              (List.getElem?_eq_some_iff.mp fourthValue).2.symm)
          omega
        have firstBound : (embedding 0).val < order.length := by omega
        have secondBound : (embedding 1).val < order.length := by omega
        have firstGet : order.getD (embedding 0).val 0 = labels 1 := by
          simpa [List.getElem?_append, firstBound, List.getElem?_eq_getElem firstBound,
            List.getD_eq_getElem _ 0 firstBound] using values 0
        have secondGet : order.getD (embedding 1).val 0 = labels 3 := by
          simpa [List.getElem?_append, secondBound, List.getElem?_eq_getElem secondBound,
            List.getD_eq_getElem _ 0 secondBound] using values 1
        have thirdGet : order.getD (embedding 2).val 0 = labels 2 := by
          simpa [List.getElem?_append, thirdBound, List.getElem?_eq_getElem thirdBound,
            List.getD_eq_getElem _ 0 thirdBound] using values 2
        refine ⟨(embedding 0).val, (embedding 1).val, (embedding 2).val,
          before, after, thirdBound, ?_, ?_⟩
        · rw [firstGet, thirdGet]; exact lower
        · rw [secondGet, thirdGet]; exact upper
      · rintro ⟨first, second, third, before, after, thirdBound, lower, upper⟩
        have firstBound : first < order.length := by omega
        have secondBound : second < order.length := by omega
        let positions : Fin 3 → ℕ := fun index =>
          if index = 0 then first else if index = 1 then second else third
        have bounded : ∀ index : Fin 3, positions index < order.length := by
          intro index; fin_cases index <;> simp [positions] <;> omega
        let embedding : Fin 3 ↪o Fin order.length :=
          OrderEmbedding.ofMapLEIff (fun index => ⟨positions index, bounded index⟩) (by
            intro left right
            fin_cases left <;> fin_cases right <;> simp [positions] <;> omega)
        have sub : [order.getD first 0, order.getD second 0, order.getD third 0].Sublist
            order := by
          apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
          refine ⟨embedding, ?_⟩
          intro index
          fin_cases index <;> simp [embedding, positions, firstBound, secondBound, thirdBound]
        have repeatedMember : order.getD third 0 ∈ order := by
          rw [List.getD_eq_getElem _ 0 thirdBound]; exact List.getElem_mem _
        refine ⟨fun index => if index = 1 then order.getD first 0 else
          if index = 2 then order.getD third 0 else order.getD second 0, ?_, ?_, ?_, by simp⟩
        · intro index positive below
          have cases : index = 1 ∨ index = 2 := by
            simp [NonnestingDefs.letters] at below; omega
          rcases cases with rfl | rfl
          · change order.getD first 0 < order.getD third 0; exact lower
          · change order.getD third 0 < order.getD second 0; exact upper
        · intro index positive below
          have cases : index = 1 ∨ index = 2 ∨ index = 3 := by
            simp [NonnestingDefs.letters] at below; omega
          rcases cases with rfl | rfl | rfl
          · change order.getD first 0 ∈ order ++ order
            exact List.mem_append_left order (sub.subset (by simp))
          · change order.getD third 0 ∈ order ++ order
            exact List.mem_append_left order repeatedMember
          · change order.getD second 0 ∈ order ++ order
            exact List.mem_append_left order (sub.subset (by simp))
        · simpa using sub.append (List.singleton_sublist.mpr repeatedMember)
    have nonnesting (order : List ℕ) (orderDistinct : order.Nodup) :
        ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (order ++ order) ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (order ++ order) := by
      apply (nonnesting_iff_equal_orders _ (double order orderDistinct)).mpr
      intro smaller smallerPresent larger largerPresent before
      have smallerMember : smaller ∈ order := by simpa using smallerPresent
      have largerMember : larger ∈ order := by simpa using largerPresent
      rw [List.idxOf_append_of_mem smallerMember,
        List.idxOf_append_of_mem largerMember] at before
      rw [secondIndex order orderDistinct smaller smallerMember,
        secondIndex order orderDistinct larger largerMember]
      omega
    let permutations : Set (List ℕ) := {order | order.Perm labels ∧ ¬ Has132 order}
    have enumeration : permutations.ncard = catalan labels.length := by
      have sets : permutations =
          {order : List ℕ | order.Perm labels.toFinset.toList ∧ ¬ Has132 order} := by
        ext order
        simp only [permutations, Set.mem_ofPred_eq]
        have labelsPermutation := List.toFinset_toList labelsDistinct
        exact and_congr ⟨fun permutation => permutation.trans labelsPermutation.symm,
          fun permutation => permutation.trans labelsPermutation⟩ Iff.rfl
      rw [sets, ncard_avoid132, List.toFinset_card_of_nodup labelsDistinct]
    rw [← enumeration]
    symm
    apply Set.ncard_congr (fun order _ => order ++ order)
    · intro order member
      have permutation : order.Perm labels := member.1
      have orderDistinct := permutation.nodup_iff.mpr labelsDistinct
      have shape : (order ++ order).take ((order ++ order).length / 2) = order := by
        have lengthEq : (order ++ order).length / 2 = order.length := by
          simp only [List.length_append]; omega
        rw [lengthEq, List.take_left]
      refine ⟨?_, (nonnesting order orderDistinct).1, (nonnesting order orderDistinct).2,
        ?_, by rw [shape]⟩
      · apply List.perm_iff_count.mpr
        intro letter
        rw [List.count_append, doubledCount, permutation.count_eq]; omega
      · intro contains
        exact member.2 ((occurrence order orderDistinct).mp contains)
    · intro left right leftMember rightMember equal
      have lengths := congrArg List.length equal
      simp only [List.length_append] at lengths
      have sameLength : left.length = right.length := by omega
      have prefixes := congrArg (List.take left.length) equal
      simpa [List.take_left, sameLength] using prefixes
    · intro word member
      let order := word.take (word.length / 2)
      have wordEq : order ++ order = word := member.2.2.2.2
      have permutation : order.Perm labels := by
        apply List.perm_iff_count.mpr
        intro letter
        have counts := member.1.count_eq letter
        rw [← wordEq, List.count_append, doubledCount] at counts
        omega
      have orderDistinct := permutation.nodup_iff.mpr labelsDistinct
      refine ⟨order, ⟨permutation, ?_⟩, wordEq⟩
      intro pattern
      apply member.2.2.2.1
      rw [← wordEq]
      exact (occurrence order orderDistinct).mpr pattern

  let parameters := alphabet.toFinset.sigma fun pivot =>
    (words (alphabet.filter fun letter => decide (pivot < letter))).sigma fun upper =>
      (words (alphabet.filter fun letter => decide (letter < pivot))).sigma fun lower =>
        cuts upper lower
  let construct := fun parameter :
      Σ _ : ℕ, Σ _ : List ℕ, Σ _ : List ℕ, ℕ ⊕ ℕ =>
    match parameter.2.2.2 with
    | Sum.inl cut => typeIWord parameter.2.1 parameter.2.2.1 parameter.1 cut
    | Sum.inr cut => typeIIWord parameter.2.1
        (parameter.2.2.1.take (parameter.2.2.1.length / 2)) parameter.1 cut
  have wordMember (labels word : List ℕ) : word ∈ words labels ↔
      word.Perm (labels.flatMap fun letter => [letter, letter]) ∧
        ¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
        ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word := by
    simp [words, List.mem_permutations]
  have properties (labels word : List ℕ) (labelsDistinct : labels.Nodup)
      (member : word ∈ words labels) :
      (∀ letter, letter ∈ word ↔ letter ∈ labels) ∧
        (∀ letter ∈ word, word.count letter = 2) := by
    have permutation := (wordMember labels word).mp member |>.1
    have members (letter : ℕ) : letter ∈ word ↔ letter ∈ labels := by
      rw [permutation.mem_iff]
      simp
    refine ⟨members, ?_⟩
    intro letter present
    rw [permutation.count_eq, doubledCount,
      List.count_eq_one_of_mem labelsDistinct ((members letter).mp present)]
  have filteredDouble (labels : List ℕ) (predicate : ℕ → Bool) :
      (labels.flatMap fun letter => [letter, letter]).filter predicate =
        (labels.filter predicate).flatMap fun letter => [letter, letter] := by
    induction labels with
    | nil => simp
    | cons letter labels inductionHypothesis =>
      cases value : predicate letter <;> simp [value, inductionHypothesis]
  have cutMember (upper lower : List ℕ) (choice : ℕ ⊕ ℕ) : choice ∈ cuts upper lower ↔
      match choice with
      | Sum.inl cut => cut ≤ lower.length ∧ ∀ letter ∈ lower, lower.idxOf letter < cut
      | Sum.inr cut =>
          lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower ∧
          cut < upper.length ∧ ∀ letter ∈ upper, upper.idxOf letter < cut := by
    cases choice with
    | inl cut =>
      by_cases mountain : lower.take (lower.length / 2) ++
          lower.take (lower.length / 2) = lower
      · simp [cuts, mountain]
      · simp [cuts, mountain]
    | inr cut =>
      by_cases mountain : lower.take (lower.length / 2) ++
          lower.take (lower.length / 2) = lower
      · simp [cuts, mountain]
      · simp [cuts, mountain]
  have parameterMember (pivot : ℕ) (upper lower : List ℕ) (choice : ℕ ⊕ ℕ) :
      (⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩ :
        Σ _ : ℕ, Σ _ : List ℕ, Σ _ : List ℕ, ℕ ⊕ ℕ) ∈ parameters ↔
      pivot ∈ alphabet ∧
        upper ∈ words (alphabet.filter fun letter => decide (pivot < letter)) ∧
        lower ∈ words (alphabet.filter fun letter => decide (letter < pivot)) ∧
        choice ∈ cuts upper lower := by
    simp [parameters]
  have constructionFacts (pivot : ℕ) (upper lower : List ℕ) (choice : ℕ ⊕ ℕ)
      (member : (⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩ :
        Σ _ : ℕ, Σ _ : List ℕ, Σ _ : List ℕ, ℕ ⊕ ℕ) ∈ parameters) :
      let word := construct ⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩
      word ∈ words alphabet ∧ pivot ∈ word ∧
        (∀ letter ∈ word, word.idxOf letter ≤ word.idxOf pivot) ∧
        word.filter (fun letter => decide (pivot < letter)) = upper ∧
        word.filter (fun letter => decide (letter < pivot)) = lower ∧
        (match choice with
        | Sum.inl cut => word.idxOf pivot = upper.length + cut
        | Sum.inr cut => word.idxOf pivot = cut + lower.length / 2) := by
    obtain ⟨pivotMember, upperMember, lowerMember, admissible⟩ :=
      (parameterMember pivot upper lower choice).mp member
    obtain ⟨upperMembers, upperDouble⟩ := properties
      (alphabet.filter fun letter => decide (pivot < letter)) upper
      (distinct.filter _) upperMember
    obtain ⟨lowerMembers, lowerDouble⟩ := properties
      (alphabet.filter fun letter => decide (letter < pivot)) lower
      (distinct.filter _) lowerMember
    have upperValues : ∀ letter ∈ upper, pivot < letter := by
      intro letter present
      simpa using (List.mem_filter.mp ((upperMembers letter).mp present)).2
    have lowerValues : ∀ letter ∈ lower, letter < pivot := by
      intro letter present
      simpa using (List.mem_filter.mp ((lowerMembers letter).mp present)).2
    have pivotUpper : pivot ∉ upper := by
      intro present; exact (Nat.lt_irrefl pivot) (upperValues pivot present)
    have pivotLower : pivot ∉ lower := by
      intro present; exact (Nat.lt_irrefl pivot) (lowerValues pivot present)
    have upperGood := (wordMember _ upper).mp upperMember |>.2
    have lowerGood := (wordMember _ lower).mp lowerMember |>.2
    have upperFilter : upper.filter (fun letter => decide (pivot < letter)) = upper := by
      exact List.filter_eq_self.mpr (fun letter present => by simp [upperValues letter present])
    have lowerFilter : lower.filter (fun letter => decide (letter < pivot)) = lower := by
      exact List.filter_eq_self.mpr (fun letter present => by simp [lowerValues letter present])
    have upperLow : upper.filter (fun letter => decide (letter < pivot)) = [] := by
      exact List.filter_eq_nil_iff.mpr (fun letter present => by
        simp [Nat.not_lt.mpr (Nat.le_of_lt (upperValues letter present))])
    have combinedCounts (letter : ℕ) :
        upper.count letter + lower.count letter + (if pivot = letter then 2 else 0) =
          (alphabet.flatMap fun entry => [entry, entry]).count letter := by
      have upperPermutation := (wordMember _ upper).mp upperMember |>.1
      have lowerPermutation := (wordMember _ lower).mp lowerMember |>.1
      rw [upperPermutation.count_eq, lowerPermutation.count_eq,
        doubledCount, doubledCount, doubledCount]
      by_cases present : letter ∈ alphabet
      · have alphabetCount := List.count_eq_one_of_mem distinct present
        by_cases equal : pivot = letter
        · subst letter
          have upperCount : (alphabet.filter fun entry => decide (pivot < entry)).count pivot =
              0 := by
            apply List.count_eq_zero.mpr
            simp
          have lowerCount : (alphabet.filter fun entry => decide (entry < pivot)).count pivot =
              0 := by
            apply List.count_eq_zero.mpr
            simp
          simp [alphabetCount, upperCount, lowerCount]
        · have different : letter ≠ pivot := Ne.symm equal
          rcases lt_or_gt_of_ne different with smaller | larger
          · have zero : (alphabet.filter fun entry => decide (pivot < entry)).count letter =
                0 := by
              apply List.count_eq_zero.mpr; simp [Nat.not_lt_of_gt smaller]
            simp [List.count_filter, alphabetCount, equal, smaller, zero]
          · have zero : (alphabet.filter fun entry => decide (entry < pivot)).count letter =
                0 := by
              apply List.count_eq_zero.mpr; simp [Nat.not_lt_of_gt larger]
            simp [List.count_filter, alphabetCount, equal, larger, zero]
      · have alphabetCount : alphabet.count letter = 0 := List.count_eq_zero.mpr present
        have different : pivot ≠ letter := by
          rintro rfl
          exact present pivotMember
        have upperZero : (alphabet.filter fun entry => decide (pivot < entry)).count letter =
            0 := List.count_eq_zero.mpr (fun member => present (List.mem_filter.mp member).1)
        have lowerZero : (alphabet.filter fun entry => decide (entry < pivot)).count letter =
            0 := List.count_eq_zero.mpr (fun member => present (List.mem_filter.mp member).1)
        simp [alphabetCount, different, upperZero, lowerZero]
    have lastOpening (initial suffix : List ℕ) (absent : pivot ∉ initial)
        (covered : ∀ letter ∈ initial ++ [pivot] ++ suffix ++ [pivot],
          letter = pivot ∨ letter ∈ initial) :
        (initial ++ [pivot] ++ suffix ++ [pivot]).idxOf pivot = initial.length ∧
        ∀ letter ∈ initial ++ [pivot] ++ suffix ++ [pivot],
          (initial ++ [pivot] ++ suffix ++ [pivot]).idxOf letter ≤
            (initial ++ [pivot] ++ suffix ++ [pivot]).idxOf pivot := by
      have pivotIndex : (initial ++ [pivot] ++ suffix ++ [pivot]).idxOf pivot =
          initial.length := by
        simp [List.idxOf_append, absent]
      refine ⟨pivotIndex, ?_⟩
      intro letter present
      rcases covered letter present with equal | early
      · simp [equal]
      · rw [pivotIndex]
        have initialIndex : (initial ++ [pivot] ++ suffix ++ [pivot]).idxOf letter =
            initial.idxOf letter := by simp [List.idxOf_append, early]
        rw [initialIndex]
        exact Nat.le_of_lt (List.idxOf_lt_length_iff.mpr early)
    cases choice with
    | inl cut =>
      obtain ⟨cutBound, terminal⟩ := (cutMember upper lower (.inl cut)).mp admissible
      have early : ∀ letter ∈ lower, letter ∈ lower.take cut := by
        intro letter present
        exact (List.mem_take_iff_idxOf_lt present).mpr (terminal letter present)
      have splitCounts (letter : ℕ) :
          (lower.take cut).count letter + (lower.drop cut).count letter = lower.count letter := by
        rw [← List.count_append, List.take_append_drop]
      have permutation : (typeIWord upper lower pivot cut).Perm
          (alphabet.flatMap fun entry => [entry, entry]) := by
        apply List.perm_iff_count.mpr
        intro letter
        have split := splitCounts letter
        calc
          (typeIWord upper lower pivot cut).count letter =
              upper.count letter + lower.count letter +
                (if pivot = letter then 2 else 0) := by
            by_cases equal : pivot = letter <;>
              simp [typeIWord, List.count_append, equal] <;> omega
          _ = _ := combinedCounts letter
      have good := NonnestingOneThreeTwoTwoTypeINesting.typeI_nonnesting
        upper lower pivot cut upperValues lowerValues lowerDouble
        ⟨upperGood.1, upperGood.2.1⟩ ⟨lowerGood.1, lowerGood.2.1⟩ terminal
      have avoidance := typeI_avoids upper lower pivot cut upperValues lowerValues
        upperDouble lowerDouble upperGood.2.2 lowerGood.2.2 terminal
      have pivotIndex := lastOpening (upper ++ lower.take cut) (lower.drop cut)
        (by
          simp only [List.mem_append, not_or]
          exact ⟨pivotUpper, fun present => pivotLower (List.mem_of_mem_take present)⟩) (by
          intro letter present; simp only [List.mem_append, List.mem_singleton] at present ⊢
          rcases present with (((present | present) | equal) | present) | equal
          · exact Or.inr (Or.inl present)
          · exact Or.inr (Or.inr present)
          · exact Or.inl equal
          · exact Or.inr (Or.inr (early letter (List.mem_of_mem_drop present)))
          · exact Or.inl equal)
      have lowerTakeHigh : (lower.take cut).filter
          (fun letter => decide (pivot < letter)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro letter present
        simp [Nat.not_lt_of_gt (lowerValues letter (List.mem_of_mem_take present))]
      have lowerDropHigh : (lower.drop cut).filter
          (fun letter => decide (pivot < letter)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro letter present
        simp [Nat.not_lt_of_gt (lowerValues letter (List.mem_of_mem_drop present))]
      refine ⟨(wordMember _ _).mpr ⟨permutation, good.1, good.2, avoidance⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [construct, typeIWord]
      · simpa [construct, typeIWord, List.append_assoc] using pivotIndex.2
      · simp [construct, typeIWord, List.filter_append, upperFilter,
          lowerTakeHigh, lowerDropHigh]
      · simp only [construct, typeIWord, List.filter_append, upperLow]
        simp only [List.filter_cons, List.filter_nil, lt_self_iff_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil]
        rw [← List.filter_append, List.take_append_drop, lowerFilter]
      · simpa [construct, typeIWord, List.append_assoc, List.length_take,
          Nat.min_eq_left cutBound] using pivotIndex.1
    | inr cut =>
      obtain ⟨mountain, cutBound, terminal⟩ :=
        (cutMember upper lower (.inr cut)).mp admissible
      let order := lower.take (lower.length / 2)
      have orderEq : order ++ order = lower := mountain
      have orderLength : order.length = lower.length / 2 := by
        simp [order, Nat.min_eq_left (Nat.div_le_self _ _)]
      have orderValues : ∀ letter ∈ order, letter < pivot := by
        intro letter present; exact lowerValues letter (List.mem_of_mem_take present)
      have orderDistinct : order.Nodup := by
        rw [List.nodup_iff_count_le_one]
        intro letter
        by_cases present : letter ∈ order
        · have total := lowerDouble letter (by rw [← orderEq]; simp [present])
          rw [← orderEq, List.count_append] at total
          omega
        · simp [List.count_eq_zero.mpr present]
      have early : ∀ letter ∈ upper, letter ∈ upper.take cut := by
        intro letter present
        exact (List.mem_take_iff_idxOf_lt present).mpr (terminal letter present)
      have good := NonnestingOneThreeTwoTwoTypeIINesting.typeII_nonnesting
        upper order pivot cut upperValues orderValues upperDouble orderDistinct
        ⟨upperGood.1, upperGood.2.1⟩
        (by simpa [orderEq] using ⟨lowerGood.1, lowerGood.2.1⟩) terminal
      have avoidance := typeII_avoids upper order pivot cut upperValues orderValues
        upperDouble orderDistinct upperGood.2.2 (by simpa [orderEq] using lowerGood.2.2)
        terminal
      have splitCounts (letter : ℕ) :
          (upper.take cut).count letter + (upper.drop cut).count letter = upper.count letter := by
        rw [← List.count_append, List.take_append_drop]
      have permutation : (typeIIWord upper order pivot cut).Perm
          (alphabet.flatMap fun entry => [entry, entry]) := by
        apply List.perm_iff_count.mpr
        intro letter
        have split := splitCounts letter
        calc
          (typeIIWord upper order pivot cut).count letter =
              upper.count letter + lower.count letter +
                (if pivot = letter then 2 else 0) := by
            rw [← orderEq, List.count_append]
            by_cases equal : pivot = letter <;>
              simp [typeIIWord, List.count_append, equal] <;> omega
          _ = _ := combinedCounts letter
      have pivotOrder : pivot ∉ order := fun present =>
        pivotLower (List.mem_of_mem_take present)
      have pivotIndex := lastOpening (upper.take cut ++ order) (upper.drop cut ++ order)
        (by
          simp only [List.mem_append, not_or]
          exact ⟨fun present => pivotUpper (List.mem_of_mem_take present), pivotOrder⟩) (by
          intro letter present; simp only [List.mem_append, List.mem_singleton] at present ⊢
          rcases present with (((present | present) | equal) | (present | present)) | equal
          · exact Or.inr (Or.inl present)
          · exact Or.inr (Or.inr present)
          · exact Or.inl equal
          · exact Or.inr (Or.inl (early letter (List.mem_of_mem_drop present)))
          · exact Or.inr (Or.inr present)
          · exact Or.inl equal)
      have orderHigh : order.filter (fun letter => decide (pivot < letter)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro letter present; simp [Nat.not_lt_of_gt (orderValues letter present)]
      have orderLow : order.filter (fun letter => decide (letter < pivot)) = order := by
        exact List.filter_eq_self.mpr (fun letter present => by simp [orderValues letter present])
      have upperTakeLow : (upper.take cut).filter
          (fun letter => decide (letter < pivot)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro letter present
        simp [Nat.not_lt_of_gt (upperValues letter (List.mem_of_mem_take present))]
      have upperDropLow : (upper.drop cut).filter
          (fun letter => decide (letter < pivot)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro letter present
        simp [Nat.not_lt_of_gt (upperValues letter (List.mem_of_mem_drop present))]
      refine ⟨(wordMember _ _).mpr ⟨permutation, good.1, good.2, avoidance⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [construct, typeIIWord]
      · simpa [construct, typeIIWord, order, List.append_assoc] using pivotIndex.2
      · change (typeIIWord upper order pivot cut).filter _ = upper
        simp only [typeIIWord, List.filter_append, orderHigh]
        simp only [List.filter_cons, List.filter_nil, lt_self_iff_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.append_nil]
        rw [← List.filter_append, List.take_append_drop, upperFilter]
      · change (typeIIWord upper order pivot cut).filter _ = lower
        simp [typeIIWord, List.filter_append,
          upperTakeLow, upperDropLow, orderLow, orderEq]
      · change (typeIIWord upper order pivot cut).idxOf pivot = cut + lower.length / 2
        simpa [typeIIWord, List.append_assoc, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt cutBound), orderLength] using pivotIndex.1
  have mountainCut (lower : List ℕ) (cut : ℕ)
      (mountain : lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower)
      (double : ∀ letter ∈ lower, lower.count letter = 2)
      (terminal : ∀ letter ∈ lower, lower.idxOf letter < cut) : lower.length / 2 ≤ cut := by
    by_contra notBound
    have halfLength : (lower.take (lower.length / 2)).length = lower.length / 2 := by
      simp [Nat.min_eq_left (Nat.div_le_self _ _)]
    have orderDistinct : (lower.take (lower.length / 2)).Nodup := by
      rw [List.nodup_iff_count_le_one]
      intro letter
      by_cases present : letter ∈ lower.take (lower.length / 2)
      · have total := double letter (List.mem_of_mem_take present)
        rw [← mountain, List.count_append] at total
        omega
      · simp [List.count_eq_zero.mpr present]
    have position : cut < (lower.take (lower.length / 2)).length := by omega
    let letter := (lower.take (lower.length / 2))[cut]
    have present := List.getElem_mem position
    have firstIndex : lower.idxOf letter = cut := by
      rw [← mountain, List.idxOf_append_of_mem present, orderDistinct.idxOf_getElem]
    have early := terminal letter (List.mem_of_mem_take present)
    rw [firstIndex] at early
    omega
  have injective : ∀ left ∈ parameters, ∀ right ∈ parameters,
      construct left = construct right → left = right := by
    rintro ⟨pivot, upper, lower, choice⟩ leftMember
      ⟨pivot', upper', lower', choice'⟩ rightMember equal
    obtain ⟨_, pivotMember, lastPivot, high, low, index⟩ :=
      constructionFacts pivot upper lower choice leftMember
    obtain ⟨_, pivotMember', lastPivot', high', low', index'⟩ :=
      constructionFacts pivot' upper' lower' choice' rightMember
    have pivotEqual : pivot = pivot' := by
      have leftBound := lastPivot pivot' (by rw [equal]; exact pivotMember')
      have rightBound := lastPivot' pivot (by rw [← equal]; exact pivotMember)
      rw [← equal] at rightBound
      have sameIndex := Nat.le_antisymm rightBound leftBound
      exact (List.idxOf_inj pivotMember).mp sameIndex
    subst pivot'
    have upperEqual : upper = upper' := by rw [← high, equal, high']
    have lowerEqual : lower = lower' := by rw [← low, equal, low']
    subst upper'
    subst lower'
    cases choice with
    | inl cut =>
      cases choice' with
      | inl cut' =>
        dsimp only at index index'
        rw [← equal] at index'
        have cutEqual : cut = cut' := by omega
        simp [cutEqual]
      | inr cut' =>
        obtain ⟨_, _, _, admissible⟩ :=
          (parameterMember pivot upper lower (.inr cut')).mp rightMember
        have bounds := (cutMember upper lower (.inr cut')).mp admissible
        rw [← equal] at index'
        have lowerMember := (parameterMember pivot upper lower (.inl cut)).mp leftMember
        have terminal := (cutMember upper lower (.inl cut)).mp lowerMember.2.2.2
        have halfEarly := mountainCut lower cut bounds.1
          (properties _ lower (distinct.filter _) lowerMember.2.2.1).2 terminal.2
        omega
    | inr cut =>
      cases choice' with
      | inl cut' =>
        obtain ⟨_, _, _, admissible⟩ :=
          (parameterMember pivot upper lower (.inr cut)).mp leftMember
        have bounds := (cutMember upper lower (.inr cut)).mp admissible
        rw [← equal] at index'
        have lowerMember := (parameterMember pivot upper lower (.inl cut')).mp rightMember
        have terminal := (cutMember upper lower (.inl cut')).mp lowerMember.2.2.2
        have halfEarly := mountainCut lower cut' bounds.1
          (properties _ lower (distinct.filter _) lowerMember.2.2.1).2 terminal.2
        omega
      | inr cut' =>
        rw [← equal] at index'
        have cutEqual : cut = cut' := by omega
        simp [cutEqual]
  have surjective : ∀ word ∈ words alphabet,
      ∃ parameter ∈ parameters, construct parameter = word := by
    intro word wordPresent
    obtain ⟨wordMembers, double⟩ := properties alphabet word distinct wordPresent
    have wordNonempty : word.toFinset.Nonempty := by
      obtain ⟨letter, present⟩ := List.exists_mem_of_ne_nil alphabet nonempty
      exact ⟨letter, List.mem_toFinset.mpr ((wordMembers letter).mpr present)⟩
    obtain ⟨pivot, pivotPresent, maximal⟩ :=
      Finset.exists_max_image word.toFinset (fun letter => word.idxOf letter) wordNonempty
    have pivotMember : pivot ∈ word := List.mem_toFinset.mp pivotPresent
    have lastPivot : ∀ letter ∈ word, word.idxOf letter ≤ word.idxOf pivot := by
      intro letter present; exact maximal letter (List.mem_toFinset.mpr present)
    let upper := word.filter fun letter => decide (pivot < letter)
    let lower := word.filter fun letter => decide (letter < pivot)
    have decomposition := (NonnestingOneThreeTwoTwoTerminal.terminal_factorization
      word pivot pivotMember double lastPivot).mp ((wordMember _ _).mp wordPresent).2
    have upperPresent : upper ∈
        words (alphabet.filter fun letter => decide (pivot < letter)) := by
      apply (wordMember _ _).mpr
      refine ⟨?_, decomposition.1⟩
      exact filteredDouble alphabet _ ▸ (((wordMember _ _).mp wordPresent).1.filter _)
    have lowerPresent : lower ∈
        words (alphabet.filter fun letter => decide (letter < pivot)) := by
      apply (wordMember _ _).mpr
      refine ⟨?_, decomposition.2.1⟩
      exact filteredDouble alphabet _ ▸ (((wordMember _ _).mp wordPresent).1.filter _)
    obtain ⟨choice, admissible, _⟩ := decomposition.2.2
    cases choice with
    | inl cut =>
      refine ⟨⟨pivot, ⟨upper, ⟨lower, Sum.inl cut⟩⟩⟩, ?_, admissible.2.1.symm⟩
      apply (parameterMember pivot upper lower (.inl cut)).mpr
      refine ⟨(wordMembers pivot).mp pivotMember, upperPresent, lowerPresent, ?_⟩
      exact (cutMember upper lower (.inl cut)).mpr ⟨admissible.1, admissible.2.2.1⟩
    | inr pair =>
      have lowerEq : lower = pair.1 ++ pair.1 := admissible.2.2.1
      have halfLength : lower.length / 2 = pair.1.length := by
        rw [lowerEq, List.length_append]; omega
      have orderEq : lower.take (lower.length / 2) = pair.1 := by
        rw [halfLength, lowerEq, List.take_left]
      refine ⟨⟨pivot, ⟨upper, ⟨lower, Sum.inr pair.2⟩⟩⟩, ?_, ?_⟩
      · apply (parameterMember pivot upper lower (.inr pair.2)).mpr
        refine ⟨(wordMembers pivot).mp pivotMember, upperPresent, lowerPresent, ?_⟩
        apply (cutMember upper lower (.inr pair.2)).mpr
        exact ⟨by rw [orderEq, ← lowerEq], admissible.2.2.2.1, admissible.2.2.2.2.1⟩
      · simpa [construct, orderEq] using admissible.1.symm
  have bijection :
      (∑ parameter ∈ parameters,
        match parameter.2.2.2 with
        | Sum.inl cut => weight (parameter.2.2.1.length - cut + 1)
        | Sum.inr cut =>
            weight (parameter.2.1.length - cut + parameter.2.2.1.length / 2 + 1)) =
      ∑ word ∈ words alphabet,
        weight (word.length - word.toFinset.sup (fun letter => word.idxOf letter) - 1) := by
    apply Finset.sum_bij (fun parameter _ => construct parameter)
    · rintro ⟨pivot, upper, lower, choice⟩ member
      exact (constructionFacts pivot upper lower choice member).1
    · exact injective
    · intro word member
      obtain ⟨parameter, present, equal⟩ := surjective word member
      exact ⟨parameter, present, equal⟩
    · rintro ⟨pivot, upper, lower, choice⟩ member
      obtain ⟨_, pivotPresent, maximal, _, _, index⟩ :=
        constructionFacts pivot upper lower choice member
      have maximum : (construct ⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩).toFinset.sup
          (fun letter => (construct ⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩).idxOf letter) =
            (construct ⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩).idxOf pivot := by
        apply Nat.le_antisymm
        · apply Finset.sup_le
          intro letter present; exact maximal letter (List.mem_toFinset.mp present)
        · exact Finset.le_sup (f := fun letter =>
            (construct ⟨pivot, ⟨upper, ⟨lower, choice⟩⟩⟩).idxOf letter)
            (List.mem_toFinset.mpr pivotPresent)
      rw [maximum]
      obtain ⟨_, _, _, admissible⟩ := (parameterMember pivot upper lower choice).mp member
      cases choice with
      | inl cut =>
        have cutBound := ((cutMember upper lower (.inl cut)).mp admissible).1
        dsimp only at index ⊢
        rw [index]
        apply congrArg weight
        simp only [construct, typeIWord, List.length_append, List.length_take,
          List.length_singleton, List.length_drop, Nat.min_eq_left cutBound]
        omega
      | inr cut =>
        obtain ⟨_, cutBound, _⟩ := (cutMember upper lower (.inr cut)).mp admissible
        dsimp only at index ⊢
        rw [index]
        apply congrArg weight
        simp only [construct, typeIIWord, List.length_append, List.length_take,
          List.length_singleton, List.length_drop, Nat.min_eq_left (Nat.le_of_lt cutBound),
          Nat.min_eq_left (Nat.div_le_self _ _)]
        omega

  rw [← bijection]
  have separate (left right : Finset ℕ) :
      Disjoint (left.map (Function.Embedding.inl : ℕ ↪ ℕ ⊕ ℕ))
        (right.map (Function.Embedding.inr : ℕ ↪ ℕ ⊕ ℕ)) := by
    simp [Finset.disjoint_left]
  have cutSum (upper lower : List ℕ) :
      (∑ choice ∈ cuts upper lower,
        match choice with
        | Sum.inl cut => weight (lower.length - cut + 1)
        | Sum.inr cut => weight (upper.length - cut + lower.length / 2 + 1)) =
      (∑ cut ∈ (Finset.range (lower.length + 1)).filter
        (fun cut => ∀ letter ∈ lower, lower.idxOf letter < cut),
          weight (lower.length - cut + 1)) +
      (if lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower then
        ∑ cut ∈ (Finset.range upper.length).filter
          (fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut),
            weight (upper.length - cut + lower.length / 2 + 1) else 0) := by
    by_cases mountain : lower.take (lower.length / 2) ++
        lower.take (lower.length / 2) = lower
    · simp [cuts, mountain, Finset.sum_union (separate _ _)]
    · simp [cuts, mountain]
  have mountainCard (labels : List ℕ) (labelsDistinct : labels.Nodup) :
      ((words labels).filter fun word =>
        word.take (word.length / 2) ++ word.take (word.length / 2) = word).card =
          catalan labels.length := by
    rw [← Set.ncard_coe_finset]
    have sets :
        (↑((words labels).filter fun word =>
          word.take (word.length / 2) ++ word.take (word.length / 2) = word) :
          Set (List ℕ)) =
        {word : List ℕ | word.Perm (labels.flatMap fun letter => [letter, letter]) ∧
          ¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
          ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word ∧
          word.take (word.length / 2) ++ word.take (word.length / 2) = word} := by
      ext word
      simp only [Finset.mem_coe, Finset.mem_filter, wordMember, Set.mem_ofPred_eq]
      tauto
    rw [sets, mountainCount labels labelsDistinct]
  have doubleLength (labels : List ℕ) :
      (labels.flatMap fun letter => [letter, letter]).length = 2 * labels.length := by
    induction labels with
    | nil => simp
    | cons letter labels inductionHypothesis => simp [inductionHypothesis]; omega
  simp only [parameters, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro pivot pivotPresent
  let lowerLabels := alphabet.filter fun letter => decide (letter < pivot)
  have mountainSum (upper : List ℕ) :
      (∑ lower ∈ words lowerLabels,
        if lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower then
          ∑ cut ∈ (Finset.range upper.length).filter
            (fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut),
              weight (upper.length - cut + lower.length / 2 + 1) else 0) =
        catalan lowerLabels.length •
          (∑ cut ∈ (Finset.range upper.length).filter
            (fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut),
              weight (upper.length - cut + lowerLabels.length + 1)) := by
    have halves (lower : List ℕ) (member : lower ∈ words lowerLabels) :
        lower.length / 2 = lowerLabels.length := by
      have lengthEq := (wordMember lowerLabels lower).mp member |>.1.length_eq
      rw [doubleLength] at lengthEq
      omega
    have replace :
        (∑ lower ∈ words lowerLabels,
          if lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower then
            ∑ cut ∈ (Finset.range upper.length).filter
              (fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut),
                weight (upper.length - cut + lower.length / 2 + 1) else 0) =
        ∑ lower ∈ words lowerLabels,
          if lower.take (lower.length / 2) ++ lower.take (lower.length / 2) = lower then
            ∑ cut ∈ (Finset.range upper.length).filter
              (fun cut => ∀ letter ∈ upper, upper.idxOf letter < cut),
                weight (upper.length - cut + lowerLabels.length + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro lower member
      rw [halves lower member]
    rw [replace, ← Finset.sum_filter]
    simp only [Finset.sum_const, mountainCard lowerLabels (distinct.filter _)]
  simp_rw [cutSum, Finset.sum_add_distrib]
  dsimp only [lowerLabels] at mountainSum
  simp_rw [mountainSum]
  rw [← Finset.smul_sum]
end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoCount
