/- GID: D5/S1/Words/Complexity/ExactDecks/UpperBound/FullLyndonRecovery
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/UpperBound/FullLyndonRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All bounded scattered counts are recovered unconditionally from Lyndon coordinates. -/

import D5.S1.Words.Complexity.ExactDecks.UpperBound.IteratedOverlapBounds
import D5.S1.Words.Complexity.ExactDecks.UpperBound.LyndonFactorization
import D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedShuffleOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.UpperBound.FullLyndonRecovery

open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedShuffleOrder
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open private lyndonFactors lyndonFactors_spec from
  D5.S1.Words.Complexity.ExactDecks.UpperBound.LyndonFactorization
open private iteratedOrdinaryShuffles iteratedOverlapInfiltrations
  mem_iteratedOrdinaryShuffles_schedule from
  D5.S1.Words.Complexity.ExactDecks.UpperBound.ShuffleScheduleComposition
open private iteratedOverlap_filter_top_length
  length_eq_of_mem_iteratedOrdinaryShuffles length_le_of_mem_iteratedOverlap
  scatteredCount_prod_eq_sum_iteratedOverlap from
  D5.S1.Words.Complexity.ExactDecks.UpperBound.IteratedOverlapBounds

variable {A : Type*}

theorem scatteredCount_eq_of_lyndon_coordinates [Fintype A] [LinearOrder A]
    (k : ℕ) (left right : List A)
    (hcoordinates : ∀ word, IsLyndon word → word.length ≤ k →
      scatteredCount word left = scatteredCount word right) :
    ∀ word, word.length ≤ k →
      scatteredCount word left = scatteredCount word right := by
  classical
  have allLengths : ∀ n, n ≤ k → ∀ word : List A, word.length = n →
      scatteredCount word left = scatteredCount word right := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnk word hwordLength
      by_contra hwordBad
      let words : Finset (List A) :=
        Finset.univ.image (fun f : Fin n → A => List.ofFn f)
      let badWords := words.filter (fun z =>
        scatteredCount z left ≠ scatteredCount z right)
      have word_mem_words : word ∈ words := by
        subst n
        exact Finset.mem_image.mpr
          ⟨word.get, Finset.mem_univ _, List.ofFn_get word⟩
      have word_mem_bad : word ∈ badWords := by
        exact Finset.mem_filter.mpr ⟨word_mem_words, hwordBad⟩
      obtain ⟨least, hleastBad, hleast⟩ :=
        Finset.exists_min_image badWords id ⟨word, word_mem_bad⟩
      have hleastData := Finset.mem_filter.mp hleastBad
      have hleastLength : least.length = n := by
        obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hleastData.1
        simp
      have hlower {z : List A} (hzLength : z.length = n)
          (hzlt : z < least) :
          scatteredCount z left = scatteredCount z right := by
        by_contra hzBad
        have hzWords : z ∈ words := by
          let f : Fin n → A := fun i =>
            z.get ⟨i, by simp [hzLength, i.isLt]⟩
          have hofFn : List.ofFn f = z := by
            apply List.ext_get
            · simp [hzLength]
            · intro i hi₁ hi₂
              simp [f]
          exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, hofFn⟩
        have hzBadWords : z ∈ badWords :=
          Finset.mem_filter.mpr ⟨hzWords, hzBad⟩
        exact (not_le_of_gt hzlt) (hleast z hzBadWords)
      let factors := lyndonFactors least
      have hfactor := lyndonFactors_spec least
      have hsumLength : (factors.map List.length).sum = n := by
        rw [← List.length_flatten, hfactor.1, hleastLength]
      have mem_length_le_sum : ∀ (xs : List (List A)) u, u ∈ xs →
          u.length ≤ (xs.map List.length).sum := by
        intro xs u hu
        induction xs with
        | nil => simp at hu
        | cons v xs ih =>
            simp only [List.mem_cons] at hu
            simp only [List.map_cons, List.sum_cons]
            rcases hu with rfl | hu
            · omega
            · exact (ih hu).trans (Nat.le_add_left _ _)
      have hfactorLength : ∀ u ∈ factors, u.length ≤ n := by
        intro u hu
        rw [← hsumLength]
        exact mem_length_le_sum factors u hu
      have hfactorCounts :
          factors.map (fun u => scatteredCount u left) =
            factors.map (fun u => scatteredCount u right) := by
        apply List.map_congr_left
        intro u hu
        exact hcoordinates u (hfactor.2.1 u hu)
          ((hfactorLength u hu).trans hnk)
      have htotal :
          ((iteratedOverlapInfiltrations factors).map
              (fun z => scatteredCount z left)).sum =
            ((iteratedOverlapInfiltrations factors).map
              (fun z => scatteredCount z right)).sum := by
        rw [← scatteredCount_prod_eq_sum_iteratedOverlap,
          ← scatteredCount_prod_eq_sum_iteratedOverlap, hfactorCounts]
      have splitSum (source : List A) :
          ((iteratedOverlapInfiltrations factors).map
              (fun z => scatteredCount z source)).sum =
            (((iteratedOverlapInfiltrations factors).filter
              (fun z => z.length = n)).map
                (fun z => scatteredCount z source)).sum +
            (((iteratedOverlapInfiltrations factors).filter
              (fun z => z.length ≠ n)).map
                (fun z => scatteredCount z source)).sum := by
        induction iteratedOverlapInfiltrations factors with
        | nil => simp
        | cons z zs ihZs =>
            by_cases hz : z.length = n <;>
              simp [hz, ihZs, Nat.add_assoc, Nat.add_left_comm]
      have hshort :
          (((iteratedOverlapInfiltrations factors).filter
              (fun z => z.length ≠ n)).map
                (fun z => scatteredCount z left)).sum =
            (((iteratedOverlapInfiltrations factors).filter
              (fun z => z.length ≠ n)).map
                (fun z => scatteredCount z right)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro z hz
        have hzMem := (List.mem_filter.mp hz).1
        have hzNe := of_decide_eq_true (List.mem_filter.mp hz).2
        have hzLe := length_le_of_mem_iteratedOverlap factors z hzMem
        exact ih z.length (by omega) (by omega) z rfl
      have htop :
          ((iteratedOrdinaryShuffles factors).map
              (fun z => scatteredCount z left)).sum =
            ((iteratedOrdinaryShuffles factors).map
              (fun z => scatteredCount z right)).sum := by
        rw [splitSum left, splitSum right, hshort] at htotal
        have htopFiltered := Nat.add_right_cancel htotal
        have hfilterTop :
            (iteratedOverlapInfiltrations factors).filter
                (fun z => z.length = n) =
              iteratedOrdinaryShuffles factors := by
          simpa [hsumLength] using iteratedOverlap_filter_top_length factors
        rw [hfilterTop] at htopFiltered
        exact htopFiltered
      have topPartition (source : List A) :
          ((iteratedOrdinaryShuffles factors).map
              (fun z => scatteredCount z source)).sum =
            (iteratedOrdinaryShuffles factors).count least *
                scatteredCount least source +
              (((iteratedOrdinaryShuffles factors).filter
                (fun z => z ≠ least)).map
                  (fun z => scatteredCount z source)).sum := by
        induction iteratedOrdinaryShuffles factors with
        | nil => simp
        | cons z zs ihZs =>
            by_cases hz : z = least
            · subst z
              simp [ihZs, Nat.add_mul, Nat.add_assoc, Nat.add_comm]
            · simp [hz, ihZs, Nat.add_left_comm]
      have hlowerSums :
          (((iteratedOrdinaryShuffles factors).filter
              (fun z => z ≠ least)).map
                (fun z => scatteredCount z left)).sum =
            (((iteratedOrdinaryShuffles factors).filter
              (fun z => z ≠ least)).map
                (fun z => scatteredCount z right)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro z hz
        have hzMem := (List.mem_filter.mp hz).1
        have hzNe := of_decide_eq_true (List.mem_filter.mp hz).2
        have hzLength := length_eq_of_mem_iteratedOrdinaryShuffles
          factors z hzMem
        obtain ⟨schedule, hvalid, heval⟩ :=
          mem_iteratedOrdinaryShuffles_schedule factors z hzMem
        have hzLe := evaluateSchedule_le_flatten factors schedule z
          hfactor.2.1 hfactor.2.2 hvalid heval
        rw [hfactor.1] at hzLe
        exact hlower (by omega) (lt_of_le_of_ne hzLe hzNe)
      rw [topPartition left, topPartition right, hlowerSums] at htop
      have hmultiple := Nat.add_right_cancel htop
      have hflatten : ∀ sources : List (List A),
          sources.flatten ∈ iteratedOrdinaryShuffles sources := by
        intro sources
        induction sources with
        | nil => simp [iteratedOrdinaryShuffles]
        | cons source sources ihSources =>
            simp only [iteratedOrdinaryShuffles, List.mem_flatMap]
            refine ⟨sources.flatten, ihSources, ?_⟩
            simp only [List.flatten_cons]
            generalize sources.flatten = right
            induction source generalizing right with
            | nil => simp [ordinaryShuffles]
            | cons a source ihSource =>
                cases right with
                | nil => simp [ordinaryShuffles]
                | cons b right =>
                    simp only [ordinaryShuffles, List.mem_append, List.mem_map]
                    exact Or.inl ⟨source ++ b :: right, ihSource (b :: right), by simp⟩
      have hpositive : 0 < (iteratedOrdinaryShuffles factors).count least :=
        List.count_pos_iff.mpr (hfactor.1 ▸ hflatten factors)
      exact hleastData.2
        (Nat.eq_of_mul_eq_mul_left hpositive hmultiple)
  intro word hword; exact allLengths word.length hword word rfl

end D5.S1.Words.Complexity.ExactDecks.UpperBound.FullLyndonRecovery
