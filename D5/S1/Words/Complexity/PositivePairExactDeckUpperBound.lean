/- GID: D5/S1/Words/Complexity/PositivePairExactDeckUpperBound
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairExactDeckUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lyndon coordinates determine every bounded-length scattered count. -/
import D5.S1.Words.Complexity.PositivePairExactDeckGrowth
import D5.S1.Words.Complexity.LyndonIndexedShuffleOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Overlap infiltration for actual scattered-subword counts

Two position selections in one source word can share positions.  The recursive
overlap infiltration records the two exclusive choices and, when the leading
letters agree, the shared choice.  It retains duplicate output words because
different alignments contribute distinct multiplicities.  Removing the shared
choice gives the ordinary shuffle, exactly the maximal-length stratum.
-/
namespace D5.S1.Words.Complexity.PositivePairExactDeckUpperBound

open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LyndonStandardBracket
open D5.S1.Words.Complexity.LyndonShuffleScheduleOrder
open D5.S1.Words.Complexity.LyndonIndexedShuffleOrder

variable {A : Type*}

/-- All overlap infiltrations of two words, with one list entry per alignment.
The third branch records a position used by both patterns. -/
def overlapInfiltrations [DecidableEq A] :
    List A → List A → List (List A)
  | [], right => [right]
  | left, [] => [left]
  | a :: left, b :: right =>
      (overlapInfiltrations left (b :: right)).map (List.cons a) ++
        (overlapInfiltrations (a :: left) right).map (List.cons b) ++
          if a = b then
            (overlapInfiltrations left right).map (List.cons a)
          else []
termination_by left right => left.length + right.length
decreasing_by
  all_goals simp_wf
  omega

/-- Ordinary shuffles, retaining one list entry per choice of left/right
positions. -/
def ordinaryShuffles : List A → List A → List (List A)
  | [], right => [right]
  | left, [] => [left]
  | a :: left, b :: right =>
      (ordinaryShuffles left (b :: right)).map (List.cons a) ++
        (ordinaryShuffles (a :: left) right).map (List.cons b)
termination_by left right => left.length + right.length
decreasing_by all_goals simp_wf

/-- The product of two actual scattered-subword counts is the sum over all
overlap infiltrations.  Repeated merged words remain repeated summands, so the
identity preserves alignment multiplicity. -/
theorem scatteredCount_mul_eq_sum_overlapInfiltrations [DecidableEq A]
    (left right source : List A) :
    scatteredCount left source * scatteredCount right source =
      ((overlapInfiltrations left right).map
        (fun merged => scatteredCount merged source)).sum := by
  have hrec :
      ∀ (a b x : A) (left right source : List A),
        ((overlapInfiltrations (a :: left) (b :: right)).map
            (fun merged => scatteredCount merged (x :: source))).sum =
          ((overlapInfiltrations (a :: left) (b :: right)).map
              (fun merged => scatteredCount merged source)).sum +
            (if a = x then
              ((overlapInfiltrations left (b :: right)).map
                (fun merged => scatteredCount merged source)).sum
            else 0) +
            (if b = x then
              ((overlapInfiltrations (a :: left) right).map
                (fun merged => scatteredCount merged source)).sum
            else 0) +
            (if a = b then
              if a = x then
                ((overlapInfiltrations left right).map
                  (fun merged => scatteredCount merged source)).sum
              else 0
            else 0) := by
    intro a b x left right source
    by_cases hab : a = b
    · subst b
      simp only [overlapInfiltrations, if_pos, List.map_append,
        List.sum_append, List.map_map, Function.comp_def]
      simp only [scatteredCount, List.sum_map_add]
      by_cases hax : a = x <;> simp [hax]
      omega
    · simp only [overlapInfiltrations, if_neg hab, List.append_nil,
        List.map_append, List.sum_append, List.map_map, Function.comp_def]
      simp only [scatteredCount, List.sum_map_add]
      by_cases hax : a = x <;> by_cases hbx : b = x <;>
        simp [hax, hbx]
      all_goals omega
  induction source generalizing left right with
  | nil =>
      cases left with
      | nil =>
          cases right <;>
            simp [scatteredCount, overlapInfiltrations]
      | cons a left =>
          cases right with
          | nil => simp [scatteredCount, overlapInfiltrations]
          | cons b right =>
              by_cases hab : a = b <;>
                simp [scatteredCount, overlapInfiltrations, hab,
                  List.map_map, Function.comp_def]
  | cons x source ih =>
      cases left with
      | nil => simp [scatteredCount, overlapInfiltrations]
      | cons a left =>
          cases right with
          | nil => simp [scatteredCount, overlapInfiltrations]
          | cons b right =>
              rw [hrec]
              rw [scatteredCount, scatteredCount]
              rw [← ih (a :: left) (b :: right),
                ← ih left (b :: right), ← ih (a :: left) right,
                ← ih left right]
              by_cases hax : a = x
              · subst a
                by_cases hbx : b = x
                · subst b
                  simp
                  ring
                · have hxb : x ≠ b := Ne.symm hbx
                  simp [hbx, hxb]
                  ring
              · by_cases hbx : b = x
                · subst b
                  simp [hax]
                  ring
                · simp [hax, hbx]

private theorem length_le_of_mem_overlapInfiltrations [DecidableEq A] :
    ∀ (left right merged : List A),
      merged ∈ overlapInfiltrations left right →
        merged.length ≤ left.length + right.length := by
  intro left
  induction left with
  | nil =>
      intro right merged hmerged
      simp only [overlapInfiltrations, List.mem_singleton] at hmerged
      subst merged
      simp
  | cons a left ihLeft =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          simp only [overlapInfiltrations, List.mem_singleton] at hmerged
          subst merged
          simp
      | cons b right ihRight =>
          intro merged hmerged
          by_cases hab : a = b
          · rw [overlapInfiltrations, if_pos hab, List.mem_append,
              List.mem_append] at hmerged
            rcases hmerged with (hleft | hright) | hshared
            · rw [List.mem_map] at hleft
              obtain ⟨middle, hmiddle, rfl⟩ := hleft
              have hlength := ihLeft (b :: right) middle hmiddle
              simp only [List.length_cons] at hlength ⊢
              omega
            · rw [List.mem_map] at hright
              obtain ⟨middle, hmiddle, rfl⟩ := hright
              have hlength := ihRight middle hmiddle
              simp only [List.length_cons] at hlength ⊢
              omega
            · rw [List.mem_map] at hshared
              obtain ⟨middle, hmiddle, rfl⟩ := hshared
              have hlength := ihLeft right middle hmiddle
              simp only [List.length_cons] at hlength ⊢
              omega
          · rw [overlapInfiltrations, if_neg hab, List.append_nil,
              List.mem_append] at hmerged
            rcases hmerged with hleft | hright
            · rw [List.mem_map] at hleft
              obtain ⟨middle, hmiddle, rfl⟩ := hleft
              have hlength := ihLeft (b :: right) middle hmiddle
              simp only [List.length_cons] at hlength ⊢
              omega
            · rw [List.mem_map] at hright
              obtain ⟨middle, hmiddle, rfl⟩ := hright
              have hlength := ihRight middle hmiddle
              simp only [List.length_cons] at hlength ⊢
              omega

/-- The maximal-length overlap infiltrations are exactly the ordinary
shuffles, with list equality retaining every shuffle multiplicity. -/
theorem overlapInfiltrations_filter_top_length [DecidableEq A]
    (left right : List A) :
    (overlapInfiltrations left right).filter
        (fun merged => merged.length = left.length + right.length) =
      ordinaryShuffles left right := by
  induction left generalizing right with
  | nil => simp [overlapInfiltrations, ordinaryShuffles]
  | cons a left ihLeft =>
      induction right with
      | nil => simp [overlapInfiltrations, ordinaryShuffles]
      | cons b right ihRight =>
          have hfirst :
              ((overlapInfiltrations left (b :: right)).map (List.cons a)).filter
                  (fun merged =>
                    merged.length = (a :: left).length + (b :: right).length) =
                (ordinaryShuffles left (b :: right)).map (List.cons a) := by
            rw [show (a :: left).length + (b :: right).length =
                (left.length + (b :: right).length) + 1 by simp; omega]
            rw [List.filter_map]
            have hfilter :
                (overlapInfiltrations left (b :: right)).filter
                    (((fun merged =>
                      decide (merged.length = left.length + (b :: right).length + 1)) ∘
                      List.cons a)) =
                  (overlapInfiltrations left (b :: right)).filter
                    (fun merged =>
                      decide (merged.length = left.length + (b :: right).length)) := by
              apply List.filter_congr
              intro merged _
              simp only [Function.comp_apply, List.length_cons]
              apply decide_eq_decide.mpr
              exact Nat.add_right_cancel_iff
            rw [hfilter, ihLeft (b :: right)]
          have hsecond :
              ((overlapInfiltrations (a :: left) right).map (List.cons b)).filter
                  (fun merged =>
                    merged.length = (a :: left).length + (b :: right).length) =
                (ordinaryShuffles (a :: left) right).map (List.cons b) := by
            rw [show (a :: left).length + (b :: right).length =
                ((a :: left).length + right.length) + 1 by simp; omega]
            rw [List.filter_map]
            have hfilter :
                (overlapInfiltrations (a :: left) right).filter
                    (((fun merged =>
                      decide (merged.length = (a :: left).length + right.length + 1)) ∘
                      List.cons b)) =
                  (overlapInfiltrations (a :: left) right).filter
                    (fun merged =>
                      decide (merged.length = (a :: left).length + right.length)) := by
              apply List.filter_congr
              intro merged _
              simp only [Function.comp_apply, List.length_cons]
              apply decide_eq_decide.mpr
              exact Nat.add_right_cancel_iff
            rw [hfilter, ihRight]
          have hshared :
              ((overlapInfiltrations left right).map (List.cons a)).filter
                  (fun merged =>
                    merged.length = (a :: left).length + (b :: right).length) =
                [] := by
            apply List.filter_eq_nil_iff.mpr
            intro merged hmerged
            rw [List.mem_map] at hmerged
            obtain ⟨middle, hmiddle, rfl⟩ := hmerged
            have hlength :=
              length_le_of_mem_overlapInfiltrations left right middle hmiddle
            intro htop
            have heq := of_decide_eq_true htop
            simp only [List.length_cons] at heq
            omega
          rw [overlapInfiltrations, ordinaryShuffles,
            List.filter_append, List.filter_append, hfirst, hsecond]
          by_cases hab : a = b
          · rw [if_pos hab, hshared]
            simp
          · rw [if_neg hab]
            simp

/-! ## Finite Lyndon factorization and iterated overlap -/

private def insertLyndon [LinearOrder A] (u : List A) :
    List (List A) → List (List A)
  | [] => [u]
  | v :: factors =>
      if u < v then insertLyndon (u ++ v) factors
      else u :: v :: factors

private def lyndonFactors [LinearOrder A] : List A → List (List A)
  | [] => []
  | a :: word => insertLyndon [a] (lyndonFactors word)

private theorem join_insertLyndon [LinearOrder A] (u : List A) :
    ∀ factors, (insertLyndon u factors).flatten = u ++ factors.flatten := by
  intro factors
  induction factors generalizing u with
  | nil => simp [insertLyndon]
  | cons v factors ih =>
      by_cases huv : u < v
      · rw [insertLyndon, if_pos huv, ih]
        simp [List.append_assoc]
      · simp [insertLyndon, huv]

private theorem insertLyndon_isLyndon [LinearOrder A]
    (u : List A) (hu : IsLyndon u) :
    ∀ factors,
      (∀ v ∈ factors, IsLyndon v) →
      factors.Pairwise (· ≥ ·) →
      (∀ v ∈ insertLyndon u factors, IsLyndon v) ∧
        (insertLyndon u factors).Pairwise (· ≥ ·) := by
  intro factors
  induction factors generalizing u with
  | nil =>
      intro _ _
      simp [insertLyndon, hu]
  | cons v factors ih =>
      intro hlyndon hordered
      have hv : IsLyndon v := hlyndon v (by simp)
      have htailL : ∀ z ∈ factors, IsLyndon z := by
        intro z hz
        exact hlyndon z (by simp [hz])
      have htailO : factors.Pairwise (· ≥ ·) :=
        (List.pairwise_cons.mp hordered).2
      by_cases huv : u < v
      · rw [insertLyndon, if_pos huv]
        exact ih (u ++ v) (isLyndon_append hu hv huv) htailL htailO
      · rw [insertLyndon, if_neg huv]
        refine ⟨?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hu
          · exact hlyndon z (by simp [hz])
        · rw [List.pairwise_cons]
          refine ⟨?_, hordered⟩
          intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact le_of_not_gt huv
          · exact ((List.pairwise_cons.mp hordered).1 z hz).trans
              (le_of_not_gt huv)

private theorem lyndonFactors_spec [LinearOrder A] (word : List A) :
    (lyndonFactors word).flatten = word ∧
      (∀ u ∈ lyndonFactors word, IsLyndon u) ∧
      (lyndonFactors word).Pairwise (· ≥ ·) := by
  induction word with
  | nil => simp [lyndonFactors]
  | cons a word ih =>
      have hins := insertLyndon_isLyndon [a] (by
        refine ⟨by simp, ?_⟩
        intro u v hu hv huv
        have hlen := congrArg List.length huv
        simp only [List.length_singleton, List.length_append] at hlen
        have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
        have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
        omega)
        (lyndonFactors word) ih.2.1 ih.2.2
      refine ⟨?_, hins⟩
      rw [lyndonFactors, join_insertLyndon, ih.1]
      simp
private def iteratedOverlapInfiltrations [DecidableEq A] :
    List (List A) → List (List A)
  | [] => [[]]
  | word :: factors =>
      (iteratedOverlapInfiltrations factors).flatMap (overlapInfiltrations word)
private def iteratedOrdinaryShuffles : List (List A) → List (List A)
  | [] => [[]]
  | word :: factors =>
      (iteratedOrdinaryShuffles factors).flatMap (ordinaryShuffles word)
private def composeIndexed : List Side → List Nat → List Nat
  | [], _ => []
  | Side.first :: binary, tail => 0 :: composeIndexed binary tail
  | Side.second :: binary, [] => []
  | Side.second :: binary, i :: tail => (i + 1) :: composeIndexed binary tail
private theorem composeIndexed_counts (binary : List Side) (tail : List Nat)
    (hlength : binary.count Side.second = tail.length) :
    (composeIndexed binary tail).count 0 = binary.count Side.first ∧
      ∀ i, (composeIndexed binary tail).count (i + 1) = tail.count i := by
  induction binary generalizing tail with
  | nil =>
      have : tail = [] := by simpa using hlength.symm
      subst tail; simp [composeIndexed]
  | cons side binary ih =>
      cases side with
      | first =>
          have htail : binary.count Side.second = tail.length := by simpa using hlength
          rcases ih tail htail with ⟨hzero, hsucc⟩
          refine ⟨by simp [composeIndexed, hzero], ?_⟩
          intro i; simp [composeIndexed, hsucc i]
      | second =>
          cases tail with
          | nil => simp at hlength
          | cons label tail =>
              have htail : binary.count Side.second = tail.length := by simpa using hlength
              rcases ih tail htail with ⟨hzero, hsucc⟩
              refine ⟨by simp [composeIndexed, hzero], ?_⟩
              intro i; by_cases hi : label = i
              · subst label
                simp [composeIndexed, hsucc]
              · have hil : label + 1 ≠ i + 1 := by omega
                simp [composeIndexed, hil, hi, hsucc]
private theorem mem_ordinaryShuffles_schedule :
    ∀ (left right merged : List A), merged ∈ ordinaryShuffles left right →
      ∃ schedule, ValidTwoSchedule left right schedule ∧
        evaluateTwo left right schedule = some merged := by
  intro left
  induction left with
  | nil =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          have : merged = [] := by simpa [ordinaryShuffles] using hmerged
          subst merged
          exact ⟨[], by simp [ValidTwoSchedule], rfl⟩
      | cons b right ih =>
          intro merged hmerged
          have hmerged' : merged = b :: right := by simpa [ordinaryShuffles] using hmerged
          subst merged
          rcases ih right (by simp [ordinaryShuffles]) with ⟨schedule, hvalid, heval⟩
          refine ⟨Side.second :: schedule,
            by simpa [ValidTwoSchedule] using hvalid, ?_⟩
          unfold evaluateTwo annotateTwo at heval ⊢
          simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
            List.mapM_cons]
          rw [annotateTwoFrom_add 0 1 schedule 0 0, List.mapM_map]
          have hread : readTwo ([] : List A) (b :: right) ∘
              shiftPairOccurrences 0 1 = readTwo [] right := by
            funext ⟨side, occurrence⟩
            cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
              readTwo, Nat.add_comm, List.getElem?_cons_succ]
          rw [hread, heval]
          rfl
  | cons a left ihLeft =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          have hmerged' : merged = a :: left := by simpa [ordinaryShuffles] using hmerged
          subst merged
          have hleftMem : left ∈ ordinaryShuffles left [] := by
            cases left <;> simp [ordinaryShuffles]
          rcases ihLeft [] left hleftMem with ⟨schedule, hvalid, heval⟩
          refine ⟨Side.first :: schedule,
            by simpa [ValidTwoSchedule] using hvalid, ?_⟩
          unfold evaluateTwo annotateTwo at heval ⊢
          simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
            List.mapM_cons]
          have hshift : annotateTwoFrom 1 0 schedule = (annotateTwo schedule).map (shiftPairOccurrences 1 0) := by
            simpa [annotateTwo] using annotateTwoFrom_add 1 0 schedule 0 0
          rw [hshift, List.mapM_map]
          have hread : readTwo (a :: left) ([] : List A) ∘
              shiftPairOccurrences 1 0 = readTwo left [] := by
            funext ⟨side, occurrence⟩
            cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
              readTwo, Nat.add_comm, List.getElem?_cons_succ]
          rw [hread]
          simp only [annotateTwo]
          rw [heval]
          rfl
      | cons b right ihRight =>
          intro merged hmerged
          rw [ordinaryShuffles, List.mem_append] at hmerged
          rcases hmerged with hfirst | hsecond
          · rw [List.mem_map] at hfirst
            rcases hfirst with ⟨middle, hmiddle, rfl⟩
            rcases ihLeft (b :: right) middle hmiddle with ⟨schedule, hvalid, heval⟩
            refine ⟨Side.first :: schedule,
              by simpa [ValidTwoSchedule] using hvalid, ?_⟩
            unfold evaluateTwo annotateTwo at heval ⊢
            simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
              List.mapM_cons]
            have hshift : annotateTwoFrom 1 0 schedule = (annotateTwo schedule).map (shiftPairOccurrences 1 0) := by
              simpa [annotateTwo] using annotateTwoFrom_add 1 0 schedule 0 0
            rw [hshift, List.mapM_map]
            have hread : readTwo (a :: left) (b :: right) ∘
                shiftPairOccurrences 1 0 = readTwo left (b :: right) := by
              funext ⟨side, occurrence⟩
              cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
                readTwo, Nat.add_comm, List.getElem?_cons_succ]
            rw [hread]
            simp only [annotateTwo]
            rw [heval]
            rfl
          · rw [List.mem_map] at hsecond
            rcases hsecond with ⟨middle, hmiddle, rfl⟩
            rcases ihRight middle hmiddle with ⟨schedule, hvalid, heval⟩
            refine ⟨Side.second :: schedule,
              by simpa [ValidTwoSchedule] using hvalid, ?_⟩
            unfold evaluateTwo annotateTwo at heval ⊢
            simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
              List.mapM_cons]
            rw [annotateTwoFrom_add 0 1 schedule 0 0, List.mapM_map]
            have hread : readTwo (a :: left) (b :: right) ∘
                shiftPairOccurrences 0 1 = readTwo (a :: left) right := by
              funext ⟨side, occurrence⟩
              cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
                readTwo, Nat.add_comm, List.getElem?_cons_succ]
            rw [hread, heval]; rfl
private def combinedUsed (firstUsed : Nat) (tailUsed : Nat → Nat) : Nat → Nat
  | 0 => firstUsed
  | i + 1 => tailUsed i
private def liftTailEntry : Nat × Nat → Nat × Nat
  | (i, occurrence) => (i + 1, occurrence)
private def composeTrace : List (Side × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], _ => []
  | (Side.first, occurrence) :: binary, tail =>
      (0, occurrence) :: composeTrace binary tail
  | (Side.second, _) :: binary, [] => []
  | (Side.second, _) :: binary, entry :: tail =>
      liftTailEntry entry :: composeTrace binary tail
private theorem annotate_composeIndexed (binary : List Side) (tail : List Nat)
    (firstUsed secondUsed : Nat) (tailUsed : Nat → Nat) :
    annotateIndexedFrom (combinedUsed firstUsed tailUsed) (composeIndexed binary tail) =
      composeTrace (annotateTwoFrom firstUsed secondUsed binary)
        (annotateIndexedFrom tailUsed tail) := by
  induction binary generalizing tail firstUsed secondUsed tailUsed with
  | nil => rfl
  | cons side binary ih =>
      cases side with
      | first =>
          have hupdate : Function.update (combinedUsed firstUsed tailUsed) 0
              (firstUsed + 1) = combinedUsed (firstUsed + 1) tailUsed := by
            funext i; cases i <;> simp [combinedUsed, Function.update]
          simp only [composeIndexed, annotateIndexedFrom, combinedUsed,
            annotateTwoFrom, composeTrace]
          rw [hupdate, ih]
      | second =>
          cases tail with
          | nil => rfl
          | cons label tail =>
              have hupdate : Function.update (combinedUsed firstUsed tailUsed)
                  (label + 1) (tailUsed label + 1) =
                combinedUsed firstUsed
                  (Function.update tailUsed label (tailUsed label + 1)) := by
                funext i
                cases i with
                | zero => simp [combinedUsed, Function.update]
                | succ i => simp [combinedUsed, Function.update, Nat.succ.injEq]
              simp only [composeIndexed, annotateIndexedFrom, combinedUsed,
                annotateTwoFrom, composeTrace, liftTailEntry]
              rw [hupdate, ih]
private theorem composeTrace_mapM (first : List A) (factors : List (List A))
    (middle : List A) (binary : List Side) (tailTrace : List (Nat × Nat))
    (firstUsed secondUsed : Nat) (hlength : binary.count Side.second = tailTrace.length)
    (htail : tailTrace.mapM (readIndexed factors) =
      some (middle.drop secondUsed)) :
    (composeTrace (annotateTwoFrom firstUsed secondUsed binary) tailTrace).mapM
        (readIndexed (first :: factors)) =
      (annotateTwoFrom firstUsed secondUsed binary).mapM
        (readTwo first middle) := by
  induction binary generalizing tailTrace firstUsed secondUsed with
  | nil =>
      have : tailTrace = [] := by
        simpa using List.length_eq_zero_iff.mp hlength.symm
      subst tailTrace; rfl
  | cons side binary ih =>
      cases side with
      | first =>
          have hlength' : binary.count Side.second = tailTrace.length := by simpa using hlength
          simp only [annotateTwoFrom, composeTrace, List.mapM_cons, readIndexed,
            List.getD_cons_zero, readTwo]
          rw [ih tailTrace (firstUsed + 1) secondUsed hlength' htail]
      | second =>
          cases tailTrace with
          | nil => simp at hlength
          | cons entry tailTrace =>
              have hlength' : binary.count Side.second = tailTrace.length := by simpa using hlength
              cases hread : readIndexed factors entry with
              | none => simp [hread] at htail
              | some value =>
                  cases hrest : tailTrace.mapM (readIndexed factors) with
                  | none => simp [hread, hrest] at htail
                  | some rest =>
                      have hdrop : middle.drop secondUsed = value :: rest := by
                        simpa [hread, hrest] using htail.symm
                      have hlt : secondUsed < middle.length := by
                        by_contra hnot
                        have hempty : middle.drop secondUsed = [] :=
                          List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hnot)
                        simp [hempty] at hdrop
                      have hparts : middle[secondUsed] = value ∧
                          middle.drop (secondUsed + 1) = rest := by
                        have := hdrop
                        rw [List.drop_eq_getElem_cons hlt] at this
                        exact List.cons.inj this
                      have hrec := ih tailTrace firstUsed (secondUsed + 1)
                        hlength' (hparts.2.symm ▸ hrest)
                      have hlift :
                          readIndexed (first :: factors) (liftTailEntry entry) =
                            readIndexed factors entry := by
                        rcases entry with ⟨i, occurrence⟩
                        simp [liftTailEntry, readIndexed]
                      simp only [annotateTwoFrom, composeTrace, List.mapM_cons]
                      rw [hlift, hread]
                      simp only [readTwo]
                      rw [List.getElem?_eq_getElem hlt, hparts.1, hrec]
private theorem composeIndexed_spec (first : List A) (factors : List (List A))
    (middle merged : List A)
    (binary : List Side) (tail : List Nat)
    (hbinaryValid : ValidTwoSchedule first middle binary)
    (hbinaryEval : evaluateTwo first middle binary = some merged)
    (htailValid : IsValidSchedule factors tail)
    (htailEval : evaluateSchedule factors tail = some middle) :
    IsValidSchedule (first :: factors) (composeIndexed binary tail) ∧
      evaluateSchedule (first :: factors) (composeIndexed binary tail) = some merged := by
  classical
  have htailRaw : (annotateIndexed tail).mapM (readIndexed factors) = some middle := by
    unfold evaluateSchedule at htailEval
    simpa [htailValid] using htailEval
  have hannLength : ∀ used schedule,
      (annotateIndexedFrom used schedule).length = schedule.length := by
    intro used schedule
    induction schedule generalizing used with
    | nil => rfl
    | cons i schedule ih => simp [annotateIndexedFrom, ih]
  have htailLength : tail.length = middle.length := by
    have h := mapM_length (readIndexed factors) (annotateIndexed tail)
      middle htailRaw
    simpa [annotateIndexed, hannLength] using h.symm
  have hcounts := composeIndexed_counts binary tail
    (by rw [hbinaryValid.2, htailLength])
  have hvalid : IsValidSchedule (first :: factors)
      (composeIndexed binary tail) := by
    intro i
    cases i with
    | zero => simpa using hcounts.1.trans hbinaryValid.1
    | succ i => simpa using (hcounts.2 i).trans (htailValid i)
  refine ⟨hvalid, ?_⟩
  unfold evaluateSchedule
  simp only [dif_pos hvalid]
  have hzero : combinedUsed 0 (fun _ => 0) = (fun _ => 0) := by
    funext i; cases i <;> rfl
  rw [annotateIndexed, ← hzero,
    annotate_composeIndexed binary tail 0 0 (fun _ => 0)]
  have htraceLength : binary.count Side.second =
      (annotateIndexed tail).length := by
    rw [hbinaryValid.2, ← htailLength]
    exact (hannLength (fun _ => 0) tail).symm
  have htrace := composeTrace_mapM first factors middle binary
    (annotateIndexed tail) 0 0 htraceLength (by simpa using htailRaw)
  change (composeTrace (annotateTwoFrom 0 0 binary)
      (annotateIndexed tail)).mapM (readIndexed (first :: factors)) =
    some merged
  rw [htrace]
  simpa [evaluateTwo, annotateTwo] using hbinaryEval
private theorem mem_iteratedOrdinaryShuffles_schedule :
    ∀ (factors : List (List A)) (merged : List A), merged ∈ iteratedOrdinaryShuffles factors →
      ∃ schedule, IsValidSchedule factors schedule ∧
        evaluateSchedule factors schedule = some merged := by
  intro factors
  induction factors with
  | nil =>
      intro merged hmerged
      have : merged = [] := by simpa [iteratedOrdinaryShuffles] using hmerged
      subst merged
      have hvalid : IsValidSchedule ([] : List (List A)) [] := by simp [IsValidSchedule]
      exact ⟨[], hvalid, by simp [evaluateSchedule, hvalid, annotateIndexed,
        annotateIndexedFrom]⟩
  | cons first factors ih =>
      intro merged hmerged
      simp only [iteratedOrdinaryShuffles, List.mem_flatMap] at hmerged
      obtain ⟨middle, hmiddle, hmerged⟩ := hmerged
      obtain ⟨tail, htailValid, htailEval⟩ := ih middle hmiddle
      obtain ⟨binary, hbinaryValid, hbinaryEval⟩ :=
        mem_ordinaryShuffles_schedule first middle merged hmerged
      obtain ⟨hvalid, heval⟩ := composeIndexed_spec first factors middle merged
        binary tail hbinaryValid hbinaryEval htailValid htailEval
      exact ⟨composeIndexed binary tail, hvalid, heval⟩
private theorem scatteredCount_prod_eq_sum_iteratedOverlap
    [DecidableEq A] (factors : List (List A)) (source : List A) :
    (factors.map (fun word => scatteredCount word source)).prod =
      ((iteratedOverlapInfiltrations factors).map
        (fun merged => scatteredCount merged source)).sum := by
  induction factors with
  | nil => simp [iteratedOverlapInfiltrations, scatteredCount]
  | cons word factors ih =>
      rw [List.map_cons, List.prod_cons, ih]
      rw [Nat.mul_comm]
      simp only [iteratedOverlapInfiltrations]
      rw [show (((iteratedOverlapInfiltrations factors).flatMap
          (overlapInfiltrations word)).map
          (fun merged => scatteredCount merged source)).sum =
          ((iteratedOverlapInfiltrations factors).map (fun middle =>
            ((overlapInfiltrations word middle).map
              (fun merged => scatteredCount merged source)).sum)).sum by
        induction iteratedOverlapInfiltrations factors with
        | nil => simp
        | cons middle rest ihRest => simp [ihRest]]
      rw [← List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro merged hmerged
      rw [Nat.mul_comm, scatteredCount_mul_eq_sum_overlapInfiltrations]

private theorem length_le_of_mem_iteratedOverlap [DecidableEq A] :
    ∀ (factors : List (List A)) (merged : List A),
      merged ∈ iteratedOverlapInfiltrations factors →
        merged.length ≤ (factors.map List.length).sum := by
  intro factors
  induction factors with
  | nil =>
      intro merged hmerged
      simp only [iteratedOverlapInfiltrations, List.mem_singleton] at hmerged
      subst merged
      simp
  | cons word factors ih =>
      intro merged hmerged
      simp only [iteratedOverlapInfiltrations, List.mem_flatMap] at hmerged
      obtain ⟨middle, hmiddle, hmerged⟩ := hmerged
      have h₁ := length_le_of_mem_overlapInfiltrations word middle merged hmerged
      have h₂ := ih middle hmiddle
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem iteratedOverlap_filter_top_length [DecidableEq A]
    (factors : List (List A)) :
    (iteratedOverlapInfiltrations factors).filter
        (fun merged => merged.length = (factors.map List.length).sum) =
      iteratedOrdinaryShuffles factors := by
  induction factors with
  | nil => simp [iteratedOverlapInfiltrations, iteratedOrdinaryShuffles]
  | cons word factors ih =>
      simp only [iteratedOverlapInfiltrations, iteratedOrdinaryShuffles,
        List.filter_flatMap]
      rw [← ih]
      simp only [List.map_cons, List.sum_cons]
      have aux : ∀ middles : List (List A),
          (∀ middle ∈ middles,
            middle.length ≤ (factors.map List.length).sum) →
          middles.flatMap (fun middle =>
              (overlapInfiltrations word middle).filter (fun merged =>
                merged.length = word.length + (factors.map List.length).sum)) =
            (middles.filter (fun middle =>
              middle.length = (factors.map List.length).sum)).flatMap
                (ordinaryShuffles word) := by
        intro middles hlengths
        induction middles with
        | nil => simp
        | cons middle middles ihMiddles =>
            have hmiddleLength := hlengths middle (by simp)
            have htail : ∀ z ∈ middles,
                z.length ≤ (factors.map List.length).sum := by
              intro z hz
              exact hlengths z (by simp [hz])
            simp only [List.flatMap_cons, List.filter_cons, decide_eq_true_eq]
            by_cases htop : middle.length = (factors.map List.length).sum
            · simp only [if_pos htop]
              rw [show (overlapInfiltrations word middle).filter
                  (fun merged => merged.length =
                    word.length + (factors.map List.length).sum) =
                  ordinaryShuffles word middle by
                simpa [htop] using
                  overlapInfiltrations_filter_top_length word middle]
              rw [ihMiddles htail]
              simp only [List.flatMap_cons]
            · simp only [if_neg htop]
              rw [show (overlapInfiltrations word middle).filter
                  (fun merged => merged.length =
                    word.length + (factors.map List.length).sum) = [] by
                apply List.filter_eq_nil_iff.mpr
                intro merged hmerged
                have hlength :=
                  length_le_of_mem_overlapInfiltrations word middle merged hmerged
                intro heq
                have heq' := of_decide_eq_true heq
                omega]
              rw [ihMiddles htail]
              simp only [List.nil_append]
      apply aux
      intro middle hmiddle
      exact length_le_of_mem_iteratedOverlap factors middle hmiddle

private theorem length_eq_of_mem_ordinaryShuffles :
    ∀ (left right merged : List A),
      merged ∈ ordinaryShuffles left right →
        merged.length = left.length + right.length := by
  intro left
  induction left with
  | nil =>
      intro right merged hmerged
      have hmerged' : merged = right := by
        simpa [ordinaryShuffles] using hmerged
      subst merged
      simp
  | cons a left ihLeft =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          have hmerged' : merged = a :: left := by
            simpa [ordinaryShuffles] using hmerged
          subst merged
          simp
      | cons b right ihRight =>
          intro merged hmerged
          rw [ordinaryShuffles, List.mem_append] at hmerged
          rcases hmerged with hleft | hright
          · rw [List.mem_map] at hleft
            obtain ⟨middle, hmiddle, rfl⟩ := hleft
            have hlength := ihLeft (b :: right) middle hmiddle
            simp only [List.length_cons] at hlength ⊢
            omega
          · rw [List.mem_map] at hright
            obtain ⟨middle, hmiddle, rfl⟩ := hright
            have hlength := ihRight middle hmiddle
            simp only [List.length_cons] at hlength ⊢
            omega

private theorem length_eq_of_mem_iteratedOrdinaryShuffles :
    ∀ (factors : List (List A)) (merged : List A),
      merged ∈ iteratedOrdinaryShuffles factors →
        merged.length = (factors.map List.length).sum := by
  intro factors
  induction factors with
  | nil =>
      intro merged hmerged
      simpa [iteratedOrdinaryShuffles] using congrArg List.length
        (List.mem_singleton.mp hmerged)
  | cons word factors ih =>
      intro merged hmerged
      simp only [iteratedOrdinaryShuffles, List.mem_flatMap] at hmerged
      obtain ⟨middle, hmiddle, hmerged⟩ := hmerged
      rw [length_eq_of_mem_ordinaryShuffles word middle merged hmerged,
        ih middle hmiddle]
      simp
/-- Agreement on Lyndon coordinates through length `k` determines every
scattered-subword count through length `k`. -/
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
end D5.S1.Words.Complexity.PositivePairExactDeckUpperBound
