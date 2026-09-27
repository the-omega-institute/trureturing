/- GID: D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ArchiveClockRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Synchronized pairs characterize clock recovery and bound finite ambiguity. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.TFAE
import Mathlib.Tactic

/- Library-search audit trail (2026-09-27):
   * Repository searches for archive recovery, synchronized paths, and finite
     clock ambiguity found no declaration with the theorem's statement shape.
   * Pinned Mathlib supplies `Function.factorsThrough_iff`, `List.TFAE`,
     `List.Nodup.length_le_card`, `Nat.find_spec`, and `Nat.find_min'`. Its
     simple-graph path bound is not an exact hit because synchronized transitions
     are directed and action-labelled.
   * The proof below therefore constructs the synchronized execution semantics,
     removes a repeated-state loop from a shortest directed action word, and
     applies the finite-cardinality bound directly. -/

namespace D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- A finite deterministic partial-action model. `successor` and `cost` are
total, while `reading` is defined only on the action's domain. Values outside
the domain never enter a legal execution, so this faithfully represents the
source partial maps (including empty reading types and empty domains). -/
structure System (X A Y : Type*) where
  domain : A -> X -> Prop
  domainDecidable : forall a x, Decidable (domain a x)
  successor : A -> X -> X
  reading : (a : A) -> (x : X) -> domain a x -> Y
  cost : A -> X -> Int

/-- The state reached after applying an action word from left to right. -/
def stateAfter {X A Y : Type*} (S : System X A Y) (x : X) : List A -> X
  | [] => x
  | a :: word => stateAfter S (S.successor a x) word

/-- An action word is legal when each action is in the domain at the state
where that action is executed. -/
def Legal {X A Y : Type*} (S : System X A Y) (x : X) : List A -> Prop
  | [] => True
  | a :: word => S.domain a x ∧ Legal S (S.successor a x) word

/-- The visible archive records both the chosen action and its reading. -/
def visibleArchive {X A Y : Type*} (S : System X A Y) (x : X) :
    List A -> List (A × Y)
  | [] => []
  | a :: word =>
      letI := S.domainDecidable a x
      dite (S.domain a x)
        (fun h => (a, S.reading a x h) ::
          visibleArchive S (S.successor a x) word)
        (fun _ => [])

/-- The accumulated integer clock along an action word. -/
def clock {X A Y : Type*} (S : System X A Y) (x : X) : List A -> Int
  | [] => 0
  | a :: word => S.cost a x + clock S (S.successor a x) word

/-- A synchronized edge applies one legal action to both states and exposes
the same reading on both sides. -/
def SynchronizedEdge {X A Y : Type*} (S : System X A Y)
    (pair : X × X) (a : A) : Prop :=
  ∃ hleft : S.domain a pair.1, ∃ hright : S.domain a pair.2,
    S.reading a pair.1 hleft = S.reading a pair.2 hright

/-- A synchronized path follows the same action word through two legal
executions while matching the reading at every step. -/
def SynchronizedPath {X A Y : Type*} (S : System X A Y) :
    X -> X -> List A -> Prop
  | _, _, [] => True
  | x, x', a :: word =>
      SynchronizedEdge S (x, x') a ∧
        SynchronizedPath S (S.successor a x) (S.successor a x') word

/-- The synchronized state-pair trace, including its initial vertex. -/
def pairTrace {X A Y : Type*} (S : System X A Y) :
    X -> X -> List A -> List (X × X)
  | x, x', [] => [(x, x')]
  | x, x', a :: word =>
      (x, x') :: pairTrace S (S.successor a x) (S.successor a x') word

/-- The sum of edge-cost differences along a synchronized action word. -/
def deltaSum {X A Y : Type*} (S : System X A Y) :
    X -> X -> List A -> Int
  | _, _, [] => 0
  | x, x', a :: word =>
      (S.cost a x - S.cost a x') +
        deltaSum S (S.successor a x) (S.successor a x') word

/-- A state pair is synchronously reachable when a synchronized action word
from two allowed initial states ends at that pair. -/
def SynchronouslyReachable {X A Y : Type*} (S : System X A Y)
    (X0 : Set X) (pair : X × X) : Prop :=
  exists x, x ∈ X0 ∧ exists x', x' ∈ X0 ∧ exists word,
    SynchronizedPath S x x' word ∧
      (stateAfter S x word, stateAfter S x' word) = pair

/-- The clock is recoverable from visible archives on every legal execution
from the allowed initial set. -/
def ArchiveRecoverable {X A Y : Type*} (S : System X A Y)
    (X0 : Set X) : Prop :=
  exists recover : List (A × Y) -> Int,
    forall x, x ∈ X0 -> forall word, Legal S x word ->
      recover (visibleArchive S x word) = clock S x word

/-- Archive recovery, zero synchronized path sums, and zero reachable edge
differences are equivalent. If recovery fails, equal visible archives with
different clocks already occur at a common length at most the square of the
configuration count. -/
theorem archive_clock_recovery_and_finite_ambiguity
    {X A Y : Type*} [Fintype X] [Fintype A] [Fintype Y]
    (n : Nat) (hcard : Fintype.card X = n)
    (X0 : Set X) (_hX0 : X0.Nonempty) (S : System X A Y) :
    List.TFAE [
      ArchiveRecoverable S X0,
      forall x, x ∈ X0 -> forall x', x' ∈ X0 -> forall word,
        SynchronizedPath S x x' word -> deltaSum S x x' word = 0,
      forall pair, SynchronouslyReachable S X0 pair -> forall a,
        SynchronizedEdge S pair a -> S.cost a pair.1 - S.cost a pair.2 = 0] ∧
    (Not (ArchiveRecoverable S X0) ->
      exists x, x ∈ X0 ∧ exists x', x' ∈ X0 ∧ exists word,
        Legal S x word ∧ Legal S x' word ∧
          visibleArchive S x word = visibleArchive S x' word ∧
          clock S x word ≠ clock S x' word ∧ word.length <= n ^ 2) := by
  classical
  have stateAfter_append : forall (x : X) (first second : List A),
      stateAfter S x (first ++ second) =
        stateAfter S (stateAfter S x first) second := by
    intro x first second
    induction first generalizing x with
    | nil => rfl
    | cons a first ih =>
        simp only [List.cons_append, stateAfter]
        exact ih (S.successor a x)
  have synchronizedPath_append : forall (x x' : X) (first second : List A),
      SynchronizedPath S x x' (first ++ second) <->
        SynchronizedPath S x x' first ∧
          SynchronizedPath S (stateAfter S x first)
            (stateAfter S x' first) second := by
    intro x x' first second
    induction first generalizing x x' with
    | nil => simp [SynchronizedPath, stateAfter]
    | cons a first ih =>
        simp only [List.cons_append, SynchronizedPath, stateAfter]
        rw [ih]
        aesop
  have deltaSum_append : forall (x x' : X) (first second : List A),
      deltaSum S x x' (first ++ second) =
        deltaSum S x x' first +
          deltaSum S (stateAfter S x first) (stateAfter S x' first) second := by
    intro x x' first second
    induction first generalizing x x' with
    | nil => simp [deltaSum, stateAfter]
    | cons a first ih =>
        simp only [List.cons_append, deltaSum, stateAfter]
        rw [ih]
        omega
  have synchronizedPath_iff : forall (x x' : X) (word : List A),
      SynchronizedPath S x x' word <->
        Legal S x word ∧ Legal S x' word ∧
          visibleArchive S x word = visibleArchive S x' word := by
    intro x x' word
    induction word generalizing x x' with
    | nil => simp [SynchronizedPath, Legal, visibleArchive]
    | cons a word ih =>
        constructor
        · intro hsync
          rcases hsync with ⟨⟨hleft, hright, hread⟩, htailPath⟩
          rcases (ih (S.successor a x) (S.successor a x')).mp htailPath with
            ⟨htail, htail', harchive⟩
          refine ⟨⟨hleft, htail⟩, ⟨hright, htail'⟩, ?_⟩
          simp only [visibleArchive, dif_pos hleft, dif_pos hright]
          simp only [hread, harchive]
        · rintro ⟨⟨hleft, htail⟩, ⟨hright, htail'⟩, harchive⟩
          have harchive' :
              (a, S.reading a x hleft) ::
                  visibleArchive S (S.successor a x) word =
                (a, S.reading a x' hright) ::
                  visibleArchive S (S.successor a x') word := by
            simpa only [visibleArchive, dif_pos hleft, dif_pos hright] using harchive
          have hread : S.reading a x hleft = S.reading a x' hright := by
            have hpair := (List.cons.inj harchive').1
            exact congrArg Prod.snd hpair
          refine ⟨⟨hleft, hright, hread⟩, ?_⟩
          exact (ih (S.successor a x) (S.successor a x')).mpr
            ⟨htail, htail', (List.cons.inj harchive').2⟩
  have deltaSum_eq_clock_sub : forall (x x' : X) (word : List A),
      deltaSum S x x' word = clock S x word - clock S x' word := by
    intro x x' word
    induction word generalizing x x' with
    | nil => simp [deltaSum, clock]
    | cons a word ih =>
        simp only [deltaSum, clock]
        rw [ih]
        omega
  have archive_actions : forall (x : X) (word : List A), Legal S x word ->
      (visibleArchive S x word).map Prod.fst = word := by
    intro x word hlegal
    induction word generalizing x with
    | nil => rfl
    | cons a word ih =>
        have ha := hlegal.1
        have htail := hlegal.2
        simp only [visibleArchive, dif_pos ha, List.map_cons, ih _ htail]
  have pairTrace_length : forall (x x' : X) (word : List A),
      (pairTrace S x x' word).length = word.length + 1 := by
    intro x x' word
    induction word generalizing x x' with
    | nil => rfl
    | cons a word ih =>
        simp [pairTrace, ih]
  have trace_mem_split : forall (x x' q : X) (q' : X) (word : List A),
      (q, q') ∈ pairTrace S x x' word ->
        exists first second, word = first ++ second ∧
          (stateAfter S x first, stateAfter S x' first) = (q, q') := by
    intro x x' q q' word hmem
    induction word generalizing x x' with
    | nil =>
        simp only [pairTrace, List.mem_singleton] at hmem
        exact ⟨[], [], rfl, hmem.symm⟩
    | cons a word ih =>
        simp only [pairTrace, List.mem_cons] at hmem
        rcases hmem with hcurrent | hlater
        · exact ⟨[], a :: word, rfl, hcurrent.symm⟩
        · rcases ih (S.successor a x) (S.successor a x') hlater with
            ⟨first, second, hword, hstate⟩
          refine ⟨a :: first, second, ?_, ?_⟩
          · simp [hword]
          · simpa [stateAfter] using hstate
  have shorten_repeated_path : forall (x x' : X) (word : List A),
      SynchronizedPath S x x' word ->
      Not (pairTrace S x x' word).Nodup ->
        exists shorter,
          shorter.length < word.length ∧
          SynchronizedPath S x x' shorter ∧
          (stateAfter S x shorter, stateAfter S x' shorter) =
            (stateAfter S x word, stateAfter S x' word) := by
    intro x x' word hsync hrepeated
    induction word generalizing x x' with
    | nil =>
        simp [pairTrace] at hrepeated
    | cons a word ih =>
        have hedge := hsync.1
        have htail := hsync.2
        have hnot : Not
            ((x, x') ∉ pairTrace S (S.successor a x)
                (S.successor a x') word ∧
              (pairTrace S (S.successor a x)
                (S.successor a x') word).Nodup) := by
          simpa only [pairTrace, List.nodup_cons] using hrepeated
        by_cases hreturn :
            (x, x') ∈ pairTrace S (S.successor a x)
              (S.successor a x') word
        · rcases trace_mem_split (S.successor a x) (S.successor a x') x x'
              word hreturn with ⟨loop, suffix, hword, hback⟩
          have hall : SynchronizedPath S x x' ((a :: loop) ++ suffix) := by
            simpa [hword] using hsync
          have hparts :=
            (synchronizedPath_append x x' (a :: loop) suffix).mp hall
          have hbackLeft : stateAfter S x (a :: loop) = x :=
            congrArg Prod.fst hback
          have hbackRight : stateAfter S x' (a :: loop) = x' :=
            congrArg Prod.snd hback
          have hsuffix : SynchronizedPath S x x' suffix := by
            simpa [hbackLeft, hbackRight] using hparts.2
          refine ⟨suffix, ?_, hsuffix, ?_⟩
          · rw [hword]
            simp
          · apply Prod.ext
            · simp only
              rw [show a :: word = (a :: loop) ++ suffix by simp [hword],
                stateAfter_append, hbackLeft]
            · simp only
              rw [show a :: word = (a :: loop) ++ suffix by simp [hword],
                stateAfter_append, hbackRight]
        · have htailRepeated : Not
              (pairTrace S (S.successor a x)
                (S.successor a x') word).Nodup := by
            intro hnodup
            exact hnot ⟨hreturn, hnodup⟩
          rcases ih (S.successor a x) (S.successor a x') htail htailRepeated with
            ⟨shorter, hshorter, hshortSync, hsameEnd⟩
          refine ⟨a :: shorter, ?_, ⟨hedge, hshortSync⟩, ?_⟩
          · simp only [List.length_cons]
            omega
          · simpa [stateAfter] using hsameEnd
  have equivalence : List.TFAE [
      ArchiveRecoverable S X0,
      forall x, x ∈ X0 -> forall x', x' ∈ X0 -> forall word,
        SynchronizedPath S x x' word -> deltaSum S x x' word = 0,
      forall pair, SynchronouslyReachable S X0 pair -> forall a,
        SynchronizedEdge S pair a -> S.cost a pair.1 - S.cost a pair.2 = 0] := by
    tfae_have 1 -> 2 := by
      rintro ⟨recover, hrecover⟩ x hx x' hx' word hsync
      rcases (synchronizedPath_iff x x' word).mp hsync with
        ⟨hlegal, hlegal', harchive⟩
      have hclock : clock S x word = clock S x' word := by
        rw [← hrecover x hx word hlegal, ← hrecover x' hx' word hlegal', harchive]
      rw [deltaSum_eq_clock_sub]
      omega
    tfae_have 2 -> 1 := by
      intro hzero
      let Execution := {execution : X × List A //
        execution.1 ∈ X0 ∧ Legal S execution.1 execution.2}
      let archiveOf : Execution → List (A × Y) := fun execution =>
        visibleArchive S execution.1.1 execution.1.2
      let clockOf : Execution → Int := fun execution =>
        clock S execution.1.1 execution.1.2
      have hfiber : Function.FactorsThrough clockOf archiveOf := by
        intro execution execution' harchive
        have hlegal : Legal S execution.1.1 execution.1.2 := execution.2.2
        have hlegal' : Legal S execution'.1.1 execution'.1.2 := execution'.2.2
        have hword : execution.1.2 = execution'.1.2 := by
          have hactions := congrArg (List.map Prod.fst) harchive
          dsimp only [archiveOf] at harchive hactions
          rw [archive_actions execution.1.1 execution.1.2 hlegal,
            archive_actions execution'.1.1 execution'.1.2 hlegal'] at hactions
          exact hactions
        have harchiveWord :
            visibleArchive S execution.1.1 execution.1.2 =
              visibleArchive S execution'.1.1 execution.1.2 := by
          dsimp only [archiveOf] at harchive
          exact harchive.trans (by rw [hword])
        have hsync : SynchronizedPath S execution.1.1 execution'.1.1 execution.1.2 := by
          apply (synchronizedPath_iff execution.1.1 execution'.1.1 execution.1.2).mpr
          exact ⟨hlegal, by simpa only [hword] using hlegal', harchiveWord⟩
        have hdelta := hzero execution.1.1 execution.2.1 execution'.1.1
          execution'.2.1 execution.1.2 hsync
        rw [deltaSum_eq_clock_sub] at hdelta
        dsimp only [clockOf]
        simpa only [hword] using (sub_eq_zero.mp hdelta)
      obtain ⟨recover, hfactor⟩ :=
        (Function.factorsThrough_iff (f := archiveOf) clockOf).mp hfiber
      refine ⟨recover, ?_⟩
      intro x hx word hlegal
      let execution : Execution := ⟨(x, word), hx, hlegal⟩
      have hclock := congrFun hfactor execution
      simpa only [Function.comp_apply, archiveOf, clockOf, execution] using hclock.symm
    tfae_have 2 -> 3 := by
      intro hzero pair hreachable a hedge
      rcases hreachable with ⟨x, hx, x', hx', word, hsync, hend⟩
      have hprefix := hzero x hx x' hx' word hsync
      have hedgeAtEnd : SynchronizedEdge S
          (stateAfter S x word, stateAfter S x' word) a := by
        simpa [hend] using hedge
      have hextended : SynchronizedPath S x x' (word ++ [a]) :=
        (synchronizedPath_append x x' word [a]).mpr
          ⟨hsync, by simpa [SynchronizedPath] using hedgeAtEnd⟩
      have hwhole := hzero x hx x' hx' (word ++ [a]) hextended
      rw [deltaSum_append] at hwhole
      simp only [deltaSum, add_zero] at hwhole
      have hcostAtEnd :
          S.cost a (stateAfter S x word) - S.cost a (stateAfter S x' word) = 0 := by
        omega
      rw [← hend]
      exact hcostAtEnd
    tfae_have 3 -> 2 := by
      intro hedgeZero x hx x' hx' word hsync
      have initialReachable : SynchronouslyReachable S X0 (x, x') := by
        exact ⟨x, hx, x', hx', [], by simp [SynchronizedPath], by simp [stateAfter]⟩
      have propagate : forall (u u' : X) (tail : List A),
          SynchronizedPath S u u' tail ->
          SynchronouslyReachable S X0 (u, u') -> deltaSum S u u' tail = 0 := by
        intro u u' tail htail
        induction tail generalizing u u' with
        | nil => simp [deltaSum]
        | cons b tail ih =>
            intro hreach
            have hcost := hedgeZero (u, u') hreach b htail.1
            have hnextReach : SynchronouslyReachable S X0
                (S.successor b u, S.successor b u') := by
              rcases hreach with ⟨z, hz, z', hz', priorWord, hpSync, hpEnd⟩
              refine ⟨z, hz, z', hz', priorWord ++ [b], ?_, ?_⟩
              · apply (synchronizedPath_append z z' priorWord [b]).mpr
                refine ⟨hpSync, ?_⟩
                simpa [hpEnd, SynchronizedPath] using htail.1
              · rw [stateAfter_append, stateAfter_append]
                simp only [stateAfter]
                exact congrArg
                  (fun pair : X × X =>
                    (S.successor b pair.1, S.successor b pair.2)) hpEnd
            have hrest := ih (S.successor b u) (S.successor b u') htail.2 hnextReach
            simp only [deltaSum]
            rw [hcost, hrest]
            simp
      exact propagate x x' word hsync initialReachable
    tfae_finish
  refine ⟨equivalence, ?_⟩
  intro hnotRecoverable
  have hnotEdges : Not (forall pair, SynchronouslyReachable S X0 pair -> forall a,
      SynchronizedEdge S pair a -> S.cost a pair.1 - S.cost a pair.2 = 0) := by
    intro hedges
    exact hnotRecoverable ((equivalence.out 0 2).mpr hedges)
  push Not at hnotEdges
  rcases hnotEdges with ⟨badPair, hbadReachable, badAction, hbadEdge, hbadCost⟩
  let HasPathLength (k : Nat) : Prop :=
    exists x, x ∈ X0 ∧ exists x', x' ∈ X0 ∧ exists word,
      word.length = k ∧ SynchronizedPath S x x' word ∧
        (stateAfter S x word, stateAfter S x' word) = badPair
  have hasSomeLength : exists k, HasPathLength k := by
    rcases hbadReachable with ⟨x, hx, x', hx', word, hsync, hend⟩
    exact ⟨word.length, x, hx, x', hx', word, rfl, hsync, hend⟩
  rcases Nat.find_spec hasSomeLength with
    ⟨x, hx, x', hx', word, _, hsync, hend⟩
  have htraceNodup : (pairTrace S x x' word).Nodup := by
    by_contra hrepeated
    rcases shorten_repeated_path x x' word hsync hrepeated with
      ⟨shorter, hshorter, hshortSync, hshortEnd⟩
    have hshortHas : HasPathLength shorter.length :=
      ⟨x, hx, x', hx', shorter, rfl, hshortSync, hshortEnd.trans hend⟩
    have hminimal := Nat.find_min' hasSomeLength hshortHas
    omega
  have hlengthBound : word.length + 1 <= n ^ 2 := by
    have hfinite := htraceNodup.length_le_card
    rw [pairTrace_length, Fintype.card_prod, hcard] at hfinite
    simpa [pow_two] using hfinite
  have hedgeAtEnd : SynchronizedEdge S
      (stateAfter S x word, stateAfter S x' word) badAction := by
    simpa [hend] using hbadEdge
  have hbadCostAtEnd :
      S.cost badAction (stateAfter S x word) -
        S.cost badAction (stateAfter S x' word) ≠ 0 := by
    have hleft := congrArg Prod.fst hend
    have hright := congrArg Prod.snd hend
    simp only at hleft hright
    rw [hleft, hright]
    exact hbadCost
  by_cases hprefix : deltaSum S x x' word = 0
  · have hextended : SynchronizedPath S x x' (word ++ [badAction]) :=
      (synchronizedPath_append x x' word [badAction]).mpr
        ⟨hsync, by simpa [SynchronizedPath] using hedgeAtEnd⟩
    rcases (synchronizedPath_iff x x' (word ++ [badAction])).mp hextended with
      ⟨hlegal, hlegal', harchive⟩
    refine ⟨x, hx, x', hx', word ++ [badAction], hlegal, hlegal', harchive, ?_, ?_⟩
    · intro hclock
      have hdeltaClock := deltaSum_eq_clock_sub x x' (word ++ [badAction])
      have hdeltaZero : deltaSum S x x' (word ++ [badAction]) = 0 := by
        rw [hdeltaClock, hclock]
        omega
      rw [deltaSum_append] at hdeltaZero
      simp only [deltaSum, add_zero] at hdeltaZero
      exact hbadCostAtEnd (by omega)
    · simpa using hlengthBound
  · rcases (synchronizedPath_iff x x' word).mp hsync with
      ⟨hlegal, hlegal', harchive⟩
    refine ⟨x, hx, x', hx', word, hlegal, hlegal', harchive, ?_, ?_⟩
    · intro hclock
      apply hprefix
      rw [deltaSum_eq_clock_sub, hclock]
      omega
    · omega

#print axioms archive_clock_recovery_and_finite_ambiguity

end

end D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery
