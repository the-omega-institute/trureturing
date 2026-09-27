/- GID: D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite action graphs have bounded cost exactly when all cycles cost zero. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.TFAE
import Mathlib.Data.Stream.Init
import Mathlib.Tactic

/- Library-search audit trail (2026-09-27):
   * The frozen `ControlledBehaviorUniversality.runWord` supplies left-to-right
     execution. Repository searches found finite autonomous-orbit periodicity,
     but no weighted action-graph theorem combining arbitrary input words,
     cumulative costs, cycle exclusion, and the sharp cardinality bound.
   * Pinned Mathlib supplies `Fintype.exists_ne_map_eq_of_card_lt` for the
     repeated-state step, `List.TFAE` for the equivalence shell,
     `List.take_add` for the prefix split, `Stream'.cycle_eq` and
     `Stream'.append_take` for an ultimately periodic input word, and
     `ENat.iSup_natCast_ne_top` for finite prefix supremum.
     No packaged weighted loop-erasure criterion with this conclusion was found. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound

open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- The sum of the step costs paid while executing a finite action word. -/
def Comm {Q F : Type*} (T : F → Q → Q) (w : Q → F → ℕ) :
    Q → List F → ℕ
  | _, [] => 0
  | state, action :: word => w state action + Comm T w (T action state) word

/-- The supremum, in the extended naturals, of all finite-prefix costs. -/
def InfiniteComm {Q F : Type*} (T : F → Q → Q) (w : Q → F → ℕ)
    (initial : Q) (word : ℕ → F) : ℕ∞ :=
  ⨆ n : ℕ, (Comm T w initial (Stream'.take n word) : ℕ∞)

/-- The finite supremum of the labelled-edge costs, with value zero when
either carrier is empty. -/
def maxEdgeCost {Q F : Type*} [Fintype Q] [Fintype F] (w : Q → F → ℕ) : ℕ :=
  Finset.univ.sup fun state : Q ↦ Finset.univ.sup fun action : F ↦ w state action

/-- For a finite nonempty deterministic action graph whose states are all
reachable from an initialization set, the following are equivalent:
every infinite action word has finite cumulative cost, all finite executions
share one cost bound, and every nonempty closed action word has zero cost.
Under the cycle condition, loop erasure gives the explicit bound
`(Fintype.card Q - 1) * maxEdgeCost w`. -/
theorem cumulative_communication_criterion
    {Q F : Type*} [Fintype Q] [Nonempty Q] [Fintype F] [Nonempty F]
    (I : Set Q) (T : F → Q → Q) (w : Q → F → ℕ)
    (hReach : ∀ state : Q, ∃ initial ∈ I, ∃ path : List F,
      runWord T path initial = state) :
    let finiteInfinite := ∀ initial ∈ I, ∀ word : ℕ → F,
      InfiniteComm T w initial word ≠ ⊤
    let uniformlyBounded := ∃ bound : ℕ, ∀ initial ∈ I, ∀ word : List F,
      Comm T w initial word ≤ bound
    let zeroCycles := ∀ state : Q, ∀ cycle : List F, cycle ≠ [] →
      runWord T cycle state = state → Comm T w state cycle = 0
    List.TFAE [finiteInfinite, uniformlyBounded, zeroCycles] ∧
      (zeroCycles → ∀ initial ∈ I, ∀ word : List F,
        Comm T w initial word ≤
          (Fintype.card Q - 1) * maxEdgeCost w) := by
  classical
  dsimp only
  have runWord_append (state : Q) (left right : List F) :
      runWord T (left ++ right) state = runWord T right (runWord T left state) := by
    induction left generalizing state with
    | nil => rfl
    | cons action left ih =>
        simpa only [List.cons_append, runWord] using ih (T action state)
  have comm_append (state : Q) (left right : List F) :
      Comm T w state (left ++ right) =
        Comm T w state left + Comm T w (runWord T left state) right := by
    induction left generalizing state with
    | nil => simp [Comm, runWord]
    | cons action left ih =>
        simp only [List.cons_append, Comm]
        rw [ih, Nat.add_assoc]
        rfl
  have edge_le_max (state : Q) (action : F) :
      w state action ≤ maxEdgeCost w := by
    exact (Finset.le_sup (s := Finset.univ) (f := fun a : F ↦ w state a)
      (Finset.mem_univ action)).trans
        (Finset.le_sup (s := Finset.univ)
          (f := fun q : Q ↦ Finset.univ.sup fun a : F ↦ w q a)
          (Finset.mem_univ state))
  have comm_le_length_mul (state : Q) (word : List F) :
      Comm T w state word ≤ word.length * maxEdgeCost w := by
    induction word generalizing state with
    | nil => simp [Comm]
    | cons action word ih =>
        simp only [Comm, List.length_cons]
        calc
          w state action + Comm T w (T action state) word ≤
              maxEdgeCost w + word.length * maxEdgeCost w :=
            Nat.add_le_add (edge_le_max state action) (ih (T action state))
          _ = (word.length + 1) * maxEdgeCost w := by
            simp [Nat.add_mul, Nat.add_comm]
  have bound_of_zero_cycles
      (zeroCycles : ∀ state : Q, ∀ cycle : List F, cycle ≠ [] →
        runWord T cycle state = state → Comm T w state cycle = 0) :
      ∀ initial ∈ I, ∀ word : List F,
        Comm T w initial word ≤
          (Fintype.card Q - 1) * maxEdgeCost w := by
    intro initial hInitial word
    have allLengths : ∀ n : ℕ, ∀ initial ∈ I, ∀ word : List F,
        word.length = n →
          Comm T w initial word ≤
            (Fintype.card Q - 1) * maxEdgeCost w := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro initial hInitial word wordLength
        by_cases short : word.length ≤ Fintype.card Q - 1
        · exact (comm_le_length_mul initial word).trans
            (Nat.mul_le_mul_right (maxEdgeCost w) short)
        · have cardLt : Fintype.card Q < Fintype.card (Fin (word.length + 1)) := by
            simp only [Fintype.card_fin]
            omega
          let stateAt : Fin (word.length + 1) → Q := fun index ↦
            runWord T (word.take index.val) initial
          obtain ⟨i, j, hij, statesEqual⟩ :=
            Fintype.exists_ne_map_eq_of_card_lt stateAt cardLt
          have erase_between
              (i j : Fin (word.length + 1)) (hijLt : i.val < j.val)
              (statesEqual : stateAt i = stateAt j) :
              Comm T w initial word ≤
                (Fintype.card Q - 1) * maxEdgeCost w := by
            let path := word.take i.val
            let cycle := (word.drop i.val).take (j.val - i.val)
            let suffix := word.drop j.val
            have split : word = path ++ cycle ++ suffix := by
              dsimp only [path, cycle, suffix]
              calc
                word = word.take i.val ++ word.drop i.val :=
                  (List.take_append_drop i.val word).symm
                _ = word.take i.val ++
                    ((word.drop i.val).take (j.val - i.val) ++
                      word.drop (i.val + (j.val - i.val))) := by
                    rw [List.drop_take_append_drop]
                _ = word.take i.val ++
                    (word.drop i.val).take (j.val - i.val) ++ word.drop j.val := by
                    rw [Nat.add_sub_of_le hijLt.le, List.append_assoc]
            have pathCycle : path ++ cycle = word.take j.val := by
              dsimp only [path, cycle]
              calc
                word.take i.val ++ (word.drop i.val).take (j.val - i.val) =
                    word.take (i.val + (j.val - i.val)) := List.take_add.symm
                _ = word.take j.val := by
                  rw [Nat.add_sub_of_le hijLt.le]
            have cycleNonempty : cycle ≠ [] := by
              intro cycleEmpty
              have lengthZero : cycle.length = 0 :=
                List.length_eq_zero_iff.mpr cycleEmpty
              simp only [cycle, List.length_take, List.length_drop] at lengthZero
              omega
            have cycleClosed :
                runWord T cycle (runWord T path initial) = runWord T path initial := by
              rw [← runWord_append, pathCycle]
              exact statesEqual.symm
            have cycleZero : Comm T w (runWord T path initial) cycle = 0 :=
              zeroCycles (runWord T path initial) cycle cycleNonempty cycleClosed
            have shorter : (path ++ suffix).length < word.length := by
              have cyclePositive : 0 < cycle.length := List.length_pos_of_ne_nil cycleNonempty
              have lengths := congrArg List.length split
              simp only [List.length_append] at lengths ⊢
              omega
            have shorterThanN : (path ++ suffix).length < n := by
              simpa only [wordLength] using shorter
            have reducedBound := ih (path ++ suffix).length shorterThanN
              initial hInitial (path ++ suffix) rfl
            calc
              Comm T w initial word =
                  Comm T w initial path +
                    Comm T w (runWord T path initial) cycle +
                      Comm T w (runWord T cycle (runWord T path initial)) suffix := by
                rw [split, comm_append, comm_append, runWord_append, Nat.add_assoc]
              _ = Comm T w initial path +
                    Comm T w (runWord T path initial) suffix := by
                rw [cycleZero, cycleClosed]
                simp
              _ = Comm T w initial (path ++ suffix) :=
                (comm_append initial path suffix).symm
              _ ≤ (Fintype.card Q - 1) * maxEdgeCost w := reducedBound
          rcases lt_or_gt_of_ne hij with hijLt | hjiLt
          · exact erase_between i j hijLt statesEqual
          · exact erase_between j i hjiLt statesEqual.symm
    exact allLengths word.length initial hInitial word rfl
  have finiteInfinite_implies_zeroCycles :
      (∀ initial ∈ I, ∀ word : ℕ → F,
        InfiniteComm T w initial word ≠ ⊤) →
      ∀ state : Q, ∀ cycle : List F, cycle ≠ [] →
        runWord T cycle state = state → Comm T w state cycle = 0 := by
    intro finiteInfinite state cycle cycleNonempty cycleClosed
    obtain ⟨initial, hInitial, path, pathReaches⟩ := hReach state
    by_contra cycleCostNonzero
    have cycleCostPositive : 0 < Comm T w state cycle :=
      Nat.pos_of_ne_zero cycleCostNonzero
    let periodic : Stream' F := Stream'.cycle cycle cycleNonempty
    let infiniteWord : Stream' F := path ++ₛ periodic
    have cycleTake (n : ℕ) :
        Stream'.take (n * cycle.length) periodic =
          (List.replicate n cycle).flatten := by
      induction n with
      | zero => simp [periodic]
      | succ n ih =>
          rw [Nat.succ_mul, Nat.add_comm]
          rw [show periodic = cycle ++ₛ periodic by
            exact Stream'.cycle_eq cycle cycleNonempty]
          rw [← Stream'.append_take, ih, List.replicate_succ, List.flatten_cons]
    have repeatedComm (n : ℕ) :
        Comm T w state (List.replicate n cycle).flatten =
          n * Comm T w state cycle := by
      induction n with
      | zero => simp [Comm]
      | succ n ih =>
          rw [List.replicate_succ, List.flatten_cons, comm_append, cycleClosed, ih]
          simp [Nat.succ_mul, Nat.add_comm]
    have prefixCost (n : ℕ) :
        Comm T w initial
            (Stream'.take (path.length + n * cycle.length) infiniteWord) =
          Comm T w initial path + n * Comm T w state cycle := by
      rw [← Stream'.append_take, cycleTake, comm_append, pathReaches, repeatedComm]
    have prefixCostsBounded :
        BddAbove (Set.range fun n : ℕ ↦
          Comm T w initial (Stream'.take n infiniteWord)) :=
      ENat.iSup_natCast_ne_top.mp (finiteInfinite initial hInitial infiniteWord)
    obtain ⟨bound, boundProperty⟩ := prefixCostsBounded
    have atLargeIndex := boundProperty
      (Set.mem_range_self (path.length + (bound + 1) * cycle.length))
    rw [prefixCost (bound + 1)] at atLargeIndex
    have repeatedCostLarge :
        bound + 1 ≤ (bound + 1) * Comm T w state cycle :=
      Nat.le_mul_of_pos_right (bound + 1) cycleCostPositive
    omega
  have uniformlyBounded_implies_finiteInfinite :
      (∃ bound : ℕ, ∀ initial ∈ I, ∀ word : List F,
        Comm T w initial word ≤ bound) →
      ∀ initial ∈ I, ∀ word : ℕ → F,
        InfiniteComm T w initial word ≠ ⊤ := by
    rintro ⟨bound, boundProperty⟩ initial hInitial word
    apply ENat.iSup_natCast_ne_top.mpr
    refine ⟨bound, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact boundProperty initial hInitial (Stream'.take n word)
  constructor
  · tfae_have 1 → 3 := finiteInfinite_implies_zeroCycles
    tfae_have 3 → 2 := by
      intro zeroCycles
      exact ⟨(Fintype.card Q - 1) * maxEdgeCost w, bound_of_zero_cycles zeroCycles⟩
    tfae_have 2 → 1 := uniformlyBounded_implies_finiteInfinite
    tfae_finish
  · exact bound_of_zero_cycles

#print axioms cumulative_communication_criterion

end D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
