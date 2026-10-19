/- GID: D5/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement.pairwise_signature_termination; instance=D5/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement.utilityInput
   digest: Ordered pairwise signature refinement terminates with a uniform primitive-operation bound. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/- Ordered pairwise signature refinement on explicitly enumerated states and
inputs. The abstract operation trace includes comparisons and label writes;
it does not count Lean VM steps or the implementation of observation equality.
Finite stability is applied to the actual image of the observation. The
observation carrier is arbitrary and the input alphabet may be empty. -/

namespace D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.ControlledRelationRecursion
open D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability
open D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization

universe u

noncomputable def initialClasses {X O : Type} (o : X → O) : Nat :=
  Nat.card (Quotient (Setoid.ker o))

/-- Consumed bridge: the existing finite theorem is applied to actual readouts;
the empty alphabet is handled at depth zero. -/
private theorem finite_depth_complete {X A O : Type}
    [Fintype X] [Nonempty X] [Fintype A] (F : A → X → X) (o : X → O) :
    ∃ h ≤ Nat.card X - initialClasses o,
      controlledDepthRelation F o h = controlledDepthRelation F o (h + 1) ∧
      controlledDepthRelation F o h = controlledLimitRelation F o := by
  classical
  by_cases inhabited : Nonempty A
  · letI : Nonempty A := inhabited
    let ro := Set.rangeFactorization o
    letI : Fintype (Set.range o) := Fintype.ofFinite _
    letI : Nonempty (Set.range o) := ⟨ro (Classical.choice ‹Nonempty X›)⟩
    have dr (h : Nat) : controlledDepthRelation F ro h = controlledDepthRelation F o h := by
      ext pair
      constructor
      · intro same w hw
        exact congrArg Subtype.val (same w hw)
      · intro same w hw
        exact Subtype.ext (same w hw)
    have c0 : initialClasses o = Fintype.card (Set.range o) := by
      exact (Nat.card_congr (Setoid.quotientKerEquivRange o)).trans
        (Nat.card_eq_fintype_card)
    have old := controlled_finite_stability F ro Set.rangeFactorization_surjective
    let h := controlledStabilityDepth F ro
    have stable : controlledDepthRelation F o h = controlledDepthRelation F o (h + 1) := by
      rw [← dr h, ← dr (h + 1)]
      exact old.2.2.2.1.1
    refine ⟨h, ?_, stable, controlled_stable_relation_eq_limit F o h stable⟩
    simpa only [h, c0, Nat.card_eq_fintype_card] using
      old.2.2.2.2.1.trans old.2.2.2.2.2
  · letI : IsEmpty A := not_nonempty_iff.mp inhabited
    have empty_word (w : List A) : w = [] := by
      cases w with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    have all_depth (h : Nat) : controlledDepthRelation F o h = readoutKernel o := by
      ext pair
      constructor
      · intro same
        exact same [] (Nat.zero_le _)
      · intro same w _
        rw [empty_word w]
        exact same
    have stable : controlledDepthRelation F o 0 = controlledDepthRelation F o 1 :=
      (all_depth 0).trans (all_depth 1).symm
    exact ⟨0, Nat.zero_le _, stable, controlled_stable_relation_eq_limit F o 0 stable⟩

/-- The least input index with this value. This uses the supplied order and a
supplied equality procedure, with no choice of a Fintype equivalence. -/
def label {n : Nat} {O : Type} [DecidableEq O] (f : Fin n → O) (x : Fin n) : Fin n :=
  (Finset.univ.filter fun y => f y = f x).min' ⟨x, by simp⟩

private theorem label_value {n : Nat} {O : Type} [DecidableEq O]
    (f : Fin n → O) (x : Fin n) : f (label f x) = f x := by
  have mem : label f x ∈ Finset.univ.filter (fun y : Fin n => f y = f x) :=
    Finset.min'_mem _ _
  exact (Finset.mem_filter.mp mem).2

private theorem label_eq_iff {n : Nat} {O : Type} [DecidableEq O]
    (f : Fin n → O) (x y : Fin n) : label f x = label f y ↔ f x = f y := by
  constructor
  · intro same
    exact (label_value f x).symm.trans ((congrArg f same).trans (label_value f y))
  · intro same
    simp only [label, same]

/-- Canonical class names depend only on the equality partition, so a stable
relation gives equality of the actual label tables, not just isomorphism. -/
private theorem label_congr {n : Nat} {O P : Type}
    [DecidableEq O] [DecidableEq P] (f : Fin n → O) (g : Fin n → P)
    (same : ∀ x y, f x = f y ↔ g x = g y) : label f = label g := by
  funext x
  have sets : (Finset.univ.filter fun y => f y = f x) =
      (Finset.univ.filter fun y => g y = g x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, same]
  simpa only [label, sets]

/-- The signature uses old class labels, not recursively expanded histories. -/
def nextSignature {n k : Nat} {O : Type}
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (c : Fin n → Fin n)
    (x : Fin n) : O × (Fin k → Fin n) := (o x, fun a => c (F a x))

def labelsAt {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) : Nat → Fin n → Fin n
  | 0 => label o
  | h + 1 => label (nextSignature F o (labelsAt F o h))

private theorem labelsAt_correct {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) :
    ∀ h x y, labelsAt F o h x = labelsAt F o h y ↔
      (x,y) ∈ controlledDepthRelation F o h := by
  intro h
  induction h with
  | zero =>
      intro x y
      rw [(controlled_behavior_relation_recursion F o 0).1]
      exact label_eq_iff o x y
  | succ h ih =>
      intro x y
      rw [labelsAt, label_eq_iff, (controlled_behavior_relation_recursion F o h).2]
      change (o x, fun a => labelsAt F o h (F a x)) =
        (o y, fun a => labelsAt F o h (F a y)) ↔ _
      simp only [Prod.mk.injEq, funext_iff, ih, Set.mem_inter_iff,
        readoutKernel, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Prod.map_apply]

/-- Mathematical semantics of a full pairwise scan. Each constructor denotes
one unit operation in the input model; operands/results prevent a scalar cost
assertion from being substituted for the prescribed comparisons. -/
inductive UnitOp (n k : Nat) (O : Type) where
  | statePair : Fin n → Fin n → UnitOp n k O
  | action : Fin k → UnitOp n k O
  | transition : Fin k → Fin n → Fin n → UnitOp n k O
  | observationEq : O → O → Bool → UnitOp n k O
  | labelRead : Fin n → Fin n → UnitOp n k O
  | labelEq : Fin n → Fin n → Bool → UnitOp n k O
  | selectCandidate : Fin n → Fin n → Bool → UnitOp n k O
  | recordCoordinate : Bool → UnitOp n k O
  | compareFlags : Bool → Bool → Bool → UnitOp n k O
  | storeLabel : Fin n → Fin n → UnitOp n k O
  | writeCell : Fin n → Fin n → Bool → UnitOp n k O

/-- Ordered implementation of least-index relabeling with its operation trace.
The callback emits the already evaluated pair comparisons and candidate update;
`best` is the actual running minimum, not an arbitrary representative. -/
def scanTrace {n : Nat} {P E : Type} [DecidableEq P]
    (f : Fin n → P) (x : Fin n)
    (emit : Fin n → Fin n → Bool → List E) :
    List (Fin n) → Fin n → Fin n × List E
  | [], best => (best, [])
  | y :: ys, best =>
      let next := if f y = f x then min best y else best
      let tail := scanTrace f x emit ys next
      (tail.1, emit best y (decide (f y = f x)) ++ tail.2)

private theorem scanTrace_invariant {n : Nat} {P E : Type} [DecidableEq P]
    (f : Fin n → P) (x : Fin n) (emit : Fin n → Fin n → Bool → List E)
    (m : Nat) (hem : ∀ best y test, (emit best y test).length = m)
    (ys : List (Fin n)) (best : Fin n) (hbest : f best = f x) :
    f (scanTrace f x emit ys best).1 = f x ∧
    (scanTrace f x emit ys best).1 ≤ best ∧
    (∀ y ∈ ys, f y = f x → (scanTrace f x emit ys best).1 ≤ y) ∧
    (scanTrace f x emit ys best).2.length = ys.length*m := by
  induction ys generalizing best with
  | nil => simp [scanTrace, hbest]
  | cons y ys ih =>
      let next := if f y = f x then min best y else best
      have hn : f next = f x := by
        by_cases hy : f y = f x
        · simp only [next, if_pos hy]
          rcases le_total best y with h | h
          · rw [min_eq_left h]
            exact hbest
          · rw [min_eq_right h]
            exact hy
        · simpa only [next, if_neg hy] using hbest
      have hle : next ≤ best := by
        dsimp [next]
        split
        · exact min_le_left _ _
        · exact le_rfl
      have ihScan := ih next hn
      change f (scanTrace f x emit ys next).1 = f x ∧
        (scanTrace f x emit ys next).1 ≤ best ∧
        (∀ z ∈ y :: ys, f z = f x → (scanTrace f x emit ys next).1 ≤ z) ∧
        (emit best y (decide (f y = f x)) ++ (scanTrace f x emit ys next).2).length =
          (y :: ys).length*m
      refine ⟨ihScan.1, ihScan.2.1.trans hle, ?_, ?_⟩
      · intro z hz equal
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ihScan.2.1.trans (by simpa [next, equal] using (min_le_right best y))
        · exact ihScan.2.2.1 z hz equal
      · rw [List.length_append, hem, ihScan.2.2.2, List.length_cons]
        ring

private theorem scanTrace_eq_label {n : Nat} {P E : Type} [DecidableEq P]
    (f : Fin n → P) (x : Fin n) (emit : Fin n → Fin n → Bool → List E)
    (m : Nat) (hem : ∀ best y test, (emit best y test).length = m) :
    (scanTrace f x emit (List.finRange n) x).1 = label f x := by
  have spec := scanTrace_invariant f x emit m hem (List.finRange n) x rfl
  apply le_antisymm
  · exact spec.2.2.1 (label f x) (by simp) (label_value f x)
  · exact Finset.min'_le _ _ (by simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]; exact spec.1)

/-- Compare every coordinate, even after a mismatch. Candidate selection uses
these recorded coordinate tests to select the first matching index in finRange.
No recursive history comparison is performed by the execution contract. -/
def pairTrace {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O)
    (c : Fin n → Fin n) (x y : Fin n) : List (UnitOp n k O) :=
  [.statePair x y, .observationEq (o x) (o y) (decide (o x = o y))] ++
  (List.finRange k).flatMap (fun a =>
    [.action a, .transition a x (F a x), .transition a y (F a y),
     .labelRead (F a x) (c (F a x)), .labelRead (F a y) (c (F a y)),
     .labelEq (c (F a x)) (c (F a y)) (decide (c (F a x) = c (F a y))),
     .recordCoordinate (decide (c (F a x) = c (F a y)))]) ++
  [.writeCell x y (decide (nextSignature F o c x = nextSignature F o c y))]

/-- The second scan compares the two equality matrices after new labels have
been stored. All Boolean comparison results are explicitly represented. -/
def stabilityTrace {n k : Nat} {O : Type} (c d : Fin n → Fin n) :
    List (UnitOp n k O) :=
  (List.finRange n).flatMap fun x => (List.finRange n).flatMap fun y =>
    [.statePair x y,
     .labelEq (c x) (c y) (decide (c x = c y)),
     .labelEq (d x) (d y) (decide (d x = d y)),
     .compareFlags (decide (c x = c y)) (decide (d x = d y))
       (decide ((c x = c y) ↔ (d x = d y)))]

def roundScan {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (h : Nat) (x : Fin n) :
    Fin n × List (UnitOp n k O) :=
  scanTrace (nextSignature F o (labelsAt F o h)) x
    (fun best y test => pairTrace F o (labelsAt F o h) x y ++
      [.selectCandidate best y test]) (List.finRange n) x

def initialScan {n k : Nat} {O : Type} [DecidableEq O]
    (o : Fin n → O) (x : Fin n) : Fin n × List (UnitOp n k O) :=
  scanTrace o x (fun best y test =>
    [.statePair x y, .observationEq (o y) (o x) test,
     .writeCell x y test, .selectCandidate best y test]) (List.finRange n) x

def roundTrace {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (h : Nat) :
    List (UnitOp n k O) :=
  ((List.finRange n).flatMap fun x => (roundScan F o h x).2) ++
  (List.finRange n).map (fun x => .storeLabel x (roundScan F o h x).1) ++
  stabilityTrace (labelsAt F o h) (fun x => (roundScan F o h x).1)

def initialTrace {n k : Nat} {O : Type} [DecidableEq O]
    (o : Fin n → O) : List (UnitOp n k O) :=
  ((List.finRange n).flatMap fun x => (initialScan (k := k) o x).2) ++
  (List.finRange n).map (fun x => .storeLabel x (initialScan (k := k) o x).1)

/-- Initial labeling, h strict refinements, and the final comparison round. -/
def totalTrace {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (h : Nat) :
    List (UnitOp n k O) :=
  initialTrace (k := k) o ++ (List.range (h + 1)).flatMap (roundTrace F o)

private theorem flatMap_length_const {α β : Type*} (l : List α)
    (f : α → List β) (c : Nat) (hf : ∀ x ∈ l, (f x).length = c) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [hf x (by simp), ih (by intro y hy; exact hf y (by simp [hy]))]
      simp [Nat.add_mul, Nat.add_comm]

private theorem pairTrace_length {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O)
    (c : Fin n → Fin n) (x y : Fin n) :
    (pairTrace F o c x y).length = 7*k+3 := by
  unfold pairTrace
  simp only [List.length_append]
  rw [flatMap_length_const _ _ 7 (by intros; rfl)]
  simp only [List.length_finRange, List.length_cons, List.length_nil]
  omega

private theorem roundScan_spec {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (h : Nat) (x : Fin n) :
    (roundScan F o h x).1 = labelsAt F o (h+1) x ∧
    (roundScan F o h x).2.length = n*(7*k+4) := by
  have hem (best y : Fin n) (test : Bool) :
      (pairTrace F o (labelsAt F o h) x y ++
        [UnitOp.selectCandidate best y test]).length = 7*k+4 := by
    rw [List.length_append, pairTrace_length]
    simp only [List.length_cons, List.length_nil]
  refine ⟨scanTrace_eq_label _ _ _ (7*k+4) hem, ?_⟩
  simpa only [roundScan, List.length_finRange] using
    (scanTrace_invariant (nextSignature F o (labelsAt F o h)) x
      (fun best y test => pairTrace F o (labelsAt F o h) x y ++
        [.selectCandidate best y test]) (7*k+4) hem (List.finRange n) x rfl).2.2.2

private theorem initialScan_spec {n k : Nat} {O : Type} [DecidableEq O]
    (o : Fin n → O) (x : Fin n) :
    (initialScan (k := k) o x).1 = label o x ∧
    (initialScan (k := k) o x).2.length = n*4 := by
  have hem (best y : Fin n) (test : Bool) :
      ([UnitOp.statePair (k := k) (O := O) x y, .observationEq (o y) (o x) test,
        .writeCell x y test, .selectCandidate best y test]).length = 4 := rfl
  refine ⟨scanTrace_eq_label _ _ _ 4 hem, ?_⟩
  simpa only [initialScan, List.length_finRange] using
    (scanTrace_invariant o x _ 4 hem (List.finRange n) x rfl).2.2.2

private theorem roundTrace_length {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (h : Nat) :
    (roundTrace F o h).length = n*n*(7*k+8)+n := by
  have stable (c d : Fin n → Fin n) :
      (stabilityTrace (k := k) (O := O) c d).length = 4*n*n := by
    unfold stabilityTrace
    rw [flatMap_length_const _ _ (n*4) (by
      intro x _
      rw [flatMap_length_const _ _ 4 (by intros; rfl)]
      simp)]
    simp only [List.length_finRange]
    ring
  unfold roundTrace
  simp only [List.length_append, List.length_map, List.length_finRange, stable]
  rw [flatMap_length_const _ _ (n*(7*k+4)) (by
    intro x _; exact (roundScan_spec F o h x).2)]
  simp only [List.length_finRange]
  ring

private theorem totalTrace_length {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O) (h : Nat) :
    (totalTrace F o h).length = 4*n*n+n + (h+1)*(n*n*(7*k+8)+n) := by
  have init : (initialTrace (k := k) o).length = 4*n*n+n := by
    unfold initialTrace
    simp only [List.length_append, List.length_map, List.length_finRange]
    rw [flatMap_length_const _ _ (n*4) (by
      intro x _; exact (initialScan_spec (k := k) o x).2)]
    simp only [List.length_finRange]
    ring
  unfold totalTrace
  rw [List.length_append, init,
    flatMap_length_const _ _ (n*n*(7*k+8)+n) (by intros; apply roundTrace_length)]
  simp

/-- Formal count relation for the specified pairwise implementation. A witness
contains the computed label table and complete primitive trace, as well as the
actual stopping test. No complexity bound is a premise. -/
def Terminates {n k : Nat} {O : Type} [DecidableEq O]
    (F : Fin k → Fin n → Fin n) (o : Fin n → O)
    (h cost : Nat) (c : Fin n → Fin n) : Prop :=
  c = labelsAt F o h ∧ labelsAt F o h = labelsAt F o (h+1) ∧
    cost = (totalTrace F o h).length ∧
    (∀ x, (initialScan (k := k) o x).1 = labelsAt F o 0 x) ∧
    (∀ j ≤ h, ∀ x, (roundScan F o j x).1 = labelsAt F o (j+1) x)

/-- Uniform pairwise-signature termination, exact quotient, distinguishing-word
bound and unit-operation count. O is arbitrary; its equality procedure belongs
only to this execution interface. k may be zero. The constant 14 is independent
of n, k, the transition table, observation values and the equality procedure. -/
theorem pairwise_signature_termination {n k : Nat} (hn : 0 < n)
    {O : Type} [DecidableEq O] (F : Fin k → Fin n → Fin n) (o : Fin n → O) :
    ∃ h cost c, h ≤ n - initialClasses o ∧ Terminates F o h cost c ∧
      (∀ x y, c x = c y ↔ controlledBehavior F o x = controlledBehavior F o y) ∧
      (∀ x y, controlledBehavior F o x ≠ controlledBehavior F o y →
        ∃ w : List (Fin k), w.length ≤ n - initialClasses o ∧
          o (runWord F w x) ≠ o (runWord F w y)) ∧
      cost = 4*n*n+n + (h+1)*(n*n*(7*k+8)+n) ∧
      cost ≤ 14*(k+1)*n*n*(n-initialClasses o+1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨h, hb, hs, hc⟩ := finite_depth_complete F o
  have hb' : h ≤ n - initialClasses o := by simpa using hb
  have table : labelsAt F o h = labelsAt F o (h+1) := by
    have kernel : ∀ x y, labelsAt F o h x = labelsAt F o h y ↔
        labelsAt F o (h+1) x = labelsAt F o (h+1) y := by
      intro x y
      rw [labelsAt_correct, labelsAt_correct, hs]
    cases h with
    | zero =>
        apply label_congr
        intro x y
        simpa only [labelsAt, label_eq_iff] using kernel x y
    | succ h =>
        apply label_congr
        intro x y
        simpa only [labelsAt, label_eq_iff] using kernel x y
  refine ⟨h, (totalTrace F o h).length, labelsAt F o h, hb',
    ⟨rfl, table, rfl, (fun x => (initialScan_spec (k := k) o x).1),
      (fun j _ x => (roundScan_spec F o j x).1)⟩,
    ?_, ?_, totalTrace_length F o h, ?_⟩
  · intro x y
    rw [labelsAt_correct, hc]
    rfl
  · intro x y different
    have notBounded : ¬ (x,y) ∈ controlledDepthRelation F o h := by
      rw [hc]
      exact different
    change ¬ (∀ w : List (Fin k), w.length ≤ h →
      o (runWord F w x) = o (runWord F w y)) at notBounded
    push_neg at notBounded
    obtain ⟨w, hw, hd⟩ := notBounded
    exact ⟨w, hw.trans hb', hd⟩
  · rw [totalTrace_length]
    let D := n-initialClasses o+1
    have hD : 1 ≤ D := by omega
    have hn2 : n ≤ n*n := by nlinarith
    have hround : n*n*(7*k+8)+n ≤ n*n*(7*k+9) := by nlinarith
    have hinit : 4*n*n+n ≤ 5*n*n*D := by
      have hm := Nat.mul_le_mul_left (5*n*n) hD
      nlinarith
    calc
      4*n*n+n + (h+1)*(n*n*(7*k+8)+n)
          ≤ 5*n*n*D + D*(n*n*(7*k+9)) :=
            Nat.add_le_add hinit (Nat.mul_le_mul (by omega) hround)
      _ = (7*k+14)*n*n*D := by ring
      _ ≤ 14*(k+1)*n*n*D := by gcongr; omega

/-- Concrete ordered input for the original 2.3 utility check: states 0 and 1
initially agree; the action sends 1 to the differently observed state 2. -/
def utilityInput : (Fin 1 → Fin 3 → Fin 3) × (Fin 3 → Bool) :=
  (fun _ x => if x = 1 then 2 else x, fun x => decide (x = 2))

end D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement
