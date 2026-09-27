/- GID: D5/S1/Recurrence/Raney/MaximalBlockEvolution
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/MaximalBlockEvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stabilize morphism iterates and locate maximal blocks inside uniform images. -/

import Mathlib

namespace TrureTuring
namespace Raney

/-- The set of letters reached from `s` by one simultaneous morphism step. -/
private def supportStep {Alphabet : Type*} [DecidableEq Alphabet]
    (morphism : Alphabet -> List Alphabet) (s : Finset Alphabet) : Finset Alphabet :=
  s.biUnion fun a => (morphism a).toFinset

/-- Literal iteration of a word morphism. -/
def morphismPower {Alphabet : Type*} (morphism : Alphabet -> List Alphabet) :
    Nat -> List Alphabet -> List Alphabet
  | 0, word => word
  | n + 1, word => (morphismPower morphism n word).flatMap morphism

/-- BKS Lemma 10 in the finite-alphabet form needed by the Raney construction.

The exponent is constructed from eventual repetition of the powers of the finite
endomorphism on letter supports.  Passing beyond the preperiod and to a multiple
of the resulting period makes that power idempotent, so every further positive
power has exactly the same reachable-letter support. -/
theorem exists_support_stabilizing_power
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (morphism : Alphabet -> List Alphabet) :
    ∃ q : Nat, 0 < q ∧ ∀ (a : Alphabet) (n : Nat), 0 < n ->
      (morphismPower morphism (q * n) [a]).toFinset =
        (morphismPower morphism q [a]).toFinset := by
  let f : Finset Alphabet -> Finset Alphabet := supportStep morphism
  have support_eq (a : Alphabet) (n : Nat) :
      f^[n] {a} = (morphismPower morphism n [a]).toFinset := by
    induction n with
    | zero => simp [morphismPower]
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        ext b
        simp [f, supportStep, morphismPower]
  obtain ⟨i, j, hlt, hpowers⟩ :
      ∃ i j : Nat, i < j ∧ f^[i] = f^[j] := by
    obtain ⟨i, j, hij, hpowers⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun n : Nat => f^[n])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨i, j, hlt, hpowers⟩
    · exact ⟨j, i, hlt, hpowers.symm⟩
  let d := j - i
  have hd : 0 < d := Nat.sub_pos_of_lt hlt
  have hj : j = i + d := by omega
  have hperiod : ∀ k : Nat, f^[i + k] = f^[i + d + k] := by
    intro k
    calc
      f^[i + k] = f^[i] ∘ f^[k] := Function.iterate_add f i k
      _ = f^[j] ∘ f^[k] := congrArg (fun g => g ∘ f^[k]) hpowers
      _ = f^[j + k] := (Function.iterate_add f j k).symm
      _ = f^[i + d + k] := by rw [hj]
  let q := d * (i + 1)
  have hiq : i ≤ q := by
    exact (Nat.le_succ i).trans (Nat.le_mul_of_pos_left (i + 1) hd)
  have hq : 0 < q := mul_pos hd (Nat.succ_pos i)
  have hshift : ∀ t : Nat, f^[q] = f^[q + t * d] := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        rw [Nat.succ_mul, ← Nat.add_assoc]
        calc
          f^[q] = f^[q + t * d] := iht
          _ = f^[q + t * d + d] := by
            have hibase : i ≤ q + t * d := hiq.trans (Nat.le_add_right q (t * d))
            obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hibase
            rw [hk]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hperiod k
  refine ⟨q, hq, ?_⟩
  intro a n hn
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hpow : f^[q * (t + 1)] = f^[q] := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    simpa [q, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (hshift (t * (i + 1))).symm
  have hs := congrFun hpow {a}
  rw [support_eq, support_eq] at hs
  simpa [Nat.add_comm] using hs

/-- A letter at an offset in one uniform image word. -/
def uniformLetter {Alphabet : Type*} {P : Nat}
    (morphism : Alphabet -> List Alphabet)
    (uniform : ∀ a, (morphism a).length = P) (a : Alphabet) (offset : Fin P) : Alphabet :=
  (morphism a).get ⟨offset, by rw [uniform a]; exact offset.isLt⟩

/-- A finite maximal `Delta`-interval in an infinite word, including the start-zero convention. -/
def IsMaximalDeltaInterval {Alphabet : Type*} [DecidableEq Alphabet]
    (Delta : Finset Alphabet) (word : Nat -> Alphabet) (first last : Nat) : Prop :=
  first <= last ∧
    (∀ n, first <= n -> n <= last -> word n ∈ Delta) ∧
    (first = 0 ∨ word (first - 1) ∉ Delta) ∧
    word (last + 1) ∉ Delta

/-- The uniform specialization of BKS Lemma 11, with boundary-safe intervals.

The quotient endpoints form the shortest source interval whose image contains the
block.  Support stability forces its central letters into `Delta`: otherwise the
same complementary letter occurs in a complete second-order image cell inside the
block.  Applying the same argument to the two maximality witnesses puts a
complementary letter in each bounded source neighborhood.

The length bound `2 * P^2` is the safe threshold that also makes the central interval
nonempty.  The arithmetic transport below uses one wider endpoint than the paper's
displayed neighborhoods.  This is a conservative formal variant, not a claim that the
paper's stated range fails under its full hypotheses. -/
theorem uniform_bks11_predecessor
    {Alphabet : Type*} [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (uniform : ∀ a, (morphism a).length = P) (word : Nat -> Alphabet)
    (fixed : ∀ (i : Nat) (offset : Fin P),
      word (P * i + offset) = uniformLetter morphism uniform (word i) offset)
    (supportStable : ∀ a,
      (morphismPower morphism 2 [a]).toFinset = (morphism a).toFinset)
    (Delta : Finset Alphabet) (first last : Nat)
    (block : IsMaximalDeltaInterval Delta word first last)
    (late : P < first) (long : 2 * P ^ 2 < last + 1 - first) :
    let sourceFirst := first / P
    let sourceLast := last / P
    sourceFirst + P <= sourceLast - P ∧
      (∀ n, sourceFirst + P <= n -> n <= sourceLast - P -> word n ∈ Delta) ∧
      (∃ n, sourceFirst - P <= n ∧ n <= sourceFirst + P - 1 ∧ word n ∉ Delta) ∧
      (∃ n, sourceLast - P + 1 <= n ∧ n <= sourceLast + P ∧ word n ∉ Delta) := by
  dsimp
  rcases block with ⟨hFirstLast, hInside, hLeft, hRight⟩
  have hP0 : 0 < P := by omega
  have source_cell (source : Nat) (offset : Fin P) :
      word (P * source + offset) = (morphism (word source)).get
        ⟨offset, by rw [uniform (word source)]; exact offset.isLt⟩ := by
    simpa [uniformLetter] using fixed source offset
  have source_mem_image (source : Nat) (offset : Fin P) :
      word (P * source + offset) ∈ morphism (word source) := by
    rw [source_cell]
    exact List.get_mem _ _
  have hSourceOrder : first / P <= last / P := Nat.div_le_div_right hFirstLast
  have hCoveredLength : last + 1 - first <= P * (last / P - first / P + 1) := by
    have hFirstLower : P * (first / P) <= first := Nat.mul_div_le first P
    have hLastUpper : last < P * (last / P + 1) := by
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (last / P))
    calc
      last + 1 - first <= last + 1 - P * (first / P) :=
        Nat.sub_le_sub_left hFirstLower (last + 1)
      _ <= P * (last / P + 1) - P * (first / P) :=
        Nat.sub_le_sub_right (Nat.succ_le_iff.mpr hLastUpper) (P * (first / P))
      _ = P * ((last / P + 1) - first / P) :=
        (Nat.mul_sub_left_distrib P (last / P + 1) (first / P)).symm
      _ = P * (last / P - first / P + 1) := by
        congr 1
        omega
  have hCentral : first / P + P <= last / P - P := by
    by_contra h
    have hSourceSpan : last / P - first / P + 1 <= 2 * P := by omega
    have : last + 1 - first <= 2 * P ^ 2 := by
      calc
        last + 1 - first <= P * (last / P - first / P + 1) := hCoveredLength
        _ <= P * (2 * P) := Nat.mul_le_mul_left P hSourceSpan
        _ = 2 * P ^ 2 := by ring
    omega
  refine ⟨hCentral, ?_, ?_, ?_⟩
  · intro n hnLeft hnRight
    by_contra hnDelta
    let parent := n / P
    let firstOffset : Fin P := ⟨n % P, Nat.mod_lt n hP0⟩
    have hnImage : word n ∈ morphism (word parent) := by
      have hnCoord : n = P * parent + firstOffset := by
        dsimp [parent, firstOffset]
        exact (Nat.div_add_mod n P).symm
      rw [hnCoord]
      exact source_mem_image parent firstOffset
    have hnSecond : word n ∈ morphismPower morphism 2 [word parent] := by
      have : word n ∈ (morphismPower morphism 2 [word parent]).toFinset := by
        rw [supportStable]
        simpa using hnImage
      simpa using this
    obtain ⟨middle, hMiddle, hnMiddle⟩ :
        ∃ middle ∈ morphism (word parent), word n ∈ morphism middle := by
      simpa [morphismPower] using
        (show ∃ a ∈ morphism (word parent), word n ∈ morphism a from by
          simpa [morphismPower] using hnSecond)
    obtain ⟨middleOffset, hMiddleAt⟩ := List.mem_iff_get.mp hMiddle
    obtain ⟨finalOffset, hFinalAt⟩ := List.mem_iff_get.mp hnMiddle
    let middleFin : Fin P :=
      ⟨middleOffset, by simpa [uniform (word parent)] using middleOffset.isLt⟩
    let finalFin : Fin P :=
      ⟨finalOffset, by simpa [uniform middle] using finalOffset.isLt⟩
    let witness := P * (P * parent + middleFin) + finalFin
    have hMiddleWord : word (P * parent + middleFin) = middle := by
      rw [source_cell]
      simpa [middleFin] using hMiddleAt
    have hWitnessWord : word witness = word n := by
      dsimp [witness]
      rw [source_cell, hMiddleWord]
      simpa [finalFin] using hFinalAt
    have hParentLower : first <= P * (P * parent) := by
      have hnUpper : n < P * (parent + 1) := by
        dsimp [parent]
        simpa [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (n / P))
      have hSourceStrict : first / P < P * parent := by
        rw [Nat.mul_add, Nat.mul_one] at hnUpper
        omega
      have hFirstUpper : first < P * (first / P + 1) := by
        simpa [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (first / P))
      exact hFirstUpper.le.trans
        (Nat.mul_le_mul_left P (Nat.succ_le_iff.mpr hSourceStrict))
    have hParentUpper : P * (P * (parent + 1)) <= last := by
      have hnLower : P * parent <= n := by
        dsimp [parent]
        exact Nat.mul_div_le n P
      have hPSourceLast : P <= last / P := by
        exact (Nat.le_add_left P (first / P)).trans
          (hCentral.trans (Nat.sub_le (last / P) P))
      have hParentToSourceLast : P * (parent + 1) <= last / P := by
        calc
          P * (parent + 1) = P * parent + P := by rw [Nat.mul_add, Nat.mul_one]
          _ <= n + P := Nat.add_le_add_right hnLower P
          _ <= (last / P - P) + P := Nat.add_le_add_right hnRight P
          _ = last / P := Nat.sub_add_cancel hPSourceLast
      have hLastLower : P * (last / P) <= last := Nat.mul_div_le last P
      exact (Nat.mul_le_mul_left P hParentToSourceLast).trans hLastLower
    have hWitnessLower : first <= witness := by
      apply hParentLower.trans
      dsimp [witness]
      rw [Nat.mul_add]
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    have hWitnessUpper : witness <= last := by
      have hFinalLt : (finalFin : Nat) < P := finalFin.isLt
      have hMiddleLt : (middleFin : Nat) < P := middleFin.isLt
      have hOffsets : P * (middleFin : Nat) + finalFin < P * P := by
        calc
          P * (middleFin : Nat) + finalFin < P * (middleFin : Nat) + P :=
            Nat.add_lt_add_left hFinalLt _
          _ = P * ((middleFin : Nat) + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ <= P * P := Nat.mul_le_mul_left P (Nat.succ_le_iff.mpr hMiddleLt)
      have hInsideSecond : witness < P * (P * (parent + 1)) := by
        calc
          witness = P * (P * parent) +
              (P * (middleFin : Nat) + finalFin) := by
            dsimp [witness]
            rw [Nat.mul_add, Nat.add_assoc]
          _ < P * (P * parent) + P * P := Nat.add_lt_add_left hOffsets _
          _ = P * (P * (parent + 1)) := by ring
      exact (hInsideSecond.trans_le hParentUpper).le
    exact hnDelta (hWitnessWord ▸ hInside witness hWitnessLower hWitnessUpper)
  · have hFirstPos : 0 < first := by omega
    have hLeftOutside : word (first - 1) ∉ Delta := hLeft.resolve_left hFirstPos.ne'
    let sourceBefore := (first - 1) / P
    let parent := sourceBefore / P
    let beforeOffset : Fin P := ⟨(first - 1) % P, Nat.mod_lt _ hP0⟩
    have hBeforeImage : word (first - 1) ∈ morphism (word sourceBefore) := by
      have hCoord : first - 1 = P * sourceBefore + beforeOffset := by
        dsimp [sourceBefore, beforeOffset]
        exact (Nat.div_add_mod (first - 1) P).symm
      rw [hCoord]
      exact source_mem_image sourceBefore beforeOffset
    let sourceOffset : Fin P := ⟨sourceBefore % P, Nat.mod_lt _ hP0⟩
    have hSourceImage : word sourceBefore ∈ morphism (word parent) := by
      have hCoord : sourceBefore = P * parent + sourceOffset := by
        dsimp [parent, sourceOffset]
        exact (Nat.div_add_mod sourceBefore P).symm
      rw [hCoord]
      exact source_mem_image parent sourceOffset
    have hBeforeSecond : word (first - 1) ∈ morphismPower morphism 2 [word parent] := by
      simpa [morphismPower] using
        (show ∃ a ∈ morphism (word parent), word (first - 1) ∈ morphism a from
          ⟨word sourceBefore, hSourceImage, hBeforeImage⟩)
    have hBeforeFirst : word (first - 1) ∈ morphism (word parent) := by
      have : word (first - 1) ∈ (morphismPower morphism 2 [word parent]).toFinset := by
        simpa using hBeforeSecond
      rw [supportStable] at this
      simpa using this
    obtain ⟨offset, hOffsetAt⟩ := List.mem_iff_get.mp hBeforeFirst
    let offsetFin : Fin P :=
      ⟨offset, by simpa [uniform (word parent)] using offset.isLt⟩
    refine ⟨P * parent + offsetFin, ?_, ?_, ?_⟩
    · have hFirstQuotientNear : first / P <= sourceBefore + 1 := by
        have hFirstLower : P * (first / P) <= first := Nat.mul_div_le first P
        have hBeforeUpper : first - 1 < P * (sourceBefore + 1) := by
          dsimp [sourceBefore]
          simpa [Nat.mul_comm] using
            (Nat.div_lt_iff_lt_mul hP0).mp
              (Nat.lt_succ_self ((first - 1) / P))
        have hFirstCell : first <= P * (sourceBefore + 1) := by omega
        exact Nat.le_of_mul_le_mul_left (hFirstLower.trans hFirstCell) hP0
      have hParentCell : sourceBefore < P * (parent + 1) := by
        dsimp [parent]
        simpa [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (sourceBefore / P))
      rw [Nat.mul_add, Nat.mul_one] at hParentCell
      have hSourceSucc : sourceBefore + 1 <= P * parent + P := hParentCell
      have hFirstToParent : first / P <= P * parent + P :=
        hFirstQuotientNear.trans hSourceSucc
      have hBaseLower : first / P - P <= P * parent := by
        exact (Nat.sub_le_iff_le_add').mpr (by
          simpa [Nat.add_comm] using hFirstToParent)
      exact hBaseLower.trans (Nat.le_add_right _ _)
    · have hSourceBeforeUpper : sourceBefore <= first / P := by
        dsimp [sourceBefore]
        exact Nat.div_le_div_right (Nat.sub_le first 1)
      have hParentStart : P * parent <= sourceBefore := by
        dsimp [parent]
        exact Nat.mul_div_le sourceBefore P
      have hOffsetLt : (offsetFin : Nat) < P := offsetFin.isLt
      apply Nat.le_sub_one_of_lt
      calc
        P * parent + (offsetFin : Nat) < P * parent + P :=
          Nat.add_lt_add_left hOffsetLt _
        _ <= sourceBefore + P := Nat.add_le_add_right hParentStart P
        _ <= first / P + P := Nat.add_le_add_right hSourceBeforeUpper P
    · have hWitnessWord : word (P * parent + offsetFin) = word (first - 1) := by
        rw [source_cell]
        simpa [offsetFin] using hOffsetAt
      rw [hWitnessWord]
      exact hLeftOutside
  · let sourceAfter := (last + 1) / P
    let parent := sourceAfter / P
    let afterOffset : Fin P := ⟨(last + 1) % P, Nat.mod_lt _ hP0⟩
    have hAfterImage : word (last + 1) ∈ morphism (word sourceAfter) := by
      have hCoord : last + 1 = P * sourceAfter + afterOffset := by
        dsimp [sourceAfter, afterOffset]
        exact (Nat.div_add_mod (last + 1) P).symm
      rw [hCoord]
      exact source_mem_image sourceAfter afterOffset
    let sourceOffset : Fin P := ⟨sourceAfter % P, Nat.mod_lt _ hP0⟩
    have hSourceImage : word sourceAfter ∈ morphism (word parent) := by
      have hCoord : sourceAfter = P * parent + sourceOffset := by
        dsimp [parent, sourceOffset]
        exact (Nat.div_add_mod sourceAfter P).symm
      rw [hCoord]
      exact source_mem_image parent sourceOffset
    have hAfterSecond : word (last + 1) ∈ morphismPower morphism 2 [word parent] := by
      simpa [morphismPower] using
        (show ∃ a ∈ morphism (word parent), word (last + 1) ∈ morphism a from
          ⟨word sourceAfter, hSourceImage, hAfterImage⟩)
    have hAfterFirst : word (last + 1) ∈ morphism (word parent) := by
      have : word (last + 1) ∈ (morphismPower morphism 2 [word parent]).toFinset := by
        simpa using hAfterSecond
      rw [supportStable] at this
      simpa using this
    obtain ⟨offset, hOffsetAt⟩ := List.mem_iff_get.mp hAfterFirst
    let offsetFin : Fin P :=
      ⟨offset, by simpa [uniform (word parent)] using offset.isLt⟩
    refine ⟨P * parent + offsetFin, ?_, ?_, ?_⟩
    · have hSourceAfterLower : last / P <= sourceAfter := by
        dsimp [sourceAfter]
        exact Nat.div_le_div_right (Nat.le_add_right last 1)
      have hParentStart : P * parent <= sourceAfter := by
        dsimp [parent]
        exact Nat.mul_div_le sourceAfter P
      have hParentCell : sourceAfter < P * (parent + 1) := by
        dsimp [parent]
        simpa [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (sourceAfter / P))
      rw [Nat.mul_add, Nat.mul_one] at hParentCell
      have hPSourceLast : P <= last / P := by
        exact (Nat.le_add_left P (first / P)).trans
          (hCentral.trans (Nat.sub_le (last / P) P))
      have hSourceLastToParent : last / P < P * parent + P :=
        hSourceAfterLower.trans_lt hParentCell
      have hBaseLower : last / P - P + 1 <= P * parent := by
        apply Nat.succ_le_iff.mpr
        exact (Nat.sub_lt_iff_lt_add' hPSourceLast).mpr (by
          simpa [Nat.add_comm] using hSourceLastToParent)
      exact hBaseLower.trans (Nat.le_add_right _ _)
    · have hSourceAfterUpper : sourceAfter <= last / P + 1 := by
        have hSourceStart : P * sourceAfter <= last + 1 := by
          dsimp [sourceAfter]
          exact Nat.mul_div_le (last + 1) P
        have hLastUpper : last < P * (last / P + 1) := by
          simpa [Nat.mul_comm] using
            (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (last / P))
        have hSourceMul : P * sourceAfter <= P * (last / P + 1) :=
          hSourceStart.trans (Nat.succ_le_iff.mpr hLastUpper)
        exact Nat.le_of_mul_le_mul_left hSourceMul hP0
      have hParentStart : P * parent <= sourceAfter := by
        dsimp [parent]
        exact Nat.mul_div_le sourceAfter P
      have hOffsetLt : (offsetFin : Nat) < P := offsetFin.isLt
      have hWitnessLt : P * parent + (offsetFin : Nat) < (last / P + P) + 1 := by
        calc
          P * parent + (offsetFin : Nat) < P * parent + P :=
            Nat.add_lt_add_left hOffsetLt _
          _ <= sourceAfter + P := Nat.add_le_add_right hParentStart P
          _ <= (last / P + 1) + P := Nat.add_le_add_right hSourceAfterUpper P
          _ = (last / P + P) + 1 := by omega
      exact Nat.lt_succ_iff.mp hWitnessLt
    · have hWitnessWord : word (P * parent + offsetFin) = word (last + 1) := by
        rw [source_cell]
        simpa [offsetFin] using hOffsetAt
      rw [hWitnessWord]
      exact hRight

/-- The uniform specialization of BKS Lemma 12, including the maximalization
used in Corollary 13.

The image of the central trim is still a `Delta`-block.  The two complementary
letters immediately outside the original block are transported, using stable
two-step support, into the images of the bounded edge contexts.  Those two
witnesses make the maximal successor containing the central image finite and
unique.  The one-cell-wider edge bounds agree with the conservative windows in
`uniform_bks11_predecessor`. -/
theorem uniform_bks12_successor
    {Alphabet : Type*} [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (uniform : forall a, (morphism a).length = P) (word : Nat -> Alphabet)
    (fixed : forall (i : Nat) (offset : Fin P),
      word (P * i + offset) = uniformLetter morphism uniform (word i) offset)
    (supportStable : forall a,
      (morphismPower morphism 2 [a]).toFinset = (morphism a).toFinset)
    (Delta : Finset Alphabet) (first last : Nat)
    (block : IsMaximalDeltaInterval Delta word first last)
    (late : P < first) (long : P ^ 2 < last + 1 - first) :
    let centralFirst := P * (first + P)
    let centralLast := P * (last - P + 1) - 1
    (forall n, centralFirst <= n -> n <= centralLast -> word n ∈ Delta) /\
      (exists n, P * (first - P) <= n /\ n < centralFirst /\ word n ∉ Delta) /\
      (exists n, centralLast < n /\ n < P * (last + P + 1) /\ word n ∉ Delta) /\
      ∃! endpoints : Nat × Nat,
        IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
          P * (first - P) < endpoints.1 /\ endpoints.1 <= centralFirst /\
          centralLast <= endpoints.2 /\ endpoints.2 < P * (last + P + 1) := by
  dsimp
  rcases block with ⟨hFirstLast, hInside, hLeft, hRight⟩
  have hP0 : 0 < P := by omega
  have hCentralSource : first + P <= last - P := by
    have hTwoP : 2 * P <= P ^ 2 := by nlinarith
    have hLength : 2 * P < last + 1 - first := hTwoP.trans_lt long
    omega
  have hPLast : P <= last := by omega
  have hCentralCoords :
      P * (first + P) <= P * (last - P + 1) - 1 := by
    have hmul : P * (first + P) < P * (last - P + 1) := by
      apply Nat.mul_lt_mul_of_pos_left _ hP0
      omega
    omega
  have source_cell (source : Nat) (offset : Fin P) :
      word (P * source + offset) = (morphism (word source)).get
        ⟨offset, by rw [uniform (word source)]; exact offset.isLt⟩ := by
    simpa [uniformLetter] using fixed source offset
  have source_mem_image (source : Nat) (offset : Fin P) :
      word (P * source + offset) ∈ morphism (word source) := by
    rw [source_cell]
    exact List.get_mem _ _
  have centralCell (source : Nat) (hSourceLeft : first + P <= source)
      (hSourceRight : source <= last - P) (offset : Fin P) :
      word (P * source + offset) ∈ Delta := by
    let parent := source / P
    let sourceOffset : Fin P := ⟨source % P, Nat.mod_lt source hP0⟩
    have hSourceImage : word source ∈ morphism (word parent) := by
      have hCoord : source = P * parent + sourceOffset := by
        dsimp [parent, sourceOffset]
        exact (Nat.div_add_mod source P).symm
      rw [hCoord]
      exact source_mem_image parent sourceOffset
    have hLetterImage : word (P * source + offset) ∈ morphism (word source) :=
      source_mem_image source offset
    have hSecond : word (P * source + offset) ∈
        morphismPower morphism 2 [word parent] := by
      simpa [morphismPower] using
        (show ∃ a ∈ morphism (word parent),
            word (P * source + offset) ∈ morphism a from
          ⟨word source, hSourceImage, hLetterImage⟩)
    have hFirst : word (P * source + offset) ∈ morphism (word parent) := by
      have hmem : word (P * source + offset) ∈
          (morphismPower morphism 2 [word parent]).toFinset := by
        simpa using hSecond
      rw [supportStable] at hmem
      simpa using hmem
    obtain ⟨witnessOffset, hWitnessAt⟩ := List.mem_iff_get.mp hFirst
    let witnessFin : Fin P :=
      ⟨witnessOffset, by simpa [uniform (word parent)] using witnessOffset.isLt⟩
    have hParentStart : P * parent <= source := by
      dsimp [parent]
      exact Nat.mul_div_le source P
    have hParentEnd : source < P * (parent + 1) := by
      dsimp [parent]
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self (source / P))
    have hWitnessLower : first <= P * parent + witnessFin := by
      have hStart : first < P * parent := by
        rw [Nat.mul_add, Nat.mul_one] at hParentEnd
        omega
      exact hStart.le.trans (Nat.le_add_right _ _)
    have hWitnessUpper : P * parent + witnessFin <= last := by
      have hOffsetLt : (witnessFin : Nat) < P := witnessFin.isLt
      omega
    have hWitnessWord :
        word (P * parent + witnessFin) = word (P * source + offset) := by
      rw [source_cell]
      simpa [witnessFin] using hWitnessAt
    rw [← hWitnessWord]
    exact hInside _ hWitnessLower hWitnessUpper
  have hCentral : forall n,
      P * (first + P) <= n -> n <= P * (last - P + 1) - 1 ->
        word n ∈ Delta := by
    intro n hnLeft hnRight
    let source := n / P
    let offset : Fin P := ⟨n % P, Nat.mod_lt n hP0⟩
    have hCoord : n = P * source + offset := by
      dsimp [source, offset]
      exact (Nat.div_add_mod n P).symm
    have hSourceLeft : first + P <= source := by
      have hmul : P * (first + P) < P * (source + 1) := by
        calc
          P * (first + P) <= n := hnLeft
          _ = P * source + offset := hCoord
          _ < P * source + P := Nat.add_lt_add_left offset.isLt _
          _ = P * (source + 1) := by rw [Nat.mul_add, Nat.mul_one]
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hmul)
    have hSourceRight : source <= last - P := by
      have hSourceStart : P * source <= n := by rw [hCoord]; omega
      have hTargetPos : 0 < P * (last - P + 1) :=
        Nat.mul_pos hP0 (Nat.succ_pos _)
      have hnStrict : n < P * (last - P + 1) := by omega
      have : P * source < P * (last - P + 1) := hSourceStart.trans_lt hnStrict
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left this)
    rw [hCoord]
    exact centralCell source hSourceLeft hSourceRight offset
  have edgeWitness (boundary : Nat) (hBoundaryPos : 0 < boundary)
      (outside : word (boundary - 1) ∉ Delta) :
      ∃ source : Nat, ∃ offset : Fin P,
        boundary - P <= source /\ source < boundary - 1 + P /\
          word (P * source + offset) = word (boundary - 1) := by
    let parent := (boundary - 1) / P
    let boundaryOffset : Fin P :=
      ⟨(boundary - 1) % P, Nat.mod_lt (boundary - 1) hP0⟩
    have hBoundaryImage : word (boundary - 1) ∈ morphism (word parent) := by
      have hCoord : boundary - 1 = P * parent + boundaryOffset := by
        dsimp [parent, boundaryOffset]
        exact (Nat.div_add_mod (boundary - 1) P).symm
      rw [hCoord]
      exact source_mem_image parent boundaryOffset
    have hSecond : word (boundary - 1) ∈ morphismPower morphism 2 [word parent] := by
      have hmem : word (boundary - 1) ∈ (morphism (word parent)).toFinset := by
        simpa using hBoundaryImage
      rw [← supportStable] at hmem
      simpa using hmem
    obtain ⟨middle, hMiddle, hBoundaryMiddle⟩ :
        ∃ middle ∈ morphism (word parent),
          word (boundary - 1) ∈ morphism middle := by
      simpa [morphismPower] using hSecond
    obtain ⟨middleOffset, hMiddleAt⟩ := List.mem_iff_get.mp hMiddle
    obtain ⟨finalOffset, hFinalAt⟩ := List.mem_iff_get.mp hBoundaryMiddle
    let middleFin : Fin P :=
      ⟨middleOffset, by simpa [uniform (word parent)] using middleOffset.isLt⟩
    let finalFin : Fin P :=
      ⟨finalOffset, by simpa [uniform middle] using finalOffset.isLt⟩
    let source := P * parent + middleFin
    have hParentStart : P * parent <= boundary - 1 := by
      dsimp [parent]
      exact Nat.mul_div_le (boundary - 1) P
    have hParentEnd : boundary - 1 < P * (parent + 1) := by
      dsimp [parent]
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hP0).mp (Nat.lt_succ_self ((boundary - 1) / P))
    have hSourceLower : boundary - P <= source := by
      dsimp [source]
      rw [Nat.mul_add, Nat.mul_one] at hParentEnd
      omega
    have hSourceUpper : source < boundary - 1 + P := by
      have hMiddleLt : (middleFin : Nat) < P := middleFin.isLt
      dsimp [source]
      have hParentLower : P * parent <= boundary - 1 := hParentStart
      omega
    refine ⟨source, finalFin, hSourceLower, hSourceUpper, ?_⟩
    have hMiddleWord : word source = middle := by
      dsimp [source]
      rw [source_cell]
      simpa [middleFin] using hMiddleAt
    rw [source_cell, hMiddleWord]
    simpa [finalFin] using hFinalAt
  have hFirstPos : 0 < first := by omega
  have hLeftOutside : word (first - 1) ∉ Delta := hLeft.resolve_left hFirstPos.ne'
  obtain ⟨leftSource, leftOffset, hLeftSourceLower, hLeftSourceUpper,
      hLeftWord⟩ := edgeWitness first hFirstPos hLeftOutside
  let leftWitness := P * leftSource + leftOffset
  have hLeftWitness :
      P * (first - P) <= leftWitness /\
        leftWitness < P * (first + P) /\ word leftWitness ∉ Delta := by
    have hOffsetLt : (leftOffset : Nat) < P := leftOffset.isLt
    refine ⟨?_, ?_, ?_⟩
    · exact (Nat.mul_le_mul_left P hLeftSourceLower).trans (Nat.le_add_right _ _)
    · have : leftSource + 1 <= first + P := by omega
      calc
        leftWitness < P * leftSource + P := Nat.add_lt_add_left hOffsetLt _
        _ = P * (leftSource + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ <= P * (first + P) := Nat.mul_le_mul_left P this
    · rw [hLeftWord]
      exact hLeftOutside
  obtain ⟨rightSource, rightOffset, hRightSourceLower, hRightSourceUpper,
      hRightWord⟩ := edgeWitness (last + 2) (by omega) (by simpa using hRight)
  let rightWitness := P * rightSource + rightOffset
  have hRightWitness :
      P * (last - P + 1) <= rightWitness /\
        rightWitness < P * (last + P + 1) /\ word rightWitness ∉ Delta := by
    have hOffsetLt : (rightOffset : Nat) < P := rightOffset.isLt
    refine ⟨?_, ?_, ?_⟩
    · have hSourceLower : last - P + 1 <= rightSource := by omega
      have hmul := Nat.mul_le_mul_left P hSourceLower
      dsimp [rightWitness]
      omega
    · have : rightSource + 1 <= last + P + 1 := by omega
      calc
        rightWitness < P * rightSource + P := Nat.add_lt_add_left hOffsetLt _
        _ = P * (rightSource + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ <= P * (last + P + 1) := Nat.mul_le_mul_left P this
    · rw [hRightWord]
      simpa using hRight
  have hRightCentralPos : 0 < P * (last - P + 1) :=
    Nat.mul_pos hP0 (Nat.succ_pos _)
  have hRightCentralBefore : P * (last - P + 1) - 1 < rightWitness :=
    (Nat.sub_lt hRightCentralPos Nat.zero_lt_one).trans_le hRightWitness.1
  refine ⟨hCentral, ⟨leftWitness, hLeftWitness⟩,
    ⟨rightWitness, hRightCentralBefore, hRightWitness.2⟩, ?_⟩
  let leftSet := (Finset.range (P * (first + P))).filter fun n => word n ∉ Delta
  have hLeftSet : leftSet.Nonempty := by
    refine ⟨leftWitness, ?_⟩
    simp [leftSet, hLeftWitness.2.1, hLeftWitness.2.2]
  let leftBoundary := leftSet.max' hLeftSet
  let rightSet := (Finset.Icc (P * (last - P + 1))
      (P * (last + P + 1))).filter fun n => word n ∉ Delta
  have hRightSet : rightSet.Nonempty := by
    refine ⟨rightWitness, ?_⟩
    simp [rightSet, hRightWitness.1, hRightWitness.2.1.le,
      hRightWitness.2.2]
  let rightBoundary := rightSet.min' hRightSet
  let successor : Nat × Nat := (leftBoundary + 1, rightBoundary - 1)
  have hLeftBoundaryMem : leftBoundary ∈ leftSet := Finset.max'_mem _ _
  have hRightBoundaryMem : rightBoundary ∈ rightSet := Finset.min'_mem _ _
  have hLeftBoundary : leftBoundary < P * (first + P) /\
      word leftBoundary ∉ Delta := by
    simpa [leftSet] using (Finset.mem_filter.mp hLeftBoundaryMem)
  have hRightBoundary : P * (last - P + 1) <= rightBoundary /\
      rightBoundary <= P * (last + P + 1) /\ word rightBoundary ∉ Delta := by
    rcases Finset.mem_filter.mp hRightBoundaryMem with ⟨hmem, hout⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hlower, hupper⟩
    exact ⟨hlower, hupper, hout⟩
  have hSuccessor : IsMaximalDeltaInterval Delta word successor.1 successor.2 := by
    have hEndpoints : successor.1 <= successor.2 := by
      dsimp [successor]
      omega
    refine ⟨hEndpoints, ?_, ?_, ?_⟩
    · intro n hnLeft hnRight
      by_cases hnCentralLeft : n < P * (first + P)
      · by_contra hnDelta
        have hnMem : n ∈ leftSet := by simp [leftSet, hnCentralLeft, hnDelta]
        have hnLe : n <= leftBoundary := Finset.le_max' _ _ hnMem
        dsimp [successor] at hnLeft
        omega
      · by_cases hnCentralRight : n <= P * (last - P + 1) - 1
        · exact hCentral n (by omega) hnCentralRight
        · by_contra hnDelta
          have hnMem : n ∈ rightSet := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hnDelta⟩
            · omega
            · dsimp [successor] at hnRight
              omega
          have hBoundaryLe : rightBoundary <= n := Finset.min'_le _ _ hnMem
          dsimp [successor] at hnRight
          omega
    · right
      dsimp [successor]
      simpa using hLeftBoundary.2
    · dsimp [successor]
      have hRightPositive : 0 < rightBoundary := by omega
      rw [Nat.sub_add_cancel hRightPositive]
      exact hRightBoundary.2.2
  have hSuccessorBounds :
      P * (first - P) < successor.1 /\
        successor.1 <= P * (first + P) /\
        P * (last - P + 1) - 1 <= successor.2 /\
        successor.2 < P * (last + P + 1) := by
    have hLeftLe : leftWitness <= leftBoundary := by
      apply Finset.le_max'
      simpa [leftSet, hLeftWitness.2.1, hLeftWitness.2.2]
    have hRightLe : rightBoundary <= rightWitness := by
      apply Finset.min'_le
      simpa [rightSet, hRightWitness.1, hRightWitness.2.1.le,
        hRightWitness.2.2]
    dsimp [successor]
    omega
  refine ⟨successor, ⟨hSuccessor, hSuccessorBounds⟩, ?_⟩
  intro other hOther
  rcases hOther with ⟨otherBlock, hOtherLower, hOtherFirst,
    hOtherLast, hOtherUpper⟩
  rcases otherBlock with ⟨hOtherOrder, hOtherInside, hOtherLeft, hOtherRight⟩
  rcases hSuccessor with ⟨hSuccessorOrder, hSuccessorInside,
    hSuccessorLeft, hSuccessorRight⟩
  apply Prod.ext
  · apply le_antisymm
    · by_contra hlt
      have hOrder : successor.1 < other.1 := Nat.lt_of_not_ge hlt
      have hPredInside : word (other.1 - 1) ∈ Delta := by
        apply hSuccessorInside
        · omega
        · omega
      have hPredOutside : word (other.1 - 1) ∉ Delta := by
        exact hOtherLeft.resolve_left (by omega)
      exact hPredOutside hPredInside
    · by_contra hlt
      have hOrder : other.1 < successor.1 := Nat.lt_of_not_ge hlt
      have hPredInside : word (successor.1 - 1) ∈ Delta := by
        apply hOtherInside
        · omega
        · omega
      have hPredOutside : word (successor.1 - 1) ∉ Delta := by
        exact hSuccessorLeft.resolve_left (by
          dsimp [successor]
          omega)
      exact hPredOutside hPredInside
  · apply le_antisymm
    · by_contra hlt
      have hOrder : successor.2 < other.2 := Nat.lt_of_not_ge hlt
      have hNextInside : word (successor.2 + 1) ∈ Delta := by
        apply hOtherInside
        · omega
        · omega
      exact hSuccessorRight hNextInside
    · by_contra hlt
      have hOrder : other.2 < successor.2 := Nat.lt_of_not_ge hlt
      have hNextInside : word (other.2 + 1) ∈ Delta := by
        apply hSuccessorInside
        · omega
        · omega
      exact hOtherRight hNextInside

end Raney
end TrureTuring
