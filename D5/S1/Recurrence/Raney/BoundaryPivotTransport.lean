/- GID: D5/S1/Recurrence/Raney/BoundaryPivotTransport
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/BoundaryPivotTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport actual BKS boundary pivots through stabilized uniform morphism images. -/

import D5.S1.Recurrence.Raney.MaximalBlockDescent

namespace TrureTuring
namespace Raney

/-- A letter image meets the complement of `Delta`. -/
def imageMeetsComplement {Alphabet : Type*} [DecidableEq Alphabet] {Q : Nat}
    (g : Alphabet -> List Alphabet) (gUniform : forall a, (g a).length = Q)
    (Delta : Finset Alphabet) (a : Alphabet) : Prop :=
  exists offset : Fin Q, uniformLetter g gUniform a offset ∉ Delta

/-- At a fixed support-stabilizing power, two consecutive literal BKS steps
transport each boundary pivot inside the `g`-image of the preceding pivot.  The
left choices are rightmost and the right choices are leftmost.  The returned
next-exit extremality is read from the outer step itself, so no third edge is
needed.  Consequently both signed endpoint displacements are functions of
three finite offsets and two letters. -/
theorem actual_boundary_pivot_transport_at_power
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (word : Nat -> Alphabet) (q : Nat) (hq : 0 < q)
    (gUniform : forall a, (morphismPower morphism q [a]).length = P ^ q)
    (gFixed : forall (i : Nat) (offset : Fin (P ^ q)),
      word (P ^ q * i + offset) = uniformLetter
        (fun a => morphismPower morphism q [a]) gUniform (word i) offset)
    (gSupport : forall a,
      (morphismPower (fun b => morphismPower morphism q [b]) 2 [a]).toFinset =
        (morphismPower morphism q [a]).toFinset) :
      let Q := P ^ q
      let g : Alphabet -> List Alphabet := fun a => morphismPower morphism q [a]
      forall (Delta : Finset Alphabet) (grandparent parent child : Nat × Nat),
        IsBksDescentStep Q Delta word grandparent parent ->
        IsBksDescentStep Q Delta word parent child ->
        (exists pivot nextPivot : Nat, exists exitOffset entryOffset nextExitOffset : Fin Q,
          parent.1 = Q * pivot + exitOffset + 1 /\
          grandparent.1 = Q * nextPivot + nextExitOffset + 1 /\
          uniformLetter g gUniform (word pivot) exitOffset ∉ Delta /\
          (forall offset : Fin Q, exitOffset < offset ->
            uniformLetter g gUniform (word pivot) offset ∈ Delta) /\
          nextPivot = Q * pivot + entryOffset /\
          word nextPivot = uniformLetter g gUniform (word pivot) entryOffset /\
          imageMeetsComplement g gUniform Delta (word nextPivot) /\
          (forall offset : Fin Q, entryOffset < offset ->
            ¬ imageMeetsComplement g gUniform Delta
              (uniformLetter g gUniform (word pivot) offset)) /\
          uniformLetter g gUniform (word nextPivot) nextExitOffset ∉ Delta /\
          (forall offset : Fin Q, nextExitOffset < offset ->
            uniformLetter g gUniform (word nextPivot) offset ∈ Delta) /\
          (grandparent.1 : Int) - Q * (parent.1 : Int) =
            Q * (entryOffset : Int) + nextExitOffset + 1 -
              Q * ((exitOffset : Int) + 1)) /\
        (exists pivot nextPivot : Nat, exists exitOffset entryOffset nextExitOffset : Fin Q,
          parent.2 + 1 = Q * pivot + exitOffset /\
          grandparent.2 + 1 = Q * nextPivot + nextExitOffset /\
          uniformLetter g gUniform (word pivot) exitOffset ∉ Delta /\
          (forall offset : Fin Q, offset < exitOffset ->
            uniformLetter g gUniform (word pivot) offset ∈ Delta) /\
          nextPivot = Q * pivot + entryOffset /\
          word nextPivot = uniformLetter g gUniform (word pivot) entryOffset /\
          imageMeetsComplement g gUniform Delta (word nextPivot) /\
          (forall offset : Fin Q, offset < entryOffset ->
            ¬ imageMeetsComplement g gUniform Delta
              (uniformLetter g gUniform (word pivot) offset)) /\
          uniformLetter g gUniform (word nextPivot) nextExitOffset ∉ Delta /\
          (forall offset : Fin Q, offset < nextExitOffset ->
            uniformLetter g gUniform (word nextPivot) offset ∈ Delta) /\
          ((grandparent.2 + 1 : Nat) : Int) - Q * ((parent.2 + 1 : Nat) : Int) =
            Q * (entryOffset : Int) + nextExitOffset - Q * (exitOffset : Int)) := by
  dsimp only
  intro Delta grandparent parent child grandStep parentStep
  let Q := P ^ q
  let g : Alphabet -> List Alphabet := fun a => morphismPower morphism q [a]
  have hQ : 1 < Q := by
    dsimp [Q]
    exact one_lt_pow' hP hq.ne'
  have hQ0 : 0 < Q := by omega
  have grandStepData := grandStep
  have parentStepData := parentStep
  dsimp [IsBksDescentStep] at grandStepData parentStepData
  rcases grandStepData with ⟨grandBlock, parentBlock', _, _, _, _, parentLate,
    parentLong, _, grandLower, grandUpper, grandFirstCentral, grandCentralOrder,
    grandLastCentral, _, _, _⟩
  rcases parentStepData with ⟨parentBlock, childBlock, _, _, _, _, childLate,
    childLong, _, parentLower, parentUpper, parentFirstCentral, parentCentralOrder,
    parentLastCentral, _, _, _⟩
  have parentBlocks : parentBlock' = parentBlock := Subsingleton.elim _ _
  subst parentBlock'
  have fixedCell (source : Nat) (offset : Fin Q) :
      word (Q * source + offset) = uniformLetter g gUniform (word source) offset := by
    simpa [Q, g] using gFixed source offset
  have supportSubset (a b : Alphabet) (hb : b ∈ g a) :
      (g b).toFinset ⊆ (g a).toFinset := by
    intro x hx
    have hx2 : x ∈ (morphismPower g 2 [a]).toFinset := by
      simpa [morphismPower] using (show ∃ c ∈ g a, x ∈ g c from ⟨b, hb, by simpa using hx⟩)
    rw [gSupport] at hx2
    exact hx2
  have supportMeeting (a : Alphabet) (exitOffset : Fin Q)
      (outside : uniformLetter g gUniform a exitOffset ∉ Delta) :
      exists entry : Fin Q,
        imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a entry) := by
    let x := uniformLetter g gUniform a exitOffset
    have hx : x ∈ g a := by
      dsimp [x, uniformLetter]
      exact List.get_mem _ _
    have hx2 : x ∈ morphismPower g 2 [a] := by
      have hxFin : x ∈ (morphismPower g 2 [a]).toFinset := by
        rw [gSupport]
        simpa using hx
      simpa using hxFin
    obtain ⟨b, hb, hxb⟩ : ∃ b, b ∈ g a ∧ x ∈ g b := by
      simpa [morphismPower] using hx2
    obtain ⟨entryIndex, hEntry⟩ := List.mem_iff_get.mp hb
    obtain ⟨witnessIndex, hWitness⟩ := List.mem_iff_get.mp hxb
    let entry : Fin Q :=
      ⟨entryIndex, by
        change (entryIndex : Nat) < P ^ q
        rw [← gUniform a]
        exact entryIndex.isLt⟩
    let witness : Fin Q :=
      ⟨witnessIndex, by
        change (witnessIndex : Nat) < P ^ q
        rw [← gUniform b]
        exact witnessIndex.isLt⟩
    refine ⟨entry, witness, ?_⟩
    have hEntry' : uniformLetter g gUniform a entry = b := by
      simpa [uniformLetter, entry] using hEntry
    have hWitness' : uniformLetter g gUniform b witness = x := by
      simpa [uniformLetter, witness] using hWitness
    rw [hEntry', hWitness']
    exact outside
  have imageInsideParentCell (source : Nat)
      (cellLower : parent.1 <= Q * source)
      (cellUpper : Q * (source + 1) - 1 <= parent.2)
      (b : Alphabet) (hb : b ∈ g (word source)) (offset : Fin Q) :
      uniformLetter g gUniform b offset ∈ Delta := by
    have hOffsetMem : uniformLetter g gUniform b offset ∈ (g b).toFinset := by
      simp [uniformLetter]
    have hSourceFin := supportSubset (word source) b hb hOffsetMem
    have hSourceMem : uniformLetter g gUniform b offset ∈ g (word source) := by
      simpa using hSourceFin
    obtain ⟨sourceIndex, hSourceAt⟩ := List.mem_iff_get.mp hSourceMem
    let sourceOffset : Fin Q :=
      ⟨sourceIndex, by
        change (sourceIndex : Nat) < P ^ q
        rw [← gUniform (word source)]
        exact sourceIndex.isLt⟩
    have hPosition : word (Q * source + sourceOffset) ∈ Delta := by
      apply parentBlock.2.1
      · exact cellLower.trans (Nat.le_add_right _ _)
      · have : Q * source + (sourceOffset : Nat) < Q * (source + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.add_lt_add_left sourceOffset.isLt _
        omega
    rw [fixedCell source sourceOffset] at hPosition
    have hSourceAt' :
        uniformLetter g gUniform (word source) sourceOffset =
          uniformLetter g gUniform b offset := by
      simpa [uniformLetter, sourceOffset] using hSourceAt
    rwa [hSourceAt'] at hPosition
  have leftData (outer inner : Nat × Nat)
      (step : IsBksDescentStep Q Delta word outer inner) :
      exists pivot : Nat, exists exitOffset : Fin Q,
        outer.1 = Q * pivot + exitOffset + 1 /\
        uniformLetter g gUniform (word pivot) exitOffset ∉ Delta /\
        (forall offset : Fin Q, exitOffset < offset ->
          uniformLetter g gUniform (word pivot) offset ∈ Delta) /\
        inner.1 - Q <= pivot /\ pivot < inner.1 + Q := by
    dsimp [IsBksDescentStep] at step
    rcases step with ⟨outerBlock, _, _, _, _, _, innerLate, _, _, outerLower, _,
      outerFirstCentral, outerCentralOrder, outerLastCentral, _, _, _⟩
    have outerFirstPos : 0 < outer.1 := by
      have : 0 < Q * (inner.1 - Q) := Nat.mul_pos hQ0 (Nat.sub_pos_of_lt innerLate)
      omega
    let pivot := (outer.1 - 1) / Q
    let exitOffset : Fin Q := ⟨(outer.1 - 1) % Q, Nat.mod_lt _ hQ0⟩
    have boundaryEq : outer.1 = Q * pivot + exitOffset + 1 := by
      dsimp [pivot, exitOffset]
      have := Nat.div_add_mod (outer.1 - 1) Q
      omega
    have pivotUpper : pivot < inner.1 + Q := by
      dsimp [pivot]
      apply (Nat.div_lt_iff_lt_mul hQ0).mpr
      calc
        outer.1 - 1 < outer.1 := Nat.sub_lt outerFirstPos Nat.zero_lt_one
        _ <= Q * (inner.1 + Q) := outerFirstCentral
        _ = (inner.1 + Q) * Q := Nat.mul_comm _ _
    refine ⟨pivot, exitOffset, boundaryEq, ?_, ?_, ?_, ?_⟩
    · rw [← fixedCell]
      simpa [boundaryEq] using outerBlock.2.2.1.resolve_left outerFirstPos.ne'
    · intro offset hoffset
      rw [← fixedCell]
      apply outerBlock.2.1
      · simpa [boundaryEq] using Nat.add_le_add_left (Nat.succ_le_iff.mpr hoffset) (Q * pivot)
      · exact (show Q * pivot + offset < Q * (pivot + 1) by
          rw [Nat.mul_add, Nat.mul_one]; omega).le.trans
          ((Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr pivotUpper)).trans
            (outerCentralOrder.trans outerLastCentral))
    · dsimp [pivot]
      have hmul : Q * (inner.1 - Q) <= outer.1 - 1 := by omega
      exact (Nat.le_div_iff_mul_le hQ0).mpr (by simpa [Nat.mul_comm] using hmul)
    · exact pivotUpper
  have rightData (outer inner : Nat × Nat)
      (step : IsBksDescentStep Q Delta word outer inner) :
      exists pivot : Nat, exists exitOffset : Fin Q,
        outer.2 + 1 = Q * pivot + exitOffset /\
        uniformLetter g gUniform (word pivot) exitOffset ∉ Delta /\
        (forall offset : Fin Q, offset < exitOffset ->
          uniformLetter g gUniform (word pivot) offset ∈ Delta) /\
        inner.2 - Q + 1 <= pivot /\ pivot <= inner.2 + Q + 1 := by
    dsimp [IsBksDescentStep] at step
    rcases step with ⟨outerBlock, _, _, _, _, _, _, _, _, _, outerUpper,
      outerFirstCentral, outerCentralOrder, outerLastCentral, _, _, _⟩
    let pivot := (outer.2 + 1) / Q
    let exitOffset : Fin Q := ⟨(outer.2 + 1) % Q, Nat.mod_lt _ hQ0⟩
    have boundaryEq : outer.2 + 1 = Q * pivot + exitOffset := by
      dsimp [pivot, exitOffset]
      simpa [Nat.mul_comm] using (Nat.div_add_mod (outer.2 + 1) Q).symm
    have pivotLower : inner.2 - Q + 1 <= pivot := by
      dsimp [pivot]
      apply (Nat.le_div_iff_mul_le hQ0).mpr
      have : Q * (inner.2 - Q + 1) <= outer.2 + 1 := by omega
      simpa [Nat.mul_comm] using this
    refine ⟨pivot, exitOffset, boundaryEq, ?_, ?_, ?_, ?_⟩
    · rw [← fixedCell]
      simpa [boundaryEq] using outerBlock.2.2.2
    · intro offset hoffset
      rw [← fixedCell]
      have hlt : Q * pivot + (offset : Nat) < outer.2 + 1 := by
        have := Nat.add_lt_add_left hoffset (Q * pivot)
        simpa [boundaryEq] using this
      have hle : Q * pivot + (offset : Nat) <= outer.2 := Nat.lt_succ_iff.mp hlt
      apply outerBlock.2.1
      · exact outerFirstCentral.trans (outerCentralOrder.trans (by
          have hcentral : Q * (inner.2 - Q + 1) <= Q * pivot :=
            Nat.mul_le_mul_left Q pivotLower
          omega))
      · exact hle
    · exact pivotLower
    · dsimp [pivot]
      apply Nat.div_le_of_le_mul
      omega
  obtain ⟨leftPivot, leftExit, leftBoundary, leftOutside, leftExitMax,
    leftWindowLower, leftWindowUpper⟩ := leftData parent child parentStep
  obtain ⟨leftNext, leftNextExit, leftNextBoundary, leftNextOutside,
    leftNextExitMax, leftNextWindowLower, leftNextWindowUpper⟩ :=
    leftData grandparent parent grandStep
  obtain ⟨rightPivot, rightExit, rightBoundary, rightOutside, rightExitMin,
    rightWindowLower, rightWindowUpper⟩ := rightData parent child parentStep
  obtain ⟨rightNext, rightNextExit, rightNextBoundary, rightNextOutside,
    rightNextExitMin, rightNextWindowLower, rightNextWindowUpper⟩ :=
    rightData grandparent parent grandStep
  have leftTransition : exists entry : Fin Q,
      leftNext = Q * leftPivot + entry /\
      word leftNext = uniformLetter g gUniform (word leftPivot) entry /\
      imageMeetsComplement g gUniform Delta (word leftNext) /\
      forall offset : Fin Q, entry < offset ->
        ¬ imageMeetsComplement g gUniform Delta
          (uniformLetter g gUniform (word leftPivot) offset) := by
    obtain ⟨candidateOffset, candidateMeets⟩ :=
      supportMeeting (word leftPivot) leftExit leftOutside
    let candidate := Q * leftPivot + (candidateOffset : Nat)
    have candidateLetter :
        word candidate = uniformLetter g gUniform (word leftPivot) candidateOffset := by
      simpa [candidate] using fixedCell leftPivot candidateOffset
    have candidateMeetsWord : imageMeetsComplement g gUniform Delta (word candidate) := by
      rw [candidateLetter]
      exact candidateMeets
    have candidateLe : candidate <= leftNext := by
      by_contra hnot
      have nextLt : leftNext < candidate := Nat.lt_of_not_ge hnot
      obtain ⟨witness, witnessOutside⟩ := candidateMeetsWord
      have occurrenceLower : grandparent.1 <= Q * candidate + (witness : Nat) := by
        calc
          grandparent.1 = Q * leftNext + (leftNextExit : Nat) + 1 := leftNextBoundary
          _ <= Q * (leftNext + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          _ <= Q * candidate :=
            Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr nextLt)
          _ <= Q * candidate + (witness : Nat) := Nat.le_add_right _ _
      have candidateUpper : candidate < parent.1 + Q := by
        dsimp [candidate]
        rw [leftBoundary]
        omega
      have occurrenceUpper :
          Q * candidate + (witness : Nat) < Q * (parent.1 + Q) := by
        calc
          Q * candidate + (witness : Nat) < Q * (candidate + 1) := by
            calc
              Q * candidate + (witness : Nat) < Q * candidate + Q :=
                Nat.add_lt_add_left witness.isLt _
              _ = Q * (candidate + 1) := by ring
          _ <= Q * (parent.1 + Q) :=
            Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr candidateUpper)
      have occurrenceInside : word (Q * candidate + (witness : Nat)) ∈ Delta := by
        apply grandBlock.2.1
        · exact occurrenceLower
        · exact occurrenceUpper.le.trans
            (grandCentralOrder.trans grandLastCentral)
      rw [fixedCell candidate witness] at occurrenceInside
      exact witnessOutside occurrenceInside
    have centralSourceOrder : child.1 + Q < child.2 - Q + 1 := by
      apply (Nat.mul_lt_mul_left hQ0).mp
      have rightPositive : 0 < Q * (child.2 - Q + 1) := by
        apply Nat.mul_pos hQ0
        omega
      exact parentCentralOrder.trans_lt
        (Nat.sub_lt rightPositive Nat.zero_lt_one)
    have leftCellLower : parent.1 <= Q * (leftPivot + 1) := by
      rw [leftBoundary, Nat.mul_add, Nat.mul_one]
      omega
    have leftCellUpper : Q * (leftPivot + 2) - 1 <= parent.2 := by
      have sourceUpper : leftPivot + 2 <= child.2 - Q + 1 := by
        omega
      exact (Nat.sub_le_sub_right (Nat.mul_le_mul_left Q sourceUpper) 1).trans
        parentLastCentral
    have nextUpper : leftNext < Q * (leftPivot + 1) := by
      by_contra hnot
      have nextLower : Q * (leftPivot + 1) <= leftNext := Nat.le_of_not_gt hnot
      have nextCellUpper : leftNext < Q * (leftPivot + 2) := by
        calc
          leftNext < parent.1 + Q := leftNextWindowUpper
          _ <= Q * (leftPivot + 1) + Q := Nat.add_le_add_right leftCellLower Q
          _ = Q * (leftPivot + 2) := by ring
      let nextOffset : Fin Q :=
        ⟨leftNext - Q * (leftPivot + 1), by
          apply (Nat.sub_lt_iff_lt_add nextLower).mpr
          calc
            leftNext < Q * (leftPivot + 2) := nextCellUpper
            _ = Q + Q * (leftPivot + 1) := by ring⟩
      have nextCoord : leftNext = Q * (leftPivot + 1) + (nextOffset : Nat) := by
        dsimp [nextOffset]
        omega
      have nextMem : word leftNext ∈ g (word (leftPivot + 1)) := by
        rw [nextCoord, fixedCell]
        dsimp [uniformLetter]
        exact List.get_mem _ _
      exact leftNextOutside
        (imageInsideParentCell (leftPivot + 1) leftCellLower leftCellUpper
          (word leftNext) nextMem leftNextExit)
    have nextLower : Q * leftPivot <= leftNext := by
      exact (Nat.le_add_right _ _).trans candidateLe
    let entry : Fin Q :=
      ⟨leftNext - Q * leftPivot, by
        apply (Nat.sub_lt_iff_lt_add nextLower).mpr
        calc
          leftNext < Q * (leftPivot + 1) := nextUpper
          _ = Q + Q * leftPivot := by ring⟩
    have transport : leftNext = Q * leftPivot + (entry : Nat) := by
      dsimp [entry]
      omega
    refine ⟨entry, transport, ?_, ⟨leftNextExit, leftNextOutside⟩, ?_⟩
    · rw [transport, fixedCell]
    · intro offset hEntryOffset offsetMeets
      let later := Q * leftPivot + (offset : Nat)
      have nextLtLater : leftNext < later := by
        dsimp [later]
        rw [transport]
        omega
      have laterLetter :
          word later = uniformLetter g gUniform (word leftPivot) offset := by
        simpa [later] using fixedCell leftPivot offset
      have laterMeetsWord : imageMeetsComplement g gUniform Delta (word later) := by
        rw [laterLetter]
        exact offsetMeets
      obtain ⟨witness, witnessOutside⟩ := laterMeetsWord
      have occurrenceLower : grandparent.1 <= Q * later + (witness : Nat) := by
        calc
          grandparent.1 = Q * leftNext + (leftNextExit : Nat) + 1 := leftNextBoundary
          _ <= Q * (leftNext + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          _ <= Q * later :=
            Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr nextLtLater)
          _ <= Q * later + (witness : Nat) := Nat.le_add_right _ _
      have laterUpper : later < parent.1 + Q := by
        dsimp [later]
        rw [leftBoundary]
        omega
      have occurrenceUpper : Q * later + (witness : Nat) < Q * (parent.1 + Q) := by
        calc
          Q * later + (witness : Nat) < Q * (later + 1) := by
            calc
              Q * later + (witness : Nat) < Q * later + Q :=
                Nat.add_lt_add_left witness.isLt _
              _ = Q * (later + 1) := by ring
          _ <= Q * (parent.1 + Q) :=
            Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr laterUpper)
      have occurrenceInside : word (Q * later + (witness : Nat)) ∈ Delta := by
        apply grandBlock.2.1
        · exact occurrenceLower
        · exact occurrenceUpper.le.trans
            (grandCentralOrder.trans grandLastCentral)
      rw [fixedCell later witness] at occurrenceInside
      exact witnessOutside occurrenceInside
  have rightTransition : exists entry : Fin Q,
      rightNext = Q * rightPivot + entry /\
      word rightNext = uniformLetter g gUniform (word rightPivot) entry /\
      imageMeetsComplement g gUniform Delta (word rightNext) /\
      forall offset : Fin Q, offset < entry ->
        ¬ imageMeetsComplement g gUniform Delta
          (uniformLetter g gUniform (word rightPivot) offset) := by
    obtain ⟨candidateOffset, candidateMeets⟩ :=
      supportMeeting (word rightPivot) rightExit rightOutside
    let candidate := Q * rightPivot + (candidateOffset : Nat)
    have candidateLetter :
        word candidate = uniformLetter g gUniform (word rightPivot) candidateOffset := by
      simpa [candidate] using fixedCell rightPivot candidateOffset
    have candidateMeetsWord : imageMeetsComplement g gUniform Delta (word candidate) := by
      rw [candidateLetter]
      exact candidateMeets
    have centralSourceOrder : child.1 + Q < child.2 - Q + 1 := by
      apply (Nat.mul_lt_mul_left hQ0).mp
      have rightPositive : 0 < Q * (child.2 - Q + 1) := by
        apply Nat.mul_pos hQ0
        omega
      exact parentCentralOrder.trans_lt
        (Nat.sub_lt rightPositive Nat.zero_lt_one)
    have rightPivotPos : 0 < rightPivot := by
      omega
    have pivotBaseLower : parent.2 - Q + 1 <= Q * rightPivot := by
      have endpointUpper : parent.2 < Q * rightPivot + Q := by
        have boundary := rightBoundary
        omega
      omega
    have nextLeCandidate : rightNext <= candidate := by
      by_contra hnot
      have candidateLt : candidate < rightNext := Nat.lt_of_not_ge hnot
      obtain ⟨witness, witnessOutside⟩ := candidateMeetsWord
      have occurrenceLower :
          Q * (parent.2 - Q + 1) - 1 < Q * candidate + (witness : Nat) := by
        have sourceLower : parent.2 - Q + 1 <= candidate :=
          pivotBaseLower.trans (Nat.le_add_right _ _)
        have hmul := Nat.mul_le_mul_left Q sourceLower
        have hpos : 0 < Q * (parent.2 - Q + 1) := by
          apply Nat.mul_pos hQ0
          omega
        exact (Nat.sub_lt hpos Nat.zero_lt_one).trans_le
          (hmul.trans (Nat.le_add_right _ _))
      have occurrenceUpper : Q * candidate + (witness : Nat) <= grandparent.2 := by
        have beforeNext : Q * candidate + (witness : Nat) < Q * rightNext := by
          calc
            Q * candidate + (witness : Nat) < Q * (candidate + 1) := by
              calc
                Q * candidate + (witness : Nat) < Q * candidate + Q :=
                  Nat.add_lt_add_left witness.isLt _
                _ = Q * (candidate + 1) := by ring
            _ <= Q * rightNext :=
              Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr candidateLt)
        have nextImageStart : Q * rightNext <= grandparent.2 + 1 := by
          rw [rightNextBoundary]
          exact Nat.le_add_right _ _
        exact Nat.lt_succ_iff.mp (beforeNext.trans_le nextImageStart)
      have occurrenceInside : word (Q * candidate + (witness : Nat)) ∈ Delta := by
        apply grandBlock.2.1
        · exact (grandFirstCentral.trans grandCentralOrder).trans occurrenceLower.le
        · exact occurrenceUpper
      rw [fixedCell candidate witness] at occurrenceInside
      exact witnessOutside occurrenceInside
    have rightCellLower : parent.1 <= Q * (rightPivot - 1) := by
      have sourceLower : child.1 + Q <= rightPivot - 1 := by
        omega
      exact parentFirstCentral.trans (Nat.mul_le_mul_left Q sourceLower)
    have rightCellUpper : Q * ((rightPivot - 1) + 1) - 1 <= parent.2 := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr rightPivotPos.ne')]
      have : Q * rightPivot <= parent.2 + 1 := by
        rw [rightBoundary]
        exact Nat.le_add_right _ _
      omega
    have previousCellLower : Q * (rightPivot - 1) <= parent.2 - Q + 1 := by
      have pivotSplit : Q * rightPivot = Q * (rightPivot - 1) + Q := by
        conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr rightPivotPos.ne')]
        ring
      have hAdd : Q * (rightPivot - 1) + Q <= parent.2 + 1 := by
        rw [← pivotSplit, rightBoundary]
        exact Nat.le_add_right _ _
      have hSub : Q * (rightPivot - 1) <= parent.2 + 1 - Q :=
        Nat.le_sub_of_add_le hAdd
      have hQle : Q <= parent.2 + 1 :=
        (Nat.le_add_left Q (Q * (rightPivot - 1))).trans hAdd
      omega
    have nextLower : Q * rightPivot <= rightNext := by
      by_contra hnot
      have nextUpper : rightNext < Q * rightPivot := Nat.lt_of_not_ge hnot
      have nextPreviousLower : Q * (rightPivot - 1) <= rightNext :=
        previousCellLower.trans rightNextWindowLower
      let nextOffset : Fin Q :=
        ⟨rightNext - Q * (rightPivot - 1), by
          apply (Nat.sub_lt_iff_lt_add nextPreviousLower).mpr
          calc
            rightNext < Q * rightPivot := nextUpper
            _ = Q + Q * (rightPivot - 1) := by
              conv_lhs =>
                rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr rightPivotPos.ne')]
              ring⟩
      have nextCoord :
          rightNext = Q * (rightPivot - 1) + (nextOffset : Nat) := by
        dsimp [nextOffset]
        omega
      have nextMem : word rightNext ∈ g (word (rightPivot - 1)) := by
        rw [nextCoord, fixedCell]
        dsimp [uniformLetter]
        exact List.get_mem _ _
      exact rightNextOutside
        (imageInsideParentCell (rightPivot - 1) rightCellLower rightCellUpper
          (word rightNext) nextMem rightNextExit)
    have nextUpper : rightNext < Q * (rightPivot + 1) := by
      calc
        rightNext <= candidate := nextLeCandidate
        _ < Q * (rightPivot + 1) := by
          dsimp [candidate]
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.add_lt_add_left candidateOffset.isLt _
    let entry : Fin Q :=
      ⟨rightNext - Q * rightPivot, by
        apply (Nat.sub_lt_iff_lt_add nextLower).mpr
        calc
          rightNext < Q * (rightPivot + 1) := nextUpper
          _ = Q + Q * rightPivot := by ring⟩
    have transport : rightNext = Q * rightPivot + (entry : Nat) := by
      dsimp [entry]
      omega
    refine ⟨entry, transport, ?_, ⟨rightNextExit, rightNextOutside⟩, ?_⟩
    · rw [transport, fixedCell]
    · intro offset hOffsetEntry offsetMeets
      let earlier := Q * rightPivot + (offset : Nat)
      have earlierLtNext : earlier < rightNext := by
        dsimp [earlier]
        rw [transport]
        omega
      have earlierLetter :
          word earlier = uniformLetter g gUniform (word rightPivot) offset := by
        simpa [earlier] using fixedCell rightPivot offset
      have earlierMeetsWord : imageMeetsComplement g gUniform Delta (word earlier) := by
        rw [earlierLetter]
        exact offsetMeets
      obtain ⟨witness, witnessOutside⟩ := earlierMeetsWord
      have occurrenceLower :
          Q * (parent.2 - Q + 1) - 1 < Q * earlier + (witness : Nat) := by
        have sourceLower : parent.2 - Q + 1 <= earlier :=
          pivotBaseLower.trans (Nat.le_add_right _ _)
        have hmul := Nat.mul_le_mul_left Q sourceLower
        have hpos : 0 < Q * (parent.2 - Q + 1) := by
          apply Nat.mul_pos hQ0
          omega
        exact (Nat.sub_lt hpos Nat.zero_lt_one).trans_le
          (hmul.trans (Nat.le_add_right _ _))
      have occurrenceUpper : Q * earlier + (witness : Nat) <= grandparent.2 := by
        have beforeNext : Q * earlier + (witness : Nat) < Q * rightNext := by
          calc
            Q * earlier + (witness : Nat) < Q * (earlier + 1) := by
              calc
                Q * earlier + (witness : Nat) < Q * earlier + Q :=
                  Nat.add_lt_add_left witness.isLt _
                _ = Q * (earlier + 1) := by ring
            _ <= Q * rightNext :=
              Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr earlierLtNext)
        have nextImageStart : Q * rightNext <= grandparent.2 + 1 := by
          rw [rightNextBoundary]
          exact Nat.le_add_right _ _
        exact Nat.lt_succ_iff.mp (beforeNext.trans_le nextImageStart)
      have occurrenceInside : word (Q * earlier + (witness : Nat)) ∈ Delta := by
        apply grandBlock.2.1
        · exact (grandFirstCentral.trans grandCentralOrder).trans occurrenceLower.le
        · exact occurrenceUpper
      rw [fixedCell earlier witness] at occurrenceInside
      exact witnessOutside occurrenceInside
  obtain ⟨leftEntry, leftTransport, leftLetter, leftMeets, leftEntryMax⟩ := leftTransition
  obtain ⟨rightEntry, rightTransport, rightLetter, rightMeets, rightEntryMin⟩ :=
    rightTransition
  constructor
  · refine ⟨leftPivot, leftNext, leftExit, leftEntry, leftNextExit, leftBoundary,
      leftNextBoundary, leftOutside, leftExitMax, leftTransport, leftLetter,
      leftMeets, leftEntryMax, leftNextOutside, leftNextExitMax, ?_⟩
    change
      (grandparent.1 : Int) - (Q : Int) * (parent.1 : Int) =
        (Q : Int) * (leftEntry : Int) + leftNextExit + 1 -
          (Q : Int) * ((leftExit : Int) + 1)
    norm_num [leftBoundary, leftNextBoundary, leftTransport]
    ring
  · refine ⟨rightPivot, rightNext, rightExit, rightEntry, rightNextExit, rightBoundary,
      rightNextBoundary, rightOutside, rightExitMin, rightTransport, rightLetter,
      rightMeets, rightEntryMin, rightNextOutside, rightNextExitMin, ?_⟩
    change
      ((grandparent.2 + 1 : Nat) : Int) - (Q : Int) * ((parent.2 + 1 : Nat) : Int) =
        (Q : Int) * (rightEntry : Int) + rightNextExit -
          (Q : Int) * (rightExit : Int)
    norm_num [rightBoundary, rightNextBoundary, rightTransport]
    ring

/-- The pair of literal boundary-pivot letters of one actual maximal block. -/
def actualBksPivotState {Alphabet : Type*}
    (Q : Nat) (word : Nat -> Alphabet) (endpoints : Nat × Nat) : Alphabet × Alphabet :=
  (word ((endpoints.1 - 1) / Q), word ((endpoints.2 + 1) / Q))

/-- For one fixed support-stabilizing power, the paired pivot state has a
deterministic transition along actual two-edge BKS windows, and two equal
adjacent state pairs have equal signed endpoint displacements.  Every fact is
local to the two supplied literal edges. -/
theorem actual_bks_pivot_state_dynamics_at_power
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (word : Nat -> Alphabet) (q : Nat) (hq : 0 < q)
    (gUniform : forall a, (morphismPower morphism q [a]).length = P ^ q)
    (gFixed : forall (i : Nat) (offset : Fin (P ^ q)),
      word (P ^ q * i + offset) = uniformLetter
        (fun a => morphismPower morphism q [a]) gUniform (word i) offset)
    (gSupport : forall a,
      (morphismPower (fun b => morphismPower morphism q [b]) 2 [a]).toFinset =
        (morphismPower morphism q [a]).toFinset)
    (Delta : Finset Alphabet) (blocks : Nat -> Nat × Nat) :
    let Q := P ^ q
    let state := fun k => actualBksPivotState Q word (blocks (k + 1))
    let validAt := fun k =>
      IsBksDescentStep Q Delta word (blocks (k + 2)) (blocks (k + 1)) /\
        IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k)
    (forall {i j}, validAt i -> validAt j -> state i = state j ->
      state (i + 1) = state (j + 1)) /\
    forall {i j}, validAt i -> validAt j -> state i = state j ->
      state (i + 1) = state (j + 1) ->
      (((blocks (i + 2)).1 : Int) - Q * ((blocks (i + 1)).1 : Int) =
          ((blocks (j + 2)).1 : Int) - Q * ((blocks (j + 1)).1 : Int)) /\
        ((((blocks (i + 2)).2 + 1 : Nat) : Int) -
            Q * (((blocks (i + 1)).2 + 1 : Nat) : Int) =
          (((blocks (j + 2)).2 + 1 : Nat) : Int) -
            Q * (((blocks (j + 1)).2 + 1 : Nat) : Int)) := by
  dsimp only
  let Q := P ^ q
  let g : Alphabet -> List Alphabet := fun a => morphismPower morphism q [a]
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have pivotTransport := actual_boundary_pivot_transport_at_power
    P hP morphism word q hq gUniform gFixed gSupport
  let leftPivot : Nat -> Nat := fun k => ((blocks (k + 1)).1 - 1) / Q
  let rightPivot : Nat -> Nat := fun k => ((blocks (k + 1)).2 + 1) / Q
  let state : Nat -> Alphabet × Alphabet := fun k =>
    (word (leftPivot k), word (rightPivot k))
  have leftExitUnique (a : Alphabet) {x y : Fin Q}
      (hx : uniformLetter g gUniform a x ∉ Delta)
      (hxMax : forall z : Fin Q, x < z -> uniformLetter g gUniform a z ∈ Delta)
      (hy : uniformLetter g gUniform a y ∉ Delta)
      (hyMax : forall z : Fin Q, y < z -> uniformLetter g gUniform a z ∈ Delta) :
      x = y := by
    apply le_antisymm
    · by_contra hxy
      exact hx (hyMax x (lt_of_not_ge hxy))
    · by_contra hyx
      exact hy (hxMax y (lt_of_not_ge hyx))
  have rightExitUnique (a : Alphabet) {x y : Fin Q}
      (hx : uniformLetter g gUniform a x ∉ Delta)
      (hxMin : forall z : Fin Q, z < x -> uniformLetter g gUniform a z ∈ Delta)
      (hy : uniformLetter g gUniform a y ∉ Delta)
      (hyMin : forall z : Fin Q, z < y -> uniformLetter g gUniform a z ∈ Delta) :
      x = y := by
    apply le_antisymm
    · by_contra hxy
      exact hy (hxMin y (lt_of_not_ge hxy))
    · by_contra hyx
      exact hx (hyMin x (lt_of_not_ge hyx))
  have leftEntryUnique (a : Alphabet) {x y : Fin Q}
      (hx : imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a x))
      (hxMax : forall z : Fin Q, x < z ->
        ¬ imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a z))
      (hy : imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a y))
      (hyMax : forall z : Fin Q, y < z ->
        ¬ imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a z)) :
      x = y := by
    apply le_antisymm
    · by_contra hxy
      exact hyMax x (lt_of_not_ge hxy) hx
    · by_contra hyx
      exact hxMax y (lt_of_not_ge hyx) hy
  have rightEntryUnique (a : Alphabet) {x y : Fin Q}
      (hx : imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a x))
      (hxMin : forall z : Fin Q, z < x ->
        ¬ imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a z))
      (hy : imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a y))
      (hyMin : forall z : Fin Q, z < y ->
        ¬ imageMeetsComplement g gUniform Delta (uniformLetter g gUniform a z)) :
      x = y := by
    apply le_antisymm
    · by_contra hxy
      exact hxMin y (lt_of_not_ge hxy) hy
    · by_contra hyx
      exact hyMin x (lt_of_not_ge hyx) hx
  have leftFacts (k : Nat)
      (nextStep : IsBksDescentStep Q Delta word (blocks (k + 2)) (blocks (k + 1)))
      (step : IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k)) :
      exists exit entry nextExit : Fin Q,
        uniformLetter g gUniform (word (leftPivot k)) exit ∉ Delta /\
        (forall z : Fin Q, exit < z ->
          uniformLetter g gUniform (word (leftPivot k)) z ∈ Delta) /\
        imageMeetsComplement g gUniform Delta
          (uniformLetter g gUniform (word (leftPivot k)) entry) /\
        (forall z : Fin Q, entry < z ->
          ¬ imageMeetsComplement g gUniform Delta
            (uniformLetter g gUniform (word (leftPivot k)) z)) /\
        word (leftPivot (k + 1)) =
          uniformLetter g gUniform (word (leftPivot k)) entry /\
        uniformLetter g gUniform (word (leftPivot (k + 1))) nextExit ∉ Delta /\
        (forall z : Fin Q, nextExit < z ->
          uniformLetter g gUniform (word (leftPivot (k + 1))) z ∈ Delta) /\
        ((blocks (k + 2)).1 : Int) - Q * ((blocks (k + 1)).1 : Int) =
          Q * (entry : Int) + nextExit + 1 - Q * ((exit : Int) + 1) := by
    obtain ⟨left, right⟩ := pivotTransport Delta (blocks (k + 2)) (blocks (k + 1))
      (blocks k) nextStep step
    obtain ⟨pivot, nextPivot, exit, entry, nextExit, boundary, nextBoundary,
      outside, exitMax, transport, nextLetter, nextMeets, entryMax, nextOutside,
      nextExitMax, displacement⟩ := left
    have pivotEq : pivot = leftPivot k := by
      dsimp [leftPivot]
      have canonical : pivot = ((blocks (k + 1)).1 - 1) / Q := by
        have hsplit : (blocks (k + 1)).1 - 1 = (exit : Nat) + pivot * Q := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.mul_comm] using
            congrArg (fun n : Nat => n - 1) boundary
        rw [hsplit, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt exit.isLt]
        simp
      exact canonical
    have nextPivotEq : nextPivot = leftPivot (k + 1) := by
      dsimp [leftPivot]
      have hsplit : (blocks (k + 2)).1 - 1 = (nextExit : Nat) + nextPivot * Q := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.mul_comm] using
          congrArg (fun n : Nat => n - 1) nextBoundary
      rw [hsplit, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt nextExit.isLt]
      simp
    subst pivot
    subst nextPivot
    refine ⟨exit, entry, nextExit, outside, exitMax, ?_, entryMax, nextLetter,
      nextOutside, nextExitMax, displacement⟩
    simpa [nextLetter] using nextMeets
  have rightFacts (k : Nat)
      (nextStep : IsBksDescentStep Q Delta word (blocks (k + 2)) (blocks (k + 1)))
      (step : IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k)) :
      exists exit entry nextExit : Fin Q,
        uniformLetter g gUniform (word (rightPivot k)) exit ∉ Delta /\
        (forall z : Fin Q, z < exit ->
          uniformLetter g gUniform (word (rightPivot k)) z ∈ Delta) /\
        imageMeetsComplement g gUniform Delta
          (uniformLetter g gUniform (word (rightPivot k)) entry) /\
        (forall z : Fin Q, z < entry ->
          ¬ imageMeetsComplement g gUniform Delta
            (uniformLetter g gUniform (word (rightPivot k)) z)) /\
        word (rightPivot (k + 1)) =
          uniformLetter g gUniform (word (rightPivot k)) entry /\
        uniformLetter g gUniform (word (rightPivot (k + 1))) nextExit ∉ Delta /\
        (forall z : Fin Q, z < nextExit ->
          uniformLetter g gUniform (word (rightPivot (k + 1))) z ∈ Delta) /\
        (((blocks (k + 2)).2 + 1 : Nat) : Int) -
            Q * (((blocks (k + 1)).2 + 1 : Nat) : Int) =
          Q * (entry : Int) + nextExit - Q * (exit : Int) := by
    obtain ⟨left, right⟩ := pivotTransport Delta (blocks (k + 2)) (blocks (k + 1))
      (blocks k) nextStep step
    obtain ⟨pivot, nextPivot, exit, entry, nextExit, boundary, nextBoundary,
      outside, exitMin, transport, nextLetter, nextMeets, entryMin, nextOutside,
      nextExitMin, displacement⟩ := right
    have pivotEq : pivot = rightPivot k := by
      dsimp [rightPivot]
      have hsplit : (blocks (k + 1)).2 + 1 = (exit : Nat) + pivot * Q := by
        simpa [Nat.add_comm, Nat.mul_comm] using boundary
      rw [hsplit, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt exit.isLt]
      simp
    have nextPivotEq : nextPivot = rightPivot (k + 1) := by
      dsimp [rightPivot]
      have hsplit : (blocks (k + 2)).2 + 1 = (nextExit : Nat) + nextPivot * Q := by
        simpa [Nat.add_comm, Nat.mul_comm] using nextBoundary
      rw [hsplit, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt nextExit.isLt]
      simp
    subst pivot
    subst nextPivot
    refine ⟨exit, entry, nextExit, outside, exitMin, ?_, entryMin, nextLetter,
      nextOutside, nextExitMin, displacement⟩
    simpa [nextLetter] using nextMeets
  have stateStep {i j : Nat}
      (hi : IsBksDescentStep Q Delta word (blocks (i + 2)) (blocks (i + 1)) /\
        IsBksDescentStep Q Delta word (blocks (i + 1)) (blocks i))
      (hj : IsBksDescentStep Q Delta word (blocks (j + 2)) (blocks (j + 1)) /\
        IsBksDescentStep Q Delta word (blocks (j + 1)) (blocks j))
      (hstate : state i = state j) :
      state (i + 1) = state (j + 1) := by
    have hleft : word (leftPivot i) = word (leftPivot j) :=
      congrArg Prod.fst hstate
    have hright : word (rightPivot i) = word (rightPivot j) :=
      congrArg Prod.snd hstate
    obtain ⟨iexit, ientry, inextExit, _ioutside, _iexitMax, ientryGood,
      ientryMax, iletter, _inextOutside, _inextExitMax, _idisp⟩ :=
      leftFacts i hi.1 hi.2
    obtain ⟨jexit, jentry, jnextExit, _joutside, _jexitMax, jentryGood,
      jentryMax, jletter, _jnextOutside, _jnextExitMax, _jdisp⟩ :=
      leftFacts j hj.1 hj.2
    have hleftEntry : ientry = jentry := by
      apply leftEntryUnique (word (leftPivot i)) ientryGood ientryMax
      · simpa [hleft] using jentryGood
      · simpa [hleft] using jentryMax
    obtain ⟨riexit, rientry, rinextExit, _rioutside, _riexitMin, rientryGood,
      rientryMin, riletter, _rinextOutside, _rinextExitMin, _ridisp⟩ :=
      rightFacts i hi.1 hi.2
    obtain ⟨rjexit, rjentry, rjnextExit, _rjoutside, _rjexitMin, rjentryGood,
      rjentryMin, rjletter, _rjnextOutside, _rjnextExitMin, _rjdisp⟩ :=
      rightFacts j hj.1 hj.2
    have hrightEntry : rientry = rjentry := by
      apply rightEntryUnique (word (rightPivot i)) rientryGood rientryMin
      · simpa [hright] using rjentryGood
      · simpa [hright] using rjentryMin
    apply Prod.ext
    · dsimp [state]
      rw [iletter, jletter, hleft, hleftEntry]
    · dsimp [state]
      rw [riletter, rjletter, hright, hrightEntry]
  have displacementOfStates {i j : Nat}
      (hi : IsBksDescentStep Q Delta word (blocks (i + 2)) (blocks (i + 1)) /\
        IsBksDescentStep Q Delta word (blocks (i + 1)) (blocks i))
      (hj : IsBksDescentStep Q Delta word (blocks (j + 2)) (blocks (j + 1)) /\
        IsBksDescentStep Q Delta word (blocks (j + 1)) (blocks j))
      (hstate : state i = state j)
      (hnext : state (i + 1) = state (j + 1)) :
      (((blocks (i + 2)).1 : Int) - Q * ((blocks (i + 1)).1 : Int) =
          ((blocks (j + 2)).1 : Int) - Q * ((blocks (j + 1)).1 : Int)) /\
        ((((blocks (i + 2)).2 + 1 : Nat) : Int) -
            Q * (((blocks (i + 1)).2 + 1 : Nat) : Int) =
          (((blocks (j + 2)).2 + 1 : Nat) : Int) -
            Q * (((blocks (j + 1)).2 + 1 : Nat) : Int)) := by
    have hleft : word (leftPivot i) = word (leftPivot j) :=
      congrArg Prod.fst hstate
    have hright : word (rightPivot i) = word (rightPivot j) :=
      congrArg Prod.snd hstate
    have hleftNext : word (leftPivot (i + 1)) = word (leftPivot (j + 1)) :=
      congrArg Prod.fst hnext
    have hrightNext : word (rightPivot (i + 1)) = word (rightPivot (j + 1)) :=
      congrArg Prod.snd hnext
    obtain ⟨iexit, ientry, inextExit, ioutside, iexitMax, ientryGood,
      ientryMax, _iletter, inextOutside, inextExitMax, idisp⟩ :=
      leftFacts i hi.1 hi.2
    obtain ⟨jexit, jentry, jnextExit, joutside, jexitMax, jentryGood,
      jentryMax, _jletter, jnextOutside, jnextExitMax, jdisp⟩ :=
      leftFacts j hj.1 hj.2
    have hexit : iexit = jexit := by
      apply leftExitUnique (word (leftPivot i)) ioutside iexitMax
      · simpa [hleft] using joutside
      · simpa [hleft] using jexitMax
    have hentry : ientry = jentry := by
      apply leftEntryUnique (word (leftPivot i)) ientryGood ientryMax
      · simpa [hleft] using jentryGood
      · simpa [hleft] using jentryMax
    have hnextExit : inextExit = jnextExit := by
      apply leftExitUnique (word (leftPivot (i + 1))) inextOutside inextExitMax
      · simpa [hleftNext] using jnextOutside
      · simpa [hleftNext] using jnextExitMax
    obtain ⟨riexit, rientry, rinextExit, rioutside, riexitMin, rientryGood,
      rientryMin, _riletter, rinextOutside, rinextExitMin, ridisp⟩ :=
      rightFacts i hi.1 hi.2
    obtain ⟨rjexit, rjentry, rjnextExit, rjoutside, rjexitMin, rjentryGood,
      rjentryMin, _rjletter, rjnextOutside, rjnextExitMin, rjdisp⟩ :=
      rightFacts j hj.1 hj.2
    have hrexit : riexit = rjexit := by
      apply rightExitUnique (word (rightPivot i)) rioutside riexitMin
      · simpa [hright] using rjoutside
      · simpa [hright] using rjexitMin
    have hrentry : rientry = rjentry := by
      apply rightEntryUnique (word (rightPivot i)) rientryGood rientryMin
      · simpa [hright] using rjentryGood
      · simpa [hright] using rjentryMin
    have hrnextExit : rinextExit = rjnextExit := by
      apply rightExitUnique (word (rightPivot (i + 1))) rinextOutside rinextExitMin
      · simpa [hrightNext] using rjnextOutside
      · simpa [hrightNext] using rjnextExitMin
    constructor
    · rw [idisp, jdisp, hexit, hentry, hnextExit]
    · rw [ridisp, rjdisp, hrexit, hrentry, hrnextExit]
  change
    (forall {i j},
      (IsBksDescentStep Q Delta word (blocks (i + 2)) (blocks (i + 1)) /\
        IsBksDescentStep Q Delta word (blocks (i + 1)) (blocks i)) ->
      (IsBksDescentStep Q Delta word (blocks (j + 2)) (blocks (j + 1)) /\
        IsBksDescentStep Q Delta word (blocks (j + 1)) (blocks j)) ->
      state i = state j -> state (i + 1) = state (j + 1)) /\ _
  exact ⟨stateStep, displacementOfStates⟩

/-- Along every literal forward chain of actual BKS steps, both signed endpoint
displacements are eventually periodic for the same stabilized morphism power.
The finite state is the pair of actual left and right pivot letters. -/
theorem exists_eventually_periodic_actual_bks_signed_displacements
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (uniform : forall a, (morphism a).length = P) (word : Nat -> Alphabet)
    (fixed : forall (i : Nat) (offset : Fin P),
      word (P * i + offset) = uniformLetter morphism uniform (word i) offset) :
    exists q : Nat, 0 < q /\
      let Q := P ^ q
      forall (Delta : Finset Alphabet) (blocks : Nat -> Nat × Nat),
        (forall k, IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k)) ->
        exists N period : Nat, 0 < period /\ forall k, N <= k ->
          (((blocks (k + period + 1)).1 : Int) -
              Q * ((blocks (k + period)).1 : Int) =
            ((blocks (k + 1)).1 : Int) - Q * ((blocks k).1 : Int)) /\
          ((((blocks (k + period + 1)).2 + 1 : Nat) : Int) -
              Q * (((blocks (k + period)).2 + 1 : Nat) : Int) =
            (((blocks (k + 1)).2 + 1 : Nat) : Int) -
              Q * (((blocks k).2 + 1 : Nat) : Int)) := by
  obtain ⟨q, hq, powerData⟩ :=
    exists_bounded_root_descent_chain P hP morphism uniform word fixed
  dsimp only at powerData
  rcases powerData with
    ⟨gUniform, gFixed, gSupport, _earlyRoots, _lateRootWords, _contextPairs, _roots⟩
  refine ⟨q, hq, ?_⟩
  dsimp only
  intro Delta blocks chain
  let Q := P ^ q
  let state : Nat -> Alphabet × Alphabet := fun k =>
    actualBksPivotState Q word (blocks (k + 1))
  obtain ⟨stateStep, displacementOfStates⟩ :=
    actual_bks_pivot_state_dynamics_at_power
      P hP morphism word q hq gUniform gFixed gSupport Delta blocks
  have validAt (k : Nat) :
      IsBksDescentStep Q Delta word (blocks (k + 2)) (blocks (k + 1)) /\
        IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k) := by
    exact ⟨chain (k + 1), chain k⟩
  obtain ⟨i, j, hij, hcollision⟩ :=
    Finite.exists_ne_map_eq_of_infinite state
  obtain hijlt | hjilt := lt_or_gt_of_ne hij
  · let period := j - i
    have hperiod : 0 < period := Nat.sub_pos_of_lt hijlt
    have hj : j = i + period := by omega
    have statesRepeat : forall t : Nat, state (i + t) = state (j + t) := by
      intro t
      induction t with
      | zero => simpa using hcollision
      | succ t iht =>
          simpa [state, Q, Nat.add_assoc] using
            stateStep (validAt (i + t)) (validAt (j + t)) iht
    refine ⟨i + 1, period, hperiod, ?_⟩
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hcurrent := statesRepeat t
    have hfollowing := statesRepeat (t + 1)
    have hdisplacement := displacementOfStates (validAt (i + t)) (validAt (j + t))
      hcurrent (by simpa [state, Q, Nat.add_assoc] using hfollowing)
    simpa [Q, hj, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      And.intro hdisplacement.1.symm hdisplacement.2.symm
  · let period := i - j
    have hperiod : 0 < period := Nat.sub_pos_of_lt hjilt
    have hi : i = j + period := by omega
    have statesRepeat : forall t : Nat, state (j + t) = state (i + t) := by
      intro t
      induction t with
      | zero => simpa using hcollision.symm
      | succ t iht =>
          simpa [state, Q, Nat.add_assoc] using
            stateStep (validAt (j + t)) (validAt (i + t)) iht
    refine ⟨j + 1, period, hperiod, ?_⟩
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hcurrent := statesRepeat t
    have hfollowing := statesRepeat (t + 1)
    have hdisplacement := displacementOfStates (validAt (j + t)) (validAt (i + t))
      hcurrent (by simpa [state, Q, Nat.add_assoc] using hfollowing)
    simpa [Q, hi, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      And.intro hdisplacement.1.symm hdisplacement.2.symm


end Raney
end TrureTuring
