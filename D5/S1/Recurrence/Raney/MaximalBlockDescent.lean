/- GID: D5/S1/Recurrence/Raney/MaximalBlockDescent
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/MaximalBlockDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct maximal Raney block predecessors and prove strict return descent. -/

import D5.S1.Recurrence.Raney.MaximalBlockEvolution

namespace TrureTuring
namespace Raney

/-- Apply one support-stabilizing positive power to the uniform fixed word, then
construct the actual maximal predecessor supplied by BKS Lemma 11 and recover the
original block from it by BKS Lemma 12.

The proof constructs `g(a) = morphismPower morphism q [a]`; its uniform length is
`P^q`, its cells are read directly from the same fixed word, and its two-step letter
support is its one-step support.  The displayed quotient thresholds are uniform in
the block.  They make the predecessor late and long, while its right endpoint is
strictly smaller than the original right endpoint.  Return uses a literal point in
the central image shared with the original block and maximal-interval uniqueness. -/
theorem exists_uniform_power_bks11_bks12_evolution
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (uniform : forall a, (morphism a).length = P) (word : Nat -> Alphabet)
    (fixed : forall (i : Nat) (offset : Fin P),
      word (P * i + offset) = uniformLetter morphism uniform (word i) offset) :
    exists q : Nat, 0 < q /\
      let Q := P ^ q
      let g : Alphabet -> List Alphabet := fun a => morphismPower morphism q [a]
      ∃ gUniform : forall a, (g a).length = Q,
        (forall (i : Nat) (offset : Fin Q),
          word (Q * i + offset) = uniformLetter g gUniform (word i) offset) /\
        (forall a, (morphismPower g 2 [a]).toFinset = (g a).toFinset) /\
      forall (Delta : Finset Alphabet) (first last : Nat),
        IsMaximalDeltaInterval Delta word first last ->
        2 * (P ^ q) <= first / (P ^ q) ->
        2 * (P ^ q) ^ 2 < last + 1 - first ->
        (P ^ q) ^ 2 + 2 * (P ^ q) <
          last / (P ^ q) + 1 - first / (P ^ q) ->
        let Q := P ^ q
        let sourceFirst := first / Q
        let sourceLast := last / Q
        ∃ predecessor : Nat × Nat,
          IsMaximalDeltaInterval Delta word predecessor.1 predecessor.2 /\
          sourceFirst - Q < predecessor.1 /\
          predecessor.1 <= sourceFirst + Q /\
          sourceLast - Q <= predecessor.2 /\
          predecessor.2 < sourceLast + Q /\
          Q < predecessor.1 /\
          Q ^ 2 < predecessor.2 + 1 - predecessor.1 /\
          predecessor.2 < last /\
          (forall endpoints : Nat × Nat,
            IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
              endpoints.1 <= sourceFirst + Q /\ sourceLast - Q <= endpoints.2 ->
            endpoints = predecessor) /\
          (let centralFirst := Q * (predecessor.1 + Q)
           let centralLast := Q * (predecessor.2 - Q + 1) - 1
           first <= centralFirst /\ centralFirst <= last /\
             (forall n, centralFirst <= n -> n <= centralLast -> word n ∈ Delta) /\
             (exists n, Q * (predecessor.1 - Q) <= n /\
               n < centralFirst /\ word n ∉ Delta) /\
             (exists n, centralLast < n /\
               n < Q * (predecessor.2 + Q + 1) /\ word n ∉ Delta) /\
             (IsMaximalDeltaInterval Delta word first last /\
               Q * (predecessor.1 - Q) < first /\
               first <= centralFirst /\ centralLast <= last /\
               last < Q * (predecessor.2 + Q + 1)) /\
             forall endpoints : Nat × Nat,
               IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
                 Q * (predecessor.1 - Q) < endpoints.1 /\
                 endpoints.1 <= centralFirst /\ centralLast <= endpoints.2 /\
                 endpoints.2 < Q * (predecessor.2 + Q + 1) ->
               endpoints = (first, last)) := by
  obtain ⟨q, hq, hSupport⟩ := exists_support_stabilizing_power morphism
  let g : Alphabet -> List Alphabet := fun a => morphismPower morphism q [a]
  have power_length : forall (n : Nat) (xs : List Alphabet),
      (morphismPower morphism n xs).length = xs.length * P ^ n := by
    intro n
    induction n with
    | zero => intro xs; simp [morphismPower]
    | succ n ih =>
        intro xs
        simp [morphismPower, List.length_flatMap, uniform, ih, Nat.pow_succ,
          Nat.mul_assoc]
  have gUniform : forall a, (g a).length = P ^ q := by
    intro a
    simpa [g] using power_length q [a]
  have power_singleton_flatMap : forall (n : Nat) (xs : List Alphabet),
      xs.flatMap (fun a => morphismPower morphism n [a]) =
        morphismPower morphism n xs := by
    intro n
    induction n with
    | zero => intro xs; simp [morphismPower]
    | succ n ih =>
        intro xs
        simp only [morphismPower]
        rw [← List.flatMap_assoc, ih]
  have power_add : forall (m n : Nat) (xs : List Alphabet),
      morphismPower morphism (m + n) xs =
        morphismPower morphism n (morphismPower morphism m xs) := by
    intro m n
    induction n with
    | zero => intro xs; simp [morphismPower]
    | succ n ih =>
        intro xs
        rw [Nat.add_succ, morphismPower, ih, morphismPower]
  have g_power : forall (n : Nat) (xs : List Alphabet),
      morphismPower g n xs = morphismPower morphism (q * n) xs := by
    intro n
    induction n with
    | zero => intro xs; simp [morphismPower]
    | succ n ih =>
        intro xs
        rw [morphismPower, ih]
        change (morphismPower morphism (q * n) xs).flatMap
            (fun a => morphismPower morphism q [a]) = _
        rw [power_singleton_flatMap, ← power_add]
        congr 1
  have get_flatMap_uniform
      (xs : List Alphabet) (f : Alphabet -> List Alphabet) (M : Nat)
      (hf : forall a, (f a).length = M) (i : Nat) (hi : i < xs.length)
      (offset : Fin M) :
      (xs.flatMap f).get
          ⟨M * i + offset, by
            simp only [List.length_flatMap]
            simp only [hf, List.map_const', List.sum_replicate]
            calc
              M * i + offset < M * i + M := Nat.add_lt_add_left offset.isLt _
              _ = M * (i + 1) := by ring
              _ <= M * xs.length := Nat.mul_le_mul_left M (Nat.succ_le_iff.mpr hi)
              _ = xs.length * M := Nat.mul_comm _ _⟩ =
        (f (xs.get ⟨i, hi⟩)).get
          ⟨offset, by rw [hf]; exact offset.isLt⟩ := by
    induction xs generalizing i with
    | nil => simp at hi
    | cons x xs ih =>
        cases i with
        | zero =>
            simp only [List.get_eq_getElem, List.flatMap_cons, Nat.mul_zero, zero_add,
              List.getElem_cons_zero]
            rw [List.getElem_append_left]
        | succ i =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
            rw [List.get_eq_getElem, List.get_eq_getElem]
            simp only [List.flatMap_cons]
            rw [List.getElem_append_right (by
              rw [hf]
              exact (Nat.le_mul_of_pos_right M (Nat.succ_pos i)).trans
                (Nat.le_add_right _ _))]
            have hindex : M * (i + 1) + (offset : Nat) - (f x).length =
                M * i + offset := by
              rw [hf, Nat.mul_succ]
              omega
            simp only [hindex, List.get_cons_succ]
            simpa only [List.get_eq_getElem] using ih i hi
  have fixed_power_succ : forall (n : Nat) (i : Nat) (offset : Fin (P ^ (n + 1))),
        word (P ^ (n + 1) * i + offset) =
          (morphismPower morphism (n + 1) [word i]).get
            ⟨offset, by rw [power_length]; simp⟩ := by
    intro n
    induction n with
    | zero =>
        intro i offset
        let offsetP : Fin P := ⟨offset, by simpa using offset.isLt⟩
        simpa [uniformLetter, morphismPower, offsetP] using fixed i offsetP
    | succ n ih =>
        intro i offset
        have hP0 : 0 < P := by omega
        let outer : Fin (P ^ (n + 1)) :=
          ⟨offset / P, by
            have hoff : (offset : Nat) < P ^ (n + 1) * P := by
              simpa [Nat.pow_succ] using offset.isLt
            exact (Nat.div_lt_iff_lt_mul hP0).mpr (by
              simpa [Nat.mul_comm] using hoff)⟩
        let inner : Fin P := ⟨offset % P, Nat.mod_lt _ hP0⟩
        have hcoord :
            P ^ (n + 2) * i + offset =
              P * (P ^ (n + 1) * i + outer) + inner := by
          dsimp [outer, inner]
          have hdiv := (Nat.div_add_mod (offset : Nat) P).symm
          have hpow : P ^ (n + 2) = P ^ (n + 1) * P := by
            rw [show n + 2 = (n + 1) + 1 by omega, Nat.pow_succ]
          calc
            P ^ (n + 2) * i + offset = (P ^ (n + 1) * P) * i + offset := by
              exact congrArg (fun x => x * i + (offset : Nat)) hpow
            _ = P * (P ^ (n + 1) * i) + offset := by ring
            _ = P * (P ^ (n + 1) * i + offset / P) + offset % P := by
              rw [Nat.mul_add]
              omega
        rw [hcoord, fixed, ih i outer]
        simpa [uniformLetter, morphismPower, outer, inner, Nat.div_add_mod] using
          (get_flatMap_uniform
            (morphismPower morphism (n + 1) [word i]) morphism P uniform
            outer (by simpa [power_length] using outer.isLt) inner).symm
  have fixed_power : forall (n : Nat), 0 < n ->
      forall (i : Nat) (offset : Fin (P ^ n)),
        word (P ^ n * i + offset) =
          (morphismPower morphism n [word i]).get
            ⟨offset, by rw [power_length]; simp⟩ := by
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa [Nat.succ_eq_add_one] using fixed_power_succ n
  have gFixed : forall (i : Nat) (offset : Fin (P ^ q)),
      word (P ^ q * i + offset) = uniformLetter g gUniform (word i) offset := by
    intro i offset
    simpa [uniformLetter, g] using fixed_power q hq i offset
  have gSupport : forall a,
      (morphismPower g 2 [a]).toFinset = (g a).toFinset := by
    intro a
    rw [g_power]
    simpa [g] using hSupport a 2 (by omega)
  let Q := P ^ q
  have hQ : 1 < Q := by
    dsimp [Q]
    exact one_lt_pow' hP hq.ne'
  have hQ0 : 0 < Q := by omega
  refine ⟨q, hq, ?_⟩
  dsimp only
  refine ⟨gUniform, gFixed, gSupport, ?_⟩
  intro Delta first last block lateQuotient long sourceSpan
  let sourceFirst := first / Q
  let sourceLast := last / Q
  have hSourceFirst : 2 * Q <= sourceFirst := by
    simpa [sourceFirst, Q] using lateQuotient
  have hFirstLower : Q * sourceFirst <= first := by
    dsimp [sourceFirst]
    exact Nat.mul_div_le first Q
  have hLate : Q < first := by
    have hOneSource : 1 < sourceFirst := by omega
    have hmul : Q * 1 < Q * sourceFirst :=
      Nat.mul_lt_mul_of_pos_left hOneSource hQ0
    omega
  have hBks11 := uniform_bks11_predecessor Q hQ g gUniform word gFixed
    gSupport Delta first last block hLate long
  change sourceFirst + Q <= sourceLast - Q /\
      (forall n, sourceFirst + Q <= n -> n <= sourceLast - Q -> word n ∈ Delta) /\
      (exists n, sourceFirst - Q <= n /\
        n <= sourceFirst + Q - 1 /\ word n ∉ Delta) /\
      (exists n, sourceLast - Q + 1 <= n /\
        n <= sourceLast + Q /\ word n ∉ Delta) at hBks11
  rcases hBks11 with ⟨hCoreOrder, hCore, hLeftWitness, hRightWitness⟩
  let coreFirst := sourceFirst + Q
  let coreLast := sourceLast - Q
  obtain ⟨leftWitness, hLeftWitnessLower, hLeftWitnessUpper,
      hLeftWitnessOutside⟩ := hLeftWitness
  obtain ⟨rightWitness, hRightWitnessLower, hRightWitnessUpper,
      hRightWitnessOutside⟩ := hRightWitness
  let leftSet := (Finset.range coreFirst).filter fun n => word n ∉ Delta
  have hLeftSet : leftSet.Nonempty := by
    refine ⟨leftWitness, ?_⟩
    have hlt : leftWitness < coreFirst := by
      dsimp [coreFirst]
      omega
    simp [leftSet, hlt, hLeftWitnessOutside]
  let leftBoundary := leftSet.max' hLeftSet
  let rightSet := (Finset.Icc (coreLast + 1) (sourceLast + Q)).filter
    fun n => word n ∉ Delta
  have hRightSet : rightSet.Nonempty := by
    refine ⟨rightWitness, ?_⟩
    simp [rightSet, coreLast, hRightWitnessLower, hRightWitnessUpper,
      hRightWitnessOutside]
  let rightBoundary := rightSet.min' hRightSet
  let predecessor : Nat × Nat := (leftBoundary + 1, rightBoundary - 1)
  have hLeftBoundaryMem : leftBoundary ∈ leftSet := Finset.max'_mem _ _
  have hRightBoundaryMem : rightBoundary ∈ rightSet := Finset.min'_mem _ _
  have hLeftBoundary : leftBoundary < coreFirst /\ word leftBoundary ∉ Delta := by
    simpa [leftSet] using (Finset.mem_filter.mp hLeftBoundaryMem)
  have hRightBoundary : coreLast + 1 <= rightBoundary /\
      rightBoundary <= sourceLast + Q /\ word rightBoundary ∉ Delta := by
    rcases Finset.mem_filter.mp hRightBoundaryMem with ⟨hmem, hout⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hlower, hupper⟩
    exact ⟨hlower, hupper, hout⟩
  have hPredecessor :
      IsMaximalDeltaInterval Delta word predecessor.1 predecessor.2 := by
    have hEndpoints : predecessor.1 <= predecessor.2 := by
      dsimp [predecessor, coreFirst, coreLast] at *
      omega
    refine ⟨hEndpoints, ?_, ?_, ?_⟩
    · intro n hnLeft hnRight
      by_cases hnCoreLeft : n < coreFirst
      · by_contra hnDelta
        have hnMem : n ∈ leftSet := by simp [leftSet, hnCoreLeft, hnDelta]
        have hnLe : n <= leftBoundary := Finset.le_max' _ _ hnMem
        dsimp [predecessor] at hnLeft
        omega
      · by_cases hnCoreRight : n <= coreLast
        · apply hCore n
          · simpa [coreFirst] using (Nat.le_of_not_gt hnCoreLeft)
          · simpa [coreLast] using hnCoreRight
        · by_contra hnDelta
          have hnMem : n ∈ rightSet := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hnDelta⟩
            · omega
            · dsimp [predecessor] at hnRight
              omega
          have hBoundaryLe : rightBoundary <= n := Finset.min'_le _ _ hnMem
          dsimp [predecessor] at hnRight
          omega
    · right
      dsimp [predecessor]
      simpa using hLeftBoundary.2
    · dsimp [predecessor]
      have hRightPositive : 0 < rightBoundary := by omega
      rw [Nat.sub_add_cancel hRightPositive]
      exact hRightBoundary.2.2
  have hLeftWitnessLe : leftWitness <= leftBoundary := by
    apply Finset.le_max'
    have hlt : leftWitness < coreFirst := by
      dsimp [coreFirst]
      omega
    simp [leftSet, hlt, hLeftWitnessOutside]
  have hRightBoundaryLe : rightBoundary <= rightWitness := by
    apply Finset.min'_le
    simp [rightSet, coreLast, hRightWitnessLower, hRightWitnessUpper,
      hRightWitnessOutside]
  have hPredecessorBounds :
      sourceFirst - Q < predecessor.1 /\
        predecessor.1 <= sourceFirst + Q /\
        sourceLast - Q <= predecessor.2 /\
        predecessor.2 < sourceLast + Q := by
    dsimp [predecessor, coreFirst, coreLast] at *
    omega
  have maximal_eq_of_overlap (a b c d n : Nat)
      (hab : IsMaximalDeltaInterval Delta word a b)
      (hcd : IsMaximalDeltaInterval Delta word c d)
      (han : a <= n) (hnb : n <= b) (hcn : c <= n) (hnd : n <= d) :
      (a, b) = (c, d) := by
    rcases hab with ⟨habOrder, habInside, habLeft, habRight⟩
    rcases hcd with ⟨hcdOrder, hcdInside, hcdLeft, hcdRight⟩
    apply Prod.ext
    · apply le_antisymm
      · by_contra hnot
        have hca : c < a := Nat.lt_of_not_ge hnot
        have hInside : word (a - 1) ∈ Delta := by
          apply hcdInside
          · omega
          · omega
        exact habLeft.resolve_left (by omega) hInside
      · by_contra hnot
        have hac : a < c := Nat.lt_of_not_ge hnot
        have hInside : word (c - 1) ∈ Delta := by
          apply habInside
          · omega
          · omega
        exact hcdLeft.resolve_left (by omega) hInside
    · apply le_antisymm
      · by_contra hnot
        have hdb : d < b := Nat.lt_of_not_ge hnot
        have hInside : word (d + 1) ∈ Delta := by
          apply habInside
          · omega
          · omega
        exact hcdRight hInside
      · by_contra hnot
        have hbd : b < d := Nat.lt_of_not_ge hnot
        have hInside : word (b + 1) ∈ Delta := by
          apply hcdInside
          · omega
          · omega
        exact habRight hInside
  have hPredecessorUnique : forall endpoints : Nat × Nat,
      IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
        endpoints.1 <= sourceFirst + Q /\ sourceLast - Q <= endpoints.2 ->
      endpoints = predecessor := by
    intro endpoints hEndpoints
    rcases hEndpoints with ⟨hEndpointBlock, hEndpointFirst, hEndpointLast⟩
    have hEq := maximal_eq_of_overlap endpoints.1 endpoints.2
      predecessor.1 predecessor.2 coreFirst hEndpointBlock hPredecessor
      hEndpointFirst (by
        exact hCoreOrder.trans hEndpointLast)
      hPredecessorBounds.2.1 (by
        exact hCoreOrder.trans hPredecessorBounds.2.2.1)
    simpa [predecessor] using hEq
  have hPredecessorLate : Q < predecessor.1 := by
    omega
  have hPredecessorLong : Q ^ 2 < predecessor.2 + 1 - predecessor.1 := by
    change Q ^ 2 + 2 * Q < sourceLast + 1 - sourceFirst at sourceSpan
    omega
  have hLastLower : Q * sourceLast <= last := by
    dsimp [sourceLast]
    exact Nat.mul_div_le last Q
  have hQLeSourceLast : Q <= sourceLast := by omega
  have hSourceLastBound : sourceLast + Q <= Q * sourceLast := by
    calc
      sourceLast + Q <= sourceLast + sourceLast :=
        Nat.add_le_add_left hQLeSourceLast sourceLast
      _ = 2 * sourceLast := by omega
      _ <= Q * sourceLast := Nat.mul_le_mul_right sourceLast (by omega)
  have hDescent : predecessor.2 < last :=
    hPredecessorBounds.2.2.2.trans_le (hSourceLastBound.trans hLastLower)
  have hBks12 := uniform_bks12_successor Q hQ g gUniform word gFixed gSupport
    Delta predecessor.1 predecessor.2 hPredecessor hPredecessorLate hPredecessorLong
  dsimp only at hBks12
  rcases hBks12 with ⟨hCentralImage, hLeftImage, hRightImage,
    successor, hSuccessor, hSuccessorUnique⟩
  let centralFirst := Q * (predecessor.1 + Q)
  let centralLast := Q * (predecessor.2 - Q + 1) - 1
  have hFirstUpper : first < Q * (sourceFirst + 1) := by
    dsimp [sourceFirst]
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul hQ0).mp (Nat.lt_succ_self (first / Q))
  have hFirstCentral : first <= centralFirst := by
    have hSourceStrict : sourceFirst < predecessor.1 + Q := by omega
    have hSourceSucc : sourceFirst + 1 <= predecessor.1 + Q := hSourceStrict
    exact hFirstUpper.le.trans (by
      dsimp [centralFirst]
      exact Nat.mul_le_mul_left Q hSourceSucc)
  have hCentralLast : centralFirst <= last := by
    have hSourceUpper : predecessor.1 + Q <= sourceLast := by omega
    calc
      centralFirst <= Q * sourceLast := by
        dsimp [centralFirst]
        exact Nat.mul_le_mul_left Q hSourceUpper
      _ <= last := hLastLower
  rcases hSuccessor with ⟨hSuccessorBlock, hSuccessorLower, hSuccessorFirst,
    hSuccessorLast, hSuccessorUpper⟩
  have hCentralSource : predecessor.1 + Q <= predecessor.2 - Q := by
    have hTwoQ : 2 * Q <= Q ^ 2 := by nlinarith
    have hLength : 2 * Q < predecessor.2 + 1 - predecessor.1 :=
      hTwoQ.trans_lt hPredecessorLong
    omega
  have hCentralCoords : centralFirst <= centralLast := by
    have hmul : Q * (predecessor.1 + Q) <
        Q * (predecessor.2 - Q + 1) := by
      apply Nat.mul_lt_mul_of_pos_left _ hQ0
      omega
    dsimp [centralFirst, centralLast]
    omega
  have hSuccessorContainsCentral :
      successor.1 <= centralFirst /\ centralFirst <= successor.2 := by
    exact ⟨hSuccessorFirst, hCentralCoords.trans hSuccessorLast⟩
  have hSuccessorEq : successor = (first, last) := by
    have hEq := maximal_eq_of_overlap successor.1 successor.2 first last centralFirst
      hSuccessorBlock block hSuccessorContainsCentral.1
      hSuccessorContainsCentral.2 hFirstCentral hCentralLast
    simpa using hEq
  have hReturn :
      IsMaximalDeltaInterval Delta word first last /\
        Q * (predecessor.1 - Q) < first /\
        first <= centralFirst /\ centralLast <= last /\
        last < Q * (predecessor.2 + Q + 1) := by
    refine ⟨block, ?_, hFirstCentral, ?_, ?_⟩
    · simpa [hSuccessorEq] using hSuccessorLower
    · simpa [centralLast, hSuccessorEq] using hSuccessorLast
    · simpa [hSuccessorEq] using hSuccessorUpper
  have hReturnUnique : forall endpoints : Nat × Nat,
      IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
        Q * (predecessor.1 - Q) < endpoints.1 /\
        endpoints.1 <= centralFirst /\ centralLast <= endpoints.2 /\
        endpoints.2 < Q * (predecessor.2 + Q + 1) ->
      endpoints = (first, last) := by
    intro endpoints hEndpoints
    exact (hSuccessorUnique endpoints hEndpoints).trans hSuccessorEq
  refine ⟨predecessor, hPredecessor, hPredecessorBounds.1,
    hPredecessorBounds.2.1, hPredecessorBounds.2.2.1,
    hPredecessorBounds.2.2.2, hPredecessorLate, hPredecessorLong, hDescent,
    hPredecessorUnique, ?_⟩
  exact ⟨hFirstCentral, hCentralLast, hCentralImage, hLeftImage, hRightImage,
    hReturn, hReturnUnique⟩

/-- The literal letters in a finite interval. -/
def intervalWord {Alphabet : Type*} (word : Nat -> Alphabet) (endpoints : Nat × Nat) :
    List Alphabet :=
  List.ofFn fun i : Fin (endpoints.2 + 1 - endpoints.1) => word (endpoints.1 + i)

/-- One actual inverse/image evolution step.  The two context words are literal
subwords between the returned block boundary and the central image. -/
def IsBksDescentStep {Alphabet : Type*} [DecidableEq Alphabet]
    (Q : Nat) (Delta : Finset Alphabet) (word : Nat -> Alphabet)
    (parent child : Nat × Nat) : Prop :=
  let sourceFirst := parent.1 / Q
  let sourceLast := parent.2 / Q
  let centralFirst := Q * (child.1 + Q)
  let centralLast := Q * (child.2 - Q + 1) - 1
  IsMaximalDeltaInterval Delta word parent.1 parent.2 /\
    IsMaximalDeltaInterval Delta word child.1 child.2 /\
    sourceFirst - Q < child.1 /\ child.1 <= sourceFirst + Q /\
    sourceLast - Q <= child.2 /\ child.2 < sourceLast + Q /\
    Q < child.1 /\ Q ^ 2 < child.2 + 1 - child.1 /\
    child.2 < parent.2 /\
    Q * (child.1 - Q) < parent.1 /\
    parent.2 < Q * (child.2 + Q + 1) /\
    parent.1 <= centralFirst /\ centralFirst <= centralLast /\ centralLast <= parent.2 /\
    (forall n, centralFirst <= n -> n <= centralLast -> word n ∈ Delta) /\
    (intervalWord word (parent.1, centralFirst - 1)).length <= 2 * Q ^ 2 /\
    (intervalWord word (centralLast + 1, parent.2)).length <= 2 * Q ^ 2

/-- A root is reached exactly when one of the three hypotheses needed for the
next conservative BKS descent fails. -/
def IsBksRoot (Q : Nat) (endpoints : Nat × Nat) : Prop :=
  endpoints.1 / Q < 2 * Q \/
    endpoints.2 + 1 - endpoints.1 <= 2 * Q ^ 2 \/
    endpoints.2 / Q + 1 - endpoints.1 / Q <= Q ^ 2 + 2 * Q

/-- A chain made only from actual maximal-block inverse/image steps. -/
inductive IsBksDescentChain {Alphabet : Type*} [DecidableEq Alphabet]
    (Q : Nat) (Delta : Finset Alphabet) (word : Nat -> Alphabet) :
    (Nat × Nat) -> (Nat × Nat) -> Prop
  | root (endpoints : Nat × Nat)
      (block : IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2)
      (terminal : IsBksRoot Q endpoints) :
      IsBksDescentChain Q Delta word endpoints endpoints
  | step (parent child root : Nat × Nat)
      (edge : IsBksDescentStep Q Delta word parent child)
      (tail : IsBksDescentChain Q Delta word child root) :
      IsBksDescentChain Q Delta word parent root

/-- Early roots are actual maximal intervals, not words with an invented endpoint bound. -/
def earlyBksRoots {Alphabet : Type*} [DecidableEq Alphabet]
    (Q : Nat) (Delta : Finset Alphabet) (word : Nat -> Alphabet) : Set (Nat × Nat) :=
  {endpoints | IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
    endpoints.1 < 2 * Q ^ 2}

/-- Literal words of the non-early terminal intervals. -/
def lateBksRootWords {Alphabet : Type*} [DecidableEq Alphabet]
    (Q : Nat) (Delta : Finset Alphabet) (word : Nat -> Alphabet) : Set (List Alphabet) :=
  {xs | exists endpoints : Nat × Nat,
    IsMaximalDeltaInterval Delta word endpoints.1 endpoints.2 /\
      IsBksRoot Q endpoints /\ 2 * Q ^ 2 <= endpoints.1 /\
      xs = intervalWord word endpoints}

/-- The two literal edge contexts occurring in actual BKS descent steps. -/
def bksContextPairs {Alphabet : Type*} [DecidableEq Alphabet]
    (Q : Nat) (Delta : Finset Alphabet) (word : Nat -> Alphabet) :
    Set (List Alphabet × List Alphabet) :=
  {contexts | exists parent child : Nat × Nat,
    IsBksDescentStep Q Delta word parent child /\
      let centralFirst := Q * (child.1 + Q)
      let centralLast := Q * (child.2 - Q + 1) - 1
      contexts = (intervalWord word (parent.1, centralFirst - 1),
        intervalWord word (centralLast + 1, parent.2))}

private theorem maximal_interval_eq_of_same_first
    {Alphabet : Type*} [DecidableEq Alphabet]
    {Delta : Finset Alphabet} {word : Nat -> Alphabet} {a b : Nat × Nat}
    (ha : IsMaximalDeltaInterval Delta word a.1 a.2)
    (hb : IsMaximalDeltaInterval Delta word b.1 b.2) (hfirst : a.1 = b.1) : a = b := by
  rcases a with ⟨first, lastA⟩
  rcases b with ⟨firstB, lastB⟩
  simp only at hfirst
  subst firstB
  rcases ha with ⟨haOrder, haInside, _haLeft, haRight⟩
  rcases hb with ⟨hbOrder, hbInside, _hbLeft, hbRight⟩
  congr 1
  apply le_antisymm
  · by_contra hnot
    have hlt : lastB < lastA := Nat.lt_of_not_ge hnot
    exact hbRight (haInside (lastB + 1) (by omega) (by omega))
  · by_contra hnot
    have hlt : lastA < lastB := Nat.lt_of_not_ge hnot
    exact haRight (hbInside (lastA + 1) (by omega) (by omega))

/-- Iterating the reviewed BKS predecessor reaches a genuine root.  Away from
the finitely many early starts, the root word has the explicit uniform length
bound `Q * (Q^2 + 2Q)`.  Every edge carries the literal left and right contexts,
each of length at most `2Q^2`, in `IsBksDescentStep`.  The same stabilizing
power and its fixed-word/support data are returned for downstream boundary
transport; no second existential power choice is needed. -/
theorem exists_bounded_root_descent_chain
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (uniform : forall a, (morphism a).length = P) (word : Nat -> Alphabet)
    (fixed : forall (i : Nat) (offset : Fin P),
      word (P * i + offset) = uniformLetter morphism uniform (word i) offset) :
    exists q : Nat, 0 < q /\
      let Q := P ^ q
      let g : Alphabet -> List Alphabet := fun a => morphismPower morphism q [a]
      exists gUniform : forall a, (g a).length = Q,
        (forall (i : Nat) (offset : Fin Q),
          word (Q * i + offset) = uniformLetter g gUniform (word i) offset) /\
        (forall a, (morphismPower g 2 [a]).toFinset = (g a).toFinset) /\
        (forall Delta : Finset Alphabet, (earlyBksRoots Q Delta word).Finite) /\
        (forall Delta : Finset Alphabet, (lateBksRootWords Q Delta word).Finite) /\
        (forall Delta : Finset Alphabet, (bksContextPairs Q Delta word).Finite) /\
        forall (Delta : Finset Alphabet) (first last : Nat),
          IsMaximalDeltaInterval Delta word first last ->
          exists root : Nat × Nat,
            IsBksDescentChain Q Delta word (first, last) root /\
            IsMaximalDeltaInterval Delta word root.1 root.2 /\
            IsBksRoot Q root /\
            (root.1 < 2 * Q ^ 2 \/
              root.2 + 1 - root.1 <= Q * (Q ^ 2 + 2 * Q)) := by
  obtain ⟨q, hq, powerData⟩ :=
    exists_uniform_power_bks11_bks12_evolution P hP morphism uniform word fixed
  dsimp only at powerData
  rcases powerData with ⟨gUniform, gFixed, gSupport, evolution⟩
  refine ⟨q, hq, ?_⟩
  dsimp only
  let Q := P ^ q
  have hQ : 1 < Q := by
    dsimp [Q]
    exact one_lt_pow' hP hq.ne'
  have hQ0 : 0 < Q := by omega
  refine ⟨gUniform, gFixed, gSupport, ?_, ?_, ?_, ?_⟩
  · intro Delta
    apply Set.Finite.of_finite_image (f := fun endpoints : Nat × Nat => endpoints.1)
    · apply (Set.finite_lt_nat (2 * Q ^ 2)).subset
      rintro first ⟨endpoints, hEndpoints, rfl⟩
      exact hEndpoints.2
    · intro a ha b hb hfirst
      exact maximal_interval_eq_of_same_first ha.1 hb.1 hfirst
  · intro Delta
    apply (List.finite_length_le Alphabet (Q * (Q ^ 2 + 2 * Q))).subset
    intro xs hxs
    rcases hxs with ⟨endpoints, _block, terminal, notEarly, rfl⟩
    change IsBksRoot Q endpoints at terminal
    change 2 * Q ^ 2 <= endpoints.1 at notEarly
    have hLength : endpoints.2 + 1 - endpoints.1 <= Q * (Q ^ 2 + 2 * Q) := by
      rcases terminal with early | shortOrNarrow
      · have hDivUpper : endpoints.1 < Q * (endpoints.1 / Q + 1) := by
          simpa [Nat.mul_comm] using
            (Nat.div_lt_iff_lt_mul hQ0).mp (Nat.lt_succ_self (endpoints.1 / Q))
        have hQuotient : endpoints.1 / Q + 1 <= 2 * Q := by omega
        have : endpoints.1 < 2 * Q ^ 2 := by
          calc
            endpoints.1 < Q * (endpoints.1 / Q + 1) := hDivUpper
            _ <= Q * (2 * Q) := Nat.mul_le_mul_left Q hQuotient
            _ = 2 * Q ^ 2 := by ring
        omega
      · rcases shortOrNarrow with short | narrow
        · exact short.trans (by nlinarith)
        · have hFirstLower : Q * (endpoints.1 / Q) <= endpoints.1 :=
            Nat.mul_div_le endpoints.1 Q
          have hLastUpper : endpoints.2 < Q * (endpoints.2 / Q + 1) := by
            simpa [Nat.mul_comm] using
              (Nat.div_lt_iff_lt_mul hQ0).mp (Nat.lt_succ_self (endpoints.2 / Q))
          calc
            endpoints.2 + 1 - endpoints.1 <=
                Q * (endpoints.2 / Q + 1) - Q * (endpoints.1 / Q) := by omega
            _ = Q * (endpoints.2 / Q + 1 - endpoints.1 / Q) := by
              rw [Nat.mul_sub_left_distrib]
            _ <= Q * (Q ^ 2 + 2 * Q) := Nat.mul_le_mul_left Q narrow
    simpa [intervalWord] using hLength
  · intro Delta
    apply (Set.Finite.prod (List.finite_length_le Alphabet (2 * Q ^ 2))
      (List.finite_length_le Alphabet (2 * Q ^ 2))).subset
    rintro ⟨leftContext, rightContext⟩ hContexts
    rcases hContexts with ⟨parent, child, step, hContexts⟩
    change IsBksDescentStep Q Delta word parent child at step
    dsimp only at hContexts
    rw [hContexts]
    dsimp [IsBksDescentStep] at step
    rcases step with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      leftContextBound, rightContextBound⟩
    change
      (intervalWord word (parent.1, Q * (child.1 + Q) - 1)).length <= 2 * Q ^ 2 /\
      (intervalWord word (Q * (child.2 - Q + 1) - 1 + 1, parent.2)).length <=
        2 * Q ^ 2
    exact ⟨leftContextBound, rightContextBound⟩
  intro Delta first last block
  induction last using Nat.strong_induction_on generalizing first with
  | h last ih =>
      by_cases early : first / Q < 2 * Q
      · refine ⟨(first, last), .root _ block (Or.inl early), block, Or.inl early, ?_⟩
        left
        have hDivUpper : first < Q * (first / Q + 1) := by
          simpa [Nat.mul_comm] using
            (Nat.div_lt_iff_lt_mul hQ0).mp (Nat.lt_succ_self (first / Q))
        have hQuotient : first / Q + 1 <= 2 * Q := by omega
        have hBound : first < 2 * Q ^ 2 := by
          calc
            first < Q * (first / Q + 1) := hDivUpper
            _ <= Q * (2 * Q) := Nat.mul_le_mul_left Q hQuotient
            _ = 2 * Q ^ 2 := by ring
        simpa [Q] using hBound
      · have late : 2 * Q <= first / Q := Nat.le_of_not_gt early
        by_cases short : last + 1 - first <= 2 * Q ^ 2
        · refine ⟨(first, last), .root _ block (Or.inr (Or.inl short)), block,
            Or.inr (Or.inl short), ?_⟩
          right
          have hBound : last + 1 - first <= Q * (Q ^ 2 + 2 * Q) :=
            short.trans (by nlinarith)
          simpa [Q] using hBound
        · have long : 2 * Q ^ 2 < last + 1 - first := Nat.lt_of_not_ge short
          by_cases narrow : last / Q + 1 - first / Q <= Q ^ 2 + 2 * Q
          · refine ⟨(first, last), .root _ block (Or.inr (Or.inr narrow)), block,
              Or.inr (Or.inr narrow), ?_⟩
            right
            have hFirstLower : Q * (first / Q) <= first := Nat.mul_div_le first Q
            have hLastUpper : last < Q * (last / Q + 1) := by
              simpa [Nat.mul_comm] using
                (Nat.div_lt_iff_lt_mul hQ0).mp (Nat.lt_succ_self (last / Q))
            calc
              last + 1 - first <= Q * (last / Q + 1) - Q * (first / Q) := by omega
              _ = Q * (last / Q + 1 - first / Q) := by
                rw [Nat.mul_sub_left_distrib]
              _ <= Q * (Q ^ 2 + 2 * Q) := Nat.mul_le_mul_left Q narrow
          · have span : Q ^ 2 + 2 * Q < last / Q + 1 - first / Q :=
              Nat.lt_of_not_ge narrow
            obtain ⟨child, childBlock, childLeftLower, childLeftUpper,
                childRightLower, childRightUpper, childLate, childLong,
                childDescent, _childUnique, returned⟩ :=
              evolution Delta first last block late long span
            rcases returned with ⟨firstCentral, _centralFirstBound, centralInside,
              _leftWitness, _rightWitness, returnedBlock, _returnUnique⟩
            rcases returnedBlock with ⟨_, returnedLower, _, returnedCentralLast,
              returnedUpper⟩
            let centralFirst := Q * (child.1 + Q)
            let centralLast := Q * (child.2 - Q + 1) - 1
            have centralOrder : centralFirst <= centralLast := by
              have hTwoQ : 2 * Q <= Q ^ 2 := by nlinarith
              have hSourceOrder : child.1 + Q <= child.2 - Q := by
                have hLength : 2 * Q < child.2 + 1 - child.1 :=
                  hTwoQ.trans_lt childLong
                omega
              have hmul : Q * (child.1 + Q) < Q * (child.2 - Q + 1) := by
                apply Nat.mul_lt_mul_of_pos_left _ hQ0
                omega
              dsimp [centralFirst, centralLast]
              omega
            have leftContextBound :
                (intervalWord word (first, centralFirst - 1)).length <= 2 * Q ^ 2 := by
              have returnedLowerQ : Q * (child.1 - Q) < first := by
                simpa [Q] using returnedLower
              have hChildSplit : child.1 - Q + Q = child.1 :=
                Nat.sub_add_cancel (Nat.le_of_lt childLate)
              have hWindow : centralFirst = Q * (child.1 - Q) + 2 * Q ^ 2 := by
                dsimp [centralFirst]
                conv_lhs => rw [← hChildSplit]
                ring
              simp only [intervalWord, List.length_ofFn]
              have hCentralPositive : 0 < centralFirst := by
                dsimp [centralFirst]
                positivity
              rw [Nat.sub_add_cancel hCentralPositive]
              apply Nat.sub_le_iff_le_add.mpr
              rw [hWindow]
              omega
            have rightContextBound :
                (intervalWord word (centralLast + 1, last)).length <= 2 * Q ^ 2 := by
              have returnedUpperQ : last < Q * (child.2 + Q + 1) := by
                simpa [Q] using returnedUpper
              have hQLeChildLast : Q <= child.2 := by omega
              have hChildSplit : child.2 - Q + Q = child.2 :=
                Nat.sub_add_cancel hQLeChildLast
              have hCentralSucc : centralLast + 1 = Q * (child.2 - Q + 1) := by
                dsimp [centralLast]
                have hPositive : 0 < Q * (child.2 - Q + 1) := by positivity
                omega
              have hWindow : Q * (child.2 + Q + 1) =
                  Q * (child.2 - Q + 1) + 2 * Q ^ 2 := by
                conv_lhs => rw [← hChildSplit]
                ring
              simp only [intervalWord, List.length_ofFn]
              rw [hCentralSucc]
              apply Nat.sub_le_iff_le_add.mpr
              calc
                last + 1 <= Q * (child.2 + Q + 1) := returnedUpperQ
                _ = Q * (child.2 - Q + 1) + 2 * Q ^ 2 := hWindow
                _ = 2 * Q ^ 2 + Q * (child.2 - Q + 1) := Nat.add_comm _ _
            have edge : IsBksDescentStep Q Delta word (first, last) child := by
              dsimp [IsBksDescentStep]
              exact ⟨block, childBlock, childLeftLower, childLeftUpper,
                childRightLower, childRightUpper, childLate, childLong, childDescent,
                returnedLower, returnedUpper, firstCentral, centralOrder,
                returnedCentralLast, centralInside,
                leftContextBound, rightContextBound⟩
            obtain ⟨root, tail, rootBlock, rootTerminal, rootBound⟩ :=
              ih child.2 childDescent child.1 childBlock
            exact ⟨root, .step _ child root edge tail, rootBlock, rootTerminal, rootBound⟩

end Raney
end TrureTuring
