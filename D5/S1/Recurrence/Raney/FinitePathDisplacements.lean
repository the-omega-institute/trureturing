/- GID: D5/S1/Recurrence/Raney/FinitePathDisplacements
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/FinitePathDisplacements
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial-normalized signed displacements on finite actual BKS paths. -/

import D5.S1.Recurrence.Raney.BoundaryPivotTransport

namespace TrureTuring
namespace Raney

/-- One support-stabilizing power simultaneously supplies bounded actual BKS
roots and a factorial-normalized displacement period on every sufficiently
long finite actual path.  With `S` paired pivot states and `T = S!`, the
window at `j + T` uses only the two edges numbered `j + T` and `j + T + 1`;
the strict bound `j + T < n` therefore consumes no edge beyond `n`. -/
theorem exists_bounded_root_and_finite_path_displacements
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
        (forall (Delta : Finset Alphabet) (first last : Nat),
          IsMaximalDeltaInterval Delta word first last ->
          exists root : Nat × Nat,
            IsBksDescentChain Q Delta word (first, last) root /\
            IsMaximalDeltaInterval Delta word root.1 root.2 /\
            IsBksRoot Q root /\
            (root.1 < 2 * Q ^ 2 \/
              root.2 + 1 - root.1 <= Q * (Q ^ 2 + 2 * Q))) /\
        let S := Nat.card (Alphabet × Alphabet)
        let T := S.factorial
        0 < T /\
          forall (Delta : Finset Alphabet) (blocks : Nat -> Nat × Nat) (n : Nat),
            (forall k, k < n + 1 ->
              IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k)) ->
            forall j, S <= j -> j + T < n ->
              (((blocks (j + T + 2)).1 : Int) -
                    Q * ((blocks (j + T + 1)).1 : Int) =
                  ((blocks (j + 2)).1 : Int) - Q * ((blocks (j + 1)).1 : Int)) /\
                ((((blocks (j + T + 2)).2 + 1 : Nat) : Int) -
                    Q * (((blocks (j + T + 1)).2 + 1 : Nat) : Int) =
                  (((blocks (j + 2)).2 + 1 : Nat) : Int) -
                    Q * (((blocks (j + 1)).2 + 1 : Nat) : Int)) := by
  obtain ⟨q, hq, powerData⟩ :=
    exists_bounded_root_descent_chain P hP morphism uniform word fixed
  dsimp only at powerData
  rcases powerData with
    ⟨gUniform, gFixed, gSupport, earlyRoots, lateRootWords, contextPairs, roots⟩
  refine ⟨q, hq, ?_⟩
  dsimp only
  refine ⟨gUniform, gFixed, gSupport, earlyRoots, lateRootWords, contextPairs, roots, ?_⟩
  let S := Nat.card (Alphabet × Alphabet)
  let T := S.factorial
  refine ⟨Nat.factorial_pos S, ?_⟩
  intro Delta blocks n chain j hSj hjn
  change S <= j at hSj
  change j + T < n at hjn
  let Q := P ^ q
  let state : Nat -> Alphabet × Alphabet := fun k =>
    actualBksPivotState Q word (blocks (k + 1))
  obtain ⟨stateStep, displacementOfStates⟩ :=
    actual_bks_pivot_state_dynamics_at_power
      P hP morphism word q hq gUniform gFixed gSupport Delta blocks
  have validAt (k : Nat) (hk : k < n) :
      IsBksDescentStep Q Delta word (blocks (k + 2)) (blocks (k + 1)) /\
        IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k) := by
    exact ⟨chain (k + 1) (by omega), chain k (by omega)⟩
  let _ : Fintype Alphabet := Fintype.ofFinite Alphabet
  obtain ⟨x, y, hxy, hcollision⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (S + 1) => state k) (by simp [S, Nat.card_eq_fintype_card])
  let a := min (x : Nat) (y : Nat)
  let b := max (x : Nat) (y : Nat)
  have hxyVal : (x : Nat) ≠ (y : Nat) := by
    exact fun h => hxy (Fin.ext h)
  have hab : a < b := by
    dsimp [a, b]
    omega
  have hcollision' : state a = state b := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hle : (x : Nat) <= (y : Nat) := by exact_mod_cast hlt.le
      simpa [a, b, Nat.min_eq_left hle, Nat.max_eq_right hle] using hcollision
    · have hle : (y : Nat) <= (x : Nat) := by exact_mod_cast hgt.le
      simpa [a, b, Nat.min_eq_right hle, Nat.max_eq_left hle] using hcollision.symm
  have hbS : b <= S := by
    have hxBound := x.isLt
    have hyBound := y.isLt
    dsimp [b]
    omega
  let p := b - a
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hbp : b = a + p := by
    dsimp [p]
    omega
  have hpS : p <= S := by omega
  obtain ⟨m, hm⟩ := Nat.dvd_factorial hp hpS
  have hT : T = p * m := by
    simpa [T] using hm
  have hTarget : j + T + 1 <= n := by
    exact Nat.succ_le_iff.mpr hjn
  have statesRepeat : forall t, b + t <= j + T + 1 ->
      state (a + t) = state (b + t) := by
    intro t ht
    induction t with
    | zero => simpa using hcollision'
    | succ t ih =>
        have htPrev : b + t <= j + T + 1 := by omega
        have hbt : b + t < n := by omega
        have hat : a + t < n := by omega
        have hnext := stateStep (validAt (a + t) hat) (validAt (b + t) hbt)
          (ih htPrev)
        simpa [state, Q, Nat.add_assoc] using hnext
  have periodicAt (k : Nat) (hak : a <= k) (hupper : k + p <= j + T + 1) :
      state k = state (k + p) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hak
    have hrepetition := statesRepeat t (by omega)
    rw [hbp] at hrepetition
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrepetition
  have repeatPeriod (base : Nat) (hbase : a <= base) :
      forall r, r <= m -> base + p * r <= j + T + 1 ->
        state base = state (base + p * r) := by
    intro r hr hbound
    induction r with
    | zero => simp
    | succ r ih =>
        have hrm : r <= m := le_trans (Nat.le_succ r) hr
        have hmul : p * r <= p * (r + 1) :=
          Nat.mul_le_mul_left p (Nat.le_succ r)
        have hprevBound : base + p * r <= j + T + 1 :=
          (Nat.add_le_add_left hmul base).trans hbound
        calc
          state base = state (base + p * r) := ih hrm hprevBound
          _ = state ((base + p * r) + p) :=
            periodicAt (base + p * r) (hbase.trans (Nat.le_add_right _ _)) (by
              rw [Nat.mul_succ] at hbound
              simpa [Nat.add_assoc] using hbound)
          _ = state (base + p * (r + 1)) := by rw [Nat.mul_succ, Nat.add_assoc]
  have haj : a <= j := by omega
  have hcurrentRaw := repeatPeriod j haj m le_rfl (by rw [← hT]; omega)
  have hfollowingRaw := repeatPeriod (j + 1) (by omega) m le_rfl (by
    rw [← hT]
    omega)
  have hcurrent : state j = state (j + T) := by
    simpa [hT] using hcurrentRaw
  have hfollowing : state (j + 1) = state (j + T + 1) := by
    simpa [hT, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfollowingRaw
  have hdisplacement := displacementOfStates (validAt j (by omega))
    (validAt (j + T) hjn) hcurrent (by
      simpa [state, Q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfollowing)
  simpa [Q, T, S, Nat.card_eq_fintype_card, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using
    And.intro hdisplacement.1.symm hdisplacement.2.symm

/-- For one actual fixed word and one letter set, every maximal-block length
belongs to one finite family of rational `P`-power forms.  The finite set of
triples is chosen before the interval; membership does not assert that every
triple is attained. -/
theorem exists_finite_actual_maximal_block_coefficient_families
    {Alphabet : Type*} [Finite Alphabet] [DecidableEq Alphabet]
    (P : Nat) (hP : 1 < P) (morphism : Alphabet -> List Alphabet)
    (uniform : forall a, (morphism a).length = P) (word : Nat -> Alphabet)
    (fixed : forall (i : Nat) (offset : Fin P),
      word (P * i + offset) = uniformLetter morphism uniform (word i) offset) :
    forall Delta : Finset Alphabet,
      exists coefficients : Finset (Int × Int × Nat),
        (∀ abc ∈ coefficients, 0 < abc.2.2) /\
        forall first last : Nat, IsMaximalDeltaInterval Delta word first last ->
          ∃ abc ∈ coefficients, ∃ m : Nat,
            (abc.2.2 : Int) * ((last + 1 - first : Nat) : Int) =
              abc.1 * (P : Int) ^ m + abc.2.1 := by
  obtain ⟨q, hq, powerData⟩ :=
    exists_bounded_root_and_finite_path_displacements
      P hP morphism uniform word fixed
  dsimp only at powerData
  rcases powerData with
    ⟨gUniform, gFixed, gSupport, earlyFinite, lateFinite, contextFinite,
      roots, periodPositive, periodicDisplacements⟩
  intro Delta
  let Q := P ^ q
  let S := Nat.card (Alphabet × Alphabet)
  let T := S.factorial
  let A := Q ^ T
  let N := S + 1
  have hQ : 1 < Q := by
    dsimp [Q]
    exact one_lt_pow' hP hq.ne'
  have hT : 0 < T := by
    simpa [T, S] using periodPositive
  have hA : 1 < A := by
    dsimp [A]
    exact one_lt_pow' hQ hT.ne'
  let rootLengths : Finset Int :=
    ((earlyFinite Delta).toFinset.image fun endpoints =>
        ((endpoints.2 + 1 - endpoints.1 : Nat) : Int)) ∪
      ((lateFinite Delta).toFinset.image fun xs => (xs.length : Int))
  let correctionOfContext : List Alphabet × List Alphabet -> Int := fun contexts =>
    (contexts.1.length : Int) + (contexts.2.length : Int) - 2 * (Q : Int) ^ 2
  let corrections : Finset Int :=
    (contextFinite Delta).toFinset.image correctionOfContext
  let possibleLengths : Nat -> Finset Int := fun n =>
    Nat.rec rootLengths
      (fun _ previous =>
        (previous ×ˢ corrections).image fun value =>
          (Q : Int) * value.1 + value.2) n
  let correctionSums : Nat -> Finset Int := fun n =>
    Nat.rec {0}
      (fun _ previous =>
        (previous ×ˢ corrections).image fun value =>
          (Q : Int) * value.1 + value.2) n
  let boundedLengths : Finset Int :=
    (Finset.range (N + T + 1)).biUnion possibleLengths
  let constantCoefficients : Finset (Int × Int × Nat) :=
    boundedLengths.image fun length => (0, length, 1)
  let periodicCoefficients : Finset (Int × Int × Nat) :=
    (boundedLengths ×ˢ correctionSums T).image fun value =>
      (((A : Int) - 1) * value.1 + value.2, -value.2, A - 1)
  let coefficients := constantCoefficients ∪ periodicCoefficients
  refine ⟨coefficients, ?_, ?_⟩
  · intro abc habc
    rw [Finset.mem_union] at habc
    rcases habc with hconstant | hperiodic
    · rcases Finset.mem_image.mp hconstant with ⟨length, _, rfl⟩
      simp
    · rcases Finset.mem_image.mp hperiodic with ⟨value, _, rfl⟩
      dsimp
      omega
  intro first last block
  obtain ⟨root, chain, rootBlock, rootTerminal, rootBound⟩ :=
    roots Delta first last block
  have indexedPath {target root : Nat × Nat}
      (path : IsBksDescentChain Q Delta word target root) :
      exists n : Nat, exists blocks : Nat -> Nat × Nat,
        blocks 0 = root /\ blocks n = target /\
          forall k, k < n ->
            IsBksDescentStep Q Delta word (blocks (k + 1)) (blocks k) := by
    induction path with
    | root endpoints endpointBlock terminal =>
        exact ⟨0, fun _ => endpoints, rfl, rfl, by intro k hk; omega⟩
    | step parent child root edge tail ih =>
        rcases ih with ⟨n, blocks, hblocksRoot, hblocksChild, hblocksEdges⟩
        let blocks' : Nat -> Nat × Nat := fun k =>
          if k <= n then blocks k else parent
        refine ⟨n + 1, blocks', ?_, ?_, ?_⟩
        · simp [blocks', hblocksRoot]
        · simp [blocks']
        · intro k hk
          by_cases hkn : k < n
          · have hk1 : k + 1 <= n := by omega
            simpa [blocks', Nat.le_of_lt hkn, hk1] using hblocksEdges k hkn
          · have hkeq : k = n := by omega
            subst k
            simpa [blocks', hblocksChild] using edge
  obtain ⟨n, blocks, hblocksRoot, hblocksTarget, edges⟩ := indexedPath chain
  let lengthAt : Nat -> Int := fun k =>
    (((blocks k).2 + 1 - (blocks k).1 : Nat) : Int)
  let correction : Nat -> Int := fun k =>
    ((((blocks (k + 1)).2 + 1 : Nat) : Int) -
        (Q : Int) * (((blocks k).2 + 1 : Nat) : Int)) -
      (((blocks (k + 1)).1 : Int) - (Q : Int) * ((blocks k).1 : Int))
  have rootLengthMem : lengthAt 0 ∈ rootLengths := by
    dsimp [lengthAt]
    rw [hblocksRoot]
    by_cases early : root.1 < 2 * Q ^ 2
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨root, ?_, rfl⟩
      simp only [Set.Finite.mem_toFinset]
      exact ⟨rootBlock, early⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨intervalWord word root, ?_, ?_⟩
      · simp only [Set.Finite.mem_toFinset]
        refine ⟨root, rootBlock, rootTerminal, ?_, rfl⟩
        change 2 * Q ^ 2 ≤ root.1
        omega
      · simp [intervalWord]
  have edgeData (k : Nat) (hk : k < n) :
      lengthAt (k + 1) = (Q : Int) * lengthAt k + correction k /\
        correction k ∈ corrections := by
    have edge := edges k hk
    have edgeCopy := edge
    dsimp [IsBksDescentStep] at edgeCopy
    rcases edgeCopy with
      ⟨parentBlock, childBlock, _childLeftLower, _childLeftUpper,
        _childRightLower, _childRightUpper, childLate, _childLong,
        _childDescent, _returnedLower, _returnedUpper, parentCentralFirst,
        centralOrder, centralParentLast, _centralInside,
        _leftContextBound, _rightContextBound⟩
    let parent := blocks (k + 1)
    let child := blocks k
    let centralFirst := Q * (child.1 + Q)
    let centralLast := Q * (child.2 - Q + 1) - 1
    change IsMaximalDeltaInterval Delta word parent.1 parent.2 at parentBlock
    change IsMaximalDeltaInterval Delta word child.1 child.2 at childBlock
    change Q < child.1 at childLate
    change parent.1 ≤ centralFirst at parentCentralFirst
    change centralFirst ≤ centralLast at centralOrder
    change centralLast ≤ parent.2 at centralParentLast
    have parentOrder : parent.1 <= parent.2 := parentBlock.1
    have childOrder : child.1 <= child.2 := childBlock.1
    have hQChildLast : Q <= child.2 := by omega
    have centralPositive : 0 < Q * (child.2 - Q + 1) := by positivity
    have centralLastSucc : centralLast + 1 = Q * (child.2 - Q + 1) := by
      dsimp [centralLast]
      exact Nat.sub_add_cancel centralPositive
    have leftLength :
        (intervalWord word (parent.1, centralFirst - 1)).length =
          centralFirst - parent.1 := by
      simp only [intervalWord, List.length_ofFn]
      rw [Nat.sub_add_cancel (by positivity : 0 < centralFirst)]
    have rightLength :
        (intervalWord word (centralLast + 1, parent.2)).length =
          parent.2 + 1 - (centralLast + 1) := by
      simp only [intervalWord, List.length_ofFn]
    have childSplit : child.2 - Q + Q = child.2 :=
      Nat.sub_add_cancel hQChildLast
    have contextCorrection :
        correction k = correctionOfContext
          (intervalWord word (parent.1, centralFirst - 1),
            intervalWord word (centralLast + 1, parent.2)) := by
      have hParentFirstCast :
          ((centralFirst - parent.1 : Nat) : Int) =
            (centralFirst : Int) - (parent.1 : Int) := by
        exact Int.ofNat_sub parentCentralFirst
      have hParentLastCast :
          ((parent.2 + 1 - (centralLast + 1) : Nat) : Int) =
            ((parent.2 + 1 : Nat) : Int) - (((centralLast + 1 : Nat) : Int)) := by
        apply Int.ofNat_sub
        omega
      dsimp [correction, correctionOfContext, parent, child]
      rw [leftLength, rightLength, hParentFirstCast, hParentLastCast]
      rw [centralLastSucc]
      push_cast
      have hChildLast : (((child.2 - Q : Nat) : Int)) =
          (child.2 : Int) - (Q : Int) := by
        exact Int.ofNat_sub hQChildLast
      rw [hChildLast]
      dsimp [centralFirst, parent, child]
      ring
    constructor
    · have hParentLengthCast :
          ((parent.2 + 1 - parent.1 : Nat) : Int) =
            ((parent.2 + 1 : Nat) : Int) - (parent.1 : Int) := by
        exact Int.ofNat_sub (by omega)
      have hChildLengthCast :
          ((child.2 + 1 - child.1 : Nat) : Int) =
            ((child.2 + 1 : Nat) : Int) - (child.1 : Int) := by
        exact Int.ofNat_sub (by omega)
      change ((parent.2 + 1 - parent.1 : Nat) : Int) =
        (Q : Int) * ((child.2 + 1 - child.1 : Nat) : Int) +
          ((((parent.2 + 1 : Nat) : Int) -
              (Q : Int) * (((child.2 + 1 : Nat) : Int))) -
            ((parent.1 : Int) - (Q : Int) * (child.1 : Int)))
      rw [hParentLengthCast, hChildLengthCast]
      ring
    · rw [contextCorrection]
      apply Finset.mem_image.mpr
      refine ⟨(intervalWord word (parent.1, centralFirst - 1),
        intervalWord word (centralLast + 1, parent.2)), ?_, rfl⟩
      simp only [Set.Finite.mem_toFinset]
      refine ⟨parent, child, ?_, ?_⟩
      · simpa [parent, child] using edge
      · rfl
  have lengthMem : forall k, k <= n -> lengthAt k ∈ possibleLengths k := by
    intro k hk
    induction k with
    | zero => simpa [possibleLengths] using rootLengthMem
    | succ k ih =>
        have hk' : k < n := by omega
        obtain ⟨affine, correctionMem⟩ := edgeData k hk'
        simp only [possibleLengths]
        apply Finset.mem_image.mpr
        refine ⟨(lengthAt k, correction k), ?_, ?_⟩
        · exact Finset.mem_product.mpr ⟨ih (by omega), correctionMem⟩
        · simpa using affine.symm
  let segmentCorrection : Nat -> Nat -> Int := fun base r =>
    Nat.rec 0 (fun t value => (Q : Int) * value + correction (base + t)) r
  have segmentAffine (base r : Nat) (hupper : base + r <= n) :
      lengthAt (base + r) =
        (Q : Int) ^ r * lengthAt base + segmentCorrection base r := by
    induction r with
    | zero => simp [segmentCorrection]
    | succ r ih =>
        have hedge : base + r < n := by omega
        obtain ⟨affine, _⟩ := edgeData (base + r) hedge
        rw [Nat.add_succ, affine, ih (by omega)]
        simp only [segmentCorrection, pow_succ]
        ring
  have segmentCorrectionMem (base r : Nat) (hupper : base + r <= n) :
      segmentCorrection base r ∈ correctionSums r := by
    induction r with
    | zero => simp [segmentCorrection, correctionSums]
    | succ r ih =>
        have hedge : base + r < n := by omega
        have correctionMem := (edgeData (base + r) hedge).2
        simp only [segmentCorrection, correctionSums]
        apply Finset.mem_image.mpr
        exact ⟨(segmentCorrection base r, correction (base + r)),
          Finset.mem_product.mpr ⟨ih (by omega), correctionMem⟩, rfl⟩
  have correctionPeriodic (k : Nat) (hNk : N <= k) (hupper : k + T < n) :
      correction (k + T) = correction k := by
    have edgeWindow : forall r, r < (n - 1) + 1 ->
        IsBksDescentStep Q Delta word (blocks (r + 1)) (blocks r) := by
      intro r hr
      apply edges r
      omega
    have hperiodLower : S <= k - 1 := by
      dsimp [N] at hNk
      omega
    have hperiodUpper : k - 1 + T < n - 1 := by omega
    have hperiod := periodicDisplacements Delta blocks (n - 1)
      edgeWindow (k - 1) (by simpa [S] using hperiodLower)
      (by simpa [T, S] using hperiodUpper)
    rcases hperiod with ⟨leftPeriod, rightPeriod⟩
    have farNext : k - 1 + S.factorial + 2 = k + T + 1 := by
      dsimp [T]
      omega
    have farCurrent : k - 1 + S.factorial + 1 = k + T := by
      dsimp [T]
      omega
    have nearNext : k - 1 + 2 = k + 1 := by omega
    have nearCurrent : k - 1 + 1 = k := by omega
    rw [farNext, farCurrent, nearNext, nearCurrent] at leftPeriod rightPeriod
    dsimp [correction]
    have leftPeriod' :
        (((blocks (k + T + 1)).1 : Int) - (Q : Int) * ((blocks (k + T)).1 : Int)) =
          (((blocks (k + 1)).1 : Int) - (Q : Int) * ((blocks k).1 : Int)) := by
      simpa [Q, T, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using leftPeriod
    have rightPeriod' :
        ((((blocks (k + T + 1)).2 + 1 : Nat) : Int) -
            (Q : Int) * (((blocks (k + T)).2 + 1 : Nat) : Int)) =
          ((((blocks (k + 1)).2 + 1 : Nat) : Int) -
            (Q : Int) * (((blocks k).2 + 1 : Nat) : Int)) := by
      simpa [Q, T, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rightPeriod
    push_cast at rightPeriod'
    rw [leftPeriod', rightPeriod']
  have boundedMem (k : Nat) (hk : k <= n) (hbound : k <= N + T) :
      lengthAt k ∈ boundedLengths := by
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_range.mpr (by omega), lengthMem k hk⟩
  by_cases short : n <= N + T
  · let abc : Int × Int × Nat := (0, lengthAt n, 1)
    refine ⟨abc, ?_, 0, ?_⟩
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨lengthAt n, boundedMem n le_rfl short, rfl⟩
    · dsimp [abc, lengthAt]
      rw [hblocksTarget]
      simp
  · let r := (n - N) % T
    let m := (n - N) / T
    let start := N + r
    have hrT : r < T := Nat.mod_lt _ hT
    have hNn : N <= n := by omega
    have hnDecompose : n = start + T * m := by
      dsimp [start, r, m]
      have hdecompose := (Nat.mod_add_div (n - N) T).symm
      omega
    have hm : 0 < m := by
      by_contra hm0
      have : m = 0 := Nat.eq_zero_of_not_pos hm0
      rw [this, Nat.mul_zero, Nat.add_zero] at hnDecompose
      dsimp [start] at hnDecompose
      omega
    have hstartBound : start <= N + T := by
      dsimp [start]
      omega
    have hstartn : start <= n := by rw [hnDecompose]; omega
    let C := segmentCorrection start T
    have hCmem : C ∈ correctionSums T := by
      apply segmentCorrectionMem
      have hTm : T ≤ T * m := by
        simpa using Nat.mul_le_mul_left T (Nat.succ_le_iff.mpr hm)
      rw [hnDecompose]
      omega
    have hstartMem : lengthAt start ∈ boundedLengths :=
      boundedMem start hstartn hstartBound
    have shiftedCorrection (u t : Nat) (ht : t < T)
        (hwindow : start + u * T + t < n) :
        correction (start + u * T + t) = correction (start + t) := by
      induction u with
      | zero => simp
      | succ u ih =>
          have hprevious : start + u * T + t + T < n := by
            simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hwindow
          calc
            correction (start + (u + 1) * T + t) =
                correction ((start + u * T + t) + T) := by
                  simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
                    Nat.add_comm]
            _ = correction (start + u * T + t) :=
              correctionPeriodic _ (by dsimp [start, N]; omega) hprevious
            _ = correction (start + t) := ih (by omega)
    have segmentCorrection_congr (b c r : Nat)
        (hpointwise : forall t, t < r -> correction (b + t) = correction (c + t)) :
        segmentCorrection b r = segmentCorrection c r := by
      induction r with
      | zero => simp [segmentCorrection]
      | succ r ih =>
          change (Q : Int) * segmentCorrection b r + correction (b + r) =
            (Q : Int) * segmentCorrection c r + correction (c + r)
          rw [hpointwise r (by omega), ih (fun t ht => hpointwise t (by omega))]
    have shiftedSegmentCorrection (u : Nat) (hu : u < m) :
        segmentCorrection (start + u * T) T = C := by
      dsimp [C]
      have huT : (u + 1) * T ≤ m * T :=
        Nat.mul_le_mul_right T (Nat.succ_le_iff.mpr hu)
      have huT' : (u + 1) * T ≤ T * m := by
        simpa [Nat.mul_comm] using huT
      have pointwise : forall t, t < T ->
          correction (start + u * T + t) = correction (start + t) := by
        intro t ht
        apply shiftedCorrection u t ht
        have hut : u * T + t < (u + 1) * T := by
          rw [Nat.succ_mul]
          omega
        have hut' : u * T + t < T * m := hut.trans_le huT'
        rw [hnDecompose]
        omega
      exact segmentCorrection_congr _ _ _ pointwise
    have groupedStep (u : Nat) (hu : u < m) :
        lengthAt (start + (u + 1) * T) =
          (A : Int) * lengthAt (start + u * T) + C := by
      have huT : (u + 1) * T ≤ m * T :=
        Nat.mul_le_mul_right T (Nat.succ_le_iff.mpr hu)
      have huT' : (u + 1) * T ≤ T * m := by
        simpa [Nat.mul_comm] using huT
      have hwindow : start + u * T + T <= n := by
        have : u * T + T ≤ T * m := by
          rw [← Nat.succ_mul]
          exact huT'
        rw [hnDecompose]
        omega
      have affine := segmentAffine (start + u * T) T hwindow
      rw [shiftedSegmentCorrection u hu] at affine
      simpa [A, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using affine
    have groupedFormula : forall u, u <= m ->
        ((A : Int) - 1) * lengthAt (start + u * T) =
          (((A : Int) - 1) * lengthAt start + C) * (A : Int) ^ u - C := by
      intro u hu
      induction u with
      | zero => simp
      | succ u ih =>
          have hum : u < m := by omega
          rw [groupedStep u hum]
          calc
            ((A : Int) - 1) * ((A : Int) * lengthAt (start + u * T) + C) =
                (A : Int) * (((A : Int) - 1) * lengthAt (start + u * T)) +
                  ((A : Int) - 1) * C := by ring
            _ = (((A : Int) - 1) * lengthAt start + C) *
                  (A : Int) ^ (u + 1) - C := by
                    rw [ih (by omega), pow_succ]
                    ring
    let abc : Int × Int × Nat :=
      (((A : Int) - 1) * lengthAt start + C, -C, A - 1)
    refine ⟨abc, ?_, q * T * m, ?_⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(lengthAt start, C),
        Finset.mem_product.mpr ⟨hstartMem, hCmem⟩, rfl⟩
    · have formula := groupedFormula m le_rfl
      have hnm : n = start + m * T := by
        simpa [Nat.mul_comm] using hnDecompose
      rw [← hnm] at formula
      dsimp [lengthAt] at formula
      rw [hblocksTarget] at formula
      dsimp [abc, lengthAt] at formula ⊢
      have powerIdentity : (A : Int) ^ m = (P : Int) ^ (q * T * m) := by
        simp [A, Q, pow_mul]
      rw [powerIdentity] at formula
      simpa [sub_eq_add_neg,
        Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr (by omega : A ≠ 0))] using formula

end Raney
end TrureTuring
