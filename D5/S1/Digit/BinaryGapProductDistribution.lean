/- GID: D5/S1/Digit/BinaryGapProductDistribution
   generality: G
   mirror-B: D5/B/S1/Digit/BinaryGapProductDistribution
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.Nat.BitIndices]
   utility: none
   digest: Binary gap products are counted by ordered nonunit gaps and unit-gap insertions. -/

/- Library search (2026-09-06): searched D5 for bitIndices, gapProduct, binary gaps,
   and Zeckendorf; no binary-gap distribution result was found. The nearby
   MultiplicativeDigitInvariant and Zeckendorf modules concern different invariants.
   In pinned Mathlib, Nat.bitIndices and bitIndices_sum_map_two_pow supply binary
   decoding and its inverse. Composition and compositionEquiv enumerate positive
   compositions, but do not count nonunit-gap fibers. Nat.digits supplies digit
   lists, not gap lists. Finset.Nat.antidiagonalTuple enumerates fixed-sum tuples;
   Sym.card_sym_eq_choose supplies stars and bars for multisets. We use finite
   list insertions and Nat.sum_range_add_choose for the bounded-sum version.
   An external Lean/MO search returned no results in this environment.
-/

import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.BinaryGapProductDistribution

/-- Successive differences of a list of bit positions, in increasing order. -/
def gaps : List ℕ → List ℕ
  | first :: second :: rest => (second - first) :: gaps (second :: rest)
  | _ => []

/-- The product of successive differences of the binary set-bit positions. -/
def gapProduct (number : ℕ) : ℕ := (gaps number.bitIndices).prod

/-- Count the numbers with top set bit `n` and gap product `k`. -/
def gapProductCount (n k : ℕ) : ℕ :=
  ((Finset.Ico (2 ^ n) (2 ^ (n + 1))).filter fun number => gapProduct number = k).card

/-- Nonnegative lists with a prescribed length and bounded sum. -/
def unitPlacements : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | slots + 1, budget => (Finset.range (budget + 1)).biUnion fun first =>
      (unitPlacements slots (budget - first)).image (List.cons first)

theorem mem_unitPlacements (slots budget : ℕ) (counts : List ℕ) :
    counts ∈ unitPlacements slots budget ↔ counts.length = slots ∧ counts.sum ≤ budget := by
  induction slots generalizing budget counts with
  | zero => cases counts <;> simp [unitPlacements]
  | succ slots inductionHyp =>
    cases counts with
    | nil => simp [unitPlacements]
    | cons first rest =>
      simp only [unitPlacements, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
        List.cons.injEq, exists_eq_right_right, inductionHyp, List.length_cons, List.sum_cons]
      omega

theorem card_unitPlacements (slots budget : ℕ) :
    (unitPlacements slots budget).card = (budget + slots).choose slots := by
  induction slots generalizing budget with
  | zero => simp [unitPlacements]
  | succ slots inductionHyp =>
    rw [unitPlacements, Finset.card_biUnion]
    · simp_rw [Finset.card_image_of_injective _
        (fun _ _ equality => (List.cons.inj equality).2), inductionHyp]
      have reflection := Finset.sum_range_reflect
        (fun value => (value + slots).choose slots) (budget + 1)
      simp only [Nat.add_sub_cancel] at reflection
      rw [reflection, Nat.sum_range_add_choose]
      congr 1
    · intro first firstMem second secondMem distinct
      simp only [Finset.disjoint_left, Finset.mem_image]
      rintro counts ⟨rest, _, rfl⟩ ⟨other, _, equality⟩
      exact distinct (List.cons.inj equality).1.symm

/-- Delete unit gaps while recording the lengths of the intervening unit runs. -/
def splitUnits : List ℕ → List ℕ × List ℕ
  | [] => ([], [0])
  | first :: rest =>
      let previous := splitUnits rest
      if first = 1 then
        (previous.1, (previous.2.headD 0 + 1) :: previous.2.tail)
      else (first :: previous.1, 0 :: previous.2)

/-- Reinsert the recorded unit runs before, between, and after the nonunit gaps. -/
def insertUnits : List ℕ → List ℕ → List ℕ
  | [], counts => List.replicate (counts.headD 0) 1
  | first :: rest, counts =>
      List.replicate (counts.headD 0) 1 ++ first :: insertUnits rest counts.tail

theorem splitUnits_length (sequence : List ℕ) :
    (splitUnits sequence).2.length = (splitUnits sequence).1.length + 1 := by
  induction sequence with
  | nil => rfl
  | cons first rest inductionHyp =>
    simp only [splitUnits]
    split
    · simp only [List.length_cons, List.length_tail]
      omega
    · simpa using inductionHyp

private theorem splitUnits_counts_ne_nil (sequence : List ℕ) :
    (splitUnits sequence).2 ≠ [] := by
  have := splitUnits_length sequence
  intro equality
  rw [equality] at this
  simp at this

theorem splitUnits_nonunit (sequence : List ℕ) :
    (splitUnits sequence).1 = sequence.filter (· != 1) := by
  induction sequence with
  | nil => rfl
  | cons first rest inductionHyp =>
    by_cases unit : first = 1 <;> simp [splitUnits, unit, inductionHyp]

private theorem insertUnits_succ (sequence counts : List ℕ) (count : ℕ) :
    insertUnits sequence ((count + 1) :: counts) =
      1 :: insertUnits sequence (count :: counts) := by
  cases sequence <;> simp [insertUnits, List.replicate_succ]

private theorem headD_cons_tail (sequence : List ℕ) (nonempty : sequence ≠ []) :
    sequence.headD 0 :: sequence.tail = sequence := by
  cases sequence <;> simp_all

theorem insertUnits_splitUnits (sequence : List ℕ) :
    insertUnits (splitUnits sequence).1 (splitUnits sequence).2 = sequence := by
  induction sequence with
  | nil => rfl
  | cons first rest inductionHyp =>
    have nonempty := splitUnits_counts_ne_nil rest
    by_cases unit : first = 1
    · subst first
      simp only [splitUnits, ite_true]
      rw [insertUnits_succ]
      congr 1
      rw [headD_cons_tail _ nonempty]
      exact inductionHyp
    · simpa [splitUnits, unit, insertUnits] using congrArg (first :: ·) inductionHyp

private theorem splitUnits_replicate_append (count : ℕ) (sequence : List ℕ) :
    splitUnits (List.replicate count 1 ++ sequence) =
      ((splitUnits sequence).1,
        (count + (splitUnits sequence).2.headD 0) :: (splitUnits sequence).2.tail) := by
  induction count with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, zero_add]
    rw [headD_cons_tail _ (splitUnits_counts_ne_nil sequence)]
  | succ count inductionHyp =>
    simp [List.replicate_succ, splitUnits, inductionHyp, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

theorem splitUnits_insertUnits (sequence counts : List ℕ)
    (nonunit : ∀ gap ∈ sequence, gap ≠ 1)
    (lengths : counts.length = sequence.length + 1) :
    splitUnits (insertUnits sequence counts) = (sequence, counts) := by
  induction sequence generalizing counts with
  | nil =>
    obtain ⟨count, rfl⟩ := List.length_eq_one_iff.mp lengths
    simpa [insertUnits, splitUnits] using splitUnits_replicate_append count []
  | cons first rest inductionHyp =>
    cases counts with
    | nil => simp at lengths
    | cons count counts =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      have smaller := inductionHyp counts (fun gap member => nonunit gap (by simp [member]))
        lengths
      simp only [insertUnits, List.headD_cons, List.tail_cons]
      rw [splitUnits_replicate_append]
      simp [splitUnits, nonunit first (by simp), smaller]

theorem insertUnits_sum (sequence counts : List ℕ)
    (lengths : counts.length = sequence.length + 1) :
    (insertUnits sequence counts).sum = sequence.sum + counts.sum := by
  induction sequence generalizing counts with
  | nil =>
    obtain ⟨count, rfl⟩ := List.length_eq_one_iff.mp lengths
    simp [insertUnits]
  | cons first rest inductionHyp =>
    cases counts with
    | nil => simp at lengths
    | cons count counts =>
      have smaller : counts.length = rest.length + 1 := by simpa using lengths
      simp [insertUnits, inductionHyp counts smaller, Nat.add_assoc, Nat.add_left_comm]

theorem insertUnits_prod (sequence counts : List ℕ) :
    (insertUnits sequence counts).prod = sequence.prod := by
  induction sequence generalizing counts with
  | nil => simp [insertUnits]
  | cons first rest inductionHyp => simp [insertUnits, inductionHyp]

theorem insertUnits_positive (sequence counts : List ℕ)
    (positive : ∀ gap ∈ sequence, 0 < gap) :
    ∀ gap ∈ insertUnits sequence counts, 0 < gap := by
  induction sequence generalizing counts with
  | nil => simp [insertUnits]
  | cons first rest inductionHyp =>
    have firstPositive := positive first (by simp)
    have tailPositive := inductionHyp counts.tail
      (fun gap member => positive gap (by simp [member]))
    simpa [insertUnits, List.mem_append, List.mem_cons, or_imp, forall_and] using
      And.intro (by simp : ∀ gap ∈ List.replicate (counts.headD 0) 1, 0 < gap)
        (And.intro firstPositive tailPositive)

/-- All positive gap lists that fit below top bit `n`. -/
def gapSequences (n : ℕ) : Finset (List ℕ) :=
  ((Finset.range (n + 1)).biUnion fun slots => unitPlacements slots n).filter
    fun sequence => ∀ gap ∈ sequence, 0 < gap

private theorem length_le_sum (sequence : List ℕ)
    (positive : ∀ gap ∈ sequence, 0 < gap) : sequence.length ≤ sequence.sum := by
  induction sequence with
  | nil => simp
  | cons first rest inductionHyp =>
    have := inductionHyp (fun gap member => positive gap (by simp [member]))
    have := positive first (by simp)
    simp only [List.length_cons, List.sum_cons]
    omega

theorem mem_gapSequences (n : ℕ) (sequence : List ℕ) :
    sequence ∈ gapSequences n ↔ (∀ gap ∈ sequence, 0 < gap) ∧ sequence.sum ≤ n := by
  simp only [gapSequences, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    mem_unitPlacements]
  constructor
  · rintro ⟨⟨slots, _, _, bounded⟩, positive⟩
    exact ⟨positive, bounded⟩
  · rintro ⟨positive, bounded⟩
    exact ⟨⟨sequence.length, by have := length_le_sum sequence positive; omega,
      rfl, bounded⟩, positive⟩

/-- Ordered tuples of gaps at least two, with product `k` and sum at most `n`. -/
def reducedTuples (n k : ℕ) : Finset (List ℕ) :=
  (gapSequences n).filter fun sequence => (∀ gap ∈ sequence, 2 ≤ gap) ∧ sequence.prod = k

theorem mem_reducedTuples (n k : ℕ) (sequence : List ℕ) :
    sequence ∈ reducedTuples n k ↔
      (∀ gap ∈ sequence, 2 ≤ gap) ∧ sequence.prod = k ∧ sequence.sum ≤ n := by
  simp only [reducedTuples, Finset.mem_filter, mem_gapSequences]
  constructor
  · tauto
  · rintro ⟨nonunit, product, bounded⟩
    exact ⟨⟨fun gap member => by have := nonunit gap member; omega, bounded⟩,
      nonunit, product⟩

/-- Recover set-bit positions from the lowest position and the successive gaps. -/
def positions (lowest : ℕ) : List ℕ → List ℕ
  | [] => [lowest]
  | gap :: rest => lowest :: positions (lowest + gap) rest

theorem gaps_positions (lowest : ℕ) (sequence : List ℕ) :
    gaps (positions lowest sequence) = sequence := by
  induction sequence generalizing lowest with
  | nil => rfl
  | cons gap rest inductionHyp =>
    cases rest <;> simp_all [positions, gaps]

private theorem positions_bounds (lowest : ℕ) (sequence : List ℕ) :
    ∀ position ∈ positions lowest sequence,
      lowest ≤ position ∧ position ≤ lowest + sequence.sum := by
  induction sequence generalizing lowest with
  | nil => simp [positions]
  | cons gap rest inductionHyp =>
    intro position member
    simp only [positions, List.mem_cons] at member
    rcases member with rfl | member
    · simp
    · have := inductionHyp (lowest + gap) position member
      simp only [List.sum_cons]
      omega

private theorem positions_top_mem (lowest : ℕ) (sequence : List ℕ) :
    lowest + sequence.sum ∈ positions lowest sequence := by
  induction sequence generalizing lowest with
  | nil => simp [positions]
  | cons gap rest inductionHyp =>
    exact List.mem_cons_of_mem _ (by simpa [Nat.add_assoc] using inductionHyp (lowest + gap))

theorem positions_sorted (lowest : ℕ) (sequence : List ℕ)
    (positive : ∀ gap ∈ sequence, 0 < gap) :
    (positions lowest sequence).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  induction sequence generalizing lowest with
  | nil => simp [positions]
  | cons gap rest inductionHyp =>
    rw [positions, List.pairwise_cons]
    refine ⟨?_, inductionHyp (lowest + gap)
      (fun value member => positive value (by simp [member]))⟩
    intro position member
    have := (positions_bounds (lowest + gap) rest position member).1
    have := positive gap (by simp)
    omega

theorem positions_gaps (lowest : ℕ) (rest : List ℕ)
    (sorted : (lowest :: rest).SortedLT) :
    positions lowest (gaps (lowest :: rest)) = lowest :: rest := by
  induction rest generalizing lowest with
  | nil => rfl
  | cons second rest inductionHyp =>
    have pairwise := sorted.pairwise
    have smaller : lowest ≤ second :=
      Nat.le_of_lt ((List.pairwise_cons.mp pairwise).1 second (by simp))
    have tailSorted : (second :: rest).SortedLT := by
      exact List.sortedLT_iff_pairwise.mpr pairwise.tail
    simp only [gaps, positions]
    rw [Nat.add_sub_of_le smaller, inductionHyp second tailSorted]

theorem gaps_positive (bitPositions : List ℕ) (sorted : bitPositions.SortedLT) :
    ∀ gap ∈ gaps bitPositions, 0 < gap := by
  induction bitPositions with
  | nil => simp [gaps]
  | cons first rest inductionHyp =>
    cases rest with
    | nil => simp [gaps]
    | cons second rest =>
      have pairwise := List.pairwise_cons.mp sorted.pairwise
      have firstLess : first < second := pairwise.1 second (by simp)
      have tailPositive := inductionHyp (List.sortedLT_iff_pairwise.mpr pairwise.2)
      simp only [gaps, List.mem_cons, forall_eq_or_imp]
      exact ⟨by omega, tailPositive⟩

/-- Encode a gap sequence with top bit fixed at `n`. -/
def encodeGaps (n : ℕ) (sequence : List ℕ) : ℕ :=
  ((positions (n - sequence.sum) sequence).map (fun position => 2 ^ position)).sum

theorem bitIndices_encodeGaps (n : ℕ) (sequence : List ℕ)
    (positive : ∀ gap ∈ sequence, 0 < gap) :
    (encodeGaps n sequence).bitIndices = positions (n - sequence.sum) sequence :=
  Nat.bitIndices_sum_map_two_pow (positions_sorted _ _ positive)

theorem gaps_encodeGaps (n : ℕ) (sequence : List ℕ)
    (positive : ∀ gap ∈ sequence, 0 < gap) :
    gaps (encodeGaps n sequence).bitIndices = sequence := by
  rw [bitIndices_encodeGaps n sequence positive, gaps_positions]

private theorem binary_sum_lt (bitPositions : List ℕ) (sorted : bitPositions.SortedLT)
    (n : ℕ) (bounded : ∀ position ∈ bitPositions, position < n) :
    (bitPositions.map (fun position => 2 ^ position)).sum < 2 ^ n := by
  rw [← List.sum_toFinset _ sorted.nodup]
  exact Nat.geomSum_lt (by decide) (by simpa using bounded)

theorem encodeGaps_mem_interval (n : ℕ) (sequence : List ℕ)
    (member : sequence ∈ gapSequences n) :
    encodeGaps n sequence ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)) := by
  obtain ⟨positive, bounded⟩ := (mem_gapSequences n sequence).mp member
  have top : n - sequence.sum + sequence.sum = n := Nat.sub_add_cancel bounded
  apply Finset.mem_Ico.mpr
  constructor
  · apply Nat.two_pow_le_of_mem_bitIndices
    rw [bitIndices_encodeGaps n sequence positive]
    simpa only [top] using positions_top_mem (n - sequence.sum) sequence
  · apply binary_sum_lt _ (positions_sorted _ _ positive)
    intro position member
    have := (positions_bounds (n - sequence.sum) sequence position member).2
    omega

private theorem bitIndices_le_top (n number : ℕ)
    (upper : number < 2 ^ (n + 1)) :
    ∀ position ∈ number.bitIndices, position ≤ n := by
  intro position member
  have lower := Nat.two_pow_le_of_mem_bitIndices member
  by_contra notBounded
  have exponentBound : n + 1 ≤ position := by omega
  have powerBound := Nat.pow_le_pow_right (by decide : 0 < 2) exponentBound
  omega

private theorem top_mem_bitIndices (n number : ℕ)
    (member : number ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1))) : n ∈ number.bitIndices := by
  obtain ⟨lower, upper⟩ := Finset.mem_Ico.mp member
  by_contra absent
  have smaller := binary_sum_lt number.bitIndices Nat.bitIndices_sorted n (by
    intro position positionMem
    have := bitIndices_le_top n number upper position positionMem
    have : position ≠ n := by rintro rfl; exact absent positionMem
    omega)
  rw [Nat.sum_map_two_pow_bitIndices] at smaller
  omega

private theorem binary_positions (n number : ℕ)
    (member : number ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1))) :
    (gaps number.bitIndices).sum ≤ n ∧
      positions (n - (gaps number.bitIndices).sum) (gaps number.bitIndices) =
        number.bitIndices := by
  have topMem := top_mem_bitIndices n number member
  have bounded := bitIndices_le_top n number (Finset.mem_Ico.mp member).2
  have sorted : number.bitIndices.SortedLT := Nat.bitIndices_sorted
  cases equation : number.bitIndices with
  | nil => simp [equation] at topMem
  | cons lowest rest =>
    rw [equation] at topMem bounded sorted
    have reconstruction := positions_gaps lowest rest sorted
    have maximal := positions_top_mem lowest (gaps (lowest :: rest))
    rw [reconstruction] at maximal
    have maximumBound := bounded _ maximal
    have reverseBound := (positions_bounds lowest (gaps (lowest :: rest)) n
      (by rwa [reconstruction])).2
    have start : n - (gaps (lowest :: rest)).sum = lowest := by omega
    exact ⟨by omega, by rwa [start]⟩

theorem decodeGaps_mem (n number : ℕ)
    (member : number ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1))) :
    gaps number.bitIndices ∈ gapSequences n := by
  rw [mem_gapSequences]
  exact ⟨gaps_positive _ Nat.bitIndices_sorted, (binary_positions n number member).1⟩

theorem encodeGaps_decodeGaps (n number : ℕ)
    (member : number ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1))) :
    encodeGaps n (gaps number.bitIndices) = number := by
  rw [encodeGaps, (binary_positions n number member).2, Nat.sum_map_two_pow_bitIndices]

/-- The explicit bijection between bounded positive gap lists and the binary interval. -/
def gapSequenceEquiv (n : ℕ) :
    {sequence // sequence ∈ gapSequences n} ≃
      {number // number ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1))} where
  toFun sequence :=
    ⟨encodeGaps n sequence, encodeGaps_mem_interval n sequence sequence.property⟩
  invFun number := ⟨gaps number.val.bitIndices, decodeGaps_mem n number number.property⟩
  left_inv sequence := Subtype.ext (gaps_encodeGaps n sequence
    ((mem_gapSequences n sequence).mp sequence.property).1)
  right_inv number := Subtype.ext (encodeGaps_decodeGaps n number number.property)

theorem gapProductCount_eq_gapSequences (n k : ℕ) :
    gapProductCount n k = ((gapSequences n).filter fun sequence => sequence.prod = k).card := by
  symm
  apply Finset.card_bij (fun sequence _ => encodeGaps n sequence)
  · intro sequence member
    obtain ⟨member, product⟩ := Finset.mem_filter.mp member
    refine Finset.mem_filter.mpr ⟨encodeGaps_mem_interval n sequence member, ?_⟩
    rw [gapProduct, gaps_encodeGaps n sequence ((mem_gapSequences n sequence).mp member).1]
    exact product
  · intro first firstMem second secondMem equality
    have firstPositive := ((mem_gapSequences n first).mp (Finset.mem_filter.mp firstMem).1).1
    have secondPositive := ((mem_gapSequences n second).mp (Finset.mem_filter.mp secondMem).1).1
    simpa only [gaps_encodeGaps n first firstPositive, gaps_encodeGaps n second secondPositive]
      using congrArg (fun number => gaps number.bitIndices) equality
  · intro number member
    obtain ⟨member, product⟩ := Finset.mem_filter.mp member
    exact ⟨gaps number.bitIndices,
      Finset.mem_filter.mpr ⟨decodeGaps_mem n number member, product⟩,
      encodeGaps_decodeGaps n number member⟩

theorem splitUnits_sum (sequence : List ℕ) :
    sequence.sum = (splitUnits sequence).1.sum + (splitUnits sequence).2.sum := by
  have equality := insertUnits_sum _ _ (splitUnits_length sequence)
  rwa [insertUnits_splitUnits] at equality

theorem splitUnits_prod (sequence : List ℕ) :
    (splitUnits sequence).1.prod = sequence.prod := by
  have equality := insertUnits_prod (splitUnits sequence).1 (splitUnits sequence).2
  rw [insertUnits_splitUnits] at equality
  exact equality.symm

theorem splitUnits_mem_reducedTuples (n k : ℕ) (sequence : List ℕ)
    (member : sequence ∈ gapSequences n) (product : sequence.prod = k) :
    (splitUnits sequence).1 ∈ reducedTuples n k := by
  obtain ⟨positive, bounded⟩ := (mem_gapSequences n sequence).mp member
  apply (mem_reducedTuples n k _).mpr
  refine ⟨?_, (splitUnits_prod sequence).trans product, ?_⟩
  · intro gap gapMem
    rw [splitUnits_nonunit] at gapMem
    have conditions := List.mem_filter.mp gapMem
    have := positive gap conditions.1
    have : gap ≠ 1 := by simpa using conditions.2
    omega
  · have := splitUnits_sum sequence
    omega

theorem splitUnits_mem_unitPlacements (n : ℕ) (sequence : List ℕ)
    (member : sequence ∈ gapSequences n) :
    (splitUnits sequence).2 ∈
      unitPlacements ((splitUnits sequence).1.length + 1) (n - (splitUnits sequence).1.sum) := by
  apply (mem_unitPlacements _ _ _).mpr
  refine ⟨splitUnits_length sequence, ?_⟩
  have := ((mem_gapSequences n sequence).mp member).2
  have := splitUnits_sum sequence
  omega

theorem insertUnits_mem_gapSequences (n : ℕ) (sequence counts : List ℕ)
    (positive : ∀ gap ∈ sequence, 0 < gap) (bounded : sequence.sum ≤ n)
    (member : counts ∈ unitPlacements (sequence.length + 1) (n - sequence.sum)) :
    insertUnits sequence counts ∈ gapSequences n := by
  obtain ⟨lengths, sumBound⟩ := (mem_unitPlacements _ _ _).mp member
  apply (mem_gapSequences n _).mpr
  refine ⟨insertUnits_positive sequence counts positive, ?_⟩
  rw [insertUnits_sum sequence counts lengths]
  omega

/-- A reduced tuple's fiber is explicitly parametrized by its bounded unit-run counts. -/
theorem card_reduced_fiber (n k : ℕ) (sequence : List ℕ)
    (member : sequence ∈ reducedTuples n k) :
    (((gapSequences n).filter fun gaps => gaps.prod = k).filter
      fun gaps => (splitUnits gaps).1 = sequence).card =
        (n - sequence.sum + sequence.length + 1).choose (sequence.length + 1) := by
  obtain ⟨nonunit, product, bounded⟩ := (mem_reducedTuples n k sequence).mp member
  have positive : ∀ gap ∈ sequence, 0 < gap := by
    intro gap gapMem
    have := nonunit gap gapMem
    omega
  have notOne : ∀ gap ∈ sequence, gap ≠ 1 := by
    intro gap gapMem
    have := nonunit gap gapMem
    omega
  rw [Nat.add_assoc, ← card_unitPlacements]
  symm
  apply Finset.card_bij (fun counts _ => insertUnits sequence counts)
  · intro counts countsMem
    have lengths := ((mem_unitPlacements _ _ _).mp countsMem).1
    have inverse := splitUnits_insertUnits sequence counts notOne lengths
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨insertUnits_mem_gapSequences n sequence counts positive bounded countsMem,
        (insertUnits_prod sequence counts).trans product⟩,
      congrArg Prod.fst inverse⟩
  · intro first firstMem second secondMem equality
    have firstInverse := splitUnits_insertUnits sequence first notOne
      ((mem_unitPlacements _ _ _).mp firstMem).1
    have secondInverse := splitUnits_insertUnits sequence second notOne
      ((mem_unitPlacements _ _ _).mp secondMem).1
    have := congrArg splitUnits equality
    rw [firstInverse, secondInverse] at this
    exact (Prod.mk.inj this).2
  · intro gaps gapsMem
    obtain ⟨filteredMem, reduced⟩ := Finset.mem_filter.mp gapsMem
    have placements := splitUnits_mem_unitPlacements n gaps (Finset.mem_filter.mp filteredMem).1
    rw [reduced] at placements
    refine ⟨(splitUnits gaps).2, placements, ?_⟩
    rw [← reduced, insertUnits_splitUnits]

/-- The distribution of binary gap products, summed over ordered nonunit gap tuples. -/
theorem gapProductCount_eq_composition_sum (n k : ℕ) :
    gapProductCount n k = ∑ sequence ∈ reducedTuples n k,
      (n - sequence.sum + sequence.length + 1).choose (sequence.length + 1) := by
  rw [gapProductCount_eq_gapSequences]
  have mapsTo :
      (↑((gapSequences n).filter fun sequence => sequence.prod = k) : Set (List ℕ)).MapsTo
      (fun sequence => (splitUnits sequence).1) (↑(reducedTuples n k) : Set (List ℕ)) := by
    intro sequence member
    obtain ⟨member, product⟩ := Finset.mem_filter.mp member
    exact splitUnits_mem_reducedTuples n k sequence member product
  rw [Finset.card_eq_sum_card_fiberwise mapsTo]
  exact Finset.sum_congr rfl (fun sequence member => card_reduced_fiber n k sequence member)

private theorem reducedTuples_one (n : ℕ) : reducedTuples n 1 = {[]} := by
  ext sequence
  rw [mem_reducedTuples, Finset.mem_singleton]
  constructor
  · rintro ⟨nonunit, product, _⟩
    cases sequence with
    | nil => rfl
    | cons first rest =>
      have firstOne : first = 1 := Nat.eq_one_of_mul_eq_one_right product
      have := nonunit first (by simp)
      omega
  · rintro rfl
    simp

/-- For product one only the empty reduced tuple contributes. -/
theorem gapProductCount_one (n : ℕ) : gapProductCount n 1 = n + 1 := by
  rw [gapProductCount_eq_composition_sum, reducedTuples_one]
  simp

example : gapProductCount 4 2 = 6 := by decide +kernel

#print axioms gaps
#print axioms gapProduct
#print axioms gapProductCount
#print axioms unitPlacements
#print axioms mem_unitPlacements
#print axioms card_unitPlacements
#print axioms splitUnits
#print axioms insertUnits
#print axioms splitUnits_length
#print axioms splitUnits_nonunit
#print axioms insertUnits_splitUnits
#print axioms splitUnits_insertUnits
#print axioms insertUnits_sum
#print axioms insertUnits_prod
#print axioms insertUnits_positive
#print axioms gapSequences
#print axioms mem_gapSequences
#print axioms reducedTuples
#print axioms mem_reducedTuples
#print axioms positions
#print axioms gaps_positions
#print axioms positions_sorted
#print axioms positions_gaps
#print axioms gaps_positive
#print axioms encodeGaps
#print axioms bitIndices_encodeGaps
#print axioms gaps_encodeGaps
#print axioms encodeGaps_mem_interval
#print axioms decodeGaps_mem
#print axioms encodeGaps_decodeGaps
#print axioms gapSequenceEquiv
#print axioms gapProductCount_eq_gapSequences
#print axioms splitUnits_sum
#print axioms splitUnits_prod
#print axioms splitUnits_mem_reducedTuples
#print axioms splitUnits_mem_unitPlacements
#print axioms insertUnits_mem_gapSequences
#print axioms card_reduced_fiber
#print axioms gapProductCount_eq_composition_sum
#print axioms gapProductCount_one

end D5.S1.Digit.BinaryGapProductDistribution
