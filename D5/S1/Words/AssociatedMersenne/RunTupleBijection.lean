/- GID: D5/S1/Words/AssociatedMersenne/RunTupleBijection
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/RunTupleBijection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Marked circular words correspond to ordered positive run and slack tuples. -/

/-
admission_basis: escape-witness
Module content theorem: marked_admissible_tuple
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.split_replicates
  declaration statement_id: sha256:75d5c8afcb331beeb5103e5c96e02b3ba8c326ba330162eb4ccb07ab5b1cff9f
Declarations:
  splitBy_map_injective: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.owner_bool_split
  natRunData_positive: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.owner_bool_split
  natRunData_chain: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.owner_bool_split
  bool_to_nat_injective: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.owner_bool_split
  owner_bool_split: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.split_tupleList
  tupleList_cons: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.rawWord_eq_slack_encoding
  split_tupleList: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.blockLengths_tupleList
  blockLengths_tupleList: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.extract_encode_tuple
  tupleList_length: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.goodTuple_n_pos
  decode_tupleLengths: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.extract_encode_tuple
  extract_encode_tuple: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.extract_wordOfTuple
  tupleList_inj: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.tupleVector_injective
  offset_cycAdd: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.linearize_wordOfTuple
  linearize_wordOfTuple: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_wordOfTuple
  extract_wordOfTuple: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.markedTupleEquiv
  wordOfTuple_of_encoding: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.markedTupleEquiv
  split_block_constant: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.splitData_reconstruct
  split_block_last: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.splitData_alternating
  splitData_positive: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  splitData_reconstruct: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  splitData_alternating: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  splitData_head: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  splitData_last: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  alternating_data_pairs: proof_shape: content; escape_witness: RunTupleBijection.alternating_data_pairs;
  rawWord_eq_reconstruct: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  linearize_marked_head: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  linearize_marked_last: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_word_raw_pairs
  marked_word_raw_pairs: proof_shape: content; escape_witness: RunTupleBijection.marked_word_raw_pairs;
  rawWord_cons: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_gap_strict
  rawWord_append: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.linearize_at_pair
  rawWord_head: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_gap_strict
  rawWord_last: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.raw_encoding_marked
  linearize_head_value: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.raw_encoding_marked
  linearize_last_value: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.raw_encoding_marked
  raw_encoding_marked: proof_shape: content; escape_witness: CircularWords.marked_start_iff;
  first_raw_run_start: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_gap_strict
  rawWord_nonempty: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_gap_strict
  first_raw_gap_strict: proof_shape: content; escape_witness: RunTupleBijection.first_raw_gap_strict;
  raw_encoding_gaps: proof_shape: content; escape_witness: RunTupleBijection.raw_encoding_gaps;
  rawWord_boundary: proof_shape: content; escape_witness: RunTupleBijection.rawWord_boundary;
  linearize_get_optional: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_raw_boundary
  marked_raw_boundary: proof_shape: content; escape_witness: RunTupleBijection.marked_raw_boundary;
  rawWord_eq_slack_encoding: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_admissible_tuple
  marked_admissible_tuple: proof_shape: content; escape_witness: RunTupleBijection.marked_admissible_tuple;
  raw_encoding_admissible: proof_shape: content; escape_witness: RunTupleBijection.raw_encoding_admissible;
  raw_encoding_admissible_iff: proof_shape: content; escape_witness: RunTupleBijection.raw_encoding_admissible_iff;
  pairPrefix_succ: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.pairPrefix_strict
  pairPrefix_strict: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.pairPrefix_injective
  pairPrefix_lt_length: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.runCount_raw_encoding
  pairPrefix_injective: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.runCount_raw_encoding
  prefix_marked: proof_shape: content; escape_witness: CircularWords.marked_start_iff;
  runCount_raw_encoding: proof_shape: content; escape_witness: RunTupleBijection.runCount_raw_encoding;
  tupleList_eq_rawPairs: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_tuple_encoding
  tuple_word_admissible: proof_shape: content; escape_witness: RunTupleBijection.marked_raw_boundary;
  tuple_word_marked: proof_shape: content; escape_witness: CircularWords.marked_start_iff;
  tupleVector_injective: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.instFiniteGoodTuple
  instFiniteGoodTuple: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.instFintypeGoodTuple
  runCount_wordOfTuple: proof_shape: content; escape_witness: RunTupleBijection.runCount_wordOfTuple;
  extractMarked_runs: proof_shape: content; escape_witness: RunTupleBijection.alternating_data_pairs;
-/

import D5.S1.Words.Compositions.ConstantBlocksDistinctRunSums
import D5.S1.Words.AssociatedMersenne.CircularWords

open D5.S1.Words.AssociatedMersenne.CircularWords

namespace D5.S1.Words.AssociatedMersenne.RunTupleBijection

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

private theorem splitBy_map_injective {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) :
    (l.map f).splitBy (· == ·)=(l.splitBy (· == ·)).map (List.map f) := by
  have h := split_reverse_map (fun a b : α => a == b) (fun a b : β => a == b)
    f l.reverse (by
      intro a _ b _
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact hf.eq_iff.trans eq_comm)
  have hi := split_reverse_map (fun a b : α => a == b) (fun a b : α => a == b)
    id l (by intro a _ b _; simp [eq_comm])
  simp only [List.map_id] at hi
  rw [List.reverse_reverse, hi] at h
  simpa only [List.map_reverse, List.reverse_reverse, List.map_map,
    Function.comp_def] using h

private def natRunData (t : List (Nat × Nat)) : List (Nat × Nat) :=
  t.flatMap (fun b => [(1,b.1),(0,b.1+1+b.2)])

private lemma natRunData_positive (t : List (Nat × Nat)) (hp : ∀ b ∈ t,0<b.1) :
    ∀ b ∈ natRunData t,0<b.2 := by
  intro b hb
  obtain ⟨c,hc,hb⟩ := List.mem_flatMap.mp hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · exact hp c hc
  · omega

private lemma natRunData_chain (t : List (Nat × Nat)) :
    ((natRunData t).map Prod.fst).IsChain (· ≠ ·) := by
  induction t with
  | nil => simp [natRunData]
  | cons b t ih =>
    cases t with
    | nil => simp [natRunData]
    | cons c t =>
      simp only [natRunData,List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,
        Prod.fst,List.cons_append,List.nil_append] at ih ⊢
      simpa [List.isChain_cons_cons] using ih

private lemma bool_to_nat_injective : Function.Injective Bool.toNat := by
  exact Function.LeftInverse.injective Bool.ofNat_toNat

private theorem owner_bool_split (t : List (Nat × Nat)) (hp : ∀ b ∈ t,0<b.1) :
    (t.flatMap (fun b => [List.replicate b.1 true,List.replicate (b.1+1+b.2) false])).flatten.splitBy (· == ·) =
      t.flatMap (fun b => [List.replicate b.1 true,List.replicate (b.1+1+b.2) false]) := by
  let B := t.flatMap (fun b => [List.replicate b.1 true,List.replicate (b.1+1+b.2) false])
  have hb : (natRunData t).map (fun b => List.replicate b.2 b.1)=B.map (List.map Bool.toNat) := by
    induction t with
    | nil => rfl
    | cons b t ih => simp [natRunData,B,List.map_flatMap,List.map_replicate,ih]
  have hs := D5.S1.Words.Compositions.ConstantBlocksDistinctRunSums.split_replicates (natRunData t) (natRunData_positive t hp) (natRunData_chain t)
  rw [hb,← List.map_flatten,splitBy_map_injective Bool.toNat bool_to_nat_injective] at hs
  exact (List.map_injective_iff.mpr (List.map_injective_iff.mpr bool_to_nat_injective)) hs

private def runBlocks (t : List (Nat × Nat)) : List (List Bool) :=
  t.flatMap (fun b => [List.replicate b.1 true, List.replicate (b.1 + 1 + b.2) false])

def tupleList (t : List (Nat × Nat)) : List Bool := (runBlocks t).flatten

def blockLengths (w : List Bool) : List Nat := (w.splitBy (· == ·)).map List.length

private def tupleLengths (t : List (Nat × Nat)) : List Nat :=
  t.flatMap (fun b => [b.1, b.1 + 1 + b.2])

private lemma tupleList_cons (b : Nat × Nat) (t : List (Nat × Nat)) :
    tupleList (b :: t) = List.replicate b.1 true ++
      List.replicate (b.1 + 1 + b.2) false ++ tupleList t := by
  simp [tupleList, runBlocks, List.append_assoc]

private theorem split_tupleList (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1) :
    (tupleList t).splitBy (· == ·) = runBlocks t := by
  exact owner_bool_split t hp

private lemma blockLengths_tupleList (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1) :
    blockLengths (tupleList t) = tupleLengths t := by
  simp [blockLengths, split_tupleList t hp, runBlocks, tupleLengths, List.map_flatMap]

lemma tupleList_length (t : List (Nat × Nat)) :
    (tupleList t).length = (t.map (fun b => 2 * b.1 + 1 + b.2)).sum := by
  induction t with
  | nil => rfl
  | cons b t ih => simp [tupleList_cons, ih]; omega

def decodeLengths : List Nat → List (Nat × Nat)
  | r :: z :: rest => (r, z - (r + 1)) :: decodeLengths rest
  | _ => []

def extractListTuple (w : List Bool) : List (Nat × Nat) :=
  decodeLengths (blockLengths w)

private lemma decode_tupleLengths (t : List (Nat × Nat)) : decodeLengths (tupleLengths t) = t := by
  induction t with
  | nil => rfl
  | cons b t ih =>
      simp [tupleLengths, decodeLengths] at ih ⊢
      exact ih

private theorem extract_encode_tuple (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1) :
    extractListTuple (tupleList t) = t := by
  rw [extractListTuple, blockLengths_tupleList t hp, decode_tupleLengths]

private lemma tupleList_inj {t u : List (Nat × Nat)} (ht : ∀ b ∈ t, 0 < b.1)
    (hu : ∀ b ∈ u, 0 < b.1) : tupleList t = tupleList u ↔ t = u := by
  constructor
  · intro h
    have := congrArg extractListTuple h
    simpa only [extract_encode_tuple t ht, extract_encode_tuple u hu] using this
  · rintro rfl; rfl

private lemma offset_cycAdd {n : Nat} (i j : Fin n) :
    offset i (cycAdd i j.val) = j.val := by
  exact (cycAdd_inj i (offset_lt i _) j.isLt).mp (cycAdd_offset i (cycAdd i j.val))

def wordOfTuple {n : Nat} (i : Fin n) (t : List (Nat × Nat))
    (hlen : (tupleList t).length = n) : Fin n → Bool :=
  fun q => (tupleList t)[offset i q]'(by rw [hlen]; exact offset_lt i q)

theorem linearize_wordOfTuple {n : Nat} (i : Fin n) (t : List (Nat × Nat))
    (hlen : (tupleList t).length = n) :
    linearize (wordOfTuple i t hlen) i = tupleList t := by
  apply List.ext_getElem
  · simp [linearize, hlen]
  · intro j hj hj'
    have hjn : j < n := by simpa [linearize] using hj
    have h : offset i (cycAdd i j) = j := offset_cycAdd i ⟨j, hjn⟩
    simp [linearize, wordOfTuple, h]

private theorem extract_wordOfTuple {n : Nat} (i : Fin n) (t : List (Nat × Nat))
    (hlen : (tupleList t).length = n) (hp : ∀ b ∈ t, 0 < b.1) :
    extractListTuple (linearize (wordOfTuple i t hlen) i) = t := by
  rw [linearize_wordOfTuple, extract_encode_tuple t hp]

private theorem wordOfTuple_of_encoding {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (he : tupleList t = linearize w i) :
    wordOfTuple i t (he ▸ linearize_length w i) = w := by
  apply linearize_injective i
  dsimp only
  rw [linearize_wordOfTuple, he]

private def splitData (w : List Bool) : List (Bool × Nat) :=
  (w.splitBy (· == ·)).map (fun b => (b.headD false, b.length))

private lemma split_block_constant {w b : List Bool} (hb : b ∈ w.splitBy (· == ·)) :
    b = List.replicate b.length (b.headD false) := by
  have hn : b ≠ [] := List.ne_nil_of_mem_splitBy hb
  have hc : b.IsChain (· = ·) := by simpa using List.isChain_of_mem_splitBy hb
  apply List.isChain_eq_iff_eq_replicate.mp hc
  cases b with
  | nil => contradiction
  | cons a bs => simp

private lemma split_block_last {w b : List Bool} (hb : b ∈ w.splitBy (· == ·))
    (hn : b ≠ []) : b.getLast hn = b.headD false := by
  have hconst := split_block_constant hb
  have hmem := List.getLast_mem hn
  have hmem' : b.getLast hn ∈ List.replicate b.length (b.headD false) := by
    rw [← hconst]; exact hmem
  exact (List.mem_replicate.mp hmem').2

private lemma splitData_positive (w : List Bool) : ∀ b ∈ splitData w, 0 < b.2 := by
  intro b hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  exact List.length_pos_iff_ne_nil.mpr (List.ne_nil_of_mem_splitBy hr)

private theorem splitData_reconstruct (w : List Bool) :
    ((splitData w).map (fun b => List.replicate b.2 b.1)).flatten = w := by
  unfold splitData
  rw [List.map_map]
  dsimp only [Function.comp_def]
  have he : ((w.splitBy (· == ·)).map (fun b => List.replicate b.length (b.headD false))) =
      w.splitBy (· == ·) := by
    simpa only [List.map_id] using
      (List.map_congr_left (fun b hb => (split_block_constant hb).symm) :
        (w.splitBy (· == ·)).map (fun b => List.replicate b.length (b.headD false)) =
          (w.splitBy (· == ·)).map id)
  rw [he, List.flatten_splitBy]

private lemma splitData_alternating (w : List Bool) :
    ((splitData w).map Prod.fst).IsChain (· ≠ ·) := by
  unfold splitData
  rw [List.map_map, List.isChain_map]
  apply (List.isChain_getLast_head_splitBy (· == ·) w).imp_of_mem_imp
  intro a b ha hb hsep
  obtain ⟨hna, hnb, hne⟩ := hsep
  rw [split_block_last ha hna] at hne
  have he : b.head hnb = b.headD false := by
    cases b with
    | nil => contradiction
    | cons a bs => rfl
  rw [he] at hne
  simpa using hne

private lemma splitData_head (w : List Bool) (hw : w ≠ []) :
    ((splitData w).map Prod.fst).head? = w.head? := by
  let bs := w.splitBy (· == ·)
  have hb : bs ≠ [] := List.splitBy_ne_nil.mpr hw
  have hfirst : (bs.head hb).headD false = w.head hw := by
    have hn : bs.head hb ≠ [] := List.ne_nil_of_mem_splitBy (List.head_mem hb)
    calc
      (bs.head hb).headD false = (bs.head hb).head hn := by simp [List.headD_eq_head?_getD, List.head?_eq_some_head hn]
      _ = w.head hw := List.head_head_splitBy _ hw
  simp only [splitData, List.map_map, List.head?_map]
  rw [List.head?_eq_some_head hb]
  simp only [Option.map_some]
  dsimp only [Function.comp_def, Prod.fst]
  rw [hfirst, List.head?_eq_some_head hw]

private lemma splitData_last (w : List Bool) (hw : w ≠ []) :
    ((splitData w).map Prod.fst).getLast? = w.getLast? := by
  let bs := w.splitBy (· == ·)
  have hb : bs ≠ [] := List.splitBy_ne_nil.mpr hw
  have hlast : (bs.getLast hb).headD false = w.getLast hw := by
    have hn : bs.getLast hb ≠ [] := List.ne_nil_of_mem_splitBy (List.getLast_mem hb)
    calc
      (bs.getLast hb).headD false = (bs.getLast hb).getLast hn :=
        (split_block_last (List.getLast_mem hb) hn).symm
      _ = w.getLast hw := List.getLast_getLast_splitBy _ hw
  simp only [splitData, List.map_map, List.getLast?_map]
  rw [List.getLast?_eq_some_getLast hb]
  simp only [Option.map_some]
  dsimp only [Function.comp_def, Prod.fst]
  rw [hlast, List.getLast?_eq_some_getLast hw]

private def rawPairData (t : List (Nat × Nat)) : List (Bool × Nat) :=
  t.flatMap (fun b => [(true, b.1), (false, b.2)])

private theorem alternating_data_pairs (l : List (Bool × Nat))
    (hc : (l.map Prod.fst).IsChain (· ≠ ·))
    (hh : l = [] ∨ (l.map Prod.fst).head? = some true)
    (hl : l = [] ∨ (l.map Prod.fst).getLast? = some false) :
    ∃ t : List (Nat × Nat), l = rawPairData t := by
  induction l using List.twoStepInduction with
  | nil => exact ⟨[], rfl⟩
  | singleton a =>
      simp at hh hl
      have ha : a.1 = true := hh
      have hb : a.1 = false := hl
      exact False.elim (Bool.noConfusion (ha.symm.trans hb))
  | cons_cons a b l ih0 ih1 =>
      have ha : a.1 = true := by simpa using hh
      have hab : a.1 ≠ b.1 := by simpa using (List.isChain_cons_cons.mp hc).1
      have hb : b.1 = false := by cases h : b.1 <;> simp_all
      have hcl : (l.map Prod.fst).IsChain (· ≠ ·) := hc.tail.tail
      have hhl : l = [] ∨ (l.map Prod.fst).head? = some true := by
        cases l with
        | nil => exact Or.inl rfl
        | cons c cs =>
            right
            have hbc : b.1 ≠ c.1 := by simpa using (List.isChain_cons_cons.mp hc.tail).1
            have hc' : c.1 = true := by cases h : c.1 <;> simp_all
            simp [hc']
      have hll : l = [] ∨ (l.map Prod.fst).getLast? = some false := by
        cases l with
        | nil => exact Or.inl rfl
        | cons c cs => right; simpa using hl
      obtain ⟨t, ht⟩ := ih0 hcl hhl hll
      refine ⟨(a.2, b.2) :: t, ?_⟩
      cases a with
      | mk ax av =>
        cases b with
        | mk bx bv =>
          dsimp at ha hb
          subst ax; subst bx
          simp [rawPairData, ht]

def rawWord (t : List (Nat × Nat)) : List Bool :=
  (t.map (fun b => List.replicate b.1 true ++ List.replicate b.2 false)).flatten

private lemma rawWord_eq_reconstruct (t : List (Nat × Nat)) :
    rawWord t = ((rawPairData t).map (fun b => List.replicate b.2 b.1)).flatten := by
  induction t with
  | nil => rfl
  | cons b t ih =>
    simp [rawWord, rawPairData, List.append_assoc] at ih ⊢
    exact ih

private lemma linearize_marked_head {n : Nat} {w : Fin n → Bool} {i : Fin n}
    (hi : IsMarkedStart w i) : (linearize w i).head? = some true := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  simp only [linearize, List.head?_eq_getElem?, List.getElem?_ofFn]
  simp [hn, cycAdd_zero, marked_start_true hi]

private lemma linearize_marked_last {n : Nat} {w : Fin n → Bool} {i : Fin n}
    (hi : IsMarkedStart w i) : (linearize w i).getLast? = some false := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  simp only [linearize, List.getLast?_eq_getElem?, List.length_ofFn, List.getElem?_ofFn]
  simp [show n-1 < n by omega, cycAdd_sub_one, marked_start_predecessor hi]

private theorem marked_word_raw_pairs {n : Nat} {w : Fin n → Bool} {i : Fin n}
    (hi : IsMarkedStart w i) : ∃ t : List (Nat × Nat),
      (∀ b ∈ t, 0 < b.1 ∧ 0 < b.2) ∧ rawWord t = linearize w i := by
  let v := linearize w i
  have hv : v ≠ [] := by
    have hlen := linearize_length w i
    have hn := Nat.zero_lt_of_lt i.isLt
    intro he
    simp [v, he] at hlen
    omega
  have hh : ((splitData v).map Prod.fst).head? = some true := by
    rw [splitData_head v hv]
    exact linearize_marked_head hi
  have hl : ((splitData v).map Prod.fst).getLast? = some false := by
    rw [splitData_last v hv]
    exact linearize_marked_last hi
  obtain ⟨t, ht⟩ := alternating_data_pairs (splitData v) (splitData_alternating v)
    (Or.inr hh) (Or.inr hl)
  refine ⟨t, ?_, ?_⟩
  · intro b hb
    have hpos := splitData_positive v
    have hrmem : (true, b.1) ∈ rawPairData t := by
      simp only [rawPairData, List.mem_flatMap]
      exact ⟨b, hb, by simp⟩
    have hzmem : (false, b.2) ∈ rawPairData t := by
      simp only [rawPairData, List.mem_flatMap]
      exact ⟨b, hb, by simp⟩
    rw [← ht] at hrmem hzmem
    exact ⟨hpos _ hrmem, hpos _ hzmem⟩
  · rw [rawWord_eq_reconstruct, ← ht, splitData_reconstruct]

lemma rawWord_cons (b : Nat × Nat) (t : List (Nat × Nat)) :
    rawWord (b::t) = List.replicate b.1 true ++ List.replicate b.2 false ++ rawWord t := by
  simp [rawWord, List.append_assoc]

lemma rawWord_append (t u : List (Nat × Nat)) : rawWord (t++u) = rawWord t ++ rawWord u := by
  simp [rawWord]

private lemma rawWord_head (t : List (Nat × Nat)) (ht : t ≠ [])
    (hp : ∀ b ∈ t, 0 < b.1) : (rawWord t).head? = some true := by
  cases t with
  | nil => contradiction
  | cons b t =>
    have hb : b.1 ≠ 0 := Nat.ne_of_gt (hp b (by simp))
    simp [rawWord_cons, List.head?_replicate, hb]

private lemma rawWord_last (t : List (Nat × Nat)) (ht : t ≠ [])
    (hp : ∀ b ∈ t, 0 < b.2) : (rawWord t).getLast? = some false := by
  induction t with
  | nil => contradiction
  | cons b t ih =>
    have hb : b.2 ≠ 0 := Nat.ne_of_gt (hp b (by simp))
    by_cases he : t = []
    · subst t; simp [rawWord_cons, rawWord, List.getLast?_replicate, hb]
    · rw [rawWord_cons, List.getLast?_append, List.getLast?_append,
        ih he (fun c hc => hp c (by simp [hc]))]
      rfl

private lemma linearize_head_value {n : Nat} (w : Fin n → Bool) (i : Fin n) :
    (linearize w i).head? = some (w i) := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  simp [linearize, List.head?_eq_getElem?, List.getElem?_ofFn, hn, cycAdd_zero]

private lemma linearize_last_value {n : Nat} (w : Fin n → Bool) (i : Fin n) :
    (linearize w i).getLast? = some (w (cycSub i 1)) := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  simp [linearize, List.getLast?_eq_getElem?, List.getElem?_ofFn,
    show n-1 < n by omega, cycAdd_sub_one]

lemma raw_encoding_marked {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (ht : t ≠ []) (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2)
    (he : linearize w i = rawWord t) : IsMarkedStart w i := by
  apply (marked_start_iff w i).mpr
  have hh := rawWord_head t ht (fun b hb => (hp b hb).1)
  have hl := rawWord_last t ht (fun b hb => (hp b hb).2)
  rw [← he, linearize_head_value] at hh
  rw [← he, linearize_last_value] at hl
  exact ⟨Option.some.inj hl, Option.some.inj hh⟩

lemma first_raw_run_start {n r z : Nat} (w : Fin n → Bool) (i : Fin n)
    (hr : 0 < r) (hz : 0 < z) (post : List Bool)
    (hm : IsMarkedStart w i)
    (he : linearize w i = List.replicate r true ++ List.replicate z false ++ post) :
    IsOneRunStart w i r := by
  have hlen : n = r+z+post.length := by
    have := congrArg List.length he
    simpa [linearize, Nat.add_assoc] using this
  refine ⟨marked_start_predecessor hm, ?_, ?_⟩
  · intro j hj
    have hjn : j < n := by omega
    have hv : (linearize w i)[j]? = some (w (cycAdd i j)) := by
      simp [linearize, hjn]
    rw [he] at hv
    simp [List.getElem?_append, show j < r+z by omega, hj] at hv
    exact hv
  · have hrn : r < n := by omega
    have hv : (linearize w i)[r]? = some (w (cycAdd i r)) := by
      simp [linearize, hrn]
    rw [he] at hv
    simp [List.getElem?_append, show r < r+z by omega, hz] at hv
    exact hv

private lemma rawWord_nonempty (t : List (Nat × Nat)) (ht : t ≠ [])
    (hp : ∀ b ∈ t, 0 < b.1) : rawWord t ≠ [] := by
  have hh := rawWord_head t ht hp
  intro he
  simp [he] at hh

private lemma first_raw_gap_strict {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (b : Nat × Nat) (t : List (Nat × Nat))
    (hp : ∀ c ∈ b::t, 0 < c.1 ∧ 0 < c.2)
    (ha : Admissible w) (he : linearize w i = rawWord (b::t)) : b.1 < b.2 := by
  have hb := hp b (by simp)
  have hm := raw_encoding_marked w i (b::t) (by simp) hp he
  have hs := first_raw_run_start w i hb.1 hb.2 (rawWord t) hm
    (by simpa only [rawWord_cons] using he)
  apply next_one_gap_bound ha hs
  by_cases ht : t = []
  · subst t
    have hlen : n = b.1+b.2 := by
      have h := congrArg List.length he
      simpa [linearize, rawWord_cons, rawWord, Nat.add_assoc] using h
    have hc : cycAdd i (b.1+b.2) = i := by
      apply Fin.ext
      simp [← hlen, cycAdd_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    rw [hc]
    exact marked_start_true hm
  · have htpos : ∀ c ∈ t, 0 < c.1 := fun c hc => (hp c (by simp [hc])).1
    have hne := rawWord_nonempty t ht htpos
    have hlen : n = b.1+b.2+(rawWord t).length := by
      have h := congrArg List.length he
      simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
    have hj : b.1+b.2 < n := by have := List.length_pos_iff.mpr hne; omega
    have hv : (linearize w i)[b.1+b.2]? = some (w (cycAdd i (b.1+b.2))) := by
      simp [linearize, hj]
    rw [he, rawWord_cons] at hv
    simp only [List.getElem?_append, List.length_append, List.length_replicate] at hv
    simp only [show ¬b.1+b.2 < b.1 by omega, if_false,
      show b.1+b.2-b.1 = b.2 by omega, lt_self_iff_false, Nat.sub_self] at hv
    rw [← List.head?_eq_getElem?] at hv
    rw [rawWord_head t ht htpos] at hv
    exact Option.some.inj hv.symm

private theorem raw_encoding_gaps {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2)
    (ha : Admissible w) (he : linearize w i = rawWord t) :
    ∀ b ∈ t, b.1 < b.2 := by
  intro b hb
  obtain ⟨u,v,huv⟩ := List.mem_iff_append.mp hb
  have hrot : linearize w (cycAdd i (rawWord u).length) = rawWord (b::v++u) := by
    rw [linearize_move_mark, he, huv, rawWord_append,
      List.rotate_append_length_eq, ← rawWord_append]
  apply first_raw_gap_strict w (cycAdd i (rawWord u).length) b (v++u) ?_ ha hrot
  intro c hc
  apply hp
  rw [huv]
  simp only [List.mem_cons, List.mem_append] at hc ⊢
  tauto

private theorem rawWord_boundary (t : List (Nat × Nat))
    (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2) (j : Nat)
    (hj : j < (rawWord t).length) (ht : (rawWord t)[j]? = some true)
    (hprev : 0 < j → (rawWord t)[j-1]? = some false) :
    ∃ u b v, t = u++b::v ∧ j = (rawWord u).length := by
  induction t generalizing j with
  | nil => simp [rawWord] at hj
  | cons b t ih =>
    have hb := hp b (by simp)
    have hpt : ∀ c ∈ t, 0 < c.1 ∧ 0 < c.2 := fun c hc => hp c (by simp [hc])
    by_cases hjr : j < b.1
    · have hj0 : j = 0 := by
        by_contra hn
        have hv := hprev (by omega)
        simp [rawWord_cons, List.getElem?_append, show j-1 < b.1 by omega] at hv
      refine ⟨[], b, t, by simp, ?_⟩
      simp [hj0, rawWord]
    · by_cases hjz : j < b.1+b.2
      · simp [rawWord_cons, List.getElem?_append, hjr,
          show j-b.1 < b.2 by omega] at ht
      · have ht' : (rawWord t)[j-(b.1+b.2)]? = some true := by
          simpa [rawWord_cons, List.getElem?_append, hjr,
            show ¬j-b.1 < b.2 by omega, Nat.sub_sub] using ht
        have hj' : j-(b.1+b.2) < (rawWord t).length := by
          simp only [rawWord_cons, List.length_append, List.length_replicate] at hj
          omega
        have hp' : 0 < j-(b.1+b.2) →
            (rawWord t)[j-(b.1+b.2)-1]? = some false := by
          intro hpos
          have hv := hprev (by omega)
          have hsub : j-1-b.1-b.2 = j-(b.1+b.2)-1 := by omega
          simpa [rawWord_cons, List.getElem?_append,
            show ¬j-1 < b.1 by omega, show ¬j-1-b.1 < b.2 by omega,
            hsub] using hv
        obtain ⟨u,c,v,he,hjv⟩ := ih hpt _ hj' ht' hp'
        refine ⟨b::u,c,v,by simp [he], ?_⟩
        simp only [rawWord_cons, List.length_append, List.length_replicate]
        omega

lemma linearize_get_optional {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (j : Nat) (hj : j < n) :
    (linearize w i)[j]? = some (w (cycAdd i j)) := by
  simp [linearize, hj]

private theorem marked_raw_boundary {n : Nat} (w : Fin n → Bool) (i q : Fin n)
    (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2)
    (he : linearize w i = rawWord t) (hm : IsMarkedStart w q) :
    ∃ u b v, t = u++b::v ∧ q = cycAdd i (rawWord u).length := by
  let j := offset i q
  have hj : j < n := offset_lt i q
  have hc : cycAdd i j = q := cycAdd_offset i q
  have ht : (rawWord t)[j]? = some true := by
    rw [← he, linearize_get_optional w i j hj, hc, marked_start_true hm]
  have hprev : 0 < j → (rawWord t)[j-1]? = some false := by
    intro hpos
    have hpred : cycAdd i (j-1) = cycSub q 1 := by
      rw [← hc, cycAdd_predecessor_pos i j hpos]
    rw [← he, linearize_get_optional w i (j-1) (by omega), hpred,
      marked_start_predecessor hm]
  obtain ⟨u,b,v,he',hj'⟩ := rawWord_boundary t hp j (by rw [← he, linearize_length]; exact hj) ht hprev
  exact ⟨u,b,v,he',by rw [← hj']; exact hc.symm⟩

private def slackPairs (t : List (Nat × Nat)) : List (Nat × Nat) :=
  t.map (fun b => (b.1, b.2-(b.1+1)))

private lemma rawWord_eq_slack_encoding (t : List (Nat × Nat))
    (hg : ∀ b ∈ t, b.1 < b.2) : rawWord t = tupleList (slackPairs t) := by
  induction t with
  | nil => rfl
  | cons b t ih =>
    have hb : b.1+1+(b.2-(b.1+1)) = b.2 := by have := hg b (by simp); omega
    simp only [slackPairs, List.map_cons, tupleList_cons, rawWord_cons, Prod.fst, Prod.snd]
    rw [hb, ih (fun c hc => hg c (by simp [hc]))]
    rfl

theorem marked_admissible_tuple {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (ha : Admissible w) (hm : IsMarkedStart w i) :
    ∃ t : List (Nat × Nat), t ≠ [] ∧ (∀ b ∈ t, 0 < b.1) ∧
      (t.map (fun b => 2*b.1+1+b.2)).sum = n ∧
      tupleList t = linearize w i ∧ extractListTuple (linearize w i) = t := by
  obtain ⟨u,hp,he⟩ := marked_word_raw_pairs hm
  have hne : u ≠ [] := by
    intro hu
    subst u
    have hlen := congrArg List.length he
    simp [rawWord, linearize] at hlen
    have := i.isLt
    omega
  have hg := raw_encoding_gaps w i u hp ha he.symm
  have henc : tupleList (slackPairs u) = linearize w i := by
    rw [← rawWord_eq_slack_encoding u hg, he]
  have hpos : ∀ b ∈ slackPairs u, 0 < b.1 := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact (hp c hc).1
  refine ⟨slackPairs u, by simpa [slackPairs] using hne, hpos, ?_, henc, ?_⟩
  · rw [← tupleList_length, henc, linearize_length]
  · rw [← henc, extract_encode_tuple _ hpos]

theorem raw_encoding_admissible {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (hne : t ≠ [])
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord t) : Admissible w := by
  have hpos : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    have h := hp b hb
    exact ⟨h.1, by omega⟩
  have hm := raw_encoding_marked w i t hne hpos he
  refine ⟨Or.inr ⟨cycSub i 1, marked_start_predecessor hm⟩, ?_⟩
  intro q r hs j hj
  by_cases hr : r = 0
  · subst r
    have hj0 : j = 0 := by omega
    subst j
    simpa [cycAdd_zero] using hs.2.2
  · have hqm : IsMarkedStart w q := ⟨r, by omega, hs⟩
    obtain ⟨u,b,v,ht,hq⟩ := marked_raw_boundary w i q t hpos he hqm
    have hb : b ∈ t := by rw [ht]; simp
    have hbpos := hp b hb
    have hrot : linearize w q = rawWord (b::(v++u)) := by
      rw [hq, linearize_move_mark, he, ht, rawWord_append,
        List.rotate_append_length_eq, ← rawWord_append]
      rfl
    have hbr : IsOneRunStart w q b.1 := first_raw_run_start (r := b.1) (z := b.2) w q hbpos.1
      (by omega) (rawWord (v++u)) hqm (by simpa [rawWord_cons] using hrot)
    have hrb : r = b.1 := one_run_length_unique hs hbr
    subst r
    rw [cycAdd_assoc]
    have hlen : n = b.1+b.2+(rawWord (v++u)).length := by
      have h := congrArg List.length hrot
      simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
    have hjn : b.1+j < n := by omega
    have hv := linearize_get_optional w q (b.1+j) hjn
    rw [hrot, rawWord_cons] at hv
    simp [List.getElem?_append, show ¬b.1+j < b.1 by omega,
      show b.1+j-b.1 = j by omega, show j < b.2 by omega] at hv
    exact hv

theorem raw_encoding_admissible_iff {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (hne : t ≠ [])
    (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2) (he : linearize w i = rawWord t) :
    Admissible w ↔ ∀ b ∈ t, b.1 < b.2 := by
  constructor
  · intro ha
    exact raw_encoding_gaps w i t hp ha he
  · intro hg
    exact raw_encoding_admissible w i t hne (fun b hb => ⟨(hp b hb).1, hg b hb⟩) he

def pairPrefix (t : List (Nat × Nat)) (p : Nat) := (rawWord (t.take p)).length

private lemma pairPrefix_succ (t : List (Nat × Nat)) (p : Nat) (hp : p < t.length) :
    pairPrefix t (p+1) = pairPrefix t p + t[p].1+t[p].2 := by
  rw [pairPrefix, ← List.take_concat_get' t p hp, rawWord_append]
  simp [pairPrefix, rawWord_cons, rawWord, Nat.add_assoc]

private lemma pairPrefix_strict (t : List (Nat × Nat))
    (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2)
    {p q : Nat} (hpq : p < q) (hq : q ≤ t.length) : pairPrefix t p < pairPrefix t q := by
  induction q with
  | zero => omega
  | succ q ih =>
    rw [pairPrefix_succ t q (by omega)]
    have hpos := hp t[q] (List.getElem_mem (by omega))
    by_cases hpq' : p < q
    · have h := ih hpq' (by omega)
      omega
    · have he : p = q := by omega
      rw [he]
      omega

private lemma pairPrefix_lt_length (t : List (Nat × Nat))
    (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2) (p : Fin t.length) :
    pairPrefix t p.val < (rawWord t).length := by
  have h := pairPrefix_strict t hp p.isLt (le_refl t.length)
  simpa [pairPrefix] using h

private lemma pairPrefix_injective (t : List (Nat × Nat))
    (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2) :
    Function.Injective (fun p : Fin t.length => pairPrefix t p.val) := by
  intro p q he
  dsimp only at he
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := pairPrefix_strict t hp h (Nat.le_of_lt q.isLt)
    omega
  · have := pairPrefix_strict t hp h (Nat.le_of_lt p.isLt)
    omega

private lemma prefix_marked {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2)
    (he : linearize w i = rawWord t) (p : Fin t.length) :
    IsMarkedStart w (cycAdd i (pairPrefix t p.val)) := by
  have hd : t = t.take p.val ++ t[p.val]::t.drop (p.val+1) := by
    rw [← List.drop_eq_getElem_cons p.isLt]
    exact (List.take_append_drop p.val t).symm
  have hrot : linearize w (cycAdd i (pairPrefix t p.val)) =
      rawWord (t[p.val]::(t.drop (p.val+1)++t.take p.val)) := by
    have henc := congrArg rawWord hd
    rw [rawWord_append] at henc
    rw [pairPrefix, linearize_move_mark, he, henc,
      List.rotate_append_length_eq, ← rawWord_append]
    rfl
  apply raw_encoding_marked w _ _ (by simp) ?_ hrot
  intro b hb
  apply hp
  simp only [List.mem_cons, List.mem_append] at hb
  rcases hb with h | h | h
  · subst b; exact List.getElem_mem p.isLt
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

private theorem runCount_raw_encoding {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (hp : ∀ b ∈ t, 0 < b.1 ∧ 0 < b.2)
    (he : linearize w i = rawWord t) : runCount w = t.length := by
  classical
  have hlen : (rawWord t).length = n := by rw [← he, linearize_length]
  symm
  calc
    t.length = (Finset.univ : Finset (Fin t.length)).card := (Finset.card_fin _).symm
    _ = (Finset.univ.filter (IsMarkedStart w)).card := by
      apply Finset.card_bij (fun p _ => cycAdd i (pairPrefix t p.val))
      · intro p hp'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, prefix_marked w i t hp he p⟩
      · intro p hp' q hq' heq
        apply pairPrefix_injective t hp
        apply (cycAdd_inj i ?_ ?_).mp heq
        · rw [← hlen]; exact pairPrefix_lt_length t hp p
        · rw [← hlen]; exact pairPrefix_lt_length t hp q
      · intro q hq
        obtain ⟨u,b,v,ht,hq'⟩ := marked_raw_boundary w i q t hp he (Finset.mem_filter.mp hq).2
        have hule : u.length < t.length := by simp [ht]
        refine ⟨⟨u.length,hule⟩, Finset.mem_univ _, ?_⟩
        dsimp only
        rw [pairPrefix, ht, List.take_left, ← hq']

def rawPairs (t : List (Nat × Nat)) : List (Nat × Nat) :=
  t.map (fun b => (b.1,b.1+1+b.2))

lemma tupleList_eq_rawPairs (t : List (Nat × Nat)) : tupleList t = rawWord (rawPairs t) := by
  induction t with
  | nil => rfl
  | cons b t ih =>
    simp only [rawPairs, List.map_cons, rawWord_cons, tupleList_cons]
    rw [ih]
    rfl

lemma tuple_word_admissible {n : Nat} (i : Fin n) (t : List (Nat × Nat))
    (hne : t ≠ []) (hp : ∀ b ∈ t, 0 < b.1) (hlen : (tupleList t).length = n) :
    Admissible (wordOfTuple i t hlen) := by
  apply raw_encoding_admissible _ i (rawPairs t) (by simpa [rawPairs] using hne) ?_ ?_
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact ⟨hp c hc, by omega⟩
  · rw [linearize_wordOfTuple, tupleList_eq_rawPairs]

lemma tuple_word_marked {n : Nat} (i : Fin n) (t : List (Nat × Nat))
    (hne : t ≠ []) (hp : ∀ b ∈ t, 0 < b.1) (hlen : (tupleList t).length = n) :
    IsMarkedStart (wordOfTuple i t hlen) i := by
  apply raw_encoding_marked _ i (rawPairs t) (by simpa [rawPairs] using hne) ?_ ?_
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact ⟨hp c hc, by omega⟩
  · rw [linearize_wordOfTuple, tupleList_eq_rawPairs]

def GoodTuple (n : Nat) :=
  {t : List (Nat × Nat) // t ≠ [] ∧ (∀ b ∈ t, 0 < b.1) ∧ (tupleList t).length = n}

def MarkedWords (n : Nat) :=
  {p : (Fin n → Bool) × Fin n // Admissible p.1 ∧ IsMarkedStart p.1 p.2}

def extractMarked {n : Nat} (x : MarkedWords n) : Fin n × GoodTuple n := by
  let t := extractListTuple (linearize x.val.1 x.val.2)
  refine (x.val.2, ⟨t, ?_⟩)
  obtain ⟨u,hne,hp,hlen,he,hex⟩ := marked_admissible_tuple x.val.1 x.val.2
    x.property.1 x.property.2
  refine ⟨by simpa [t,hex] using hne, by simpa [t,hex] using hp, ?_⟩
  rw [show t = u from hex, he, linearize_length]

def reconstructMarked {n : Nat} (x : Fin n × GoodTuple n) : MarkedWords n :=
  ⟨(wordOfTuple x.1 x.2.val x.2.property.2.2, x.1),
    tuple_word_admissible x.1 x.2.val x.2.property.1 x.2.property.2.1 x.2.property.2.2,
    tuple_word_marked x.1 x.2.val x.2.property.1 x.2.property.2.1 x.2.property.2.2⟩

def markedTupleEquiv (n : Nat) : MarkedWords n ≃ Fin n × GoodTuple n where
  toFun := extractMarked
  invFun := reconstructMarked
  left_inv := by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · obtain ⟨u,hne,hp,hlen,he,hex⟩ := marked_admissible_tuple x.val.1 x.val.2
        x.property.1 x.property.2
      change wordOfTuple x.val.2 (extractListTuple (linearize x.val.1 x.val.2))
        (extractMarked x).2.property.2.2 = x.val.1
      exact wordOfTuple_of_encoding x.val.1 x.val.2
        (extractListTuple (linearize x.val.1 x.val.2)) ((congrArg tupleList hex).trans he)
    · rfl
  right_inv := by
    intro x
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change extractListTuple (linearize (wordOfTuple x.1 x.2.val x.2.property.2.2) x.1) = x.2.val
      exact extract_wordOfTuple x.1 x.2.val x.2.property.2.2 x.2.property.2.1

private def tupleVector {n : Nat} (t : GoodTuple n) : List.Vector Bool n :=
  ⟨tupleList t.val, t.property.2.2⟩

private lemma tupleVector_injective (n : Nat) : Function.Injective (@tupleVector n) := by
  intro t u h
  apply Subtype.ext
  apply (tupleList_inj t.property.2.1 u.property.2.1).mp
  exact congrArg Subtype.val h

instance instFiniteGoodTuple (n : Nat) : Finite (GoodTuple n) :=
  Finite.of_injective tupleVector (tupleVector_injective n)

instance instFintypeGoodTuple (n : Nat) : Fintype (GoodTuple n) := Fintype.ofFinite _

theorem runCount_wordOfTuple {n : Nat} (i : Fin n) (t : List (Nat × Nat))
    (hp : ∀ b ∈ t, 0 < b.1) (hlen : (tupleList t).length = n) :
    runCount (wordOfTuple i t hlen) = t.length := by
  have hrp : ∀ b ∈ rawPairs t, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact ⟨hp c hc, by omega⟩
  have h := runCount_raw_encoding (wordOfTuple i t hlen) i (rawPairs t) hrp
    (by rw [linearize_wordOfTuple, tupleList_eq_rawPairs])
  simpa [rawPairs] using h

lemma extractMarked_runs {n : Nat} (x : MarkedWords n) :
    runCount x.val.1 = (extractMarked x).2.val.length := by
  have h := runCount_wordOfTuple (extractMarked x).1 (extractMarked x).2.val
    (extractMarked x).2.property.2.1 (extractMarked x).2.property.2.2
  have he := congrArg (fun y : MarkedWords n => y.val.1) ((markedTupleEquiv n).left_inv x)
  change wordOfTuple (extractMarked x).1 (extractMarked x).2.val
    (extractMarked x).2.property.2.2 = x.val.1 at he
  rw [he] at h
  exact h

def RunTuples (n ell : Nat) := {t : GoodTuple n // t.val.length = ell}

end
end RunTupleBijection
