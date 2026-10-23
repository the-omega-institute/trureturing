/- GID: D5/S1/Words/BlockPalindromes/GreedyRenewal
   generality: G
   mirror-B: D5/B/S1/Words/BlockPalindromes/GreedyRenewal
   mirror-E: none(waiver:gabrić-shallit-expected-width)
   anchors: []
   utility: none
   digest: Gabrić–Shallit Conjecture 5 and its greedy renewal/composition proof. -/

/- The alphabet is Fin k; bs lists blocks from the centre outwards.
   The empty word is assigned width zero. The source's Lemma 3 is not used.
   proof_shape: IsBPFactorization=not-applicable (definition).
   proof_shape: bpWidth=not-applicable (definition).
   proof_shape: largestBPWidth=not-applicable (definition).
   proof_shape: flatten_length_ge=bind-only.
     consumers: GreedyRenewal.bpWidth_le_length.
   proof_shape: bpWidth_le_length=bind-only.
     consumers: GreedyRenewal.factor_widths_bounded, GreedyRenewal.largestBPWidth_le_length.
   proof_shape: factor_widths_nonempty=bind-only.
     consumers: GreedyRenewal.largestBPWidth_le_length, GreedyRenewal.largest_attained.
   proof_shape: factor_widths_bounded=bind-only.
     consumers: GreedyRenewal.largest_attained, GreedyRenewal.le_largestBPWidth.
   proof_shape: largestBPWidth_le_length=bind-only.
     consumers: LargestFactorizationExpectedWidth.peelPairs_le_length, LargestFactorizationExpectedWidth.width_count_grouping.
   proof_shape: le_largestBPWidth=bind-only.
     consumers: GreedyRenewal.largest_outer_recursion, GreedyRenewal.maximal_outer_unbordered.
   proof_shape: IsBorder=not-applicable (definition).
   proof_shape: IsUnbordered=not-applicable (definition).
   proof_shape: IsShortestBorder=not-applicable (definition).
   proof_shape: shortest_border_unbordered=bind-only.
     consumers: GreedyRenewal.largest_eq_peelWidth, GreedyRenewal.peelPairs_succ_iff, GreedyRenewal.shortest_partition, LargestFactorizationExpectedWidth.emptyCentre_iff_outer.
   proof_shape: exists_shortest_border=bind-only.
     consumers: GreedyRenewal.maximal_outer_unbordered, GreedyRenewal.shortestBorder, GreedyRenewal.shortestBorder_spec, GreedyRenewal.shortest_partition.
   proof_shape: shortest_border_unique=bind-only.
     consumers: GreedyRenewal.core_of_unbordered_outer, GreedyRenewal.largest_outer_recursion, GreedyRenewal.outerWords_disjoint.
   proof_shape: shortest_border_le_half=content. escape_witness: GreedyRenewal.shortest_border_le_half.
   proof_shape: unbordered_outer_shortest=bind-only.
     consumers: GreedyRenewal.core_of_unbordered_outer, GreedyRenewal.largest_outer_recursion, GreedyRenewal.outerWords_disjoint, GreedyRenewal.peelPairs_outer, GreedyRenewal.shortest_partition, LargestFactorizationExpectedWidth.peelCentre_outer.
   proof_shape: split_nonoverlapping_border=bind-only.
     consumers: GreedyRenewal.maximal_outer_unbordered, GreedyRenewal.peeledCore, GreedyRenewal.peeledCore_spec, GreedyRenewal.shortest_partition.
   proof_shape: largest_attained=bind-only.
     consumers: GreedyRenewal.largest_outer_recursion, GreedyRenewal.largest_unbordered.
   proof_shape: factor_outer_eq=bind-only.
     consumers: GreedyRenewal.largest_outer_recursion, GreedyRenewal.largest_unbordered, GreedyRenewal.maximal_outer_unbordered.
   proof_shape: add_outer_factor=bind-only.
     consumers: GreedyRenewal.largest_outer_recursion.
   proof_shape: bpWidth_append=bind-only.
     consumers: GreedyRenewal.largest_outer_recursion, GreedyRenewal.maximal_outer_unbordered.
   proof_shape: maximal_outer_unbordered=content. escape_witness: GreedyRenewal.maximal_outer_unbordered.
   proof_shape: largest_unbordered=content. escape_witness: GreedyRenewal.largest_unbordered.
   proof_shape: largest_outer_recursion=content. escape_witness: GreedyRenewal.largest_outer_recursion.
   proof_shape: shortestBorder=not-applicable (definition).
   proof_shape: shortestBorder_spec=bind-only.
     consumers: GreedyRenewal.core_of_unbordered_outer, GreedyRenewal.largest_eq_peelWidth, GreedyRenewal.peelPairs_succ_iff, GreedyRenewal.peeledCore, GreedyRenewal.peeledCore_shorter, GreedyRenewal.peeledCore_spec, LargestFactorizationExpectedWidth.emptyCentre_iff_outer.
   proof_shape: peeledCore=not-applicable (definition).
   proof_shape: peeledCore_spec=bind-only.
     consumers: GreedyRenewal.core_of_unbordered_outer, GreedyRenewal.largest_eq_peelWidth, GreedyRenewal.peelPairs_succ_iff, GreedyRenewal.peeledCore_shorter, LargestFactorizationExpectedWidth.emptyCentre_iff_outer, LargestFactorizationExpectedWidth.peelCentre_length_mod_two.
   proof_shape: peeledCore_shorter=bind-only.
     consumers: GreedyRenewal.largest_eq_peelWidth, GreedyRenewal.peelPairs, GreedyRenewal.peelPairs_outer, GreedyRenewal.peelPairs_succ_iff, GreedyRenewal.peelPairs_unbordered, GreedyRenewal.peelWidth, LargestFactorizationExpectedWidth.emptyCentre_iff_outer, LargestFactorizationExpectedWidth.largest_pairs_centre, LargestFactorizationExpectedWidth.peelCentre, LargestFactorizationExpectedWidth.peelCentre_empty, LargestFactorizationExpectedWidth.peelCentre_length_mod_two, LargestFactorizationExpectedWidth.peelCentre_outer.
   proof_shape: peelWidth=not-applicable (definition).
   proof_shape: largest_eq_peelWidth=content. escape_witness: GreedyRenewal.largest_eq_peelWidth.
   proof_shape: mem_words=bind-only.
     consumers: GreedyRenewal.mem_outerWords, GreedyRenewal.mem_tailWords, GreedyRenewal.mem_ubWords, GreedyRenewal.shortest_partition, GreedyRenewal.tailWords_zero, GreedyRenewal.uCount_one, LargestFactorizationExpectedWidth.mem_emptyWords, LargestFactorizationExpectedWidth.pair_tail_sum, LargestFactorizationExpectedWidth.sum_words_ofFn, LargestFactorizationExpectedWidth.width_count_grouping.
   proof_shape: card_words=bind-only.
     consumers: GreedyRenewal.card_outerWords, GreedyRenewal.uCount_bound, GreedyRenewal.uCount_one, GreedyRenewal.unbordered_count_add, GreedyRenewal.unbordered_count_recurrence, LargestFactorizationExpectedWidth.expectedWidth_tail_formula, LargestFactorizationExpectedWidth.tailProbability_zero.
   proof_shape: ubWords=not-applicable (definition).
   proof_shape: uCount=not-applicable (definition).
   proof_shape: mem_ubWords=bind-only.
     consumers: GreedyRenewal.card_outerWords, GreedyRenewal.card_tailOuterWords, GreedyRenewal.mem_outerWords, GreedyRenewal.mem_tailOuterWords, GreedyRenewal.uCount_one, LargestFactorizationExpectedWidth.card_emptyOuterWords, LargestFactorizationExpectedWidth.mem_emptyOuterWords.
   proof_shape: uCount_bound=bind-only.
     consumers: GreedyRenewal.qCoeff_summable, GreedyRenewal.unbordered_q_lt_one.
   proof_shape: outerWords=not-applicable (definition).
   proof_shape: mem_outerWords=bind-only.
     consumers: GreedyRenewal.outerWords_disjoint, GreedyRenewal.renewal_tail_count, GreedyRenewal.shortest_partition, LargestFactorizationExpectedWidth.empty_centre_count.
   proof_shape: outerWords_disjoint=bind-only.
     consumers: GreedyRenewal.renewal_tail_count, GreedyRenewal.unbordered_count_add, GreedyRenewal.unbordered_count_recurrence, LargestFactorizationExpectedWidth.empty_centre_count.
   proof_shape: card_outerWords=bind-only.
     consumers: GreedyRenewal.unbordered_count_add, GreedyRenewal.unbordered_count_recurrence.
   proof_shape: borderedWords=not-applicable (definition).
   proof_shape: shortest_partition=content. escape_witness: GreedyRenewal.shortest_partition.
   proof_shape: unbordered_count_recurrence=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
   proof_shape: uCount_one=bind-only.
     consumers: GreedyRenewal.uCount_two.
   proof_shape: uCount_two=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
     consumers: unbordered_q_lt_one.
   proof_shape: q=not-applicable (definition).
   proof_shape: q_summable_of_bound=bind-only.
     consumers: GreedyRenewal.qCoeff_summable, GreedyRenewal.q_lt_one_of_second_strict.
   proof_shape: q_lt_one_of_second_strict=bind-only.
     consumers: GreedyRenewal.unbordered_q_lt_one.
   proof_shape: unbordered_q_lt_one=content. escape_witness: GreedyRenewal.uCount_two.
     consumers: positive_q_powers_tsum, empty_even_summable, empty_partial_sum_bound, positive_q_powers_summable, unbordered_composition_series.
   proof_shape: peelPairs=not-applicable (definition).
   proof_shape: core_of_unbordered_outer=bind-only.
     consumers: GreedyRenewal.peelPairs_outer, LargestFactorizationExpectedWidth.peelCentre_outer.
   proof_shape: peelPairs_outer=bind-only.
     consumers: GreedyRenewal.peelPairs_succ_iff.
     consumers: peelPairs_succ_iff.
   proof_shape: peelPairs_unbordered=bind-only.
     consumers: GreedyRenewal.peelPairs_succ_iff.
   proof_shape: peelPairs_succ_iff=content. escape_witness: GreedyRenewal.peelPairs_succ_iff.
   proof_shape: tailWords=not-applicable (definition).
   proof_shape: mem_tailWords=bind-only.
     consumers: GreedyRenewal.mem_tailOuterWords, GreedyRenewal.tailWords_zero, GreedyRenewal.tail_partition, LargestFactorizationExpectedWidth.tailWords_empty.
   proof_shape: tailOuterWords=not-applicable (definition).
   proof_shape: mem_tailOuterWords=bind-only.
     consumers: GreedyRenewal.renewal_tail_count, GreedyRenewal.tail_partition.
   proof_shape: card_tailOuterWords=bind-only.
     consumers: GreedyRenewal.renewal_tail_count.
   proof_shape: tail_partition=content. escape_witness: GreedyRenewal.tail_partition.
   proof_shape: renewal_tail_count=content. escape_witness: GreedyRenewal.renewal_tail_count.
   proof_shape: tailWords_zero=bind-only.
     consumers: LargestFactorizationExpectedWidth.tailProbability_zero.
   proof_shape: qCoeff=not-applicable (definition).
   proof_shape: qCoeff_nonneg=bind-only.
     consumers: CompositionInversion.unbordered_composition_series, LargestFactorizationExpectedWidth.empty_partial_sum_bound, LargestFactorizationExpectedWidth.renewal_tail_bound, LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: qCoeff_summable=bind-only.
     consumers: CompositionInversion.unbordered_composition_series, GreedyRenewal.tsum_qCoeff, LargestFactorizationExpectedWidth.empty_partial_sum_bound, LargestFactorizationExpectedWidth.renewal_tail_bound, LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: tsum_qCoeff=bind-only.
     consumers: CompositionInversion.unbordered_composition_series, LargestFactorizationExpectedWidth.empty_partial_sum_bound, LargestFactorizationExpectedWidth.renewal_tail_bound, LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: q_nonneg=bind-only.
     consumers: LargestFactorizationExpectedWidth.positive_q_powers_summable, LargestFactorizationExpectedWidth.positive_q_powers_tsum, LargestFactorizationExpectedWidth.renewal_tail_bound, LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: unbordered_count_add=content. escape_witness: GreedyRenewal.shortest_partition.
     consumers: qCoeff_recurrence.
   proof_shape: qCoeff_recurrence=content. escape_witness: GreedyRenewal.unbordered_count_add.
     consumers: unbordered_composition_series.
   escape_witness: renewal_tail_count
   admission_basis: escape-witness
   Fixed-length words use DepthBudgetIidGreedyOptimality.words directly.
   Direct frozen dependencies: D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.words
     statement_id: sha256:ac39f4d6ac85644b4d36960e026f51c85dafd409386991d3defafb1ebead5aa6.
   No other frozen D5 declaration is used.
   The frozen words declaration above is used by:
     mem_words, card_words, ubWords, uCount, mem_ubWords, uCount_bound, outerWords, mem_outerWords,
     outerWords_disjoint, card_outerWords, borderedWords, shortest_partition,
     unbordered_count_recurrence, uCount_one, uCount_two, unbordered_q_lt_one, tailWords,
     mem_tailWords, tailOuterWords, mem_tailOuterWords, card_tailOuterWords, tail_partition,
     renewal_tail_count, tailWords_zero, qCoeff, qCoeff_nonneg, qCoeff_summable, tsum_qCoeff,
     q_nonneg, unbordered_count_add, qCoeff_recurrence.
   Direct frozen dependencies of all other declarations: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15783
   DTR reading: DTR-Unregistered (Observe) for all 25 public theorem audit targets.
   Missing evidence: source-bound dependent-family variation, sensitivity,
   observational dependence, and a compiled enrolled four-slot registration.
-/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open scoped BigOperators
open Set Finset Filter Topology
open D5.S0.Computability.Coding
namespace D5.S1.Words.BlockPalindromes.GreedyRenewal

def IsBPFactorization {α : Type} (w : List α) (bs : List (List α)) (c : List α) : Prop :=
  (∀ b ∈ bs, b ≠ []) ∧ w = bs.reverse.flatten ++ c ++ bs.flatten

def bpWidth {α : Type} (bs : List (List α)) (c : List α) : ℕ :=
  2 * bs.length + if c = [] then 0 else 1

noncomputable def largestBPWidth {α : Type} (w : List α) : ℕ :=
  sSup {t : ℕ | ∃ bs c, IsBPFactorization w bs c ∧ bpWidth bs c = t}

private lemma flatten_length_ge {α : Type} (bs : List (List α))
    (hbs : ∀ b ∈ bs, b ≠ []) : bs.length ≤ bs.flatten.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb : b ≠ [] := hbs b (by simp)
    have hbp : 1 ≤ b.length := by
      have := List.ne_nil_iff_length_pos.mp hb
      omega
    have ht : ∀ x ∈ bs, x ≠ [] := by intro x hx; exact hbs x (by simp [hx])
    have hi := ih ht
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

private lemma bpWidth_le_length {α : Type} {w : List α} {bs : List (List α)} {c : List α}
    (h : IsBPFactorization w bs c) : bpWidth bs c ≤ w.length := by
  rcases h with ⟨hbs, rfl⟩
  have h1 := flatten_length_ge bs hbs
  have h2 := flatten_length_ge bs.reverse (by simpa using hbs)
  simp only [List.length_append, List.length_reverse] at *
  unfold bpWidth
  split_ifs with hc
  · subst c
    simp only [List.length_nil]
    omega
  · have hcpos : 0 < c.length := List.ne_nil_iff_length_pos.mp hc
    omega

private lemma factor_widths_nonempty {α : Type} (w : List α) :
    {t : ℕ | ∃ bs c, IsBPFactorization w bs c ∧ bpWidth bs c = t}.Nonempty := by
  refine ⟨bpWidth [] w, [], w, ?_, rfl⟩
  simp [IsBPFactorization]

private lemma factor_widths_bounded {α : Type} (w : List α) :
    BddAbove {t : ℕ | ∃ bs c, IsBPFactorization w bs c ∧ bpWidth bs c = t} := by
  refine ⟨w.length, ?_⟩
  rintro t ⟨bs, c, h, rfl⟩
  exact bpWidth_le_length h

lemma largestBPWidth_le_length {α : Type} (w : List α) : largestBPWidth w ≤ w.length := by
  apply csSup_le (factor_widths_nonempty w)
  rintro t ⟨bs, c, h, rfl⟩
  exact bpWidth_le_length h

private lemma le_largestBPWidth {α : Type} {w : List α} {bs : List (List α)} {c : List α}
    (h : IsBPFactorization w bs c) : bpWidth bs c ≤ largestBPWidth w := by
  exact le_csSup (factor_widths_bounded w) ⟨bs, c, h, rfl⟩

def IsBorder {α : Type} (w b : List α) : Prop :=
  b ≠ [] ∧ b.length < w.length ∧ b <+: w ∧ b <:+ w

def IsUnbordered {α : Type} (w : List α) : Prop := ∀ b, ¬ IsBorder w b

def IsShortestBorder {α : Type} (w b : List α) : Prop :=
  IsBorder w b ∧ ∀ c, IsBorder w c → b.length ≤ c.length

theorem shortest_border_unbordered {α : Type} {w b : List α}
    (hb : IsShortestBorder w b) : IsUnbordered b := by
  intro c hc
  rcases hb.1 with ⟨hbne, hblt, hbp, hbs⟩
  rcases hc with ⟨hcne, hclt, hcp, hcs⟩
  have hcw : IsBorder w c :=
    ⟨hcne, lt_trans hclt hblt, hcp.trans hbp, hcs.trans hbs⟩
  exact (Nat.not_le_of_gt hclt) (hb.2 c hcw)

private theorem exists_shortest_border {α : Type} {w : List α}
    (hw : ∃ b, IsBorder w b) : ∃ b, IsShortestBorder w b := by
  classical
  have hex : ∃ n : ℕ, ∃ b : List α, IsBorder w b ∧ b.length = n := by
    obtain ⟨b, hb⟩ := hw
    exact ⟨b.length, b, hb, rfl⟩
  obtain ⟨b, hb, hblen⟩ := Nat.find_spec hex
  refine ⟨b, hb, ?_⟩
  intro c hc
  rw [hblen]
  exact Nat.find_min' hex ⟨c, hc, rfl⟩

private theorem shortest_border_unique {α : Type} {w b c : List α}
    (hb : IsShortestBorder w b) (hc : IsShortestBorder w c) : b = c := by
  have hlen : b.length = c.length := le_antisymm (hb.2 c hc.1) (hc.2 b hb.1)
  have hbp := List.prefix_iff_eq_take.mp hb.1.2.2.1
  have hcp := List.prefix_iff_eq_take.mp hc.1.2.2.1
  rw [hlen] at hbp
  exact hbp.trans hcp.symm

theorem shortest_border_le_half {α : Type} {w b : List α}
    (hb : IsShortestBorder w b) : 2 * b.length ≤ w.length := by
  by_contra hbad
  let m := b.length
  let p := w.length - m
  have hblt : m < w.length := by simpa [m] using hb.1.2.1
  have hp_lt : p < m := by dsimp [p, m]; omega
  have hp_le : p ≤ m := hp_lt.le
  have hsum : p + (m - p) = m := by omega
  have hprefix : b = w.take m := by simpa [m] using (List.prefix_iff_eq_take.mp hb.1.2.2.1)
  have hsuffix : b = w.drop p := by simpa [p, m] using (List.suffix_iff_eq_drop.mp hb.1.2.2.2)
  let c := b.take (m - p)
  have hcp : c <+: w := by
    exact (List.take_prefix (m - p) b).trans hb.1.2.2.1
  have hc_eq_drop : c = w.drop (2 * p) := by
    dsimp [c]
    rw [hsuffix, List.take_drop, hsum, ← hprefix, hsuffix, List.drop_drop]
    congr 1
    omega
  have hcs : c <:+ w := by
    rw [hc_eq_drop]
    exact List.drop_suffix (2 * p) w
  have hclen : c.length = m - p := by
    dsimp [c]
    have htake : m - p ≤ b.length := by dsimp [m]; omega
    simp [List.length_take, Nat.min_eq_left htake]
  have hcne : c ≠ [] := by
    intro hc0
    have : c.length = 0 := by simp [hc0]
    omega
  have hc : IsBorder w c := ⟨hcne, by rw [hclen]; omega, hcp, hcs⟩
  have hmle : m ≤ p := by
    have hmc : m ≤ c.length := hb.2 c hc
    rw [hclen] at hmc
    omega
  exact (Nat.not_le_of_gt hp_lt) hmle

theorem unbordered_outer_shortest {α : Type} {u v : List α}
    (hu_ne : u ≠ []) (hu : IsUnbordered u) :
    IsShortestBorder (u ++ v ++ u) u := by
  refine ⟨?_, ?_⟩
  · refine ⟨hu_ne, ?_, by simpa [List.append_assoc] using List.prefix_append u (v ++ u), by exact List.suffix_append (u ++ v) u⟩
    simp only [List.length_append]
    have hupos : 0 < u.length := List.ne_nil_iff_length_pos.mp hu_ne
    omega
  · intro c hc
    by_contra hlt
    have hlt' : c.length < u.length := Nat.lt_of_not_ge hlt
    have hcle : c.length ≤ u.length := Nat.le_of_lt hlt'
    have hpu : u <+: u ++ v ++ u := by simpa [List.append_assoc] using List.prefix_append u (v ++ u)
    have hsu : u <:+ u ++ v ++ u := by exact List.suffix_append (u ++ v) u
    have hpc : c <+: u := List.prefix_of_prefix_length_le hc.2.2.1 hpu hcle
    have hsc : c <:+ u := List.suffix_of_suffix_length_le hc.2.2.2 hsu hcle
    exact hu c ⟨hc.1, hlt', hpc, hsc⟩

private theorem split_nonoverlapping_border {α : Type} {w b : List α}
    (hb : IsBorder w b) (hhalf : 2 * b.length ≤ w.length) :
    ∃ v, w = b ++ v ++ b ∧ v.length = w.length - 2 * b.length := by
  let v := (w.drop b.length).take (w.length - 2 * b.length)
  have hp : b = w.take b.length := List.prefix_iff_eq_take.mp hb.2.2.1
  have hs : b = w.drop (w.length - b.length) := List.suffix_iff_eq_drop.mp hb.2.2.2
  refine ⟨v, ?_, ?_⟩
  · have hsplit := List.take_append_drop b.length w
    have hmid := List.take_append_drop (w.length - 2 * b.length) (w.drop b.length)
    have harg : b.length + (w.length - 2 * b.length) = w.length - b.length := by omega
    rw [List.drop_drop, harg, ← hs] at hmid
    rw [← hp, ← hmid] at hsplit
    simpa [v, List.append_assoc] using hsplit.symm
  · dsimp [v]
    rw [List.length_take, List.length_drop]
    omega

private lemma largest_attained {α : Type} (w : List α) :
    ∃ bs c, IsBPFactorization w bs c ∧ bpWidth bs c = largestBPWidth w := by
  exact Nat.sSup_mem (factor_widths_nonempty w) (factor_widths_bounded w)

private lemma factor_outer_eq {α : Type} {w c b : List α} {bs : List (List α)}
    (h : IsBPFactorization w (bs ++ [b]) c) :
    w = b ++ (bs.reverse.flatten ++ c ++ bs.flatten) ++ b := by
  simpa [IsBPFactorization, List.reverse_append, List.flatten_append,
    List.append_assoc] using h.2

private lemma add_outer_factor {α : Type} {v c b : List α} {bs : List (List α)}
    (h : IsBPFactorization v bs c) (hb : b ≠ []) :
    IsBPFactorization (b ++ v ++ b) (bs ++ [b]) c := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.1 x hx
    · have he : x = b := by simpa using hx
      simpa [he] using hb
  · rw [h.2]
    simp [List.reverse_append, List.flatten_append, List.append_assoc]

private lemma bpWidth_append {α : Type} (bs ds : List (List α)) (c : List α) :
    bpWidth (bs ++ ds) c = 2 * ds.length + bpWidth bs c := by
  simp only [bpWidth, List.length_append]
  omega

lemma maximal_outer_unbordered {α : Type} {w c b : List α} {bs : List (List α)}
    (h : IsBPFactorization w (bs ++ [b]) c)
    (hm : bpWidth (bs ++ [b]) c = largestBPWidth w) : IsUnbordered b := by
  intro x hx
  obtain ⟨u, hu⟩ := exists_shortest_border ⟨x, hx⟩
  obtain ⟨v, hb, hlen⟩ := split_nonoverlapping_border hu.1 (shortest_border_le_half hu)
  have hune := hu.1.1
  have hold := factor_outer_eq h
  have hbs : ∀ x ∈ bs, x ≠ [] := by
    intro x hx
    exact h.1 x (List.mem_append_left _ hx)
  by_cases hv : v = []
  · have hnew : IsBPFactorization w (bs ++ [u,u]) c := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hbs x hx
        · have he : x = u := by simpa using hx
          simpa [he] using hune
      · rw [hold, hb, hv]
        simp [List.reverse_append, List.flatten_append, List.append_assoc]
    have hwide := le_largestBPWidth hnew
    rw [← hm, bpWidth_append, bpWidth_append] at hwide
    simp only [List.length_cons, List.length_nil] at hwide
    omega
  · have hnew : IsBPFactorization w (bs ++ [u,v,u]) c := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hbs x hx
        · have he : x = u ∨ x = v ∨ x = u := by simpa using hx
          rcases he with rfl | rfl | rfl
          · exact hune
          · exact hv
          · exact hune
      · rw [hold, hb]
        simp [List.reverse_append, List.flatten_append, List.append_assoc]
    have hwide := le_largestBPWidth hnew
    rw [← hm, bpWidth_append, bpWidth_append] at hwide
    simp only [List.length_cons, List.length_nil] at hwide
    omega

private lemma largest_unbordered {α : Type} {w : List α} (hw : IsUnbordered w) :
    largestBPWidth w = if w = [] then 0 else 1 := by
  obtain ⟨bs,c,h,hm⟩ := largest_attained w
  have hnil : bs = [] := by
    cases bs using List.reverseRecOn with
    | nil => rfl
    | append_singleton bs b _ =>
      have hbn : b ≠ [] := h.1 b (by simp)
      have he := factor_outer_eq h
      have hb : IsBorder w b := by
        rw [he]
        refine ⟨hbn, ?_, ?_, ?_⟩
        · simp only [List.length_append]
          have := List.ne_nil_iff_length_pos.mp hbn
          omega
        · simpa [List.append_assoc] using
            List.prefix_append b ((bs.reverse.flatten ++ c ++ bs.flatten) ++ b)
        · exact List.suffix_append _ _
      exact (hw b hb).elim
  subst bs
  have hc : w = c := by simpa [IsBPFactorization] using h.2
  subst c
  simpa [bpWidth] using hm.symm

private theorem largest_outer_recursion {α : Type} {u v : List α}
    (hune : u ≠ []) (hu : IsUnbordered u) :
    largestBPWidth (u ++ v ++ u) = 2 + largestBPWidth v := by
  have hlo : 2 + largestBPWidth v ≤ largestBPWidth (u ++ v ++ u) := by
    obtain ⟨bs,c,h,hmax⟩ := largest_attained v
    have ha := le_largestBPWidth (add_outer_factor h hune)
    rw [bpWidth_append, hmax] at ha
    simpa using ha
  obtain ⟨bs,c,h,hmax⟩ := largest_attained (u ++ v ++ u)
  cases bs using List.reverseRecOn with
  | nil =>
    have hwid : bpWidth ([] : List (List α)) c ≤ 1 := by
      simp only [bpWidth, List.length_nil, Nat.mul_zero, Nat.zero_add]
      split_ifs <;> omega
    omega
  | append_singleton bs b _ =>
    have hbn : b ≠ [] := h.1 b (by simp)
    have hbub := maximal_outer_unbordered h hmax
    have hword := factor_outer_eq h
    have hbshort : IsShortestBorder (u ++ v ++ u) b := by
      rw [hword]
      exact unbordered_outer_shortest hbn hbub
    have hushort := unbordered_outer_shortest (v := v) hune hu
    have hbu : b = u := shortest_border_unique hbshort hushort
    subst b
    have hinside : v = bs.reverse.flatten ++ c ++ bs.flatten := by
      have he := List.append_cancel_right hword
      exact List.append_cancel_left he
    have hi : IsBPFactorization v bs c := by
      refine ⟨?_, hinside⟩
      intro b hb
      exact h.1 b (List.mem_append_left _ hb)
    have hwidth := le_largestBPWidth hi
    rw [bpWidth_append] at hmax
    simp only [List.length_cons, List.length_nil] at hmax
    omega

noncomputable def shortestBorder {α : Type} (w : List α) (hw : ∃ b, IsBorder w b) : List α :=
  Classical.choose (exists_shortest_border hw)

lemma shortestBorder_spec {α : Type} (w : List α) (hw : ∃ b, IsBorder w b) :
    IsShortestBorder w (shortestBorder w hw) := Classical.choose_spec (exists_shortest_border hw)

noncomputable def peeledCore {α : Type} (w : List α) (hw : ∃ b, IsBorder w b) : List α :=
  Classical.choose (split_nonoverlapping_border (shortestBorder_spec w hw).1
    (shortest_border_le_half (shortestBorder_spec w hw)))

lemma peeledCore_spec {α : Type} (w : List α) (hw : ∃ b, IsBorder w b) :
    w = shortestBorder w hw ++ peeledCore w hw ++ shortestBorder w hw ∧
    (peeledCore w hw).length = w.length - 2 * (shortestBorder w hw).length :=
  Classical.choose_spec (split_nonoverlapping_border (shortestBorder_spec w hw).1
    (shortest_border_le_half (shortestBorder_spec w hw)))

lemma peeledCore_shorter {α : Type} (w : List α) (hw : ∃ b, IsBorder w b) :
    (peeledCore w hw).length < w.length := by
  have hb := (shortestBorder_spec w hw).1
  have hpos := List.ne_nil_iff_length_pos.mp hb.1
  have hlt := hb.2.1
  rw [(peeledCore_spec w hw).2]
  omega

noncomputable def peelWidth {α : Type} (w : List α) : ℕ := by
  classical
  exact if hw : ∃ b, IsBorder w b then 2 + peelWidth (peeledCore w hw)
    else if w = [] then 0 else 1
termination_by w.length
decreasing_by exact peeledCore_shorter w hw

theorem largest_eq_peelWidth {α : Type} (w : List α) :
    largestBPWidth w = peelWidth w := by
  classical
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    rw [peelWidth]
    by_cases hw : ∃ b, IsBorder w b
    · rw [dif_pos hw]
      have hb := shortestBorder_spec w hw
      have hrec := largest_outer_recursion (v := peeledCore w hw) hb.1.1 (shortest_border_unbordered hb)
      have hsplit := (peeledCore_spec w hw).1
      rw [← hsplit] at hrec
      rw [hrec, ih _ (peeledCore_shorter w hw)]
    · rw [dif_neg hw]
      have hwu : IsUnbordered w := by
        intro b hb
        exact hw ⟨b,hb⟩
      exact largest_unbordered hwu

lemma mem_words {k n : ℕ} {w : List (Fin k)} :
    w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n ↔ w.length = n := by
  classical
  simp only [DepthBudgetIidGreedyOptimality.words, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

lemma card_words (k n : ℕ) :
    (DepthBudgetIidGreedyOptimality.words (α := Fin k) n).card = k ^ n := by
  classical
  rw [DepthBudgetIidGreedyOptimality.words]
  have hinj : Function.Injective (fun v : List.Vector (Fin k) n => v.1) := by
    intro a b h
    exact List.Vector.toList_injective h
  rw [Finset.card_image_of_injective _ hinj]
  simp

noncomputable def ubWords (k n : ℕ) : Finset (List (Fin k)) := by
  classical
  exact (DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter IsUnbordered

noncomputable def uCount (k n : ℕ) : ℕ := (ubWords k n).card

lemma mem_ubWords {k n : ℕ} {w : List (Fin k)} :
    w ∈ ubWords k n ↔ w.length = n ∧ IsUnbordered w := by
  classical
  simp [ubWords, mem_words]

private lemma uCount_bound (k n : ℕ) : uCount k n ≤ k ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (card_words k n)

noncomputable def outerWords (k n i : ℕ) : Finset (List (Fin k)) :=
  ((ubWords k i) ×ˢ (DepthBudgetIidGreedyOptimality.words (α := Fin k) (n - 2 * i))).image (fun p => p.1 ++ p.2 ++ p.1)

lemma mem_outerWords {k n i : ℕ} {w : List (Fin k)} :
    w ∈ outerWords k n i ↔ ∃ u v, u.length = i ∧ IsUnbordered u ∧
      v.length = n - 2 * i ∧ w = u ++ v ++ u := by
  classical
  simp only [outerWords, Finset.mem_image, Finset.mem_product, mem_ubWords, mem_words]
  constructor
  · rintro ⟨⟨u,v⟩, ⟨⟨hui,hu⟩,hvn⟩,he⟩
    exact ⟨u,v,hui,hu,hvn,he.symm⟩
  · rintro ⟨u,v,hui,hu,hvn,he⟩
    exact ⟨⟨u,v⟩,⟨⟨hui,hu⟩,hvn⟩,he.symm⟩

lemma outerWords_disjoint {k n i j : ℕ} (hi : 0 < i) (hj : 0 < j) (hne : i ≠ j) :
    Disjoint (outerWords k n i) (outerWords k n j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwi hwj
  obtain ⟨u,v,hui,hu,hvn,hwu⟩ := mem_outerWords.mp hwi
  obtain ⟨a,b,haj,ha,hbn,hwa⟩ := mem_outerWords.mp hwj
  have hun : u ≠ [] := by intro he; simp [he] at hui; omega
  have han : a ≠ [] := by intro he; simp [he] at haj; omega
  have hs1 : IsShortestBorder w u := hwu ▸ unbordered_outer_shortest hun hu
  have hs2 : IsShortestBorder w a := hwa ▸ unbordered_outer_shortest han ha
  have he := congrArg List.length (shortest_border_unique hs1 hs2)
  exact hne (hui.symm.trans (he.trans haj))

private lemma card_outerWords (k n i : ℕ) :
    (outerWords k n i).card = uCount k i * k ^ (n - 2 * i) := by
  classical
  have hinj : Set.InjOn (fun p : List (Fin k) × List (Fin k) => p.1 ++ p.2 ++ p.1)
      ↑(ubWords k i ×ˢ DepthBudgetIidGreedyOptimality.words (α := Fin k) (n - 2 * i)) := by
    rintro ⟨u,v⟩ hp ⟨a,b⟩ hq he
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
    have hul := (mem_ubWords.mp hp1).1
    have hal := (mem_ubWords.mp hq1).1
    have hlen : u.length = a.length := hul.trans hal.symm
    have h1 : u = a := (List.append_inj (by simpa [List.append_assoc] using he) hlen).1
    subst a
    have h2 : v = b := by simpa [List.append_assoc] using he
    exact Prod.ext rfl h2
  rw [outerWords, Finset.card_image_of_injOn hinj, Finset.card_product, card_words]
  rfl

noncomputable def borderedWords (k n : ℕ) : Finset (List (Fin k)) := by
  classical
  exact (DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter (fun w => ¬ IsUnbordered w)

lemma shortest_partition (k n : ℕ) :
    borderedWords k n = (Finset.Icc 1 (n / 2)).biUnion (outerWords k n) := by
  classical
  ext w
  simp only [borderedWords, Finset.mem_filter, mem_words, Finset.mem_biUnion,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hwn,hw⟩
    have hex : ∃ b, IsBorder w b := by simpa [IsUnbordered] using hw
    obtain ⟨u,hu⟩ := exists_shortest_border hex
    have hhalf := shortest_border_le_half hu
    obtain ⟨v,he,hvn⟩ := split_nonoverlapping_border hu.1 hhalf
    refine ⟨u.length, ?_, mem_outerWords.mpr
      ⟨u,v,rfl,shortest_border_unbordered hu,by simpa [hwn] using hvn,he⟩⟩
    have hp := List.ne_nil_iff_length_pos.mp hu.1.1
    constructor <;> omega
  · rintro ⟨i,⟨hi,hin⟩,hwi⟩
    obtain ⟨u,v,hui,hu,hvn,rfl⟩ := mem_outerWords.mp hwi
    have hun : u ≠ [] := by intro he; simp [he] at hui; omega
    have hhalf : 2 * i ≤ n := by omega
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, hui, hvn]
      omega
    · intro hwu
      exact hwu u (unbordered_outer_shortest (v := v) hun hu).1

private theorem unbordered_count_recurrence (k n : ℕ) :
    uCount k n = k ^ n - ∑ i ∈ Finset.Icc 1 (n / 2), uCount k i * k ^ (n - 2 * i) := by
  classical
  have hdisj : (↑(Finset.Icc 1 (n / 2)) : Set ℕ).PairwiseDisjoint (outerWords k n) := by
    intro i hi j hj hij
    exact outerWords_disjoint (by have := (Finset.mem_Icc.mp hi).1; omega)
      (by have := (Finset.mem_Icc.mp hj).1; omega) hij
  have hcard : (borderedWords k n).card =
      ∑ i ∈ Finset.Icc 1 (n / 2), uCount k i * k ^ (n - 2 * i) := by
    rw [shortest_partition, Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun i _ => card_outerWords k n i)
  have htotal : uCount k n + (borderedWords k n).card = k ^ n := by
    have h := Finset.card_filter_add_card_filter_not (s := DepthBudgetIidGreedyOptimality.words (α := Fin k) n) IsUnbordered
    simpa [uCount, ubWords, borderedWords, card_words] using h
  omega

private lemma uCount_one (k : ℕ) : uCount k 1 = k := by
  classical
  have he : ubWords k 1 = DepthBudgetIidGreedyOptimality.words (α := Fin k) 1 := by
    ext w
    rw [mem_ubWords, mem_words]
    refine and_iff_left_of_imp ?_
    intro hlen b hb
    have hpos := List.ne_nil_iff_length_pos.mp hb.1
    have hlt := hb.2.1
    omega
  simp [uCount, he, card_words]

private theorem uCount_two (k : ℕ) : uCount k 2 = k ^ 2 - k := by
  rw [unbordered_count_recurrence]
  norm_num [uCount_one]

noncomputable def q (k : ℕ) (u : ℕ → ℕ) : ℝ :=
  ∑' j : ℕ, (u (j + 1) : ℝ) / (k : ℝ) ^ (2 * (j + 1))

private theorem q_summable_of_bound {k : ℕ} (hk : 2 ≤ k) (u : ℕ → ℕ)
    (hu : ∀ j, u j ≤ k ^ j) :
    Summable (fun j : ℕ => (u (j + 1) : ℝ) / (k : ℝ) ^ (2 * (j + 1))) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hkpos : 0 < (k : ℝ) := by positivity
  have hx : ‖(1 / (k : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    exact (div_lt_one₀ (by positivity)).2 this
  have hinc : Function.Injective (fun j : ℕ => j + 1) := by intro a b h; exact Nat.add_right_cancel h
  have hg0 : Summable (fun j : ℕ => (1 / (k : ℝ)) ^ j) :=
    summable_geometric_of_norm_lt_one hx
  have hg : Summable (fun j : ℕ => (1 / (k : ℝ)) ^ (j + 1)) := by
    simpa [pow_succ, mul_comm] using hg0.mul_left (1 / (k : ℝ))
  apply Summable.of_norm_bounded hg
  intro j
  have hju : (u (j + 1) : ℝ) ≤ (k : ℝ) ^ (j + 1) := by
    exact_mod_cast hu (j + 1)
  have hden : 0 < (k : ℝ) ^ (2 * (j + 1)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (u (j + 1) : ℝ) / (k : ℝ) ^ (2 * (j + 1)) ≤
        (k : ℝ) ^ (j + 1) / (k : ℝ) ^ (2 * (j + 1)) := by gcongr
    _ = (1 / (k : ℝ)) ^ (j + 1) := by
      rw [one_div_pow, show 2 * (j + 1) = (j + 1) + (j + 1) by omega, pow_add]
      field_simp [hk0]
      ring

private theorem q_lt_one_of_second_strict {k : ℕ} (hk : 2 ≤ k) (u : ℕ → ℕ)
    (hu : ∀ j, u j ≤ k ^ j) (hu2 : u 2 < k ^ 2) : q k u < 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hx : ‖(1 / (k : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hkgt : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    exact (div_lt_one₀ (by positivity)).2 hkgt
  have hf := q_summable_of_bound hk u hu
  have hg : Summable (fun j : ℕ => (1 / (k : ℝ)) ^ (j + 1)) := by
    have hg0 : Summable (fun j : ℕ => (1 / (k : ℝ)) ^ j) :=
      summable_geometric_of_norm_lt_one hx
    simpa [pow_succ, mul_comm] using hg0.mul_left (1 / (k : ℝ))
  have heq (j : ℕ) : (k : ℝ) ^ (j + 1) / (k : ℝ) ^ (2 * (j + 1)) =
      (1 / (k : ℝ)) ^ (j + 1) := by
    rw [one_div_pow, show 2 * (j + 1) = (j + 1) + (j + 1) by omega, pow_add]
    field_simp [hk0]
    ring
  have hle (j : ℕ) : (u (j + 1) : ℝ) / (k : ℝ) ^ (2 * (j + 1)) ≤
      (1 / (k : ℝ)) ^ (j + 1) := by
    rw [← heq j]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hu (j + 1)
    · positivity
  have hi : (u (1 + 1) : ℝ) / (k : ℝ) ^ (2 * (1 + 1)) <
      (1 / (k : ℝ)) ^ (1 + 1) := by
    rw [← heq 1]
    apply (div_lt_div_iff_of_pos_right (by positivity)).2
    exact_mod_cast hu2
  have hq : q k u < ∑' j : ℕ, (1 / (k : ℝ)) ^ (j + 1) :=
    Summable.tsum_lt_tsum hle hi hf hg
  have hsum : (∑' j : ℕ, (1 / (k : ℝ)) ^ (j + 1)) =
      (1 / (k : ℝ)) * (1 - 1 / (k : ℝ))⁻¹ := by
    have hs := (hasSum_geometric_of_norm_lt_one hx).mul_left (1 / (k : ℝ))
    simpa [pow_succ, mul_comm] using hs.tsum_eq
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfrac : (1 / (k : ℝ)) * (1 - 1 / (k : ℝ))⁻¹ ≤ 1 := by
    have hden : 0 < (k : ℝ) - 1 := by linarith
    calc
      (1 / (k : ℝ)) * (1 - 1 / (k : ℝ))⁻¹ = 1 / ((k : ℝ) - 1) := by
        field_simp [hk0]
      _ ≤ 1 := (div_le_one hden).2 (by linarith)
  exact lt_of_lt_of_le (hsum ▸ hq) hfrac

theorem unbordered_q_lt_one {k : ℕ} (hk : 2 ≤ k) : q k (uCount k) < 1 := by
  apply q_lt_one_of_second_strict hk (uCount k) (uCount_bound k)
  rw [uCount_two]
  have hkpos : 0 < k := by omega
  have hpowpos : 0 < k ^ 2 := pow_pos hkpos _
  exact Nat.sub_lt hpowpos hkpos

noncomputable def peelPairs {α : Type} (w : List α) : ℕ := by
  classical
  exact if hw : ∃ b, IsBorder w b then 1 + peelPairs (peeledCore w hw) else 0
termination_by w.length
decreasing_by exact peeledCore_shorter w hw

lemma core_of_unbordered_outer {α : Type} {u v : List α}
    (hun : u ≠ []) (hu : IsUnbordered u) (hw : ∃ b, IsBorder (u ++ v ++ u) b) :
    peeledCore (u ++ v ++ u) hw = v := by
  have he := shortest_border_unique (shortestBorder_spec _ hw)
    (unbordered_outer_shortest hun hu)
  have hsplit := (peeledCore_spec _ hw).1
  rw [he] at hsplit
  simpa [List.append_assoc] using hsplit.symm

private lemma peelPairs_outer {α : Type} {u v : List α} (hun : u ≠ []) (hu : IsUnbordered u) :
    peelPairs (u ++ v ++ u) = 1 + peelPairs v := by
  classical
  have hw : ∃ b, IsBorder (u ++ v ++ u) b :=
    ⟨u,(unbordered_outer_shortest hun hu).1⟩
  rw [peelPairs, dif_pos hw, core_of_unbordered_outer hun hu hw]

private lemma peelPairs_unbordered {α : Type} {w : List α} (hw : IsUnbordered w) :
    peelPairs w = 0 := by
  classical
  rw [peelPairs, dif_neg (by intro h; obtain ⟨b,hb⟩ := h; exact hw b hb)]

private lemma peelPairs_succ_iff {α : Type} {w : List α} (r : ℕ) :
    r + 1 ≤ peelPairs w ↔ ∃ u v, u ≠ [] ∧ IsUnbordered u ∧
      w = u ++ v ++ u ∧ r ≤ peelPairs v := by
  classical
  constructor
  · intro hr
    have hw : ∃ b, IsBorder w b := by
      by_contra h
      have hzero : peelPairs w = 0 := peelPairs_unbordered (by intro b hb; exact h ⟨b,hb⟩)
      omega
    have hb := shortestBorder_spec w hw
    refine ⟨shortestBorder w hw, peeledCore w hw, hb.1.1,
      shortest_border_unbordered hb, (peeledCore_spec w hw).1, ?_⟩
    rw [peelPairs, dif_pos hw] at hr
    omega
  · rintro ⟨u,v,hun,hu,rfl,hr⟩
    rw [peelPairs_outer hun hu]
    omega

noncomputable def tailWords (k n r : ℕ) : Finset (List (Fin k)) := by
  classical
  exact (DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter (fun w => r ≤ peelPairs w)

lemma mem_tailWords {k n r : ℕ} {w : List (Fin k)} :
    w ∈ tailWords k n r ↔ w.length = n ∧ r ≤ peelPairs w := by
  classical
  simp [tailWords, mem_words]

private noncomputable def tailOuterWords (k n i r : ℕ) : Finset (List (Fin k)) :=
  (ubWords k i ×ˢ tailWords k (n - 2 * i) r).image (fun p => p.1 ++ p.2 ++ p.1)

private lemma mem_tailOuterWords {k n i r : ℕ} {w : List (Fin k)} :
    w ∈ tailOuterWords k n i r ↔ ∃ u v, u.length = i ∧ IsUnbordered u ∧
      v.length = n - 2 * i ∧ r ≤ peelPairs v ∧ w = u ++ v ++ u := by
  classical
  simp only [tailOuterWords, Finset.mem_image, Finset.mem_product, mem_ubWords, mem_tailWords]
  constructor
  · rintro ⟨⟨u,v⟩,⟨⟨hui,hu⟩,⟨hvn,hr⟩⟩,he⟩
    exact ⟨u,v,hui,hu,hvn,hr,he.symm⟩
  · rintro ⟨u,v,hui,hu,hvn,hr,he⟩
    exact ⟨⟨u,v⟩,⟨⟨hui,hu⟩,⟨hvn,hr⟩⟩,he.symm⟩

private lemma card_tailOuterWords (k n i r : ℕ) :
    (tailOuterWords k n i r).card = uCount k i * (tailWords k (n - 2 * i) r).card := by
  classical
  have hinj : Set.InjOn (fun p : List (Fin k) × List (Fin k) => p.1 ++ p.2 ++ p.1)
      ↑(ubWords k i ×ˢ tailWords k (n - 2 * i) r) := by
    rintro ⟨u,v⟩ hp ⟨a,b⟩ hq he
    have hul := (mem_ubWords.mp (Finset.mem_product.mp hp).1).1
    have hal := (mem_ubWords.mp (Finset.mem_product.mp hq).1).1
    have hlen : u.length = a.length := hul.trans hal.symm
    have h1 : u = a := (List.append_inj (by simpa [List.append_assoc] using he) hlen).1
    subst a
    have h2 : v = b := by simpa [List.append_assoc] using he
    exact Prod.ext rfl h2
  rw [tailOuterWords, Finset.card_image_of_injOn hinj, Finset.card_product]
  rfl

private lemma tail_partition (k n r : ℕ) :
    tailWords k n (r + 1) = (Finset.Icc 1 (n / 2)).biUnion (fun i => tailOuterWords k n i r) := by
  classical
  ext w
  rw [mem_tailWords, peelPairs_succ_iff]
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨hwn,⟨u,v,hun,hu,hwu,hr⟩⟩
    have hlen : 2 * u.length + v.length = n := by
      have h := congrArg List.length hwu
      simp only [List.length_append] at h
      omega
    have hp := List.ne_nil_iff_length_pos.mp hun
    refine ⟨u.length, ⟨by omega, by omega⟩, ?_⟩
    apply mem_tailOuterWords.mpr
    exact ⟨u,v,rfl,hu,by omega,hr,hwu⟩
  · rintro ⟨i,⟨hi,hin⟩,hwi⟩
    obtain ⟨u,v,hui,hu,hvn,hr,hwu⟩ := mem_tailOuterWords.mp hwi
    have hun : u ≠ [] := by intro he; simp [he] at hui; omega
    have hwlen : w.length = n := by
      rw [hwu]
      simp only [List.length_append, hui, hvn]
      omega
    exact ⟨hwlen,u,v,hun,hu,hwu,hr⟩

theorem renewal_tail_count (k n r : ℕ) :
    (tailWords k n (r + 1)).card =
      ∑ i ∈ Finset.Icc 1 (n / 2), uCount k i * (tailWords k (n - 2 * i) r).card := by
  classical
  have hsub (i : ℕ) : tailOuterWords k n i r ⊆ outerWords k n i := by
    intro w hw
    obtain ⟨u,v,hui,hu,hvn,hr,he⟩ := mem_tailOuterWords.mp hw
    exact mem_outerWords.mpr ⟨u,v,hui,hu,hvn,he⟩
  have hdisj : (↑(Finset.Icc 1 (n / 2)) : Set ℕ).PairwiseDisjoint
      (fun i => tailOuterWords k n i r) := by
    intro i hi j hj hij
    exact (outerWords_disjoint (by have := (Finset.mem_Icc.mp hi).1; omega)
      (by have := (Finset.mem_Icc.mp hj).1; omega) hij).mono (hsub i) (hsub j)
  rw [tail_partition, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun i _ => card_tailOuterWords k n i r)





lemma tailWords_zero (k n : ℕ) : tailWords k n 0 = DepthBudgetIidGreedyOptimality.words (α := Fin k) n := by
  classical
  ext w
  simp [mem_tailWords, mem_words]

noncomputable def qCoeff (k i : ℕ) : ℝ :=
  if i = 0 then 0 else (uCount k i : ℝ) / (k : ℝ) ^ (2 * i)

lemma qCoeff_nonneg (k i : ℕ) : 0 ≤ qCoeff k i := by
  unfold qCoeff
  split_ifs <;> positivity

lemma qCoeff_summable {k : ℕ} (hk : 2 ≤ k) : Summable (qCoeff k) := by
  apply (summable_nat_add_iff 1).mp
  simpa [qCoeff] using q_summable_of_bound hk (uCount k) (uCount_bound k)

lemma tsum_qCoeff {k : ℕ} (hk : 2 ≤ k) : (∑' i : ℕ, qCoeff k i) = q k (uCount k) := by
  rw [(qCoeff_summable hk).tsum_eq_zero_add]
  simp [qCoeff, q]

lemma q_nonneg (k : ℕ) : 0 ≤ q k (uCount k) := by
  apply tsum_nonneg
  intro i
  positivity

private lemma unbordered_count_add (k n : ℕ) : uCount k n +
    (∑ i ∈ Finset.Icc 1 (n / 2), uCount k i * k^(n - 2 * i)) = k^n := by
  classical
  have hdisj : (↑(Finset.Icc 1 (n / 2)) : Set ℕ).PairwiseDisjoint (outerWords k n) := by
    intro i hi j hj hij
    exact outerWords_disjoint (by have := (Finset.mem_Icc.mp hi).1; omega)
      (by have := (Finset.mem_Icc.mp hj).1; omega) hij
  have hcard : (borderedWords k n).card =
      ∑ i ∈ Finset.Icc 1 (n / 2), uCount k i * k^(n - 2 * i) := by
    rw [shortest_partition,Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun i _ => card_outerWords k n i)
  rw [← hcard]
  have h := Finset.card_filter_add_card_filter_not (s := DepthBudgetIidGreedyOptimality.words (α := Fin k) n) IsUnbordered
  simpa [uCount,ubWords,borderedWords,card_words] using h

lemma qCoeff_recurrence {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 0 < n) :
    qCoeff k n = (1 - ∑ i ∈ Finset.Icc 1 (n / 2), qCoeff k i) / (k : ℝ)^n := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have he : (uCount k n : ℝ) +
      (∑ i ∈ Finset.Icc 1 (n / 2), (uCount k i : ℝ) * (k : ℝ)^(n - 2 * i)) = (k : ℝ)^n := by
    exact_mod_cast unbordered_count_add k n
  have hterm (i : ℕ) (hi : i ∈ Finset.Icc 1 (n / 2)) :
      (uCount k i : ℝ) * (k : ℝ)^(n - 2 * i) = qCoeff k i * (k : ℝ)^n := by
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    have hni : 2 * i ≤ n := by have := (Finset.mem_Icc.mp hi).2; omega
    have hpow : (k : ℝ)^n = (k : ℝ)^(2 * i) * (k : ℝ)^(n - 2 * i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [qCoeff,if_neg hi0,hpow]
    field_simp
  rw [Finset.sum_congr rfl hterm,← Finset.sum_mul] at he
  rw [qCoeff,if_neg (ne_of_gt hn),show 2 * n = n + n by omega,pow_add]
  field_simp [hk0]
  nlinarith


end D5.S1.Words.BlockPalindromes.GreedyRenewal
