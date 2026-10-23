/- GID: D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth
   generality: G
   mirror-B: D5/B/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth
   mirror-E: none(waiver:gabrić-shallit-expected-width)
   anchors: []
   utility: none
   digest: Gabrić–Shallit Conjecture 5 and its greedy renewal/composition proof. -/

/- The alphabet is Fin k; bs lists blocks from the centre outwards.
   The empty word is assigned width zero. The source's Lemma 3 is not used.
   proof_shape: tailProbability=not-applicable (definition).
   proof_shape: tailProbability_nonneg=bind-only.
     consumers: LargestFactorizationExpectedWidth.expectedWidth_limit, LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: tailProbability_zero=bind-only.
     consumers: LargestFactorizationExpectedWidth.renewal_tail_bound, LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: renewal_tail_bound=content. escape_witness: LargestFactorizationExpectedWidth.renewal_tail_bound.
   proof_shape: tailProbability_recursion=content. escape_witness: GreedyRenewal.renewal_tail_count.
     consumers: renewal_tail_bound, tsum_tailTerm.
   proof_shape: tailTerm=not-applicable (definition).
   proof_shape: tsum_tailTerm=content. escape_witness: GreedyRenewal.renewal_tail_count.
     consumers: renewal_tail_limit.
   proof_shape: renewal_tail_limit=content. escape_witness: LargestFactorizationExpectedWidth.renewal_tail_limit.
   proof_shape: peelCentre=not-applicable (definition).
   proof_shape: peelCentre_outer=bind-only.
     consumers: LargestFactorizationExpectedWidth.emptyCentre_iff_outer, LargestFactorizationExpectedWidth.empty_partition.
   proof_shape: peelCentre_empty=bind-only.
     consumers: LargestFactorizationExpectedWidth.emptyWords_zero.
   proof_shape: emptyCentre_iff_outer=content. escape_witness: LargestFactorizationExpectedWidth.emptyCentre_iff_outer.
   proof_shape: emptyWords=not-applicable (definition).
   proof_shape: mem_emptyWords=bind-only.
     consumers: LargestFactorizationExpectedWidth.emptyProbability_odd, LargestFactorizationExpectedWidth.emptyWords_zero, LargestFactorizationExpectedWidth.empty_partition, LargestFactorizationExpectedWidth.mem_emptyOuterWords.
   proof_shape: emptyWords_zero=bind-only.
     consumers: LargestFactorizationExpectedWidth.emptyProbability_zero.
   proof_shape: emptyOuterWords=not-applicable (definition).
   proof_shape: mem_emptyOuterWords=bind-only.
     consumers: LargestFactorizationExpectedWidth.empty_centre_count, LargestFactorizationExpectedWidth.empty_partition.
   proof_shape: card_emptyOuterWords=bind-only.
     consumers: LargestFactorizationExpectedWidth.empty_centre_count.
   proof_shape: empty_partition=content. escape_witness: LargestFactorizationExpectedWidth.empty_partition.
   proof_shape: empty_centre_count=content. escape_witness: LargestFactorizationExpectedWidth.empty_centre_count.
   proof_shape: emptyProbability=not-applicable (definition).
   proof_shape: emptyProbability_zero=bind-only.
     consumers: LargestFactorizationExpectedWidth.empty_centre_powerSeries.
   proof_shape: emptyProbability_recursion=content. escape_witness: LargestFactorizationExpectedWidth.empty_centre_count.
     consumers: emptyProbability_even_recursion.
   proof_shape: emptyProbability_even_recursion=content. escape_witness: LargestFactorizationExpectedWidth.empty_centre_count.
     consumers: empty_centre_powerSeries.
   proof_shape: QSeries=not-applicable (definition).
   proof_shape: ESeries=not-applicable (definition).
   proof_shape: QSeries_constant_zero=bind-only.
     consumers: LargestFactorizationExpectedWidth.empty_centre_powerSeries, LargestFactorizationExpectedWidth.empty_even_convolution.
   proof_shape: empty_centre_powerSeries=content. escape_witness: LargestFactorizationExpectedWidth.empty_centre_powerSeries.
   proof_shape: emptyProbability_nonneg=bind-only.
     consumers: LargestFactorizationExpectedWidth.empty_even_summable, LargestFactorizationExpectedWidth.empty_probability_limit.
   proof_shape: empty_even_convolution=content. escape_witness: LargestFactorizationExpectedWidth.empty_centre_powerSeries.
     consumers: empty_partial_sum.
   proof_shape: empty_partial_sum=content. escape_witness: LargestFactorizationExpectedWidth.empty_centre_powerSeries.
     consumers: empty_partial_sum_bound.
   proof_shape: empty_partial_sum_bound=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
     consumers: empty_even_summable.
   proof_shape: empty_even_summable=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
     consumers: empty_probability_limit.
   proof_shape: peelCentre_length_mod_two=content. escape_witness: LargestFactorizationExpectedWidth.peelCentre_length_mod_two.
     consumers: emptyProbability_odd.
   proof_shape: emptyProbability_odd=content. escape_witness: LargestFactorizationExpectedWidth.peelCentre_length_mod_two.
     consumers: empty_probability_limit.
   proof_shape: empty_probability_limit=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
     consumers: expectedWidth_limit.
   proof_shape: largest_pairs_centre=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
   proof_shape: peelPairs_le_length=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
     consumers: tailWords_empty, pair_tail_sum.
   proof_shape: tailWords_empty=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
     consumers: tsum_positive_tails.
   proof_shape: tsum_positive_tails=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
     consumers: mean_pairs_tail.
   proof_shape: pair_tail_sum=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
     consumers: mean_pairs_tail.
   proof_shape: mean_pairs_tail=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
     consumers: expectedWidth_tail_formula.
   proof_shape: expectedWidth=not-applicable (definition).
   proof_shape: sum_words_ofFn=bind-only.
     consumers: LargestFactorizationExpectedWidth.expectedWidth_weighted_count.
   proof_shape: width_count_grouping=bind-only.
     consumers: LargestFactorizationExpectedWidth.expectedWidth_tail_formula, LargestFactorizationExpectedWidth.expectedWidth_weighted_count.
   proof_shape: expectedWidth_weighted_count=bind-only.
     consumers: LargestFactorizationExpectedWidth.expectedWidth_tail_formula.
   proof_shape: expectedWidth_tail_formula=content. escape_witness: LargestFactorizationExpectedWidth.largest_pairs_centre.
     consumers: expectedWidth_limit.
   proof_shape: positive_q_powers_summable=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
     consumers: expectedWidth_limit.
   proof_shape: positive_q_powers_tsum=content. escape_witness: GreedyRenewal.unbordered_count_recurrence.
     consumers: expectedWidth_limit.
   proof_shape: expectedWidth_limit=content. escape_witness: LargestFactorizationExpectedWidth.expectedWidth_limit.
   proof_shape: claim=not-applicable (definition).
   proof_shape: stable_series_summable=content. escape_witness: CompositionInversion.composition_series_summable.
     consumers: coefficient_series_summable, conjectured_limit_identity.
   proof_shape: stable_series_identity=content. escape_witness: CompositionInversion.unbordered_composition_series.
     consumers: conjectured_limit_identity.
   proof_shape: coefficient_series_summable=content. escape_witness: CompositionInversion.composition_series_summable.
     consumers: coefficient_limit_results.
   proof_shape: conjectured_limit_identity=content. escape_witness: CompositionInversion.unbordered_composition_series.
     consumers: coefficient_limit_results.
   proof_shape: coefficient_limit_results=content. escape_witness: LargestFactorizationExpectedWidth.expectedWidth_limit.
     consumers: result.
   proof_shape: result=content. escape_witness: LargestFactorizationExpectedWidth.expectedWidth_limit.
   escape_witness: LargestFactorizationExpectedWidth.expectedWidth_limit
   admission_basis: open-problem-resolution (#15445; Proved)
   Direct frozen dependencies: D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.words
     statement_id: sha256:ac39f4d6ac85644b4d36960e026f51c85dafd409386991d3defafb1ebead5aa6.
   The frozen words declaration above is used by:
     tailProbability, tailProbability_nonneg, tailProbability_zero, renewal_tail_bound,
     tailProbability_recursion, tailTerm, tsum_tailTerm, renewal_tail_limit, emptyWords,
     mem_emptyWords, emptyWords_zero, emptyOuterWords, mem_emptyOuterWords, card_emptyOuterWords,
     empty_partition, empty_centre_count, emptyProbability, emptyProbability_zero,
     emptyProbability_recursion, emptyProbability_even_recursion, QSeries, ESeries,
     QSeries_constant_zero, empty_centre_powerSeries, emptyProbability_nonneg,
     empty_even_convolution, empty_partial_sum, empty_partial_sum_bound, empty_even_summable,
     emptyProbability_odd, empty_probability_limit, tailWords_empty, tsum_positive_tails,
     pair_tail_sum, mean_pairs_tail, sum_words_ofFn, width_count_grouping,
     expectedWidth_weighted_count, expectedWidth_tail_formula, positive_q_powers_summable,
     positive_q_powers_tsum, expectedWidth_limit, stable_series_identity,
     conjectured_limit_identity, coefficient_limit_results, result.
   Direct frozen dependencies of all other declarations: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15783
   DTR reading: DTR-Unregistered (Observe) for all 4 public theorem audit targets.
   Missing evidence: source-bound dependent-family variation, sensitivity,
   observational dependence, and a compiled enrolled four-slot registration.
-/

import D5.S1.Words.BlockPalindromes.CompositionInversion
import Mathlib.RingTheory.PowerSeries.Inverse
open scoped BigOperators
open Set Finset Filter Topology
open D5.S0.Computability.Coding
open D5.S1.Words.BlockPalindromes.GreedyRenewal
open D5.S1.Words.BlockPalindromes.CompositionInversion
namespace D5.S1.Words.BlockPalindromes.LargestFactorizationExpectedWidth


noncomputable def tailProbability (k n r : ℕ) : ℝ :=
  ((tailWords k n r).card : ℝ) / (k : ℝ) ^ n

private lemma tailProbability_nonneg (k n r : ℕ) : 0 ≤ tailProbability k n r := by
  unfold tailProbability
  positivity

private lemma tailProbability_zero {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : tailProbability k n 0 = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  simp [tailProbability, tailWords_zero, card_words, hk0]

private lemma tailProbability_recursion {k : ℕ} (hk : 2 ≤ k) (n r : ℕ) :
    tailProbability k n (r + 1) =
      ∑ i ∈ Finset.Icc 1 (n / 2), qCoeff k i * tailProbability k (n - 2 * i) r := by
  classical
  unfold tailProbability
  rw [renewal_tail_count]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : 0 < i := by have := (Finset.mem_Icc.mp hi).1; omega
  have hile : 2 * i ≤ n := by have := (Finset.mem_Icc.mp hi).2; omega
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have he : (k : ℝ) ^ n = (k : ℝ) ^ (2 * i) * (k : ℝ) ^ (n - 2 * i) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [qCoeff, ne_of_gt hip, if_false]
  rw [he]
  field_simp

private theorem renewal_tail_bound {k : ℕ} (hk : 2 ≤ k) (n r : ℕ) :
    tailProbability k n r ≤ q k (uCount k) ^ r := by
  induction r generalizing n with
  | zero => simp [tailProbability_zero hk]
  | succ r ih =>
    rw [tailProbability_recursion hk]
    calc
      (∑ i ∈ Finset.Icc 1 (n / 2), qCoeff k i * tailProbability k (n - 2 * i) r) ≤
          ∑ i ∈ Finset.Icc 1 (n / 2), qCoeff k i * q k (uCount k) ^ r := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (ih _) (qCoeff_nonneg k i)
      _ = (∑ i ∈ Finset.Icc 1 (n / 2), qCoeff k i) * q k (uCount k) ^ r := by
        rw [Finset.sum_mul]
      _ ≤ q k (uCount k) * q k (uCount k) ^ r := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (q_nonneg k) _)
        rw [← tsum_qCoeff hk]
        exact (qCoeff_summable hk).sum_le_tsum _ (fun i _ => qCoeff_nonneg k i)
      _ = q k (uCount k) ^ (r + 1) := by ring


private noncomputable def tailTerm (k r n i : ℕ) : ℝ :=
  if i ∈ Finset.Icc 1 (n / 2) then qCoeff k i * tailProbability k (n - 2 * i) r else 0

private lemma tsum_tailTerm {k : ℕ} (hk : 2 ≤ k) (n r : ℕ) :
    (∑' i : ℕ, tailTerm k r n i) = tailProbability k n (r + 1) := by
  rw [tailProbability_recursion hk]
  rw [tsum_eq_sum (s := Finset.Icc 1 (n / 2))]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [tailTerm, hi]
  · intro i hi
    simp [tailTerm, hi]

theorem renewal_tail_limit {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    Tendsto (fun n => tailProbability k n r) atTop (𝓝 (q k (uCount k) ^ r)) := by
  induction r with
  | zero => simpa [tailProbability_zero hk] using tendsto_const_nhds
  | succ r ih =>
    let limit : ℕ → ℝ := fun i => qCoeff k i * q k (uCount k) ^ r
    have hboundSum : Summable limit := (qCoeff_summable hk).mul_right _
    have hpoint (i : ℕ) : Tendsto (fun n => tailTerm k r n i) atTop (𝓝 (limit i)) := by
      by_cases hi0 : i = 0
      · subst i
        simp [tailTerm, limit, qCoeff]
      · have ht : Tendsto (fun n => qCoeff k i * tailProbability k (n - 2 * i) r)
            atTop (𝓝 (limit i)) :=
          tendsto_const_nhds.mul (ih.comp (tendsto_sub_atTop_nat (2 * i)))
        apply ht.congr'
        filter_upwards [eventually_ge_atTop (2 * i)] with n hn
        have hi : i ∈ Finset.Icc 1 (n / 2) := by simp only [Finset.mem_Icc]; omega
        simp [tailTerm, hi]
    have hbound : ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, ‖tailTerm k r n i‖ ≤ limit i := by
      apply Filter.Eventually.of_forall
      intro n i
      unfold tailTerm
      split_ifs with hi
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (qCoeff_nonneg _ _) (tailProbability_nonneg _ _ _))]
        exact mul_le_mul_of_nonneg_left (renewal_tail_bound hk _ _) (qCoeff_nonneg k i)
      · simp only [norm_zero]
        exact mul_nonneg (qCoeff_nonneg _ _) (pow_nonneg (q_nonneg _) _)
    have ht := tendsto_tsum_of_dominated_convergence hboundSum hpoint hbound
    have hlim : (∑' i : ℕ, limit i) = q k (uCount k) ^ (r + 1) := by
      simp only [limit, tsum_mul_right, tsum_qCoeff hk]
      ring
    simpa only [tsum_tailTerm hk, hlim] using ht


noncomputable def peelCentre {α : Type} (w : List α) : List α := by
  classical
  exact if hw : ∃ b, IsBorder w b then peelCentre (peeledCore w hw) else w
termination_by w.length
decreasing_by exact peeledCore_shorter w hw

private lemma peelCentre_outer {α : Type} {u v : List α} (hun : u ≠ []) (hu : IsUnbordered u) :
    peelCentre (u ++ v ++ u) = peelCentre v := by
  classical
  have hw : ∃ b, IsBorder (u ++ v ++ u) b := ⟨u,(unbordered_outer_shortest hun hu).1⟩
  rw [peelCentre, dif_pos hw, core_of_unbordered_outer hun hu hw]

private lemma peelCentre_empty : peelCentre ([] : List α) = [] := by
  classical
  rw [peelCentre, dif_neg (by simp [IsBorder])]

private lemma emptyCentre_iff_outer {α : Type} {w : List α} (hwn : w ≠ []) :
    peelCentre w = [] ↔ ∃ u v, u ≠ [] ∧ IsUnbordered u ∧
      w = u ++ v ++ u ∧ peelCentre v = [] := by
  classical
  constructor
  · intro hc
    have hw : ∃ b, IsBorder w b := by
      by_contra h
      rw [peelCentre, dif_neg h] at hc
      exact hwn hc
    have hb := shortestBorder_spec w hw
    refine ⟨shortestBorder w hw,peeledCore w hw,hb.1.1,
      shortest_border_unbordered hb,(peeledCore_spec w hw).1,?_⟩
    rw [peelCentre, dif_pos hw] at hc
    exact hc
  · rintro ⟨u,v,hun,hu,rfl,hc⟩
    simpa only [peelCentre_outer hun hu] using hc

noncomputable def emptyWords (k n : ℕ) : Finset (List (Fin k)) := by
  classical
  exact (DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter (fun w => peelCentre w = [])

private lemma mem_emptyWords {k n : ℕ} {w : List (Fin k)} :
    w ∈ emptyWords k n ↔ w.length = n ∧ peelCentre w = [] := by
  classical
  simp [emptyWords,mem_words]

private lemma emptyWords_zero (k : ℕ) : emptyWords k 0 = {[]} := by
  classical
  ext w
  rw [mem_emptyWords, Finset.mem_singleton]
  constructor
  · intro h
    exact List.length_eq_zero_iff.mp h.1
  · rintro rfl
    exact ⟨rfl,peelCentre_empty⟩

private noncomputable def emptyOuterWords (k n i : ℕ) : Finset (List (Fin k)) :=
  (ubWords k i ×ˢ emptyWords k (n - 2 * i)).image (fun p => p.1 ++ p.2 ++ p.1)

private lemma mem_emptyOuterWords {k n i : ℕ} {w : List (Fin k)} :
    w ∈ emptyOuterWords k n i ↔ ∃ u v, u.length = i ∧ IsUnbordered u ∧
      v.length = n - 2 * i ∧ peelCentre v = [] ∧ w = u ++ v ++ u := by
  classical
  simp only [emptyOuterWords, Finset.mem_image, Finset.mem_product, mem_ubWords, mem_emptyWords]
  constructor
  · rintro ⟨⟨u,v⟩,⟨⟨hui,hu⟩,⟨hvn,hc⟩⟩,he⟩
    exact ⟨u,v,hui,hu,hvn,hc,he.symm⟩
  · rintro ⟨u,v,hui,hu,hvn,hc,he⟩
    exact ⟨⟨u,v⟩,⟨⟨hui,hu⟩,⟨hvn,hc⟩⟩,he.symm⟩

private lemma card_emptyOuterWords (k n i : ℕ) :
    (emptyOuterWords k n i).card = uCount k i * (emptyWords k (n - 2 * i)).card := by
  classical
  have hinj : Set.InjOn (fun p : List (Fin k) × List (Fin k) => p.1 ++ p.2 ++ p.1)
      ↑(ubWords k i ×ˢ emptyWords k (n - 2 * i)) := by
    rintro ⟨u,v⟩ hp ⟨a,b⟩ hq he
    have hul := (mem_ubWords.mp (Finset.mem_product.mp hp).1).1
    have hal := (mem_ubWords.mp (Finset.mem_product.mp hq).1).1
    have hlen : u.length = a.length := hul.trans hal.symm
    have h1 : u = a := (List.append_inj (by simpa [List.append_assoc] using he) hlen).1
    subst a
    have h2 : v = b := by simpa [List.append_assoc] using he
    exact Prod.ext rfl h2
  rw [emptyOuterWords, Finset.card_image_of_injOn hinj, Finset.card_product]
  rfl

private lemma empty_partition (k n : ℕ) (hn : 0 < n) :
    emptyWords k n = (Finset.Icc 1 (n / 2)).biUnion (emptyOuterWords k n) := by
  classical
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · intro hw
    obtain ⟨hwn,hc⟩ := mem_emptyWords.mp hw
    have hnonempty : w ≠ [] := by intro he; simp [he] at hwn; omega
    obtain ⟨u,v,hun,hu,hwu,hvc⟩ := (emptyCentre_iff_outer hnonempty).mp hc
    have hlen : 2 * u.length + v.length = n := by
      have h := congrArg List.length hwu
      simp only [List.length_append] at h
      omega
    have hp := List.ne_nil_iff_length_pos.mp hun
    exact ⟨u.length,⟨by omega,by omega⟩,
      mem_emptyOuterWords.mpr ⟨u,v,rfl,hu,by omega,hvc,hwu⟩⟩
  · rintro ⟨i,⟨hi,hin⟩,hwi⟩
    obtain ⟨u,v,hui,hu,hvn,hvc,hwu⟩ := mem_emptyOuterWords.mp hwi
    have hun : u ≠ [] := by intro he; simp [he] at hui; omega
    apply mem_emptyWords.mpr
    rw [hwu]
    refine ⟨?_,?_⟩
    · simp only [List.length_append,hui,hvn]
      omega
    · simpa only [peelCentre_outer hun hu] using hvc

private theorem empty_centre_count (k n : ℕ) (hn : 0 < n) :
    (emptyWords k n).card = ∑ i ∈ Finset.Icc 1 (n / 2),
      uCount k i * (emptyWords k (n - 2 * i)).card := by
  classical
  have hsub (i : ℕ) : emptyOuterWords k n i ⊆ outerWords k n i := by
    intro w hw
    obtain ⟨u,v,hui,hu,hvn,hc,he⟩ := mem_emptyOuterWords.mp hw
    exact mem_outerWords.mpr ⟨u,v,hui,hu,hvn,he⟩
  have hdisj : (↑(Finset.Icc 1 (n / 2)) : Set ℕ).PairwiseDisjoint (emptyOuterWords k n) := by
    intro i hi j hj hij
    exact (outerWords_disjoint (by have := (Finset.mem_Icc.mp hi).1; omega)
      (by have := (Finset.mem_Icc.mp hj).1; omega) hij).mono (hsub i) (hsub j)
  rw [empty_partition k n hn,Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun i _ => card_emptyOuterWords k n i)


noncomputable def emptyProbability (k n : ℕ) : ℝ :=
  ((emptyWords k n).card : ℝ) / (k : ℝ) ^ n

private lemma emptyProbability_zero (k : ℕ) : emptyProbability k 0 = 1 := by
  simp [emptyProbability,emptyWords_zero]

private lemma emptyProbability_recursion {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 0 < n) :
    emptyProbability k n = ∑ i ∈ Finset.Icc 1 (n / 2),
      qCoeff k i * emptyProbability k (n - 2 * i) := by
  classical
  unfold emptyProbability
  rw [empty_centre_count k n hn]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : 0 < i := by have := (Finset.mem_Icc.mp hi).1; omega
  have hile : 2 * i ≤ n := by have := (Finset.mem_Icc.mp hi).2; omega
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have he : (k : ℝ) ^ n = (k : ℝ) ^ (2 * i) * (k : ℝ) ^ (n - 2 * i) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [qCoeff,ne_of_gt hip,if_false]
  rw [he]
  field_simp

private lemma emptyProbability_even_recursion {k : ℕ} (hk : 2 ≤ k) (m : ℕ) (hm : 0 < m) :
    emptyProbability k (2 * m) = ∑ i ∈ Finset.Icc 1 m,
      qCoeff k i * emptyProbability k (2 * (m - i)) := by
  rw [emptyProbability_recursion hk _ (by omega)]
  simp only [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  omega

noncomputable def QSeries (k : ℕ) : PowerSeries ℝ := PowerSeries.mk (qCoeff k)
noncomputable def ESeries (k : ℕ) : PowerSeries ℝ := PowerSeries.mk (fun m => emptyProbability k (2 * m))

private lemma QSeries_constant_zero (k : ℕ) : PowerSeries.constantCoeff (QSeries k) = 0 := by
  simp [QSeries,qCoeff]

theorem empty_centre_powerSeries {k : ℕ} (hk : 2 ≤ k) :
    ESeries k = (1 - QSeries k)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [QSeries_constant_zero])).mpr
  rw [mul_comm,sub_mul,one_mul]
  ext m
  simp only [map_sub,PowerSeries.coeff_mk,ESeries,PowerSeries.coeff_mul,
    QSeries,PowerSeries.coeff_one]
  by_cases hm : m = 0
  · subst m
    simp [emptyProbability_zero,qCoeff]
  · rw [if_neg hm,sub_eq_zero,emptyProbability_even_recursion hk _ (by omega)]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hset : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
      ext i
      simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
      omega
    rw [hset,Finset.sum_insert (by simp)]
    simp [qCoeff]


private lemma emptyProbability_nonneg (k n : ℕ) : 0 ≤ emptyProbability k n := by
  unfold emptyProbability
  positivity

private lemma empty_even_convolution {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    emptyProbability k (2 * m) = (if m = 0 then 1 else 0) +
      ∑ i ∈ Finset.range (m + 1), qCoeff k i * emptyProbability k (2 * (m - i)) := by
  have hp : ESeries k * (1 - QSeries k) = 1 :=
    (PowerSeries.eq_inv_iff_mul_eq_one (by simp [QSeries_constant_zero])).mp (empty_centre_powerSeries hk)
  rw [mul_comm,sub_mul,one_mul] at hp
  have hc := congrArg (PowerSeries.coeff (R := ℝ) m) hp
  simp only [map_sub,PowerSeries.coeff_mk,ESeries,PowerSeries.coeff_mul,
    QSeries,PowerSeries.coeff_one] at hc
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  linarith

private lemma empty_partial_sum {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), emptyProbability k (2 * m)) = 1 +
      ∑ i ∈ Finset.range (n + 1), qCoeff k i *
        ∑ m ∈ Finset.range (n + 1 - i), emptyProbability k (2 * m) := by
  have hc : (∑ m ∈ Finset.range (n + 1), emptyProbability k (2 * m)) =
      ∑ m ∈ Finset.range (n + 1), ((if m = 0 then 1 else 0) +
        ∑ i ∈ Finset.range (m + 1), qCoeff k i * emptyProbability k (2 * (m - i))) :=
    Finset.sum_congr rfl (fun m _ => empty_even_convolution hk m)
  rw [hc]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ m ∈ Finset.range (n + 1), if m = 0 then (1 : ℝ) else 0) = 1 := by
    simp
  rw [hfirst, Finset.sum_range_diag_flip (n + 1) (fun i m => qCoeff k i * emptyProbability k (2 * m))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

private lemma empty_partial_sum_bound {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), emptyProbability k (2 * m)) ≤
      1 / (1 - q k (uCount k)) := by
  have hq := unbordered_q_lt_one hk
  have hB : 0 ≤ 1 / (1 - q k (uCount k)) := by positivity
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [empty_partial_sum hk]
    have hsum :
        (∑ i ∈ Finset.range (n + 1), qCoeff k i *
          ∑ m ∈ Finset.range (n + 1 - i), emptyProbability k (2 * m)) ≤
        (∑ i ∈ Finset.range (n + 1), qCoeff k i) * (1 / (1 - q k (uCount k))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simp [qCoeff]
      · have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
        have heq : n + 1 - i = (n - i) + 1 := by omega
        rw [heq]
        exact mul_le_mul_of_nonneg_left (ih (n - i) (by omega)) (qCoeff_nonneg _ _)
    have hmass : (∑ i ∈ Finset.range (n + 1), qCoeff k i) ≤ q k (uCount k) := by
      rw [← tsum_qCoeff hk]
      exact (qCoeff_summable hk).sum_le_tsum _ (fun i _ => qCoeff_nonneg k i)
    calc
      _ ≤ 1 + (∑ i ∈ Finset.range (n + 1), qCoeff k i) * (1 / (1 - q k (uCount k))) := by linarith
      _ ≤ 1 + q k (uCount k) * (1 / (1 - q k (uCount k))) := by
        linarith [mul_le_mul_of_nonneg_right hmass hB]
      _ = 1 / (1 - q k (uCount k)) := by
        field_simp [ne_of_gt (sub_pos.mpr hq)]
        <;> ring

private theorem empty_even_summable {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun m => emptyProbability k (2 * m)) := by
  apply summable_of_sum_range_le (fun m => emptyProbability_nonneg k (2 * m))
    (c := 1 / (1 - q k (uCount k)))
  intro n
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr (unbordered_q_lt_one hk)))
  | succ n => exact empty_partial_sum_bound hk n

private lemma peelCentre_length_mod_two {α : Type} (w : List α) :
    (peelCentre w).length % 2 = w.length % 2 := by
  classical
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    by_cases hw : ∃ b, IsBorder w b
    · rw [peelCentre, dif_pos hw, ih _ (peeledCore_shorter w hw)]
      have he := (peeledCore_spec w hw).1
      have hl := congrArg List.length he
      simp only [List.length_append] at hl
      omega
    · rw [peelCentre, dif_neg hw]

private lemma emptyProbability_odd (k n : ℕ) (hn : n % 2 = 1) : emptyProbability k n = 0 := by
  classical
  have he : emptyWords k n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro w hw
    obtain ⟨hlen,hc⟩ := mem_emptyWords.mp hw
    have hm := peelCentre_length_mod_two w
    simp only [hc, List.length_nil, Nat.zero_mod, hlen, hn] at hm
    omega
  simp [emptyProbability,he]

private theorem empty_probability_limit {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (emptyProbability k) atTop (𝓝 0) := by
  have he := (empty_even_summable hk).tendsto_atTop_zero
  have hd : Tendsto (fun n : ℕ => n / 2) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  have hev := he.comp hd
  apply squeeze_zero (fun n => emptyProbability_nonneg k n) _ hev
  intro n
  by_cases hn : n % 2 = 0
  · have heq : 2 * (n / 2) = n := by omega
    simp [heq]
  · have hn1 : n % 2 = 1 := by omega
    rw [emptyProbability_odd k n hn1]
    exact emptyProbability_nonneg _ _

private theorem largest_pairs_centre {α : Type} (w : List α) :
    largestBPWidth w = 2 * peelPairs w + if peelCentre w = [] then 0 else 1 := by
  classical
  rw [largest_eq_peelWidth]
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    by_cases hw : ∃ b, IsBorder w b
    · rw [peelWidth, dif_pos hw, peelPairs, dif_pos hw,
        peelCentre, dif_pos hw, ih _ (peeledCore_shorter w hw)]
      omega
    · rw [peelWidth, dif_neg hw, peelPairs, dif_neg hw, peelCentre, dif_neg hw]
      simp




private lemma peelPairs_le_length {α : Type} (w : List α) : peelPairs w ≤ w.length := by
  have h := largestBPWidth_le_length w
  rw [largest_pairs_centre] at h
  omega

private lemma tailWords_empty {k n r : ℕ} (hr : n < r) : tailWords k n r = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  obtain ⟨hn,hp⟩ := mem_tailWords.mp hw
  have hb := peelPairs_le_length w
  omega

private lemma tsum_positive_tails (k n : ℕ) :
    (∑' r : ℕ, tailProbability k n (r + 1)) =
      ∑ r ∈ Finset.range n, tailProbability k n (r + 1) := by
  apply tsum_eq_sum
  intro r hr
  have hnr : n < r + 1 := by
    have hh : ¬ r < n := by simpa only [Finset.mem_range] using hr
    omega
  simp [tailProbability,tailWords_empty hnr]

private lemma pair_tail_sum (k n : ℕ) :
    (∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n, (peelPairs w : ℝ)) =
      ∑ r ∈ Finset.range n, ((tailWords k n (r + 1)).card : ℝ) := by
  classical
  have hone (w : List (Fin k)) (hw : w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n) :
      (peelPairs w : ℝ) = ∑ r ∈ Finset.range n, if r + 1 ≤ peelPairs w then (1 : ℝ) else 0 := by
    have hp : peelPairs w ≤ n := by simpa only [mem_words.mp hw] using peelPairs_le_length w
    have hfilter : (Finset.range n).filter (fun r => r + 1 ≤ peelPairs w) = Finset.range (peelPairs w) := by
      ext r
      simp only [Finset.mem_filter,Finset.mem_range]
      omega
    rw [Finset.sum_boole, hfilter, Finset.card_range]
  rw [Finset.sum_congr rfl hone,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp [tailWords]

private lemma mean_pairs_tail (k n : ℕ) :
    (∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n, (peelPairs w : ℝ)) / (k : ℝ)^n =
      ∑' r : ℕ, tailProbability k n (r + 1) := by
  rw [tsum_positive_tails, pair_tail_sum,Finset.sum_div]
  rfl

noncomputable def expectedWidth (k n : ℕ) : ℝ :=
  (∑ w : Fin n → Fin k, (largestBPWidth (List.ofFn w) : ℝ)) / (k : ℝ) ^ n

private lemma sum_words_ofFn (k n : ℕ) (f : List (Fin k) → ℝ) :
    (∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n, f w) = ∑ w : Fin n → Fin k, f (List.ofFn w) := by
  classical
  have he : DepthBudgetIidGreedyOptimality.words (α := Fin k) n =
      (Finset.univ : Finset (Fin n → Fin k)).image List.ofFn := by
    ext w
    rw [mem_words]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hw
      subst n
      exact ⟨w.get, List.ofFn_get w⟩
    · rintro ⟨g, rfl⟩
      exact List.length_ofFn
  rw [he,Finset.sum_image]
  intro a ha b hb he
  exact List.ofFn_injective he

private lemma width_count_grouping (k n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (i : ℝ) *
      (((DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter
        (fun w => largestBPWidth w = i)).card : ℝ)) =
      ∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n,
        (largestBPWidth w : ℝ) := by
  classical
  have hcount (i : ℕ) : (i : ℝ) *
      (((DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter
        (fun w => largestBPWidth w = i)).card : ℝ) =
      ∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n,
        if largestBPWidth w = i then (i : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hcount i), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hle : largestBPWidth w ≤ n := by
    simpa only [mem_words.mp hw] using largestBPWidth_le_length w
  by_cases hz : largestBPWidth w = 0
  · simp [hz]
  · have hmem : largestBPWidth w ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz, hle⟩
    simp [hmem]

private lemma expectedWidth_weighted_count (k n : ℕ) :
    expectedWidth k n =
      (∑ i ∈ Finset.Icc 1 n, (i : ℝ) *
        (((DepthBudgetIidGreedyOptimality.words (α := Fin k) n).filter
          (fun w => largestBPWidth w = i)).card : ℝ)) / (k : ℝ) ^ n := by
  rw [expectedWidth, width_count_grouping, sum_words_ofFn]

private lemma expectedWidth_tail_formula {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    expectedWidth k n = 2 * (∑' r : ℕ, tailProbability k n (r + 1)) +
      1 - emptyProbability k n := by
  classical
  have hsum : (∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n, (largestBPWidth w : ℝ)) =
      2 * (∑ w ∈ DepthBudgetIidGreedyOptimality.words (α := Fin k) n, (peelPairs w : ℝ)) +
        ((DepthBudgetIidGreedyOptimality.words (α := Fin k) n).card : ℝ) - ((emptyWords k n).card : ℝ) := by
    have hw (w : List (Fin k)) : (largestBPWidth w : ℝ) =
        2 * (peelPairs w : ℝ) + 1 - (if peelCentre w = [] then 1 else 0) := by
      rw [largest_pairs_centre]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl (fun w _ => hw w)]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, mul_one,Finset.sum_boole]
    rfl
  rw [expectedWidth_weighted_count, width_count_grouping, hsum, card_words]
  push_cast
  rw [sub_div,add_div,mul_div_assoc, mean_pairs_tail]
  have hkn : (k : ℝ)^n ≠ 0 := by positivity
  simp only [div_self hkn]
  rfl

private lemma positive_q_powers_summable {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun r : ℕ => q k (uCount k)^(r + 1)) := by
  exact (summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (q_nonneg k) (unbordered_q_lt_one hk))

private lemma positive_q_powers_tsum {k : ℕ} (hk : 2 ≤ k) :
    (∑' r : ℕ, q k (uCount k)^(r + 1)) = 1 / (1 - q k (uCount k)) - 1 := by
  have hgeom := summable_geometric_of_lt_one (q_nonneg k) (unbordered_q_lt_one hk)
  have ht := hgeom.tsum_eq_zero_add
  rw [tsum_geometric_of_lt_one (q_nonneg k) (unbordered_q_lt_one hk)] at ht
  simp only [pow_zero] at ht
  rw [one_div]
  linarith

theorem expectedWidth_limit {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (expectedWidth k) atTop (𝓝 (2 / (1 - q k (uCount k)) - 1)) := by
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      ‖tailProbability k n (r + 1)‖ ≤ q k (uCount k)^(r + 1) := by
    apply Filter.Eventually.of_forall
    intro n r
    rw [Real.norm_eq_abs,abs_of_nonneg (tailProbability_nonneg _ _ _)]
    exact renewal_tail_bound hk n (r + 1)
  have ht := tendsto_tsum_of_dominated_convergence (positive_q_powers_summable hk)
    (fun r => renewal_tail_limit hk (r + 1)) hbound
  rw [positive_q_powers_tsum hk] at ht
  have he : Tendsto (fun n => 2 * (∑' r : ℕ, tailProbability k n (r + 1)) +
      1 - emptyProbability k n) atTop
      (𝓝 (2 * (1 / (1 - q k (uCount k)) - 1) + 1 - 0)) :=
    ((tendsto_const_nhds.mul ht).add tendsto_const_nhds).sub (empty_probability_limit hk)
  have hlim : 2 * (1 / (1 - q k (uCount k)) - 1) + 1 - 0 =
      2 / (1 - q k (uCount k)) - 1 := by ring
  simpa only [← expectedWidth_tail_formula hk,hlim] using he



def claim : Prop := ∀ k : ℕ, 2 ≤ k → ∃ a : ℕ → ℝ,
    (∀ d, Tendsto (fun N : ℕ => (a274190 N (N - d) : ℝ)) atTop (𝓝 (a d))) ∧
    Summable (fun i : ℕ => 2 * a (i + 1) / (k : ℝ) ^ (i + 1)) ∧
    Tendsto (fun n => expectedWidth k n) atTop (𝓝 (1 + ∑' i : ℕ, 2 * a (i + 1) / (k : ℝ) ^ (i + 1)))

private lemma stable_series_summable {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun d : ℕ => (a274190 (2 * d) d : ℝ) / (k : ℝ)^d) := by
  simpa only [a274190_stable_compCount] using composition_series_summable hk

private lemma stable_series_identity {k : ℕ} (hk : 2 ≤ k) :
    (∑' d : ℕ, (a274190 (2 * d) d : ℝ) / (k : ℝ)^d) =
      1 / (1 - q k (uCount k)) := by
  simpa only [totalSeries,compTerm,a274190_stable_compCount] using unbordered_composition_series hk

private lemma coefficient_series_summable {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun i : ℕ => 2 * (a274190 (2 * (i + 1)) (i + 1) : ℝ) / (k : ℝ)^(i + 1)) := by
  have hs := (summable_nat_add_iff 1).mpr (stable_series_summable hk)
  simpa only [mul_div_assoc] using hs.mul_left 2

private lemma conjectured_limit_identity {k : ℕ} (hk : 2 ≤ k) :
    2 / (1 - q k (uCount k)) - 1 =
      1 + ∑' i : ℕ, 2 * (a274190 (2 * (i + 1)) (i + 1) : ℝ) / (k : ℝ)^(i + 1) := by
  have he := (stable_series_summable hk).tsum_eq_zero_add
  rw [stable_series_identity hk] at he
  simp only [Nat.mul_zero,a274190.eq_1,pow_zero,Nat.cast_one,div_one] at he
  simp only [mul_div_assoc,tsum_mul_left]
  simp only [div_eq_mul_inv,one_mul] at he ⊢
  linarith

private lemma coefficient_limit_results : ∀ k : ℕ, 2 ≤ k → ∃ a : ℕ → ℝ,
    (∀ d, Tendsto (fun N : ℕ => (a274190 N (N - d) : ℝ)) atTop (𝓝 (a d))) ∧
    Summable (fun i : ℕ => 2 * a (i + 1) / (k : ℝ) ^ (i + 1)) ∧
    Tendsto (fun n => expectedWidth k n) atTop
      (𝓝 (1 + ∑' i : ℕ, 2 * a (i + 1) / (k : ℝ) ^ (i + 1))) := by
  intro k hk
  refine ⟨fun d => (a274190 (2 * d) d : ℝ),?_,?_,?_⟩
  · intro d
    exact a274190_diagonal_limit d
  · exact coefficient_series_summable hk
  · simpa only [conjectured_limit_identity hk] using expectedWidth_limit hk

theorem result : claim := coefficient_limit_results


end D5.S1.Words.BlockPalindromes.LargestFactorizationExpectedWidth
