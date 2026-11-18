/- GID: D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Polynomials/MatchingPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact matching-count fibers over edges outside a fixed matching. -/

import D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching
import Mathlib.Data.Nat.Choose.Basic

/-! Matching fibers split into an outside matching and freely selected untouched edges. -/

/-
admission_basis: escape-witness
proof_shape: matching_fiber_card: content; count_partition: bind-only, consumed by
  matchingCount_partition; matchingCount_partition: bind-only, consumed by
  matchingCount_complement_le; maximum_outside_bounds: content;
  matchingCount_complement_le: content; matchingCount_rigidity: content.
escape_witness: matching_fiber_card constructs the inverse fiber bijection M ↦ M ∩ Q;
  maximum_outside_bounds injects touched Q-edges into vertices of the outside matching.
matchingCount_rigidity additionally consumes the live small-defect construction and
  the three defect-gap estimates. The native graph comparison consumes both constructions. No weighted graph or bound on
vertex order is assumed. These prerequisites do not characterize matching permutations.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31461
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Polynomials.MatchingPartition

open Finset
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
open D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All matchings using only edges outside `Q`, including the empty matching. -/
noncomputable def outsideMatchings (E Q : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) := by
  classical
  exact (E \ Q).powerset.filter
    (fun F => ∀ e ∈ F, ∀ f ∈ F, e ≠ f → EdgeDisjoint e f)

/-- Edges of `Q` not touched by any edge of `F`. -/
noncomputable def untouched (Q F : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact Q.filter (fun q => ∀ f ∈ F, EdgeDisjoint q f)

omit [Fintype V] [DecidableEq V] in
private theorem disjoint_symm {e f : Sym2 V} (h : EdgeDisjoint e f) :
    EdgeDisjoint f e := fun v hv hve => h v hve hv

private theorem mem_outside {E Q F : Finset (Sym2 V)} :
    F ∈ outsideMatchings E Q ↔ F ⊆ E \ Q ∧
      ∀ e ∈ F, ∀ f ∈ F, e ≠ f → EdgeDisjoint e f := by
  classical
  simp [outsideMatchings]

private theorem union_matching {E Q F A : Finset (Sym2 V)}
    (hQ : Q ∈ matchingsIn E Q.card) (hF : F ∈ outsideMatchings E Q)
    (hA : A ⊆ untouched Q F) :
    F ∪ A ∈ matchingsIn E (F.card + A.card) := by
  classical
  obtain ⟨hQc, hQm⟩ := mem_filter.mp hQ
  obtain ⟨hQE, _⟩ := mem_powersetCard.mp hQc
  obtain ⟨hFE, hFm⟩ := mem_outside.mp hF
  have hAQ : A ⊆ Q := hA.trans (filter_subset _ _)
  have hd : Disjoint F A := by
    rw [disjoint_left]
    intro e heF heA
    exact (mem_sdiff.mp (hFE heF)).2 (hAQ heA)
  refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, card_union_of_disjoint hd⟩, ?_⟩
  · exact union_subset (fun e he => (mem_sdiff.mp (hFE he)).1) (hAQ.trans hQE)
  · intro e he f hf hef
    rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
    · exact hFm e he f hf hef
    · exact disjoint_symm ((mem_filter.mp (hA hf)).2 e he)
    · exact (mem_filter.mp (hA he)).2 f hf
    · exact hQm e (hAQ he) f (hAQ hf) hef

/-- The fiber over `F` consists of arbitrary subsets of untouched matching edges.
The guard retains zero coefficients when `k < |F|`. -/
theorem matching_fiber_card (E Q F : Finset (Sym2 V)) (k : ℕ)
    (hQ : Q ∈ matchingsIn E Q.card) (hF : F ∈ outsideMatchings E Q) :
    ((matchingsIn E k).filter (fun M => M \ Q = F)).card =
      if F.card ≤ k then (untouched Q F).card.choose (k - F.card) else 0 := by
  classical
  by_cases hFk : F.card ≤ k
  · rw [if_pos hFk, ← card_powersetCard]
    symm
    refine card_bij (fun A _ => F ∪ A) ?_ ?_ ?_
    · intro A hA
      obtain ⟨hAsub, hAc⟩ := mem_powersetCard.mp hA
      have hm := union_matching hQ hF hAsub
      have hcard : F.card + A.card = k := by omega
      rw [hcard] at hm
      refine mem_filter.mpr ⟨hm, ?_⟩
      have hFE := (mem_outside.mp hF).1
      have hAQ : A ⊆ Q := hAsub.trans (filter_subset _ _)
      ext e
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨he | he, hn⟩
        · exact he
        · exact False.elim (hn (hAQ he))
      · intro he
        exact ⟨Or.inl he, (mem_sdiff.mp (hFE he)).2⟩
    · intro A hA B hB hAB
      have hAQ := (mem_powersetCard.mp hA).1.trans (filter_subset _ _)
      have hBQ := (mem_powersetCard.mp hB).1.trans (filter_subset _ _)
      have hFE := (mem_outside.mp hF).1
      ext e
      constructor <;> intro he
      · have hh : e ∈ F ∪ B := hAB ▸ mem_union_right F he
        rcases mem_union.mp hh with hh | hh
        · exact False.elim ((mem_sdiff.mp (hFE hh)).2 (hAQ he))
        · exact hh
      · have hh : e ∈ F ∪ A := hAB.symm ▸ mem_union_right F he
        rcases mem_union.mp hh with hh | hh
        · exact False.elim ((mem_sdiff.mp (hFE hh)).2 (hBQ he))
        · exact hh
    · intro M hM
      obtain ⟨hMk, hMF⟩ := mem_filter.mp hM
      obtain ⟨hMkc, hMm⟩ := mem_filter.mp hMk
      obtain ⟨hME, hMc⟩ := mem_powersetCard.mp hMkc
      refine ⟨M ∩ Q, mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
      · intro e he
        obtain ⟨heM, heQ⟩ := mem_inter.mp he
        refine mem_filter.mpr ⟨heQ, ?_⟩
        intro f hf
        have hf' : f ∈ M \ Q := hMF.symm ▸ hf
        exact hMm e heM f (mem_sdiff.mp hf').1
          (fun hef => (mem_sdiff.mp hf').2 (hef ▸ heQ))
      · have hc := card_sdiff_add_card_inter M Q
        rw [hMF, hMc] at hc
        omega
      · rw [← hMF]
        exact sdiff_union_inter M Q
  · rw [if_neg hFk]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro M hM
    obtain ⟨hm, hMF⟩ := mem_filter.mp hM
    have hMc := (mem_powersetCard.mp (mem_filter.mp hm).1).2
    have hc := card_le_card (sdiff_subset : M \ Q ⊆ M)
    rw [hMF, hMc] at hc
    exact hFk hc

/-- Exact coefficient partition over actual outside matchings, with no maximality assumption. -/
theorem count_partition (E Q : Finset (Sym2 V)) (k : ℕ)
    (hQ : Q ∈ matchingsIn E Q.card) :
    cnt E k = ∑ F ∈ outsideMatchings E Q,
      if F.card ≤ k then (untouched Q F).card.choose (k - F.card) else 0 := by
  classical
  unfold cnt
  rw [card_eq_sum_card_fiberwise (f := fun M => M \ Q) (t := outsideMatchings E Q)]
  · exact sum_congr rfl (fun F hF => matching_fiber_card E Q F k hQ hF)
  · intro M hM
    obtain ⟨hMc, hMm⟩ := mem_filter.mp hM
    obtain ⟨hME, _⟩ := mem_powersetCard.mp hMc
    exact mem_outside.mpr ⟨fun e he => mem_sdiff.mpr ⟨hME (mem_sdiff.mp he).1,
        (mem_sdiff.mp he).2⟩,
      fun e he f hf hef => hMm e (mem_sdiff.mp he).1 f (mem_sdiff.mp hf).1 hef⟩

/-- The partition uses the original graph matching counts, with arbitrary finite vertex order. -/
theorem matchingCount_partition {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (Q : Finset (Sym2 (Fin N))) (k : ℕ)
    (hQ : Q ∈ matchingsIn G.edgeFinset Q.card) :
    matchingCount G k = ∑ F ∈ outsideMatchings G.edgeFinset Q,
      if F.card ≤ k then (untouched Q F).card.choose (k - F.card) else 0 := by
  rw [MatchingCountBridge.matchingCount_eq_cnt]
  exact count_partition G.edgeFinset Q k hQ

private theorem touched_card_le (E Q F : Finset (Sym2 V))
    (hQ : Q ∈ matchingsIn E Q.card) :
    Q.card - (untouched Q F).card ≤ 2 * F.card := by
  classical
  have hQm := (mem_filter.mp hQ).2
  let S := Q \ untouched Q F
  let T := F.biUnion Sym2.toFinset
  have hw : ∀ q ∈ S, ∃ v ∈ T, v ∈ q := by
    intro q hq
    obtain ⟨hqQ, hqU⟩ := mem_sdiff.mp hq
    have hn : ¬ ∀ f ∈ F, EdgeDisjoint q f := by
      intro h
      exact hqU (mem_filter.mpr ⟨hqQ, h⟩)
    push_neg at hn
    obtain ⟨f, hf, hnf⟩ := hn
    unfold EdgeDisjoint at hnf
    push_neg at hnf
    obtain ⟨v, hvq, hvf⟩ := hnf
    exact ⟨v, mem_biUnion.mpr ⟨f, hf, Sym2.mem_toFinset.mpr hvf⟩, hvq⟩
  choose g hgT hgq using hw
  let j : {q // q ∈ S} → {v // v ∈ T} := fun q => ⟨g q.1 q.2, hgT q.1 q.2⟩
  have hj : Function.Injective j := by
    intro q r heq
    apply Subtype.ext
    by_contra hne
    have heq' : g q.1 q.2 = g r.1 r.2 := congrArg Subtype.val heq
    exact hQm q.1 (mem_sdiff.mp q.2).1 r.1 (mem_sdiff.mp r.2).1 hne
      (g q.1 q.2) (hgq q.1 q.2) (heq' ▸ hgq r.1 r.2)
  have hcard : S.card ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective j hj
  have hT : T.card ≤ 2 * F.card := by
    calc
      T.card ≤ ∑ f ∈ F, f.toFinset.card := card_biUnion_le
      _ ≤ ∑ _f ∈ F, 2 := sum_le_sum (fun f _ => by rw [Sym2.card_toFinset]; split <;> omega)
      _ = 2 * F.card := by simp [mul_comm]
  have hU : untouched Q F ⊆ Q := filter_subset _ _
  rw [show S.card = Q.card - (untouched Q F).card from card_sdiff_of_subset hU] at hcard
  exact hcard.trans hT

private theorem support_bounded {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : BddAbove {i | 0 < matchingCount G i} := by
  classical
  refine ⟨N, ?_⟩
  intro i hi
  by_contra hn
  have hz := MatchingCountBridge.matchingCount_eq_zero_of_card_lt G i (by omega)
  simpa [hz] using hi

private theorem matching_card_le_number {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (M : Finset (Sym2 (Fin N)))
    (hM : M ∈ matchingsIn G.edgeFinset M.card) : M.card ≤ matchingNumber G := by
  apply le_csSup (support_bounded G)
  change 0 < matchingCount G M.card
  rw [MatchingCountBridge.matchingCount_eq_cnt]
  exact card_pos.mpr ⟨M, hM⟩

private theorem exists_maximum {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : ∃ Q : Finset (Sym2 (Fin N)),
      Q ∈ matchingsIn G.edgeFinset Q.card ∧ matchingNumber G = Q.card := by
  classical
  have hzero : 0 < matchingCount G 0 := by
    rw [MatchingCountBridge.matchingCount_eq_cnt]
    exact card_pos.mpr ⟨∅, by simp [matchingsIn]⟩
  have hpos := Nat.sSup_mem ⟨0, hzero⟩ (support_bounded G)
  change 0 < matchingCount G (matchingNumber G) at hpos
  rw [MatchingCountBridge.matchingCount_eq_cnt] at hpos
  obtain ⟨Q, hQ⟩ := card_pos.mp hpos
  have hc := (mem_powersetCard.mp (mem_filter.mp hQ).1).2
  exact ⟨Q, hc.symm ▸ hQ, hc.symm⟩

/-- For a maximum matching of a native graph, an outside `t`-matching touches between
`t` and `2t` matching edges. The graph's vertex order is unrestricted. -/
theorem maximum_outside_bounds {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (Q F : Finset (Sym2 (Fin N)))
    (hQ : Q ∈ matchingsIn G.edgeFinset Q.card) (hmax : matchingNumber G = Q.card)
    (hF : F ∈ outsideMatchings G.edgeFinset Q) :
    F.card ≤ Q.card - (untouched Q F).card ∧
      Q.card - (untouched Q F).card ≤ min (2 * F.card) Q.card := by
  classical
  have hm := union_matching hQ hF (Subset.refl (untouched Q F))
  have hc : (F ∪ untouched Q F).card = F.card + (untouched Q F).card :=
    (mem_powersetCard.mp (mem_filter.mp hm).1).2
  rw [← hc] at hm
  have hle := matching_card_le_number G _ hm
  rw [hc, hmax] at hle
  exact ⟨by omega, le_min (touched_card_le _ _ _ hQ) (Nat.sub_le _ _)⟩

omit [Fintype V] [DecidableEq V] in
private theorem choose_comparison (a b c : ℕ) (hab : a ≤ b) (hsum : a + b ≤ c) :
    c.choose a ≤ c.choose b := by
  have low : ∀ d, a ≤ d → 2 * d ≤ c → c.choose a ≤ c.choose d := by
    intro d had
    induction d, had using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ d had ih =>
      intro hd
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hb : 2 * b ≤ c
  · exact low b hab hb
  · have hbc : b ≤ c := by omega
    rw [← Nat.choose_symm hbc]
    exact low (c - b) (by omega) (by omega)

private theorem complementary_term (n t s k : ℕ) (hts : t ≤ s) (hst : s ≤ 2 * t)
    (hsn : s ≤ n) (hk : 2 * k ≤ n) :
    (if t ≤ k then (n - s).choose (k - t) else 0) ≤
      if t ≤ n - k then (n - s).choose (n - k - t) else 0 := by
  by_cases ht : t ≤ k
  · have ht' : t ≤ n - k := by omega
    rw [if_pos ht, if_pos ht']
    have hi : n - k - t ≤ n - s := by omega
    rw [← Nat.choose_symm hi]
    apply choose_comparison <;> omega
  · rw [if_neg ht]
    exact Nat.zero_le _

/-- Every lower-half matching count is bounded by its complementary count.
This is about one actual unweighted simple graph, without a vertex-order bound. -/
theorem matchingCount_complement_le {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (k : ℕ) (hk : 2 * k ≤ matchingNumber G) :
    matchingCount G k ≤ matchingCount G (matchingNumber G - k) := by
  classical
  obtain ⟨Q, hQ, hmax⟩ := exists_maximum G
  rw [hmax] at hk ⊢
  rw [matchingCount_partition G Q k hQ, matchingCount_partition G Q (Q.card - k) hQ]
  apply sum_le_sum
  intro F hF
  have hb := maximum_outside_bounds G Q F hQ hmax hF
  have hU : (untouched Q F).card ≤ Q.card := card_le_card (filter_subset _ _)
  have hterm := complementary_term Q.card F.card (Q.card - (untouched Q F).card) k
    hb.1 (le_trans hb.2 (min_le_left _ _)) (Nat.sub_le _ _) hk
  simpa only [Nat.sub_sub_self hU] using hterm

private noncomputable def blocked (Q F : Finset (Sym2 V)) : Finset (Sym2 V) := Q \ untouched Q F

private theorem blocked_card (Q F : Finset (Sym2 V)) :
    (blocked Q F).card = Q.card - (untouched Q F).card := by
  classical
  exact card_sdiff_of_subset (filter_subset _ _)

private theorem outside_subset {E Q F A : Finset (Sym2 V)}
    (hF : F ∈ outsideMatchings E Q) (hA : A ⊆ F) : A ∈ outsideMatchings E Q := by
  obtain ⟨hFE, hFm⟩ := mem_outside.mp hF
  exact mem_outside.mpr ⟨hA.trans hFE,
    fun e he f hf hef => hFm e (hA he) f (hA hf) hef⟩

private theorem blocked_biUnion (Q F : Finset (Sym2 V)) :
    blocked Q F = F.biUnion (fun e => blocked Q {e}) := by
  classical
  ext q
  simp only [blocked, mem_sdiff, untouched, mem_filter, mem_biUnion,
    mem_singleton, forall_eq]
  aesop

private theorem blocked_pair (Q : Finset (Sym2 V)) (e f : Sym2 V) :
    blocked Q {e, f} = blocked Q {e} ∪ blocked Q {f} := by
  classical
  rw [blocked_biUnion]
  simp

private theorem balanced_of_small (E Q : Finset (Sym2 V))
    (hQ : Q ∈ matchingsIn E Q.card)
    (hsmall : ∀ A ∈ outsideMatchings E Q, A.card ≤ 2 →
      (blocked Q A).card = 2 * A.card) :
    ∀ F ∈ outsideMatchings E Q, (blocked Q F).card = 2 * F.card := by
  classical
  intro F hF
  have hs : ∀ e ∈ F, (blocked Q {e}).card = 2 := by
    intro e he
    simpa using hsmall {e} (outside_subset hF (singleton_subset_iff.mpr he)) (by simp)
  rw [blocked_biUnion, card_biUnion]
  · simp only [sum_congr rfl hs, sum_const, smul_eq_mul, mul_comm]
  · intro e he f hf hef
    have hpair : ({e, f} : Finset (Sym2 V)).card = 2 := card_pair hef
    have hp := hsmall {e, f} (outside_subset hF (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨he, hf⟩)) (by omega)
    rw [hpair, blocked_pair] at hp
    have hc := card_union_add_card_inter (blocked Q {e}) (blocked Q {f})
    rw [hs e he, hs f hf, hp] at hc
    rw [Function.onFun, disjoint_iff_inter_eq_empty, ← card_eq_zero]
    omega

private theorem small_defect_or_balanced {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (Q : Finset (Sym2 (Fin N)))
    (hQ : Q ∈ matchingsIn G.edgeFinset Q.card) (hmax : matchingNumber G = Q.card) :
    (∀ F ∈ outsideMatchings G.edgeFinset Q, (blocked Q F).card = 2 * F.card) ∨
      ∃ F ∈ outsideMatchings G.edgeFinset Q,
        (F.card = 1 ∧ (blocked Q F).card = 1) ∨
        (F.card = 2 ∧ ((blocked Q F).card = 2 ∨ (blocked Q F).card = 3)) := by
  classical
  by_cases hd : ∃ F ∈ outsideMatchings G.edgeFinset Q,
      F.card ≤ 2 ∧ (blocked Q F).card < 2 * F.card
  · obtain ⟨F, hF, hc, hd⟩ := hd
    right
    refine ⟨F, hF, ?_⟩
    have hb := maximum_outside_bounds G Q F hQ hmax hF
    rw [← blocked_card] at hb
    omega
  · left
    apply balanced_of_small _ _ hQ
    intro F hF hc
    have hb := touched_card_le G.edgeFinset Q F hQ
    rw [← blocked_card] at hb
    have hn : ¬ (blocked Q F).card < 2 * F.card := fun h => hd ⟨F, hF, hc, h⟩
    omega

private def sc (a t k : ℕ) : ℕ := if t ≤ k then a.choose (k - t) else 0

private theorem sc_pascal (a t k : ℕ) :
    sc (a + 1) t k = sc a t k + sc a (t + 1) k := by
  unfold sc
  by_cases ht : t ≤ k
  · by_cases ht' : t + 1 ≤ k
    · rw [if_pos ht, if_pos ht, if_pos ht']
      have he : k - t = (k - (t + 1)) + 1 := by omega
      rw [he, Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      omega
    · have he : k = t := by omega
      subst k
      simp
  · simp [ht, show ¬t + 1 ≤ k by omega]

private theorem sc_reflect (a t u k : ℕ) (hk : k ≤ a + t + u) :
    sc a t (a + t + u - k) = sc a u k := by
  unfold sc
  by_cases ht : t ≤ a + t + u - k <;> by_cases hu : u ≤ k
  · rw [if_pos ht, if_pos hu]
    have hi : k - u ≤ a := by omega
    have he : a + t + u - k - t = a - (k - u) := by omega
    rw [he, Nat.choose_symm hi]
  · rw [if_pos ht, if_neg hu, Nat.choose_eq_zero_of_lt (by omega)]
  · rw [if_neg ht, if_pos hu, Nat.choose_eq_zero_of_lt (by omega)]
  · simp [ht, hu]

private theorem choose_strict (a r : ℕ) (h : 2 * r + 1 < a) :
    a.choose r < a.choose (r + 1) := by
  have hp := Nat.choose_pos (show r ≤ a by omega)
  have he := Nat.choose_succ_right_eq a r
  have hstep : r + 1 < a - r := by omega
  by_contra hn
  have hh := Nat.mul_le_mul_right (r + 1) (show a.choose (r + 1) ≤ a.choose r by omega)
  have hm := Nat.mul_lt_mul_of_pos_left hstep hp
  omega

private theorem gap_positive (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k < n) :
    0 < sc (n - 3) 1 k - sc (n - 3) 2 k := by
  by_cases hk2 : 2 ≤ k
  · have h := choose_strict (n - 3) (k - 2) (by omega)
    have he : k - 2 + 1 = k - 1 := by omega
    rw [he] at h
    simpa [sc, hk, hk2] using Nat.sub_pos_of_lt h
  · have he : k = 1 := by omega
    subst k
    simp [sc]

private theorem small_term_gap (n t s k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hkn : 2 * k < n)
    (hd : (t = 1 ∧ s = 1) ∨ (t = 2 ∧ (s = 2 ∨ s = 3))) :
    sc (n - s) t k + (sc (n - 3) 1 k - sc (n - 3) 2 k) ≤
      sc (n - s) t (n - k) := by
  have hpos := gap_positive n k hn hk hkn
  have hmono : sc (n - 3) 3 k ≤ sc (n - 3) 0 k := by
    have h := complementary_term n 3 3 k (by omega) (by omega) hn (by omega)
    change sc (n - 3) 3 k ≤ sc (n - 3) 3 (n - k) at h
    have he : n - 3 + 3 + 0 = n := by omega
    have hh := sc_reflect (n - 3) 3 0 k (by omega)
    rw [he] at hh
    rwa [hh] at h
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · have he : n - 1 = (n - 3) + 1 + 1 := by omega
    have hr := sc_reflect (n - 1) 1 0 k (by omega)
    have hrn : n - 1 + 1 + 0 = n := by omega
    rw [hrn] at hr
    rw [hr, he]
    simp only [sc_pascal, Nat.reduceAdd]
    omega
  · have he : n - 2 = (n - 3) + 1 := by omega
    have hr := sc_reflect (n - 2) 2 0 k (by omega)
    have hrn : n - 2 + 2 + 0 = n := by omega
    rw [hrn] at hr
    rw [hr, he]
    simp only [sc_pascal, Nat.reduceAdd]
    omega
  · have hr := sc_reflect (n - 3) 2 1 k (by omega)
    have hrn : n - 3 + 2 + 1 = n := by omega
    rw [hrn] at hr
    rw [hr]
    omega

private theorem sum_extra_le {α : Type*} [DecidableEq α] (S : Finset α)
    (a b : α → ℕ) (x : α) (hx : x ∈ S) (d : ℕ)
    (hab : ∀ y ∈ S, a y ≤ b y) (hxd : a x + d ≤ b x) :
    (∑ y ∈ S, a y) + d ≤ ∑ y ∈ S, b y := by
  rw [← sum_erase_add S a hx, ← sum_erase_add S b hx]
  have he : (∑ y ∈ S.erase x, a y) ≤ ∑ y ∈ S.erase x, b y :=
    sum_le_sum (fun y hy => hab y (mem_of_mem_erase hy))
  omega

/-- A native graph is palindromic, or every lower-half complementary gap is at least
the positive P6 gap. The guards implement zero binomial coefficients at negative indices. -/
theorem matchingCount_rigidity {N : ℕ} (G : SimpleGraph (Fin N))
    (hn : 3 ≤ matchingNumber G) :
    (∀ k ≤ matchingNumber G, matchingCount G k = matchingCount G (matchingNumber G - k)) ∨
      ∀ k, 1 ≤ k → 2 * k < matchingNumber G →
        let d := (matchingNumber G - 3).choose (k - 1) -
          (if 2 ≤ k then (matchingNumber G - 3).choose (k - 2) else 0)
        0 < d ∧ matchingCount G k + d ≤ matchingCount G (matchingNumber G - k) := by
  classical
  obtain ⟨Q, hQ, hmax⟩ := exists_maximum G
  rw [hmax] at hn ⊢
  rcases small_defect_or_balanced G Q hQ hmax with hb | ⟨F, hF, hd⟩
  · left
    intro k hk
    rw [matchingCount_partition G Q k hQ, matchingCount_partition G Q (Q.card - k) hQ]
    apply sum_congr rfl
    intro F hF
    have hbal := hb F hF
    rw [blocked_card] at hbal
    have hU : (untouched Q F).card ≤ Q.card := card_le_card (filter_subset _ _)
    have he : (untouched Q F).card + F.card + F.card = Q.card := by omega
    have hs := sc_reflect (untouched Q F).card F.card F.card k (by omega)
    rw [he] at hs
    exact hs.symm
  · right
    intro k hk hkn
    dsimp only
    have hp := gap_positive Q.card k hn hk hkn
    simp only [sc, if_pos hk] at hp
    refine ⟨hp, ?_⟩
    rw [matchingCount_partition G Q k hQ, matchingCount_partition G Q (Q.card - k) hQ]
    apply sum_extra_le _ _ _ F hF
    · intro A hA
      have hb := maximum_outside_bounds G Q A hQ hmax hA
      have hU : (untouched Q A).card ≤ Q.card := card_le_card (filter_subset _ _)
      have ht := complementary_term Q.card A.card (Q.card - (untouched Q A).card) k
        hb.1 (le_trans hb.2 (min_le_left _ _)) (Nat.sub_le _ _) (by omega)
      simpa only [Nat.sub_sub_self hU] using ht
    · have hU : (untouched Q F).card ≤ Q.card := card_le_card (filter_subset _ _)
      have ht := small_term_gap Q.card F.card (blocked Q F).card k hn hk hkn hd
      rw [blocked_card, Nat.sub_sub_self hU] at ht
      simpa only [sc, if_pos hk] using ht

end D5.S3.Combinatorics.Graph.Polynomials.MatchingPartition
