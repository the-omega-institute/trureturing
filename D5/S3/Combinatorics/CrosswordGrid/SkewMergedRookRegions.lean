/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions
   mirror-E: none(waiver:inversion-graph-pattern-criterion)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: A clique exchange characterizes skew-merged permutations by pattern avoidance. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookRegions

theorem graph_split_criterion {n : ℕ} (_positive : 1 ≤ n) (graph : SimpleGraph (Fin n))
    (no_pairs : ∀ first second third fourth : Fin n,
      graph.Adj first second → graph.Adj third fourth →
      ¬ graph.Adj first third → ¬ graph.Adj first fourth →
      ¬ graph.Adj second third → ¬ graph.Adj second fourth → False)
    (no_four : ∀ first second third fourth : Fin n,
      graph.Adj first second → graph.Adj second third → graph.Adj third fourth →
      graph.Adj fourth first → first ≠ third → second ≠ fourth →
      ¬ graph.Adj first third → ¬ graph.Adj second fourth → False)
    (no_five : ∀ first second third fourth fifth : Fin n,
      graph.Adj first second → graph.Adj second third → graph.Adj third fourth →
      graph.Adj fourth fifth → graph.Adj fifth first →
      ¬ graph.Adj first third → ¬ graph.Adj first fourth → ¬ graph.Adj second fourth →
      ¬ graph.Adj second fifth → ¬ graph.Adj third fifth → False) :
    ∃ clique : Finset (Fin n), graph.IsClique (clique : Set (Fin n)) ∧
      ∀ first ∉ clique, ∀ second ∉ clique, ¬ graph.Adj first second := by
  classical
  let cliques := Finset.univ.powerset.filter fun part : Finset (Fin n) =>
    graph.IsClique (part : Set (Fin n))
  have clique_mem (part : Finset (Fin n)) :
      part ∈ cliques ↔ graph.IsClique (part : Set (Fin n)) := by
    simp [cliques]
  have nonempty : cliques.Nonempty := by
    refine ⟨∅, (clique_mem ∅).mpr ?_⟩
    simp
  obtain ⟨largest, hlargest, max_card⟩ :=
    Finset.exists_max_image cliques Finset.card nonempty
  let largest_cliques := cliques.filter fun part => part.card = largest.card
  have largest_nonempty : largest_cliques.Nonempty := by
    exact ⟨largest, Finset.mem_filter.mpr ⟨hlargest, rfl⟩⟩
  obtain ⟨clique, hclique, max_degree⟩ := Finset.exists_max_image largest_cliques
    (fun part => ∑ vertex ∈ part, graph.degree vertex) largest_nonempty
  have hc : graph.IsClique (clique : Set (Fin n)) :=
    (clique_mem clique).mp (Finset.mem_filter.mp hclique).1
  have hc_card : clique.card = largest.card := (Finset.mem_filter.mp hclique).2
  have maximal (part : Finset (Fin n)) (hpart : graph.IsClique (part : Set (Fin n))) :
      part.card ≤ clique.card := by
    rw [hc_card]
    exact max_card part ((clique_mem part).mpr hpart)
  have nonneighbor (vertex : Fin n) (hvertex : vertex ∉ clique) :
      ∃ missing ∈ clique, ¬ graph.Adj vertex missing := by
    by_contra hnone
    have all : ∀ missing ∈ clique, graph.Adj vertex missing := by
      intro missing hmissing
      by_contra hnot
      exact hnone ⟨missing, hmissing, hnot⟩
    have inserted : graph.IsClique ((insert vertex clique : Finset (Fin n)) : Set (Fin n)) := by
      intro first hfirst second hsecond hne
      simp only [Finset.mem_coe, Finset.mem_insert] at hfirst hsecond
      rcases hfirst with rfl | hfirst <;> rcases hsecond with rfl | hsecond
      · exact False.elim (hne rfl)
      · exact all _ hsecond
      · exact graph.adj_symm (all _ hfirst)
      · exact hc hfirst hsecond hne
    have hcard := maximal (insert vertex clique) inserted
    rw [Finset.card_insert_of_notMem hvertex] at hcard
    omega
  have contradiction (first second : Fin n) (hfirst : first ∉ clique)
      (hsecond : second ∉ clique) (edge : graph.Adj first second)
      (nested : ∀ missing ∈ clique,
        ¬ graph.Adj first missing → ¬ graph.Adj second missing) :
      False := by
    obtain ⟨removed, hremoved, first_removed⟩ := nonneighbor first hfirst
    have second_removed := nested removed hremoved first_removed
    have unique (other : Fin n) (hother : other ∈ clique)
        (first_other : ¬ graph.Adj first other) : other = removed := by
      by_contra hne
      have second_other := nested other hother first_other
      exact no_pairs first second removed other edge (hc hremoved hother (Ne.symm hne))
        first_removed first_other second_removed second_other
    have first_other (other : Fin n) (hother : other ∈ clique) (hne : other ≠ removed) :
        graph.Adj first other := by
      by_contra hnot
      exact hne (unique other hother hnot)
    have double_insert (all : ∀ other ∈ clique, other ≠ removed → graph.Adj second other) :
        graph.IsClique
          ((insert first (insert second (clique.erase removed)) : Finset (Fin n)) :
            Set (Fin n)) := by
      intro vertex hvertex other hother hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hvertex hother
      rcases hvertex with rfl | rfl | hvertex <;> rcases hother with rfl | rfl | hother
      · exact False.elim (hne rfl)
      · exact edge
      · exact first_other _ hother.2 hother.1
      · exact graph.adj_symm edge
      · exact False.elim (hne rfl)
      · exact all _ hother.2 hother.1
      · exact graph.adj_symm (first_other _ hvertex.2 hvertex.1)
      · exact graph.adj_symm (all _ hvertex.2 hvertex.1)
      · exact hc hvertex.2 hother.2 hne
    have extra : ∃ other ∈ clique, other ≠ removed ∧ ¬ graph.Adj second other := by
      by_contra hnone
      have all : ∀ other ∈ clique, other ≠ removed → graph.Adj second other := by
        intro other hother hne
        by_contra hnot
        exact hnone ⟨other, hother, hne, hnot⟩
      have hcard := maximal _ (double_insert all)
      have hsecond_erase : second ∉ clique.erase removed :=
        fun h => hsecond (Finset.mem_of_mem_erase h)
      have hfirst_insert : first ∉ insert second (clique.erase removed) := by
        simp only [Finset.mem_insert, Finset.mem_erase, not_or]
        exact ⟨graph.ne_of_adj edge, fun h => hfirst h.2⟩
      rw [Finset.card_insert_of_notMem hfirst_insert,
        Finset.card_insert_of_notMem hsecond_erase, Finset.card_erase_of_mem hremoved] at hcard
      have nonzero : 0 < clique.card := Finset.card_pos.mpr ⟨removed, hremoved⟩
      omega
    obtain ⟨other, hother, hother_removed, second_other⟩ := extra
    have first_other_edge := first_other other hother hother_removed
    have removed_other := hc hremoved hother hother_removed.symm
    have neighbors (vertex : Fin n) (removed_vertex : graph.Adj removed vertex) :
        graph.Adj first vertex := by
      by_contra first_vertex
      have first_ne_vertex : first ≠ vertex := by
        intro heq
        exact first_removed (graph.adj_symm (heq ▸ removed_vertex))
      by_cases second_vertex : graph.Adj second vertex
      · by_cases other_vertex : graph.Adj other vertex
        · have other_ne_second : other ≠ second := by
            intro heq
            exact hsecond (heq ▸ hother)
          exact no_four first other vertex second first_other_edge other_vertex
            (graph.adj_symm second_vertex) (graph.adj_symm edge) first_ne_vertex other_ne_second
            first_vertex (fun h => second_other (graph.adj_symm h))
        · exact no_five removed other first second vertex removed_other
            (graph.adj_symm first_other_edge) edge second_vertex (graph.adj_symm removed_vertex)
            (fun h => first_removed (graph.adj_symm h))
            (fun h => second_removed (graph.adj_symm h))
            (fun h => second_other (graph.adj_symm h)) other_vertex first_vertex
      · exact no_pairs removed vertex first second removed_vertex edge
          (fun h => first_removed (graph.adj_symm h))
          (fun h => second_removed (graph.adj_symm h))
          (fun h => first_vertex (graph.adj_symm h))
          (fun h => second_vertex (graph.adj_symm h))
    have degree_lt : graph.degree removed < graph.degree first := by
      rw [← graph.card_neighborFinset_eq_degree, ← graph.card_neighborFinset_eq_degree]
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro vertex hvertex
        exact (graph.mem_neighborFinset _ _).mpr
          (neighbors vertex ((graph.mem_neighborFinset _ _).mp hvertex))
      · intro heq
        have hmem : second ∈ graph.neighborFinset first :=
          (graph.mem_neighborFinset _ _).mpr edge
        rw [← heq] at hmem
        exact second_removed (graph.adj_symm ((graph.mem_neighborFinset _ _).mp hmem))
    let replacement := insert first (clique.erase removed)
    have replacement_clique : graph.IsClique (replacement : Set (Fin n)) := by
      intro vertex hvertex other hother hne
      simp only [replacement, Finset.mem_coe, Finset.mem_insert, Finset.mem_erase]
        at hvertex hother
      rcases hvertex with rfl | hvertex <;> rcases hother with rfl | hother
      · exact False.elim (hne rfl)
      · exact first_other _ hother.2 hother.1
      · exact graph.adj_symm (first_other _ hvertex.2 hvertex.1)
      · exact hc hvertex.2 hother.2 hne
    have first_erase : first ∉ clique.erase removed :=
      fun h => hfirst (Finset.mem_of_mem_erase h)
    have replacement_card : replacement.card = clique.card := by
      dsimp only [replacement]
      rw [Finset.card_insert_of_notMem first_erase, Finset.card_erase_of_mem hremoved]
      have nonzero : 0 < clique.card := Finset.card_pos.mpr ⟨removed, hremoved⟩
      omega
    have replacement_mem : replacement ∈ largest_cliques :=
      Finset.mem_filter.mpr ⟨(clique_mem _).mpr replacement_clique,
        replacement_card.trans hc_card⟩
    have hsum := max_degree replacement replacement_mem
    dsimp only [replacement] at hsum
    rw [Finset.sum_insert first_erase] at hsum
    have htotal := Finset.sum_erase_add clique (fun vertex => graph.degree vertex) hremoved
    omega
  refine ⟨clique, hc, ?_⟩
  intro first hfirst second hsecond edge
  by_cases nested : ∀ missing ∈ clique,
      ¬ graph.Adj first missing → ¬ graph.Adj second missing
  · exact contradiction first second hfirst hsecond edge nested
  · have reverse_nested : ∀ missing ∈ clique,
        ¬ graph.Adj second missing → ¬ graph.Adj first missing := by
      intro missing hmissing second_missing
      by_contra first_missing
      obtain ⟨other, hother, first_other, second_other⟩ :
          ∃ other ∈ clique, ¬ graph.Adj first other ∧ graph.Adj second other := by
        simpa only [not_forall, Classical.not_imp, not_not, exists_prop] using nested
      have other_ne_missing : other ≠ missing := by
        intro heq
        exact first_other (heq ▸ first_missing)
      have first_ne_other : first ≠ other := by
        intro heq
        exact hfirst (heq ▸ hother)
      have second_ne_missing : second ≠ missing := by
        intro heq
        exact hsecond (heq ▸ hmissing)
      exact no_four first second other missing edge second_other
        (hc hother hmissing other_ne_missing) (graph.adj_symm first_missing)
        first_ne_other second_ne_missing first_other second_missing
    exact contradiction second first hsecond hfirst (graph.adj_symm edge) reverse_nested

theorem skew_iff_avoidance {n : ℕ} (positive : 1 ≤ n) (w : Equiv.Perm (Fin n)) :
    D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs.SkewMerged w ↔
      ∀ first second third fourth : Fin n,
        first < second → second < third → third < fourth →
        ¬ ((w second < w first ∧ w first < w fourth ∧ w fourth < w third) ∨
          (w third < w fourth ∧ w fourth < w first ∧ w first < w second)) := by
  classical
  constructor
  · rintro ⟨increasing, inc, dec⟩ first second third fourth hfirst hsecond hthird forbidden
    by_cases hfirst_mem : first ∈ increasing <;>
      by_cases hsecond_mem : second ∈ increasing <;>
      by_cases hthird_mem : third ∈ increasing <;>
      by_cases hfourth_mem : fourth ∈ increasing <;>
      rcases forbidden with forbidden | forbidden
    all_goals
      try have value_first_second := inc first hfirst_mem second hsecond_mem hfirst
      try have value_first_second := dec first hfirst_mem second hsecond_mem hfirst
      try have value_first_third := inc first hfirst_mem third hthird_mem (hfirst.trans hsecond)
      try have value_first_third := dec first hfirst_mem third hthird_mem (hfirst.trans hsecond)
      try
        have value_first_fourth := inc first hfirst_mem fourth hfourth_mem
          (hfirst.trans (hsecond.trans hthird))
      try
        have value_first_fourth := dec first hfirst_mem fourth hfourth_mem
          (hfirst.trans (hsecond.trans hthird))
      try have value_second_third := inc second hsecond_mem third hthird_mem hsecond
      try have value_second_third := dec second hsecond_mem third hthird_mem hsecond
      try
        have value_second_fourth := inc second hsecond_mem fourth hfourth_mem
          (hsecond.trans hthird)
      try
        have value_second_fourth := dec second hsecond_mem fourth hfourth_mem
          (hsecond.trans hthird)
      try have value_third_fourth := inc third hthird_mem fourth hfourth_mem hthird
      try have value_third_fourth := dec third hthird_mem fourth hfourth_mem hthird
      omega
  · intro avoidance
    let graph : SimpleGraph (Fin n) :=
      { Adj := fun row other =>
          (row < other ∧ w other < w row) ∨ (other < row ∧ w row < w other)
        symm := ⟨by intro row other hedge; tauto⟩
        loopless := ⟨by intro row; simp⟩ }
    have pairs (permutation : Equiv.Perm (Fin n))
        (avoids : ∀ first second third fourth : Fin n,
          first < second → second < third → third < fourth →
          ¬ (permutation second < permutation first ∧ permutation first < permutation fourth ∧
            permutation fourth < permutation third))
        (first second third fourth : Fin n)
        (edge_first : (first < second ∧ permutation second < permutation first) ∨
          (second < first ∧ permutation first < permutation second))
        (edge_second : (third < fourth ∧ permutation fourth < permutation third) ∨
          (fourth < third ∧ permutation third < permutation fourth))
        (cross_first : ¬ ((first < third ∧ permutation third < permutation first) ∨
          (third < first ∧ permutation first < permutation third)))
        (cross_second : ¬ ((first < fourth ∧ permutation fourth < permutation first) ∨
          (fourth < first ∧ permutation first < permutation fourth)))
        (cross_third : ¬ ((second < third ∧ permutation third < permutation second) ∨
          (third < second ∧ permutation second < permutation third)))
        (cross_fourth : ¬ ((second < fourth ∧ permutation fourth < permutation second) ∨
          (fourth < second ∧ permutation second < permutation fourth))) : False := by
      have ordered (left right low high : Fin n)
          (left_right : left < right) (low_high : low < high)
          (left_values : permutation right < permutation left)
          (right_values : permutation high < permutation low)
          (cross_left : ¬ ((left < low ∧ permutation low < permutation left) ∨
            (low < left ∧ permutation left < permutation low)))
          (cross_right : ¬ ((left < high ∧ permutation high < permutation left) ∨
            (high < left ∧ permutation left < permutation high)))
          (cross_low : ¬ ((right < low ∧ permutation low < permutation right) ∨
            (low < right ∧ permutation right < permutation low)))
          (cross_high : ¬ ((right < high ∧ permutation high < permutation right) ∨
            (high < right ∧ permutation right < permutation high))) : False := by
        have unequal_left : left ≠ low := by
          intro heq
          exact cross_low (Or.inr ⟨heq ▸ left_right, heq ▸ left_values⟩)
        have unequal_right : right ≠ low := by
          intro heq
          exact cross_left (Or.inl ⟨heq ▸ left_right, heq ▸ left_values⟩)
        have left_value_ne : permutation left ≠ permutation low :=
          permutation.injective.ne unequal_left
        have right_value_ne : permutation right ≠ permutation low :=
          permutation.injective.ne unequal_right
        by_cases left_low : left < low
        · have right_low : right < low := by
            have hne := unequal_right
            have hneval : right.val ≠ low.val := fun heq => hne (Fin.ext heq)
            have hval : (permutation left).val ≠ (permutation low).val :=
              fun heq => left_value_ne (Fin.ext heq)
            have hval' : (permutation right).val ≠ (permutation low).val :=
              fun heq => right_value_ne (Fin.ext heq)
            omega
          have left_high_ne : permutation left ≠ permutation high := by
            apply permutation.injective.ne
            exact ne_of_lt (left_low.trans low_high)
          have hval : (permutation left).val ≠ (permutation high).val :=
            fun heq => left_high_ne (Fin.ext heq)
          apply avoids left right low high left_right right_low low_high
          omega
        · have low_left : low < left := lt_of_le_of_ne (le_of_not_gt left_low)
            (Ne.symm unequal_left)
          have high_left : high < left := by
            have high_ne_left : high ≠ left := by
              intro heq
              exact cross_left (Or.inr ⟨heq ▸ low_high, heq ▸ right_values⟩)
            have hneval : high.val ≠ left.val := fun heq => high_ne_left (Fin.ext heq)
            have hval : (permutation left).val ≠ (permutation low).val :=
              fun heq => left_value_ne (Fin.ext heq)
            have hval' : (permutation high).val ≠ (permutation left).val :=
              fun heq => (permutation.injective.ne high_ne_left) (Fin.ext heq)
            omega
          have low_right_ne : permutation low ≠ permutation right := by
            apply permutation.injective.ne
            exact ne_of_lt (low_left.trans left_right)
          have hval : (permutation low).val ≠ (permutation right).val :=
            fun heq => low_right_ne (Fin.ext heq)
          apply avoids low high left right low_high high_left left_right
          omega
      rcases edge_first with hfirst | hfirst <;> rcases edge_second with hsecond | hsecond
      · exact ordered first second third fourth hfirst.1 hsecond.1 hfirst.2 hsecond.2
          cross_first cross_second cross_third cross_fourth
      · exact ordered first second fourth third hfirst.1 hsecond.1 hfirst.2 hsecond.2
          cross_second cross_first cross_fourth cross_third
      · exact ordered second first third fourth hfirst.1 hsecond.1 hfirst.2 hsecond.2
          cross_third cross_fourth cross_first cross_second
      · exact ordered second first fourth third hfirst.1 hsecond.1 hfirst.2 hsecond.2
          cross_fourth cross_third cross_second cross_first
    have no_pairs : ∀ first second third fourth : Fin n,
        graph.Adj first second → graph.Adj third fourth →
        ¬ graph.Adj first third → ¬ graph.Adj first fourth →
        ¬ graph.Adj second third → ¬ graph.Adj second fourth → False := by
      apply pairs w
      intro first second third fourth hfirst hsecond hthird forbidden
      exact avoidance first second third fourth hfirst hsecond hthird (Or.inl forbidden)
    have complement_edge (first second : Fin n) (hne : first ≠ second) :
        ((first < second ∧ (w second).rev < (w first).rev) ∨
          (second < first ∧ (w first).rev < (w second).rev)) ↔ ¬ graph.Adj first second := by
      have hvalue : (w first).val ≠ (w second).val :=
        fun heq => (w.injective.ne hne) (Fin.ext heq)
      have hposition : first.val ≠ second.val := fun heq => hne (Fin.ext heq)
      simp only [Fin.rev_lt_rev]
      change ((first < second ∧ w first < w second) ∨
        (second < first ∧ w second < w first)) ↔
        ¬ ((first < second ∧ w second < w first) ∨ (second < first ∧ w first < w second))
      omega
    have no_four : ∀ first second third fourth : Fin n,
        graph.Adj first second → graph.Adj second third → graph.Adj third fourth →
        graph.Adj fourth first → first ≠ third → second ≠ fourth →
        ¬ graph.Adj first third → ¬ graph.Adj second fourth → False := by
      intro first second third fourth edge_first edge_second edge_third edge_fourth
        distinct_first distinct_second diagonal_first diagonal_second
      have complement_avoids : ∀ first second third fourth : Fin n,
          first < second → second < third → third < fourth →
          ¬ ((w.trans Fin.revPerm) second < (w.trans Fin.revPerm) first ∧
            (w.trans Fin.revPerm) first < (w.trans Fin.revPerm) fourth ∧
            (w.trans Fin.revPerm) fourth < (w.trans Fin.revPerm) third) := by
        intro first second third fourth hfirst hsecond hthird forbidden
        change (w second).rev < (w first).rev ∧ (w first).rev < (w fourth).rev ∧
          (w fourth).rev < (w third).rev at forbidden
        simp only [Fin.rev_lt_rev] at forbidden
        exact avoidance first second third fourth hfirst hsecond hthird
          (Or.inr ⟨forbidden.2.2, forbidden.2.1, forbidden.1⟩)
      apply pairs (w.trans Fin.revPerm) complement_avoids first third second fourth
      · exact (complement_edge first third distinct_first).mpr diagonal_first
      · exact (complement_edge second fourth distinct_second).mpr diagonal_second
      · exact fun h => (complement_edge first second (graph.ne_of_adj edge_first)).mp h edge_first
      · exact fun h => (complement_edge first fourth
          (graph.ne_of_adj edge_fourth).symm).mp h (graph.adj_symm edge_fourth)
      · exact fun h => (complement_edge third second
          (graph.ne_of_adj edge_second).symm).mp h (graph.adj_symm edge_second)
      · exact fun h => (complement_edge third fourth (graph.ne_of_adj edge_third)).mp h edge_third
    have no_five : ∀ first second third fourth fifth : Fin n,
        graph.Adj first second → graph.Adj second third → graph.Adj third fourth →
        graph.Adj fourth fifth → graph.Adj fifth first →
        ¬ graph.Adj first third → ¬ graph.Adj first fourth → ¬ graph.Adj second fourth →
        ¬ graph.Adj second fifth → ¬ graph.Adj third fifth → False := by
      intro first second third fourth fifth edge_first edge_second edge_third edge_fourth
        edge_fifth chord_first chord_second chord_third chord_fourth chord_fifth
      change (first < second ∧ w second < w first) ∨
        (second < first ∧ w first < w second) at edge_first
      change (second < third ∧ w third < w second) ∨
        (third < second ∧ w second < w third) at edge_second
      change (third < fourth ∧ w fourth < w third) ∨
        (fourth < third ∧ w third < w fourth) at edge_third
      change (fourth < fifth ∧ w fifth < w fourth) ∨
        (fifth < fourth ∧ w fourth < w fifth) at edge_fourth
      change (fifth < first ∧ w first < w fifth) ∨
        (first < fifth ∧ w fifth < w first) at edge_fifth
      change ¬ ((first < third ∧ w third < w first) ∨
        (third < first ∧ w first < w third)) at chord_first
      change ¬ ((first < fourth ∧ w fourth < w first) ∨
        (fourth < first ∧ w first < w fourth)) at chord_second
      change ¬ ((second < fourth ∧ w fourth < w second) ∨
        (fourth < second ∧ w second < w fourth)) at chord_third
      change ¬ ((second < fifth ∧ w fifth < w second) ∨
        (fifth < second ∧ w second < w fifth)) at chord_fourth
      change ¬ ((third < fifth ∧ w fifth < w third) ∨
        (fifth < third ∧ w third < w fifth)) at chord_fifth
      rcases edge_first with edge_first | edge_first <;>
        rcases edge_second with edge_second | edge_second <;>
        rcases edge_third with edge_third | edge_third <;>
        rcases edge_fourth with edge_fourth | edge_fourth <;>
        rcases edge_fifth with edge_fifth | edge_fifth <;> omega
    obtain ⟨clique, hclique, independent⟩ :=
      graph_split_criterion positive graph no_pairs no_four no_five
    refine ⟨Finset.univ \ clique, ?_, ?_⟩
    · intro first hfirst second hsecond hlt
      have hnonedge := independent first (Finset.mem_sdiff.mp hfirst).2
        second (Finset.mem_sdiff.mp hsecond).2
      have hvalue : (w first).val ≠ (w second).val :=
        fun heq => (w.injective.ne (ne_of_lt hlt)) (Fin.ext heq)
      change ¬ ((first < second ∧ w second < w first) ∨
        (second < first ∧ w first < w second)) at hnonedge
      omega
    · intro first hfirst second hsecond hlt
      have hmem_first : first ∈ clique := by simpa using hfirst
      have hmem_second : second ∈ clique := by simpa using hsecond
      have hedge := hclique hmem_first hmem_second (ne_of_lt hlt)
      change (first < second ∧ w second < w first) ∨
        (second < first ∧ w first < w second) at hedge
      omega

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookRegions
