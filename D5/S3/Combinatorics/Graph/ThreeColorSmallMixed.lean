/- GID: D5/S3/Combinatorics/Graph/ThreeColorSmallMixed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ThreeColorSmallMixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Actual finite graph consumer for the bounded small-mixed reciprocal inequality. -/

import D5.S3.Combinatorics.Graph.ThreeColorSmallMixedCore

open D5.S3.Combinatorics.Graph.ThreeColorReciprocal
open D5.S3.Combinatorics.Graph.ColoredReciprocalDeletion
open Finset
open scoped Classical

namespace D5.S3.Combinatorics.Graph.ThreeColorSmallMixed

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1200000 in
/-- The bounded small-mixed reciprocal inequality for an actual finite properly
three-colored simple graph. Isolates and empty color classes are retained. -/
theorem small_mixed_graph_potential (G : SimpleGraph V)
    (c : G.Coloring (Fin 3))
    (hmixed : ∀ v, ColoredReciprocalDeletion.Mixed G c v → G.degree v = 2)
    (hmrange : 2 ≤ (univ.filter (fun v => ColoredReciprocalDeletion.Mixed G c v)).card ∧
      (univ.filter (fun v => ColoredReciprocalDeletion.Mixed G c v)).card ≤ 5) :
    (2 : ℚ) ≤ ColoredReciprocalDeletion.potential G c := by
  let s : Finset V := univ.filter (fun v => (G.neighborFinset v).Nonempty)
  have hsym (u : V) (hu : u ∈ s) (v : V) (hv : v ∈ s) (h : G.Adj u v) : G.Adj v u := h.symm
  have hproper (u : V) (hu : u ∈ s) (v : V) (hv : v ∈ s) (h : G.Adj u v) : c u ≠ c v := c.valid h
  have neighbors (v : V) (hv : v ∈ univ) :
      neighborhood s G.Adj v = neighborhood (univ : Finset V) G.Adj v := by
    ext u
    simp only [neighborhood, mem_filter]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hu, huv⟩
      exact huv
    · intro huv
      refine ⟨?_, huv⟩
      have hne : (G.neighborFinset u).Nonempty := by
        refine ⟨v, ?_⟩
        exact (G.mem_neighborFinset _ _).mpr huv.symm
      exact mem_filter.mpr ⟨mem_univ _, hne⟩
  have adj_mem_s (v u : V) (h : G.Adj v u) : u ∈ s := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact ⟨v, (G.mem_neighborFinset _ _).mpr h.symm⟩
  have mixed_iff (v : V) :
      Mixed s G.Adj c v ↔ ColoredReciprocalDeletion.Mixed G c v := by
    constructor
    · rintro ⟨u, hu, w, hw, hne⟩
      exact ⟨u, w, (mem_filter.mp hu).2, (mem_filter.mp hw).2, hne⟩
    · rintro ⟨u, w, hu, hw, hne⟩
      exact ⟨u, mem_filter.mpr ⟨adj_mem_s v u hu, hu⟩,
        w, mem_filter.mpr ⟨adj_mem_s v w hw, hw⟩, hne⟩
  have hm (v : V) (hv : v ∈ s) (h : Mixed s G.Adj c v) :
      (neighborhood s G.Adj v).card = 2 := by
    rw [neighbors v (mem_univ _)]
    rw [show neighborhood (univ : Finset V) G.Adj v = G.neighborFinset v by
      ext u; simp [neighborhood, SimpleGraph.mem_neighborFinset]]
    rw [G.card_neighborFinset_eq_degree]
    exact hmixed v ((mixed_iff v).mp h)
  have hne (v : V) (hv : v ∈ s) : (neighborhood s G.Adj v).Nonempty := by
    rw [neighbors v (mem_univ _)]
    rw [show neighborhood (univ : Finset V) G.Adj v = G.neighborFinset v by
      ext u; simp [neighborhood, SimpleGraph.mem_neighborFinset]]
    exact (mem_filter.mp hv).2
  have red := population_reduction s G.Adj c hsym hproper hm hne
  let m : Fin 3 → Nat := fun i => (mixedColor s G.Adj c i).card
  have mixedColor_eq (i : Fin 3) :
      mixedColor s G.Adj c i =
        (univ.filter (fun v => c v = i ∧ ColoredReciprocalDeletion.Mixed G c v)) := by
    ext v
    constructor
    · intro hv
      have hvm := (mem_filter.mp hv).2.2
      have hvg := (mixed_iff v).mp hvm
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2.1, hvg⟩
    · intro hv
      have h := mem_filter.mp hv
      refine mem_filter.mpr ⟨?_, h.2.1, ?_⟩
      · exact mem_filter.mpr ⟨mem_univ _, by
          rcases h.2.2 with ⟨u,w,hu,hw,_⟩
          exact ⟨u, (G.mem_neighborFinset _ _).mpr hu⟩⟩
      · exact (mixed_iff v).mpr h.2.2
  have hMcard :
      (∑ i : Fin 3, (mixedColor s G.Adj c i).card) =
        (univ.filter (fun v => ColoredReciprocalDeletion.Mixed G c v)).card := by
    let M := univ.filter (fun v => ColoredReciprocalDeletion.Mixed G c v)
    calc
      (∑ i : Fin 3, (mixedColor s G.Adj c i).card) =
          ∑ i : Fin 3, (M.filter (fun v => c v = i)).card := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [mixedColor_eq]
            simp [M, Finset.filter_filter, and_comm, and_left_comm, and_assoc]
      _ = M.card := by
        symm
        simpa using (card_eq_sum_card_fiberwise (s := M)
          (t := (univ : Finset (Fin 3))) (f := c) (fun _ _ => mem_univ _))
      _ = (univ.filter (fun v => ColoredReciprocalDeletion.Mixed G c v)).card := by rfl
  have hsmall : ∑ i, m i ≤ 5 := by
    change (∑ i : Fin 3, (mixedColor s G.Adj c i).card) ≤ 5
    rw [hMcard]
    exact hmrange.2
  have hlarge : 2 ≤ ∑ i, m i := by
    change 2 ≤ (∑ i : Fin 3, (mixedColor s G.Adj c i).card)
    rw [hMcard]
    exact hmrange.1
  have base : (2 : ℚ) ≤ potential s G.Adj c := by
    have hpop := small_population_bound m (fun i j => (ordinary s G.Adj c i j).card)
      red.1 red.2.1 hlarge hsmall
    exact hpop.trans red.2.2
  have isolated (v : V) (hv : v ∈ (univ : Finset V) \ s) :
      neighborhood (univ : Finset V) G.Adj v = ∅ := by
    have hn : ¬(neighborhood (univ : Finset V) G.Adj v).Nonempty := by
      intro hn
      have hvuniv : v ∈ (univ : Finset V) := (mem_sdiff.mp hv).1
      have hn' : (G.neighborFinset v).Nonempty := by
        rw [← show neighborhood (univ : Finset V) G.Adj v = G.neighborFinset v by
          ext u; simp [neighborhood, SimpleGraph.mem_neighborFinset]]
        exact hn
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨hvuniv, hn'⟩)
    exact not_nonempty_iff_eq_empty.mp hn
  have scalar (a r : Nat) :
      1 / ((a : ℚ)+1) ≤ 1 / ((a+r : Nat)+1 : ℚ) + (r : ℚ)/2 := by
    cases r with
    | zero => simp
    | succ r =>
      push_cast
      apply le_of_sub_nonneg
      field_simp
      ring_nf
      positivity
  have disj : Disjoint s ((univ : Finset V) \ s) :=
    disjoint_left.mpr (fun v hv hz => (mem_sdiff.mp hz).2 hv)
  have count (i : Fin 3) :
      ((univ : Finset V).filter fun v => c v = i).card =
        (s.filter fun v => c v = i).card +
          (((univ : Finset V) \ s).filter fun v => c v = i).card := by
    have hs : (univ : Finset V) = s ∪ ((univ : Finset V) \ s) :=
      (union_sdiff_of_subset (filter_subset _ _)).symm
    conv_lhs => rw [hs, filter_union]
    exact card_union_of_disjoint (disj.mono (filter_subset _ _) (filter_subset _ _))
  have cardz : (((univ : Finset V) \ s).card : ℚ) =
      ∑ i : Fin 3, ((((univ : Finset V) \ s).filter fun v => c v = i).card : ℚ) := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s := (univ : Finset V) \ s)
      (t := (univ : Finset (Fin 3))) (f := c) (fun _ _ => mem_univ _))
  have classes :
      (∑ i : Fin 3, 1 / ((((s.filter fun v => c v = i).card : ℚ) + 1))) ≤
      (∑ i : Fin 3, 1 / (((((univ : Finset V).filter fun v => c v = i).card : ℚ) + 1))) +
        (((univ : Finset V) \ s).card : ℚ)/2 := by
    calc
      _ ≤ ∑ i : Fin 3,
          (1 / (((((univ : Finset V).filter fun v => c v = i).card : ℚ) + 1)) +
            (((((univ : Finset V) \ s).filter fun v => c v = i).card : ℚ) / 2)) := by
        apply sum_le_sum
        intro i hi
        rw [count]
        exact scalar _ _
      _ = (∑ i : Fin 3,
          1 / (((((univ : Finset V).filter fun v => c v = i).card : ℚ) + 1))) +
            (((univ : Finset V) \ s).card : ℚ) / 2 := by
        rw [sum_add_distrib, ← Finset.sum_div, cardz]
  have weights :
      (∑ v ∈ (univ : Finset V), 1/((neighborhood (univ : Finset V) G.Adj v).card+1 : ℚ)) =
        (∑ v ∈ s, 1/((neighborhood s G.Adj v).card+1 : ℚ)) +
          (((univ : Finset V) \ s).card : ℚ) := by
    have live : (∑ v ∈ s, 1/((neighborhood (univ : Finset V) G.Adj v).card+1 : ℚ)) =
        ∑ v ∈ s, 1/((neighborhood s G.Adj v).card+1 : ℚ) := by
      apply sum_congr rfl
      intro v hv
      rw [neighbors v (mem_univ _)]
    have dead : (∑ v ∈ (univ : Finset V) \ s,
        1/((neighborhood (univ : Finset V) G.Adj v).card+1 : ℚ)) =
          (((univ : Finset V) \ s).card : ℚ) := by
      simp only [sum_congr rfl (fun v hv => congrArg (fun a : Nat => 1/(a+1 : ℚ))
        (congrArg Finset.card (isolated v hv))), card_empty]
      simp
    calc
      _ = (∑ v ∈ s, 1/((neighborhood (univ : Finset V) G.Adj v).card+1 : ℚ)) +
          ∑ v ∈ (univ : Finset V) \ s,
            1/((neighborhood (univ : Finset V) G.Adj v).card+1 : ℚ) := by
        rw [← sum_union disj, union_sdiff_of_subset (filter_subset _ _)]
      _ = _ := by rw [live, dead]
  have hfinite : (2 : ℚ) ≤ potential (univ : Finset V) G.Adj c := by
    unfold ThreeColorReciprocal.potential at base ⊢
    rw [weights]
    linarith [classes]
  have hdegree_sum :
      (∑ v ∈ (univ : Finset V),
        1 / ((neighborhood (univ : Finset V) G.Adj v).card + 1 : ℚ)) =
        ∑ v, 1 / (G.degree v + 1 : ℚ) := by
    apply sum_congr rfl
    intro v hv
    rw [show neighborhood (univ : Finset V) G.Adj v = G.neighborFinset v by
      ext u; simp [neighborhood, SimpleGraph.mem_neighborFinset],
      G.card_neighborFinset_eq_degree]
  unfold ThreeColorReciprocal.potential at hfinite
  rw [hdegree_sum] at hfinite
  simpa [ColoredReciprocalDeletion.potential] using hfinite
end D5.S3.Combinatorics.Graph.ThreeColorSmallMixed
