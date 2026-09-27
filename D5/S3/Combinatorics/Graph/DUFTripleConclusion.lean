/- GID: D5/S3/Combinatorics/Graph/DUFTripleConclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFTripleConclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unconditional triple DUF bound and exact four-distinct-triple forcing asymptotic. -/

import D5.S3.Combinatorics.Graph.DUFGlobalAllocation
import D5.S3.Combinatorics.Graph.ThreeColorSmallMixed
import D5.S3.Combinatorics.Graph.ThreeColorOuterCases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph
open DUFStructure DUFReciprocal DUFPacketOwnership DUFLocalPackets DUFMarkedStars
open ColoredReciprocalDeletion
open DUFRowGeometry DUFRowPayment DUFGlobalAllocation
open Filter Topology

namespace D5.S3.Combinatorics.Graph.DUFTripleConclusion

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def dufTripleFamilies (n : ℕ) :
    Finset (Finset (Finset (Fin n))) :=
  (((univ : Finset (Fin n)).powersetCard 3).powerset).filter DUFStructure.DUF

noncomputable def M3 (n : ℕ) : ℕ :=
  (dufTripleFamilies n).sup Finset.card

def starTriples {n : ℕ} (v : Fin n) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard 3).filter fun e => {v} ⊆ e

def fourDistinctCollision {V : Type} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) : Prop :=
  ∃ A ∈ H, ∃ B ∈ H, ∃ C ∈ H, ∃ D ∈ H,
    List.Pairwise (fun x y : Finset V => x ≠ y) [A, B, C, D] ∧
      Disjoint A B ∧ Disjoint C D ∧ A ∪ B = C ∪ D

def collisionForcing (n m : ℕ) : Prop :=
  ∀ H : Finset (Finset (Fin n)),
    (∀ e ∈ H, e.card = 3) → m ≤ H.card → fourDistinctCollision H

def F3 (n : ℕ) : ℕ := sInf {m : ℕ | collisionForcing n m}

/-- The support bound for every finite ambient type, the literal finite maximum,
the exact collision threshold, its binomial bounds, and its real asymptotic. -/
theorem result :
    (∀ {V : Type u} [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      (∀ e ∈ H, e.card = 3) → DUF H →
      2 * H.card ≤ (pairs.filter fun p => (neighbors H p).Nonempty).card +
        (pairs.filter fun q => (common H q).Nonempty).card ∧
      H.card ≤ (Fintype.card V).choose 2) ∧
    (∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      (∀ e ∈ H, e.card = 3) → (¬ DUFStructure.DUF H ↔ fourDistinctCollision H)) ∧
    (∀ n, (∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧ DUFStructure.DUF H ∧ H.card = M3 n) ∧
      (∀ H : Finset (Finset (Fin n)),
        (∀ e ∈ H, e.card = 3) → DUFStructure.DUF H → H.card ≤ M3 n) ∧
      F3 n = M3 n + 1 ∧ IsLeast {m : ℕ | collisionForcing n m} (F3 n) ∧
      ∀ m, collisionForcing n m ↔ F3 n ≤ m) ∧
    (∀ n, 3 ≤ n → (n-1).choose 2 + 1 ≤ F3 n ∧ F3 n ≤ n.choose 2 + 1) ∧
    Tendsto (fun n : ℕ => (F3 n : ℝ) / (n.choose 2 : ℝ)) atTop (𝓝 1) := by
  have uniform_three_bound {V : Type u} [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (hu : ∀ e ∈ H, e.card = 3) (hd : DUF H) :
      2 * H.card ≤ (pairs.filter fun p => (neighbors H p).Nonempty).card +
        (pairs.filter fun q => (common H q).Nonempty).card ∧
      H.card ≤ (Fintype.card V).choose 2 := by
    obtain ⟨color_eq_iff, neighbor_transport, degree_transport, mixed_iff, mixed_degree,
      potential_transport, leaf_iff, row_disjoint, row_i_notMem, row_members_facts, recipient_mem,
      internal_subset, internal_zero, internal_one, internal_many, other_spec, internal_owner,
      internal_disjoint, assigned_actual, assigned_mixed, assigned_injective,
      configuration_coverage⟩ :=
      DUFRowGeometry.result (V := V)
    obtain ⟨incoming_residual, internalUnion_subset, remainingScore_of_mem, global_balance⟩ :=
      DUFGlobalAllocation.result (V := V)
    have reciprocal_identity (H : Finset (Finset V))
        (hu : ∀ e ∈ H, e.card = 3) :
        (∑ e ∈ H, weight H e) =
          ((pairs.filter fun p => (neighbors H p).Nonempty).card : ℚ) +
          ((pairs.filter fun q => (common H q).Nonempty).card : ℚ) := by
      have reindex (f : Finset V → V → ℚ) :
          (∑ e ∈ H, ∑ a ∈ e, f (e.erase a) a) =
            ∑ p ∈ pairs, ∑ a ∈ neighbors H p, f p a := by
        rw [sum_sigma', sum_sigma']
        apply sum_bij (fun z _ => ⟨z.1.erase z.2, z.2⟩)
        · rintro ⟨e, a⟩ hz
          obtain ⟨he, ha⟩ := mem_sigma.mp hz
          apply mem_sigma.mpr
          refine ⟨?_, ?_⟩
          · simp [pairs, card_erase_of_mem ha, hu e he]
          · simp only [neighbors, mem_filter, mem_univ, true_and]
            exact ⟨by simp, (insert_erase ha).symm ▸ he⟩
        · rintro ⟨e, a⟩ hz ⟨f, b⟩ hw h
          obtain ⟨he, ha⟩ := mem_sigma.mp hz
          obtain ⟨hf, hb⟩ := mem_sigma.mp hw
          have hab : a = b := congrArg Sigma.snd h
          subst b
          have hef : e.erase a = f.erase a := congrArg Sigma.fst h
          have : e = f := (insert_erase ha).symm.trans ((congrArg (insert a) hef).trans (insert_erase hb))
          subst f
          rfl
        · rintro ⟨p, a⟩ hz
          obtain ⟨hp, ha⟩ := mem_sigma.mp hz
          obtain ⟨hap, hH⟩ := (mem_filter.mp ha).2
          refine ⟨⟨insert a p, a⟩, mem_sigma.mpr ⟨hH, mem_insert_self _ _⟩, ?_⟩
          simp [erase_insert hap]
        · intro z hz
          rfl
      have ordered (S : Finset V) (f : Finset V → ℚ) :
          (∑ a ∈ S, ∑ x ∈ S.erase a, f {a, x}) =
            2 * ∑ q ∈ S.powersetCard 2, f q := by
        have hh : (∑ z ∈ S.offDiag, f {z.1, z.2}) =
            ∑ a ∈ S, ∑ x ∈ S.erase a, f {a, x} := by
          apply sum_finset_product
          intro z
          simp only [mem_offDiag, mem_erase]
          tauto
        rw [← hh, ← sum_fiberwise_of_maps_to' (t := S.powersetCard 2)
          (g := fun z : V × V => ({z.1, z.2} : Finset V))
          (fun z hz => by
            obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp hz
            simp [mem_powersetCard, insert_subset_iff, ha, hb, hab]) f]
        rw [mul_sum]
        apply sum_congr rfl
        intro q hq
        obtain ⟨hqS, hq2⟩ := mem_powersetCard.mp hq
        obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hq2
        have ha : a ∈ S := hqS (by simp)
        have hb : b ∈ S := hqS (by simp)
        have he : (S.offDiag.filter fun z => ({z.1, z.2} : Finset V) = {a, b}) =
            {(a, b), (b, a)} := by
          ext z
          simp only [mem_filter, mem_offDiag, mem_insert, mem_singleton]
          constructor
          · rintro ⟨⟨hz1, hz2, hne⟩, he⟩
            have h1 : z.1 = a ∨ z.1 = b := by
              have : z.1 ∈ ({a, b} : Finset V) := he ▸ (by simp)
              simpa using this
            have h2 : z.2 = a ∨ z.2 = b := by
              have : z.2 ∈ ({a, b} : Finset V) := he ▸ (by simp)
              simpa using this
            rcases z with ⟨u, v⟩
            simp only at *
            rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all
          · rintro (rfl | rfl) <;> simp [ha, hb, hab, hab.symm, pair_comm]
        rw [he]
        simp [hab, hab.symm, two_mul]
      have first : (∑ e ∈ H, ∑ a ∈ e,
          1 / ((neighbors H (e.erase a)).card : ℚ)) =
            ((pairs.filter fun p => (neighbors H p).Nonempty).card : ℚ) := by
        rw [reindex (fun p _ => 1 / ((neighbors H p).card : ℚ))]
        simp only [sum_const, nsmul_eq_mul]
        rw [← sum_boole]
        apply sum_congr rfl
        intro p hp
        by_cases h : (neighbors H p).Nonempty
        · have hn : ((neighbors H p).card : ℚ) ≠ 0 := by
            exact_mod_cast (card_pos.mpr h).ne'
          simp [h, hn]
        · simp [not_nonempty_iff_eq_empty.mp h]
      have second : (∑ e ∈ H, ∑ a ∈ e,
          ∑ x ∈ (neighbors H (e.erase a)).erase a,
            1 / ((common H {a, x}).card : ℚ)) =
          2 * ((pairs.filter fun q => (common H q).Nonempty).card : ℚ) := by
        rw [reindex (fun p a => ∑ x ∈ (neighbors H p).erase a,
          1 / ((common H {a, x}).card : ℚ))]
        simp_rw [ordered _ (fun q => 1 / ((common H q).card : ℚ))]
        rw [← mul_sum]
        congr 1
        have hp (S : Finset V) : S.powersetCard 2 = pairs.filter fun q => q ⊆ S := by
          ext q
          simp [pairs, and_comm]
        simp_rw [hp, sum_filter]
        rw [sum_comm]
        have ht : (∑ q ∈ pairs, ∑ p ∈ pairs,
            if q ⊆ neighbors H p then 1 / ((common H q).card : ℚ) else 0) =
            ∑ q ∈ pairs, ((common H q).card : ℚ) *
              (1 / ((common H q).card : ℚ)) := by
          apply sum_congr rfl
          intro q hq
          rw [← sum_filter]
          simp [common]
        rw [ht, ← sum_boole]
        apply sum_congr rfl
        intro q hq
        by_cases h : (common H q).Nonempty
        · have hn : ((common H q).card : ℚ) ≠ 0 := by
            exact_mod_cast (card_pos.mpr h).ne'
          simp [h, hn]
        · simp [not_nonempty_iff_eq_empty.mp h]
      simp only [weight, sum_add_distrib, ← mul_sum]
      rw [first, second]
      ring
    have obstruction {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) (c : G.Coloring (Fin 3))
        (hm : ∀ w, Mixed G c w → G.degree w = 2)
        (hB : potential G c < 2) :
        ∃ w l : W, (∀ v, Mixed G c v ↔ v = w) ∧
          G.neighborFinset l = {w} ∧ (univ.filter fun v => c v = c l) = {l} := by
      have hN (v : W) : ThreeColorReciprocal.neighborhood univ G.Adj v =
          G.neighborFinset v := by
        ext u
        simp [ThreeColorReciprocal.neighborhood, SimpleGraph.mem_neighborFinset]
      have hM (v : W) : ThreeColorReciprocal.Mixed univ G.Adj c v ↔ Mixed G c v := by
        simp only [ThreeColorReciprocal.Mixed, hN, SimpleGraph.mem_neighborFinset, Mixed]
        constructor
        · rintro ⟨u, hu, w, hw, hc⟩; exact ⟨u, w, hu, hw, hc⟩
        · rintro ⟨u, w, hu, hw, hc⟩; exact ⟨u, hu, w, hw, hc⟩
      have hP : ThreeColorReciprocal.potential univ G.Adj c = potential G c := by
        simp only [ThreeColorReciprocal.potential, potential, hN,
          SimpleGraph.card_neighborFinset_eq_degree]
      have hsmall : ¬(2 ≤ (univ.filter (Mixed G c)).card ∧
          (univ.filter (Mixed G c)).card ≤ 5) := by
        intro hr
        exact (not_le_of_gt hB) (ThreeColorSmallMixed.small_mixed_graph_potential G c hm hr)
      have houter : (univ.filter (ThreeColorReciprocal.Mixed univ G.Adj c)).card = 0 ∨
          (univ.filter (ThreeColorReciprocal.Mixed univ G.Adj c)).card = 1 ∨
          6 ≤ (univ.filter (ThreeColorReciprocal.Mixed univ G.Adj c)).card := by
        have hfilter : univ.filter (ThreeColorReciprocal.Mixed univ G.Adj c) =
            univ.filter (Mixed G c) := by
          ext v
          simp only [mem_filter, hM]
        rw [hfilter]
        omega
      obtain ⟨w, _, l, _, unique, leaf, color⟩ := ThreeColorOuterCases.result univ G.Adj c
        (fun _ _ _ _ h => h.symm) (fun _ _ _ _ h => c.valid h)
        (by intro v _ hv; rw [hN, SimpleGraph.card_neighborFinset_eq_degree];
            exact hm v ((hM v).mp hv)) houter (by rwa [hP])
      exact ⟨w, l, fun v => (hM v).symm.trans (unique v (mem_univ _)),
        (hN l).symm.trans leaf, color⟩
    have negative_covered (e : Finset V) (he : e ∈ H) (hn : weight H e < 2) :
        e ∈ internalUnion H := by
      obtain ⟨w,l,unique,leaf,color⟩ := obstruction (graph H e) (coloring H e (hu e he))
        (mixed_degree H hd e he (hu e he)) (by rwa [potential_transport H hd e he (hu e he)])
      have hwl : (graph H e).Adj w l := by
        apply SimpleGraph.Adj.symm
        apply (SimpleGraph.mem_neighborFinset _ _ _).mp
        rw [leaf]; simp
      have hl : (graph H e).degree l = 1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, leaf, card_singleton]
      obtain ⟨r,b,hr,hmark,hei,_⟩ := configuration_coverage H hd e he (hu e he) w l
        ((unique w).mpr rfl) hwl color hl
      exact mem_biUnion.mpr ⟨⟨r,hr⟩,mem_univ _,hei⟩
    have residual_bound (e : Finset V) (he : e ∈ H)
        (hW : (selectedVertices H e).Nonempty) :
        2 ≤ potential ((graph H e).induce {w | w ∉ selectedVertices H e})
          (residualColoring H e (hu e he)) := by
      have hr := incoming_residual H hd e he (hu e he) hW
      by_contra h
      obtain ⟨w,l,_,hleaf,hcolor⟩ := obstruction
        ((graph H e).induce {w | w ∉ selectedVertices H e})
        (residualColoring H e (hu e he)) hr.1 (lt_of_not_ge h)
      apply hr.2 l hcolor
      apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      have hadj (z) : ((graph H e).induce {w | w ∉ selectedVertices H e}).Adj l z ↔ z = w := by
        simpa only [SimpleGraph.mem_neighborFinset, mem_singleton] using
          (Finset.ext_iff.mp hleaf z)
      exact ⟨w, (hadj w).mpr rfl, fun z hz => (hadj z).mp hz⟩
    have outside (e : Finset V) (he : e ∈ H \ internalUnion H) :
        2 ≤ remainingScore H hu e := by
      rw [remainingScore_of_mem H hu e (mem_sdiff.mp he).1]
      split_ifs with hW
      · exact residual_bound e (mem_sdiff.mp he).1 hW
      · exact le_of_not_gt (fun h => (mem_sdiff.mp he).2
          (negative_covered e (mem_sdiff.mp he).1 h))
    have total : 2 * (H.card : ℚ) ≤ ∑ e ∈ H, weight H e := by
      have hsum := sum_le_sum outside
      have hcard : (internalUnion H).card + (H \ internalUnion H).card = H.card := by
        rw [card_sdiff_of_subset (internalUnion_subset H)]
        exact Nat.add_sub_of_le (card_le_card (internalUnion_subset H))
      have hcardQ : ((internalUnion H).card : ℚ) + (H \ internalUnion H).card = H.card := by
        exact_mod_cast hcard
      have hb := global_balance H hu hd
      simp only [sum_const, nsmul_eq_mul] at hsum
      linarith
    rw [reciprocal_identity H hu] at total
    have pair_count : (pairs (V := V)).card = (Fintype.card V).choose 2 := by
      simp [pairs]
    have hs : (pairs.filter fun p => (neighbors H p).Nonempty).card ≤
        (Fintype.card V).choose 2 := by
      rw [← pair_count]; exact card_le_card (filter_subset _ _)
    have ht : (pairs.filter fun q => (common H q).Nonempty).card ≤
        (Fintype.card V).choose 2 := by
      rw [← pair_count]; exact card_le_card (filter_subset _ _)
    have totalN : 2 * H.card ≤ (pairs.filter fun p => (neighbors H p).Nonempty).card +
        (pairs.filter fun q => (common H q).Nonempty).card := by exact_mod_cast total
    exact ⟨totalN, by omega⟩
  have bound (n : ℕ) (H : Finset (Finset (Fin n)))
      (hu : ∀ e ∈ H, e.card = 3) (hd : DUF H) : H.card ≤ n.choose 2 := by
    let f : Fin n ↪ ULift.{u} (Fin n) := ⟨ULift.up, ULift.up_injective⟩
    let ff : Finset (Fin n) ↪ Finset (ULift.{u} (Fin n)) := ⟨Finset.map f, Finset.map_injective f⟩
    have hcard : (H.map ff).card = H.card := card_map _
    have hduf : DUFStructure.DUF (H.map ff) := by
      intro A hA B hB C hC D hD hAB hCD heq
      obtain ⟨A,hAH,rfl⟩ := mem_map.mp hA
      obtain ⟨B,hBH,rfl⟩ := mem_map.mp hB
      obtain ⟨C,hCH,rfl⟩ := mem_map.mp hC
      obtain ⟨D,hDH,rfl⟩ := mem_map.mp hD
      change Disjoint (A.map f) (B.map f) at hAB
      change Disjoint (C.map f) (D.map f) at hCD
      change A.map f ∪ B.map f = C.map f ∪ D.map f at heq
      rw [← map_union, ← map_union, Finset.map_inj] at heq
      rcases hd A hAH B hBH C hCH D hDH ((Finset.disjoint_map f).mp hAB)
        ((Finset.disjoint_map f).mp hCD) heq with h | h
      · exact Or.inl ⟨congrArg ff h.1, congrArg ff h.2⟩
      · exact Or.inr ⟨congrArg ff h.1, congrArg ff h.2⟩
    have h := (uniform_three_bound (H.map ff) (by
      intro e he
      obtain ⟨e,heH,rfl⟩ := mem_map.mp he
      exact (card_map _).trans (hu e heH)) hduf).2
    simpa only [hcard, Fintype.card_ulift, Fintype.card_fin] using h
  refine ⟨uniform_three_bound, ?_⟩

  have mem_dufTripleFamilies_iff (n : ℕ) (H : Finset (Finset (Fin n))) :
      H ∈ dufTripleFamilies n ↔
        (∀ e ∈ H, e.card = 3) ∧ DUFStructure.DUF H := by
    simp only [dufTripleFamilies, mem_filter, mem_powerset]
    constructor
    · rintro ⟨hsub, hd⟩
      exact ⟨fun e he => (mem_powersetCard.mp (hsub he)).2, hd⟩
    · rintro ⟨hu, hd⟩
      exact ⟨fun e he => mem_powersetCard.mpr ⟨subset_univ _, hu e he⟩, hd⟩
  have empty_mem_dufTripleFamilies (n : ℕ) :
      (∅ : Finset (Finset (Fin n))) ∈ dufTripleFamilies n := by
    rw [mem_dufTripleFamilies_iff]
    simp [DUFStructure.DUF]
  have M3_attained (n : ℕ) :
      ∃ H : Finset (Finset (Fin n)),
        (∀ e ∈ H, e.card = 3) ∧ DUFStructure.DUF H ∧ H.card = M3 n := by
    obtain ⟨H, hH, hcard⟩ := Finset.exists_mem_eq_sup (dufTripleFamilies n)
      ⟨∅, empty_mem_dufTripleFamilies n⟩ Finset.card
    obtain ⟨hu, hd⟩ := (mem_dufTripleFamilies_iff n H).mp hH
    exact ⟨H, hu, hd, hcard.symm⟩
  have card_le_M3 (n : ℕ) (H : Finset (Finset (Fin n)))
      (hu : ∀ e ∈ H, e.card = 3) (hd : DUFStructure.DUF H) :
      H.card ≤ M3 n := by
    exact Finset.le_sup ((mem_dufTripleFamilies_iff n H).mpr ⟨hu, hd⟩)
  have starTriples_uniform {n : ℕ} (v : Fin n) :
      ∀ e ∈ starTriples v, e.card = 3 := by
    intro e he
    exact (mem_powersetCard.mp (mem_filter.mp he).1).2
  have starTriples_duf {n : ℕ} (v : Fin n) :
      DUFStructure.DUF (starTriples v) := by
    intro A hA B hB C _ D _ hAB _ _
    have hvA : v ∈ A := (mem_filter.mp hA).2 (mem_singleton_self v)
    have hvB : v ∈ B := (mem_filter.mp hB).2 (mem_singleton_self v)
    exact (Finset.disjoint_left.mp hAB hvA hvB).elim
  have card_starTriples {n : ℕ} (v : Fin n) :
      (starTriples v).card = (n - 1).choose 2 := by
    simpa only [starTriples, card_singleton, card_univ, Fintype.card_fin,
      Nat.reduceSub] using
      (Finset.card_filter_powersetCard_subset ({v} : Finset (Fin n)) univ 3
        (subset_univ _) (by simp))
  have star_lower_bound (n : ℕ) (hn : 1 ≤ n) :
      (n - 1).choose 2 ≤ M3 n := by
    let v : Fin n := ⟨0, hn⟩
    rw [← card_starTriples v]
    exact card_le_M3 n (starTriples v) (starTriples_uniform v) (starTriples_duf v)
  have fourDistinctCollision_of_not_duf
      {V : Type} [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3)
      (hn : ¬ DUFStructure.DUF H) : fourDistinctCollision H := by
    rw [DUFStructure.DUF] at hn
    push Not at hn
    obtain ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hU, hfail⟩ := hn
    have hAne : A ≠ ∅ := by
      intro h
      have hc := hu A hA
      simp [h] at hc
    have hCne : C ≠ ∅ := by
      intro h
      have hc := hu C hC
      simp [h] at hc
    have hABne : A ≠ B := by
      intro h
      subst B
      obtain ⟨x, hx⟩ := (nonempty_iff_ne_empty.mpr hAne)
      exact (disjoint_left.mp hAB) hx hx
    have hCDne : C ≠ D := by
      intro h
      subst D
      obtain ⟨x, hx⟩ := (nonempty_iff_ne_empty.mpr hCne)
      exact (disjoint_left.mp hCD) hx hx
    have hAC : A ≠ C := by
      intro h
      apply (hfail.1 h)
      subst C
      calc
        B = (A ∪ B) \ A := (union_sdiff_cancel_left hAB).symm
        _ = (A ∪ D) \ A := congrArg (fun X : Finset V => X \ A) hU
        _ = D := union_sdiff_cancel_left hCD
    have hBD : B ≠ D := by
      intro h
      apply (hfail.1 ?_ h)
      subst D
      calc
        A = (A ∪ B) \ B := (union_sdiff_cancel_right hAB).symm
        _ = (C ∪ B) \ B := congrArg (fun X : Finset V => X \ B) hU
        _ = C := union_sdiff_cancel_right hCD
    have hAD : A ≠ D := by
      intro h
      apply (hfail.2 h)
      subst D
      calc
        B = (A ∪ B) \ A := (union_sdiff_cancel_left hAB).symm
        _ = (C ∪ A) \ A := congrArg (fun X : Finset V => X \ A) hU
        _ = C := union_sdiff_cancel_right hCD
    have hBC : B ≠ C := by
      intro h
      apply (hfail.2 ?_ h)
      subst C
      calc
        A = (A ∪ B) \ B := (union_sdiff_cancel_right hAB).symm
        _ = (B ∪ D) \ B := congrArg (fun X : Finset V => X \ B) hU
        _ = D := union_sdiff_cancel_left hCD
    refine ⟨A, hA, B, hB, C, hC, D, hD, ?_, hAB, hCD, hU⟩
    simpa [List.pairwise_cons] using
      (show (A ≠ B ∧ A ≠ C ∧ A ≠ D) ∧ (B ≠ C ∧ B ≠ D) ∧ C ≠ D from
        ⟨⟨hABne, hAC, hAD⟩, ⟨hBC, hBD⟩, hCDne⟩)
  have not_duf_of_fourDistinctCollision
      {V : Type} [Fintype V] [DecidableEq V]
      (H : Finset (Finset V))
      (hc : fourDistinctCollision H) : ¬ DUFStructure.DUF H := by
    rintro hd
    obtain ⟨A, hA, B, hB, C, hC, D, hD, hp, hAB, hCD, hU⟩ := hc
    have hp' : (A ≠ B ∧ A ≠ C ∧ A ≠ D) ∧ (B ≠ C ∧ B ≠ D) ∧ C ≠ D := by
      simpa [List.pairwise_cons] using hp
    rcases hp' with ⟨⟨hAB', hAC, hAD⟩, ⟨hBC, hBD⟩, hCD'⟩
    rcases hd A hA B hB C hC D hD hAB hCD hU with h | h
    · exact hAC h.1
    · exact hAD h.1
  have not_duf_iff_fourDistinctCollision
      {V : Type} [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3) :
      ¬ DUFStructure.DUF H ↔ fourDistinctCollision H := by
    constructor
    · exact fourDistinctCollision_of_not_duf H hu
    · exact not_duf_of_fourDistinctCollision H
  have forcing_iff (n m : ℕ) : collisionForcing n m ↔ M3 n < m := by
    constructor
    · intro hf
      obtain ⟨H,hu,hd,hcard⟩ := M3_attained n
      by_contra h
      exact (not_duf_iff_fourDistinctCollision H hu).mpr
        (hf H hu (hcard ▸ Nat.le_of_not_gt h)) hd
    · intro hm H hu hcard
      apply (not_duf_iff_fourDistinctCollision H hu).mp
      intro hd
      exact (Nat.not_lt_of_ge (hcard.trans (card_le_M3 n H hu hd))) hm
  have least (n : ℕ) : IsLeast {m : ℕ | collisionForcing n m} (M3 n + 1) := by
    refine ⟨(forcing_iff n _).mpr (Nat.lt_succ_self _), ?_⟩
    intro m hm
    exact (forcing_iff n m).mp hm
  have eqF (n : ℕ) : F3 n = M3 n + 1 := (least n).csInf_eq
  have bounds (n : ℕ) (hn : 3 ≤ n) :
      (n-1).choose 2 + 1 ≤ F3 n ∧ F3 n ≤ n.choose 2 + 1 := by
    rw [eqF]
    have lower := star_lower_bound n (by omega)
    obtain ⟨H,hu,hd,hcard⟩ := M3_attained n
    have upper := bound n H hu hd
    omega
  have tendsto_lower_endpoint :
      Tendsto (fun n : ℕ => (((n - 1).choose 2 : ℝ) + 1) / (n.choose 2 : ℝ))
        atTop (𝓝 1) := by
    have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have he : Tendsto (fun n : ℕ => (2 : ℝ) / n / (n - 1 : ℕ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_one_div, mul_zero] using
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).mul
          (hi.comp (tendsto_sub_atTop_nat 1))
    have h : Tendsto (fun n : ℕ => 1 - (2 : ℝ) / n + 2 / n / (n - 1 : ℕ))
        atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))).add he
    apply h.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 3) hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn10 : (n : ℝ) - 1 ≠ 0 := by linarith
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hn1, Nat.cast_one]
    field_simp [hn0, hn10]
    ring

  have tendsto_upper_endpoint :
      Tendsto (fun n : ℕ => ((n.choose 2 : ℝ) + 1) / (n.choose 2 : ℝ))
        atTop (𝓝 1) := by
    have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have he : Tendsto (fun n : ℕ => (2 : ℝ) / n / (n - 1 : ℕ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_one_div, mul_zero] using
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).mul
          (hi.comp (tendsto_sub_atTop_nat 1))
    have h : Tendsto (fun n : ℕ => 1 + (2 : ℝ) / n / (n - 1 : ℕ))
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add he
    apply h.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 3) hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn10 : (n : ℝ) - 1 ≠ 0 := by linarith
    rw [Nat.cast_choose_two, Nat.cast_sub hn1, Nat.cast_one]
    field_simp [hn0, hn10]





  refine ⟨fun H hu => not_duf_iff_fourDistinctCollision H hu, ?_, bounds, ?_⟩
  · intro n
    refine ⟨M3_attained n, card_le_M3 n, eqF n, ?_, ?_⟩
    · rw [eqF]; exact least n
    · intro m
      rw [forcing_iff, eqF]
      exact Nat.lt_iff_add_one_le
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_lower_endpoint tendsto_upper_endpoint
    · filter_upwards [eventually_ge_atTop 3] with n hn
      have h := (bounds n hn).1
      have hr : (((n-1).choose 2 : ℝ) + 1) ≤ (F3 n : ℝ) := by exact_mod_cast h
      exact div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 3] with n hn
      have h := (bounds n hn).2
      have hr : (F3 n : ℝ) ≤ (n.choose 2 : ℝ) + 1 := by exact_mod_cast h
      exact div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)

end D5.S3.Combinatorics.Graph.DUFTripleConclusion
