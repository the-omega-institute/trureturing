/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: The minimum double five-set cover on eight points has fourteen triples. -/

module

public import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SingletonFiveMask
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FanoDeletion
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SevenVertexBipartite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin

/-! The sharp eight-point double-cover bound forces a singly covered five-mask
among at most twenty triple types on nine axes. -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SingletonFiveMask

open Finset
open Q9FanoDeletion (q9Star q9Through q9_trace_sdiff_pair q9_trace_sdiff_triple
  q9_through_triple_card q9_degree_ge_seven_of_fano_deletion)
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

private theorem q9_sum_degrees {F : Finset (Finset α)} {S : Finset α}
    (hF : F ⊆ S.powersetCard 3) :
    (∑ x ∈ S, (q9Star F x).card) = F.card * 3 := by
  calc
    _ = ∑ t ∈ F, (S.filter (· ∈ t)).card := by
      simpa only [q9Star, bipartiteAbove, bipartiteBelow] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := S) (t := F) fun (x : α) (t : Finset α) => x ∈ t)
    _ = ∑ _t ∈ F, 3 := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨htS, htc⟩ := mem_powersetCard.mp (hF ht)
      have he : S.filter (· ∈ t) = t := by
        ext x
        exact ⟨fun hx => (mem_filter.mp hx).2, fun hx => mem_filter.mpr ⟨htS hx, hx⟩⟩
      rw [he, htc]
    _ = _ := by simp

private theorem q9_sum_indicator {β : Type*} (s : Finset β) (p : β → Prop)
    [DecidablePred p] (n : ℕ) :
    (∑ x ∈ s, if p x then n else 0) = (s.filter p).card * n := by
  rw [← sum_filter]
  simp

private theorem q9_high_pair_degree_sum {F : Finset (Finset α)} {S : Finset α} (z : α)
    (hF : F ⊆ S.powersetCard 3) (hFc : F.card = 13) (hz : (q9Star F z).card = 4) :
    (∑ p ∈ (S.erase z).powersetCard 2, (q9Through F p).card) = 31 := by
  let P := (S.erase z).powersetCard 2
  let r := fun (p t : Finset α) => p ⊆ t
  have hfiber (t : Finset α) (ht : t ∈ F) :
      (P.bipartiteBelow r t).card = if z ∈ t then 1 else 3 := by
    obtain ⟨htS, htc⟩ := mem_powersetCard.mp (hF ht)
    have he : P.bipartiteBelow r t = (t.erase z).powersetCard 2 := by
      ext p
      simp only [P, mem_bipartiteBelow, r, mem_powersetCard, subset_erase]
      exact ⟨fun h => ⟨⟨h.2, h.1.1.2⟩, h.1.2⟩,
        fun h => ⟨⟨⟨h.1.1.trans htS, h.1.2⟩, h.2⟩, h.1.1⟩⟩
    rw [he, card_powersetCard]
    by_cases hzt : z ∈ t
    · rw [ite_eq_left hzt, card_erase_of_mem hzt, htc]
      decide
    · rw [ite_eq_right hzt, erase_eq_of_notMem hzt, htc]
      decide
  have hrest := card_filter_add_card_filter_not (s := F) (z ∈ ·)
  change (q9Star F z).card + _ = F.card at hrest
  have hre : (F.filter (z ∉ ·)).card = 9 := by omega
  calc
    _ = ∑ t ∈ F, (P.bipartiteBelow r t).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := P) (t := F) r
    _ = ∑ t ∈ F, ((if z ∈ t then 1 else 0) + (if z ∉ t then 3 else 0)) := by
      apply sum_congr rfl
      intro t ht
      rw [hfiber t ht]
      by_cases hzt : z ∈ t <;> simp [hzt]
    _ = 31 := by
      rw [sum_add_distrib, q9_sum_indicator, q9_sum_indicator, hz, hre]

private theorem q9_pair_subset {A : Finset α} {a b : α} (ha : a ∈ A) (hb : b ∈ A) :
    ({a, b} : Finset α) ⊆ A :=
  insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩

private theorem q9_mk_high_graph {F : Finset (Finset α)} {S H : Finset α}
    (hS : S.card = 8) (hF : F ⊆ S.powersetCard 3) (hFc : F.card = 13)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (trace F U).card)
    (hHS : H ⊆ S) (hH : H.card = 7) (hd : ∀ x ∈ H, (q9Star F x).card = 5)
    (hsum : (∑ p ∈ H.powersetCard 2, (q9Through F p).card) = 31) :
    ∃ A B : Finset α, A.card = 4 ∧ B.card = 3 ∧ Disjoint A B ∧ A ∪ B = H ∧
      ∀ p ∈ H.powersetCard 2, (if p ⊆ A ∨ p ⊆ B then 2 else 1) ≤ (q9Through F p).card := by
  classical
  let P := H.powersetCard 2
  let c := fun p : Finset α => (q9Through F p).card
  have hP : P.card = 21 := by
    rw [show P = H.powersetCard 2 from rfl, card_powersetCard, hH]
    decide
  have hpos (p : Finset α) (hp : p ∈ P) : 1 ≤ c p := by
    obtain ⟨hpH, hpc⟩ := mem_powersetCard.mp hp
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hpc
    have ha : a ∈ H := hpH (by simp)
    have hb : b ∈ H := hpH (by simp)
    have hU : (S \ ({a, b} : Finset α)).card = 6 := by
      rw [card_sdiff_of_subset (hpH.trans hHS), hS, card_pair hab]
    have hlocal := double_cover_bound (trace_uniform (U := S \ {a, b}) hF)
      (double_cover_trace hcover sdiff_subset)
    rw [hU] at hlocal
    change 12 ≤ (trace F (S \ {a, b})).card * 3 at hlocal
    have hi := q9_trace_sdiff_pair hF a b
    rw [hd a ha, hd b hb, hFc] at hi
    change 1 ≤ (q9Through F {a, b}).card
    omega
  let good := P.filter (fun p => c p = 1)
  have hgood : 11 ≤ good.card := by
    have hpoint (p : Finset α) (hp : p ∈ P) : 1 + (if c p ≠ 1 then 1 else 0) ≤ c p := by
      have hc := hpos p hp
      by_cases he : c p = 1
      · simp [he]
      · simp [he]
        omega
    have hlo := sum_le_sum hpoint
    change (∑ p ∈ P, c p) = 31 at hsum
    rw [sum_add_distrib, q9_sum_indicator, hsum] at hlo
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, hP] at hlo
    have hpartition := card_filter_add_card_filter_not (s := P) (fun p => c p = 1)
    change good.card + _ = P.card at hpartition
    rw [hP] at hpartition
    change good.card + (P.filter (fun p => c p ≠ 1)).card = 21 at hpartition
    omega
  let W := {x // x ∈ H}
  let val : W ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  let G : SimpleGraph W :=
    { Adj := fun a b => a ≠ b ∧ c {a.val, b.val} = 1
      symm := ⟨by
        intro a b h
        exact ⟨h.1.symm, by simpa only [pair_comm b.val a.val] using h.2⟩⟩
      loopless := ⟨by
        intro a h
        exact h.1 rfl⟩ }
  let _ : DecidableRel G.Adj := fun a b =>
    inferInstanceAs (Decidable (a ≠ b ∧ c {a.val, b.val} = 1))
  have hW : Fintype.card W = 7 := (Fintype.card_coe H).trans hH
  have hGlarge : 11 ≤ G.edgeFinset.card := by
    let toPair := fun e : Sym2 W => e.toFinset.map val
    have hsub : good ⊆ G.edgeFinset.image toPair := by
      intro p hp
      obtain ⟨hpP, hcp⟩ := mem_filter.mp hp
      obtain ⟨hpH, hpc⟩ := mem_powersetCard.mp hpP
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hpc
      let x : W := ⟨a, hpH (by simp)⟩
      let y : W := ⟨b, hpH (by simp)⟩
      have hxy : x ≠ y := fun h => hab (congrArg Subtype.val h)
      refine mem_image.mpr ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr
        (by simpa only [SimpleGraph.mem_edgeSet] using (show G.Adj x y from ⟨hxy, hcp⟩)), ?_⟩
      simp [toPair, Sym2.toFinset_mk_eq, val, x, y]
    exact hgood.trans ((card_le_card hsub).trans card_image_le)
  have htriangle (x y w : W) (hxy : G.Adj x y) (hyw : G.Adj y w) (hwx : G.Adj w x) :
      False := by
    have hxy' : x.val ≠ y.val := fun h => hxy.1 (Subtype.ext h)
    have hyw' : y.val ≠ w.val := fun h => hyw.1 (Subtype.ext h)
    have hxw' : x.val ≠ w.val := fun h => hwx.1 (Subtype.ext h.symm)
    let t : Finset α := {x.val, y.val, w.val}
    have ht : t ⊆ S := insert_subset_iff.mpr
      ⟨hHS x.property, q9_pair_subset (hHS y.property) (hHS w.property)⟩
    have htc : t.card = 3 := by
      change (insert x.val ({y.val, w.val} : Finset α)).card = 3
      rw [card_insert_of_notMem (by simp [hxy', hxw']), card_pair hyw']
    have hU : S \ t ∈ S.powersetCard 5 := by
      refine mem_powersetCard.mpr ⟨sdiff_subset, ?_⟩
      rw [card_sdiff_of_subset ht, hS, htc]
    have hcov := hcover (S \ t) hU
    have hi := q9_trace_sdiff_triple hF x.val y.val w.val
    have hxyc : (q9Through F {x.val, y.val}).card = 1 := hxy.2
    have hywc : (q9Through F {y.val, w.val}).card = 1 := hyw.2
    have hxwc : (q9Through F {x.val, w.val}).card = 1 := by
      rw [pair_comm]
      exact hwx.2
    rw [hd _ x.property, hd _ y.property, hd _ w.property, hFc, hxyc, hxwc, hywc] at hi
    change (trace F (S \ t)).card + 5 + 5 + 5 + _ = _ at hi
    omega
  obtain ⟨A₀, hA₀, hB₀, hAB₀⟩ :=
    Q9SevenVertexBipartite.seven_vertex_bipartition G hW htriangle hGlarge
  let B₀ := A₀ᶜ
  let A := A₀.map val
  let B := B₀.map val
  have hAB : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro a ha hb
    obtain ⟨x, hx, hxa⟩ := mem_map.mp ha
    obtain ⟨y, hy, hya⟩ := mem_map.mp hb
    have hxy := val.injective (hxa.trans hya.symm)
    exact (mem_compl.mp hy) (hxy ▸ hx)
  have hpart : A ∪ B = H := by
    ext a
    constructor
    · intro ha
      rcases mem_union.mp ha with ha | ha
      · obtain ⟨x, _, rfl⟩ := mem_map.mp ha
        exact x.property
      · obtain ⟨x, _, rfl⟩ := mem_map.mp ha
        exact x.property
    · intro ha
      let x : W := ⟨a, ha⟩
      by_cases hx : x ∈ A₀
      · exact mem_union.mpr (Or.inl (mem_map.mpr ⟨x, hx, rfl⟩))
      · exact mem_union.mpr (Or.inr (mem_map.mpr ⟨x, mem_compl.mpr hx, rfl⟩))
  have hno (C : Finset W)
      (hind : ∀ x ∈ C, ∀ y ∈ C, ¬G.Adj x y) (p : Finset α) (hp : p ∈ P)
      (hpC : p ⊆ C.map val) : c p ≠ 1 := by
    obtain ⟨_, hpc⟩ := mem_powersetCard.mp hp
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hpc
    obtain ⟨x, hx, hxa⟩ := mem_map.mp (hpC (by simp : a ∈ ({a, b} : Finset α)))
    obtain ⟨y, hy, hyb⟩ := mem_map.mp (hpC (by simp : b ∈ ({a, b} : Finset α)))
    have hxy : x ≠ y := fun he => hab (hxa.symm.trans ((congrArg val he).trans hyb))
    intro he
    apply hind x hx y hy
    change x ≠ y ∧ c {val x, val y} = 1
    exact ⟨hxy, by rwa [hxa, hyb]⟩
  have hAind (x : W) (hx : x ∈ A₀) (y : W) (hy : y ∈ A₀) : ¬G.Adj x y := by
    intro he
    rcases hAB₀.mem_of_adj he with h | h
    · exact (mem_compl.mp (show y ∈ B₀ from h.2)) hy
    · exact (mem_compl.mp (show x ∈ B₀ from h.1)) hx
  have hBind (x : W) (hx : x ∈ B₀) (y : W) (hy : y ∈ B₀) : ¬G.Adj x y := by
    intro he
    rcases hAB₀.mem_of_adj he with h | h
    · exact (mem_compl.mp hx) h.1
    · exact (mem_compl.mp hy) h.2
  refine ⟨A, B, (card_map _).trans hA₀, (card_map _).trans hB₀, hAB, hpart, ?_⟩
  intro p hp
  have hbase := hpos p hp
  by_cases hin : p ⊆ A ∨ p ⊆ B
  · rw [ite_eq_left hin]
    have hn := hin.elim (hno A₀ hAind p hp) (hno B₀ hBind p hp)
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hbase (Ne.symm hn))
  · simpa only [ite_eq_right hin] using hbase

/-- Nine internal pairs spend nine of the ten excess pair incidences.
The single remaining excess cannot account for all twelve cross pairs. -/
private theorem q9_cross_pair_obstruction
    {F : Finset (Finset α)} {S A B : Finset α} {z : α}
    (hS : S.card = 8) (hF : F ⊆ S.powersetCard 3) (hFc : F.card = 13)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (trace F U).card)
    (hAc : A.card = 4) (hBc : B.card = 3) (hAB : Disjoint A B)
    (hpart : A ∪ B = S.erase z) (hz : (q9Star F z).card = 4)
    (hdeg : ∀ x ∈ S.erase z, (q9Star F x).card = 5)
    (hbase : ∀ p ∈ (S.erase z).powersetCard 2,
      (if p ⊆ A ∨ p ⊆ B then 2 else 1) ≤ (q9Through F p).card) : False := by
  classical
  let H := S.erase z
  let P := H.powersetCard 2
  let K := q9Star F z
  let internal := fun p : Finset α => p ⊆ A ∨ p ⊆ B
  let c := fun p : Finset α => (q9Through F p).card
  let w := fun p : Finset α => if internal p then 2 else 1
  let E := P.filter (fun p => w p < c p)
  let pair := fun ab : α × α => ({ab.1, ab.2} : Finset α)
  let X := (A ×ˢ B).image pair
  let M := (trace F H).filter (fun t => ¬internal t)
  have hAH : A ⊆ H := by
    change A ⊆ S.erase z
    rw [← hpart]
    exact subset_union_left
  have hBH : B ⊆ H := by
    change B ⊆ S.erase z
    rw [← hpart]
    exact subset_union_right
  have hHc : H.card = 7 := by
    rw [show H = S.erase z from rfl, ← hpart, card_union_of_disjoint hAB, hAc, hBc]
  have hP : P.card = 21 := by
    rw [show P = H.powersetCard 2 from rfl, card_powersetCard, hHc]
    decide
  have hne {a b : α} (ha : a ∈ A) (hb : b ∈ B) : a ≠ b :=
    fun h => disjoint_left.mp hAB ha (h.symm ▸ hb)
  have hcross {a b : α} (ha : a ∈ A) (hb : b ∈ B) : ¬internal {a, b} := by
    intro hi
    rcases hi with hi | hi
    · exact disjoint_left.mp hAB (hi (by simp : b ∈ ({a, b} : Finset α))) hb
    · exact disjoint_left.mp hAB ha (hi (by simp : a ∈ ({a, b} : Finset α)))
  have hX : X.card = 12 := by
    have hi : Set.InjOn pair (↑(A ×ˢ B) : Set (α × α)) := by
      intro u hu v hv he
      obtain ⟨huA, huB⟩ := mem_product.mp (show u ∈ A ×ˢ B from hu)
      obtain ⟨hvA, hvB⟩ := mem_product.mp (show v ∈ A ×ˢ B from hv)
      change ({u.1, u.2} : Finset α) = {v.1, v.2} at he
      have h₁ : u.1 ∈ ({v.1, v.2} : Finset α) := by rw [← he]; simp
      have h₂ : u.2 ∈ ({v.1, v.2} : Finset α) := by rw [← he]; simp
      simp only [mem_insert, mem_singleton] at h₁ h₂
      exact Prod.ext (h₁.resolve_right (hne huA hvB)) (h₂.resolve_left (hne hvA huB).symm)
    change ((A ×ˢ B).image pair).card = 12
    rw [card_image_of_injOn hi, card_product, hAc, hBc]
  have hI : (P.filter internal).card = 9 := by
    have he : P.filter internal = A.powersetCard 2 ∪ B.powersetCard 2 := by
      ext p
      simp only [P, internal, mem_filter, mem_union, mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hpc⟩, hpA | hpB⟩
        · exact Or.inl ⟨hpA, hpc⟩
        · exact Or.inr ⟨hpB, hpc⟩
      · rintro (⟨hpA, hpc⟩ | ⟨hpB, hpc⟩)
        · exact ⟨⟨hpA.trans hAH, hpc⟩, Or.inl hpA⟩
        · exact ⟨⟨hpB.trans hBH, hpc⟩, Or.inr hpB⟩
    have hd : Disjoint (A.powersetCard 2) (B.powersetCard 2) := by
      refine disjoint_left.mpr ?_
      intro p hpA hpB
      obtain ⟨hpA, hpc⟩ := mem_powersetCard.mp hpA
      have hpB := (mem_powersetCard.mp hpB).1
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < p.card)
      exact disjoint_left.mp hAB (hpA hx) (hpB hx)
    rw [he, card_union_of_disjoint hd, card_powersetCard, card_powersetCard, hAc, hBc]
    decide
  have hwsum : (∑ p ∈ P, w p) = 30 := by
    calc
      _ = ∑ p ∈ P, (1 + (if internal p then 1 else 0)) := by
        apply sum_congr rfl
        intro p _
        by_cases hi : internal p <;> simp [w, hi]
      _ = _ := by
        rw [sum_add_distrib, q9_sum_indicator, hI]
        simp [hP]
  have hE : E.card ≤ 1 := by
    have hpoint (p : Finset α) (hp : p ∈ P) :
        w p + (if w p < c p then 1 else 0) ≤ c p := by
      have hle : w p ≤ c p := hbase p hp
      split <;> omega
    have hlow := sum_le_sum hpoint
    have hsum : (∑ p ∈ P, c p) = 31 := q9_high_pair_degree_sum z hF hFc hz
    rw [sum_add_distrib, hwsum, q9_sum_indicator, hsum] at hlow
    change 30 + E.card * 1 ≤ 31 at hlow
    omega
  have hexception (t : Finset α) (ht : t ∈ M) : ∃ p ∈ E, p ⊆ t := by
    obtain ⟨htH, hmix⟩ := mem_filter.mp ht
    obtain ⟨htF, htH⟩ := mem_filter.mp htH
    have htc := (mem_powersetCard.mp (hF htF)).2
    have hside {x : α} (hx : x ∈ t) : x ∈ A ∨ x ∈ B := by
      apply mem_union.mp
      rw [hpart]
      exact htH hx
    have hnotB : ¬t ⊆ B := fun h => hmix (Or.inr h)
    have hnotA : ¬t ⊆ A := fun h => hmix (Or.inl h)
    obtain ⟨a, hat, haB⟩ := not_subset.mp hnotB
    obtain ⟨b, hbt, hbA⟩ := not_subset.mp hnotA
    have ha := (hside hat).resolve_right haB
    have hb := (hside hbt).resolve_left hbA
    have hrest : (t \ {a, b}).card = 1 := by
      rw [card_sdiff_of_subset (q9_pair_subset hat hbt), htc, card_pair (hne ha hb)]
    obtain ⟨d, hdt⟩ := card_pos.mp (by omega : 0 < (t \ {a, b}).card)
    obtain ⟨hdt, hdab⟩ := mem_sdiff.mp hdt
    have hda : d ≠ a := fun he => hdab (by simp [he])
    have hdb : d ≠ b := fun he => hdab (by simp [he])
    have hant : a ∉ ({d, b} : Finset α) := by simp [hda.symm, hne ha hb]
    have hbnt : b ∉ ({d, a} : Finset α) := by simp [hdb.symm, (hne ha hb).symm]
    have horiented {x y u : α}
        (he : t = {x, y, u}) (hxy' : x ≠ y) (hxup : x ≠ u) (hyup : y ≠ u)
        (hxy : internal {x, y})
        (hxu : ¬internal {x, u}) (hyu : ¬internal {y, u}) :
        ∃ p ∈ E, p ⊆ t := by
      have hpF (p : Finset α) (hp : p ⊆ t) : p ⊆ H := hp.trans htH
      have hxt : x ∈ t := by simp [he]
      have hyt : y ∈ t := by simp [he]
      have hut : u ∈ t := by simp [he]
      have hxyP : ({x, y} : Finset α) ∈ P :=
        mem_powersetCard.mpr ⟨hpF _ (q9_pair_subset hxt hyt), card_pair hxy'⟩
      have hxuP : ({x, u} : Finset α) ∈ P :=
        mem_powersetCard.mpr ⟨hpF _ (q9_pair_subset hxt hut), card_pair hxup⟩
      have hyuP : ({y, u} : Finset α) ∈ P :=
        mem_powersetCard.mpr ⟨hpF _ (q9_pair_subset hyt hut), card_pair hyup⟩
      have hhigh (v : α) (hv : v ∈ t) : (q9Star F v).card = 5 := by
        exact hdeg v (htH hv)
      have hU : S \ t ∈ S.powersetCard 5 := by
        refine mem_powersetCard.mpr ⟨sdiff_subset, ?_⟩
        rw [card_sdiff_of_subset (mem_powersetCard.mp (hF htF)).1, hS, htc]
      have hcov := hcover (S \ t) hU
      have hi := q9_trace_sdiff_triple hF x y u
      have hone := q9_through_triple_card hF htF
      rw [he] at hone
      rw [hhigh x hxt, hhigh y hyt, hhigh u hut, hFc, hone] at hi
      rw [he] at hcov
      have hsum : 5 ≤ c {x, y} + c {x, u} + c {y, u} := by
        change _ + 5 + 5 + 5 + 1 = 13 + c {x, y} + c {x, u} + c {y, u} at hi
        omega
      by_cases h₁ : {x, y} ∈ E
      · exact ⟨_, h₁, q9_pair_subset hxt hyt⟩
      by_cases h₂ : {x, u} ∈ E
      · exact ⟨_, h₂, q9_pair_subset hxt hut⟩
      by_cases h₃ : {y, u} ∈ E
      · exact ⟨_, h₃, q9_pair_subset hyt hut⟩
      have hn₁ : ¬w {x, y} < c {x, y} := fun h => h₁ (mem_filter.mpr ⟨hxyP, h⟩)
      have hn₂ : ¬w {x, u} < c {x, u} := fun h => h₂ (mem_filter.mpr ⟨hxuP, h⟩)
      have hn₃ : ¬w {y, u} < c {y, u} := fun h => h₃ (mem_filter.mpr ⟨hyuP, h⟩)
      simp only [w, ite_eq_left hxy, ite_eq_right hxu, ite_eq_right hyu] at hn₁ hn₂ hn₃
      omega
    rcases hside hdt with hd | hd
    · have ht' : t = {a, d, b} := by
        apply (eq_of_subset_of_card_le
          (insert_subset_iff.mpr ⟨hat, q9_pair_subset hdt hbt⟩) ?_).symm
        rw [htc, card_insert_of_notMem hant, card_pair (hne hd hb)]
      exact horiented ht' hda.symm (hne ha hb) hdb
        (Or.inl (q9_pair_subset ha hd)) (hcross ha hb) (hcross hd hb)
    · have ht' : t = {b, d, a} := by
        apply (eq_of_subset_of_card_le
          (insert_subset_iff.mpr ⟨hbt, q9_pair_subset hdt hat⟩) ?_).symm
        rw [htc, card_insert_of_notMem hbnt, card_pair (hne ha hd).symm]
      exact horiented ht' hdb.symm (hne ha hb).symm hda (Or.inr (q9_pair_subset hb hd))
        (by rw [pair_comm]; exact hcross ha hb) (by rw [pair_comm]; exact hcross ha hd)
  have hM : M.card ≤ 3 := by
    by_cases hnon : M.Nonempty
    · obtain ⟨t, ht⟩ := hnon
      obtain ⟨p, hp, _⟩ := hexception t ht
      have hsub : M ⊆ q9Through F p := by
        intro u hu
        obtain ⟨q, hq, hqu⟩ := hexception u hu
        have he := card_le_one.mp hE q hq p hp
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hu).1).1, he ▸ hqu⟩
      have hpP := (mem_filter.mp hp).1
      have hupper : c p ≤ w p + 1 := by
        have hlow := sum_le_sum (s := P.erase p) (f := w) (g := c)
          (fun q hq => hbase q (mem_erase.mp hq).2)
        have hw := sum_erase_add P w hpP
        have hc := sum_erase_add P c hpP
        have hsum : (∑ q ∈ P, c q) = 31 := q9_high_pair_degree_sum z hF hFc hz
        rw [hwsum] at hw
        rw [hsum] at hc
        omega
      have hwcap : w p ≤ 2 := by
        by_cases hi : internal p <;> simp [w, hi]
      exact (card_le_card hsub).trans (by change c p ≤ 3; omega)
    · rw [not_nonempty_iff_eq_empty.mp hnon, card_empty]
      decide
  let crossPairs := fun t : Finset α => X.filter (· ⊆ t)
  have hcapM (t : Finset α) (ht : t ∈ M) : (crossPairs t).card ≤ 2 := by
    let C := A ∩ t
    let D := B ∩ t
    have hsub : crossPairs t ⊆ (C ×ˢ D).image pair := by
      intro p hp
      obtain ⟨hpX, hpt⟩ := mem_filter.mp hp
      obtain ⟨ab, hab, rfl⟩ := mem_image.mp hpX
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      exact mem_image.mpr ⟨ab, mem_product.mpr
        ⟨mem_inter.mpr ⟨ha, hpt (by simp [pair])⟩,
          mem_inter.mpr ⟨hb, hpt (by simp [pair])⟩⟩, rfl⟩
    have hd : Disjoint C D := by
      refine disjoint_left.mpr ?_
      intro x hx hy
      exact disjoint_left.mp hAB (mem_inter.mp hx).1 (mem_inter.mp hy).1
    have hsum : C.card + D.card ≤ 3 := by
      have htc := (mem_powersetCard.mp (hF (mem_filter.mp (mem_filter.mp ht).1).1)).2
      rw [← card_union_of_disjoint hd, ← htc]
      exact card_le_card (union_subset inter_subset_right inter_subset_right)
    have hle := (card_le_card hsub).trans (card_image_le (s := C ×ˢ D) (f := pair))
    rw [card_product] at hle
    rcases (show C.card = 0 ∨ C.card = 1 ∨ C.card = 2 ∨ C.card = 3 by omega) with
      hc | hc | hc | hc <;> rw [hc] at hsum hle <;> omega
  have hcapK (t : Finset α) (ht : t ∈ K) : (crossPairs t).card ≤ 1 := by
    obtain ⟨htF, hzt⟩ := mem_filter.mp ht
    have hsub : crossPairs t ⊆ (t.erase z).powersetCard 2 := by
      intro p hp
      obtain ⟨hpX, hpt⟩ := mem_filter.mp hp
      obtain ⟨ab, hab, rfl⟩ := mem_image.mp hpX
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      have hpH : pair ab ⊆ H := q9_pair_subset (hAH ha) (hBH hb)
      exact mem_powersetCard.mpr
        ⟨subset_erase.mpr ⟨hpt, (subset_erase.mp hpH).2⟩, card_pair (hne ha hb)⟩
    have hl := card_le_card hsub
    rw [card_powersetCard, card_erase_of_mem hzt, (mem_powersetCard.mp (hF htF)).2] at hl
    exact hl
  have hcovered : X ⊆ M.biUnion crossPairs ∪ K.biUnion crossPairs := by
    intro p hp
    obtain ⟨ab, hab, rfl⟩ := mem_image.mp hp
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    have hpP : pair ab ∈ P :=
      mem_powersetCard.mpr ⟨q9_pair_subset (hAH ha) (hBH hb), card_pair (hne ha hb)⟩
    have hpos : 0 < c (pair ab) := by
      have hl := hbase _ hpP
      rw [ite_eq_right (hcross ha hb)] at hl
      exact hl
    obtain ⟨t, ht⟩ := card_pos.mp hpos
    obtain ⟨htF, hpt⟩ := mem_filter.mp ht
    have hmem : pair ab ∈ crossPairs t := mem_filter.mpr ⟨hp, hpt⟩
    by_cases hzt : z ∈ t
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨t, mem_filter.mpr ⟨htF, hzt⟩, hmem⟩))
    · have htH : t ⊆ H := subset_erase.mpr ⟨(mem_powersetCard.mp (hF htF)).1, hzt⟩
      have htM : t ∈ M := mem_filter.mpr
        ⟨mem_filter.mpr ⟨htF, htH⟩, fun hi =>
          hcross ha hb (hi.elim (fun h => Or.inl (hpt.trans h)) (fun h => Or.inr (hpt.trans h)))⟩
      exact mem_union.mpr (Or.inl (mem_biUnion.mpr ⟨t, htM, hmem⟩))
  have hMcover : (M.biUnion crossPairs).card ≤ M.card * 2 := by
    calc
      _ ≤ ∑ t ∈ M, (crossPairs t).card := card_biUnion_le
      _ ≤ ∑ _t ∈ M, 2 := sum_le_sum hcapM
      _ = _ := by simp
  have hKcover : (K.biUnion crossPairs).card ≤ K.card * 1 := by
    calc
      _ ≤ ∑ t ∈ K, (crossPairs t).card := card_biUnion_le
      _ ≤ ∑ _t ∈ K, 1 := sum_le_sum hcapK
      _ = _ := by simp
  have htotal := (card_le_card hcovered).trans (card_union_le _ _)
  rw [hX] at htotal
  change K.card = 4 at hz
  omega

/-- Double coverage of all five-sets on eight points requires fourteen triples. -/
theorem fourteen_le_card_of_double_five_cover {S : Finset α} {F : Finset (Finset α)}
    (hS : S.card = 8) (hF : F ⊆ S.powersetCard 3)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (F.filter (· ⊆ U)).card) :
    14 ≤ F.card := by
  by_contra hsmall
  have hFc : F.card = 13 := by
    have hl := thirteen_le_card_of_double_five_cover hS hF hcover
    omega
  let d := fun x : α => (q9Star F x).card
  have hd (x : α) (hx : x ∈ S) : d x ≤ 5 := by
    have herase : (S.erase x).card = 7 := by rw [card_erase_of_mem hx, hS]
    have hseven := double_cover_bound (trace_uniform (U := S.erase x) hF)
      (double_cover_trace hcover (erase_subset x S))
    rw [herase] at hseven
    change 42 ≤ (trace F (S.erase x)).card * 6 at hseven
    have htotal := erase_trace_add_degree
      (fun t ht => (mem_powersetCard.mp (hF ht)).1) x
    change (trace F (S.erase x)).card + d x = F.card at htotal
    by_contra hgt
    have htight : (trace F (S.erase x)).card = 7 := by omega
    have hlink : 7 ≤ d x := q9_degree_ge_seven_of_fano_deletion hS hF hx hcover htight
    omega
  have hsum : (∑ x ∈ S, d x) = 39 := by rw [q9_sum_degrees hF, hFc]
  have hzexists : ∃ z ∈ S, d z < 5 := by
    by_contra hn
    have hmin (x : α) (hx : x ∈ S) : 5 ≤ d x :=
      le_of_not_gt (fun h => hn ⟨x, hx, h⟩)
    have hlo := sum_le_sum hmin
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, hS, hsum] at hlo
    omega
  obtain ⟨z, hzS, hzlow⟩ := hzexists
  let H := S.erase z
  have hH : H.card = 7 := by rw [show H = S.erase z from rfl, card_erase_of_mem hzS, hS]
  have hHS : H ⊆ S := erase_subset z S
  have hsplit : (∑ x ∈ H, d x) + d z = 39 := (sum_erase_add S d hzS).trans hsum
  have hcap : (∑ x ∈ H, d x) ≤ 35 := by
    calc
      _ ≤ ∑ _x ∈ H, 5 := sum_le_sum fun x hx => hd x (hHS hx)
      _ = _ := by simp [hH]
  have hz : d z = 4 := by omega
  have hhigh (x : α) (hx : x ∈ H) : d x = 5 := by
    by_contra hn
    have hlt : (∑ y ∈ H, d y) < ∑ _y ∈ H, 5 := sum_lt_sum
      (fun y hy => hd y (hHS hy)) ⟨x, hx, by have := hd x (hHS hx); omega⟩
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, hH] at hlt
    omega
  have hpairSum := q9_high_pair_degree_sum z hF hFc hz
  obtain ⟨A, B, hA, hB, hdis, hpart, hbase⟩ :=
    q9_mk_high_graph hS hF hFc hcover hHS hH hhigh hpairSum
  exact q9_cross_pair_obstruction hS hF hFc hcover hA hB hdis hpart hz hhigh hbase

/-- A covering family of at most twenty triples on nine axes has a five-set
containing exactly one triple. -/
theorem exists_singleton_five_mask_of_card_le_twenty (F : Finset (Finset (Fin 9)))
    (hF : ∀ t ∈ F, t.card = 3) (hFc : F.card ≤ 20)
    (hcover : ∀ U : Finset (Fin 9), U.card = 5 → 1 ≤ (F.filter (· ⊆ U)).card) :
    ∃ U : Finset (Fin 9), U.card = 5 ∧ (F.filter (· ⊆ U)).card = 1 := by
  let S : Finset (Fin 9) := univ
  have hS : S.card = 9 := by simp [S]
  have hFS : F ⊆ S.powersetCard 3 := by
    intro t ht
    exact mem_powersetCard.mpr ⟨subset_univ _, hF t ht⟩
  by_contra hnone
  have hdouble (U : Finset (Fin 9)) (hU : U ∈ S.powersetCard 5) :
      2 ≤ (trace F U).card := by
    have hUc := (mem_powersetCard.mp hU).2
    have hlo := hcover U hUc
    have hne : (trace F U).card ≠ 1 := fun he => hnone ⟨U, hUc, he⟩
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hlo hne.symm)
  have hlarge (V : Finset (Fin 9)) (hV : V ∈ S.powersetCard 8) :
      14 ≤ (trace F V).card := by
    obtain ⟨hVS, hVc⟩ := mem_powersetCard.mp hV
    exact fourteen_le_card_of_double_five_cover hVc (trace_uniform hFS)
      (double_cover_trace hdouble hVS)
  have hlower := sum_le_sum hlarge
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, card_powersetCard, hS] at hlower
  have hsum := trace_card_sum hFS (k := 8) (by decide)
  rw [hS] at hsum
  change (∑ U ∈ S.powersetCard 8, (trace F U).card) = F.card * 6 at hsum
  rw [hsum] at hlower
  change 126 ≤ F.card * 6 at hlower
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The explicit witness checks all 56 five-sets by kernel reduction.
/-- The seven cyclic Fano lines and the seven triples obtained by adjoining
axis seven to the edges of the seven-cycle attain the eight-axis bound. -/
theorem exists_fourteen_triple_double_five_cover :
    ∃ F : Finset (Finset (Fin 8)), F.card = 14 ∧ F ⊆ (univ : Finset (Fin 8)).powersetCard 3 ∧
      ∀ U ∈ (univ : Finset (Fin 8)).powersetCard 5, 2 ≤ (F.filter (· ⊆ U)).card := by
  refine ⟨{{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2},
    {7, 0, 1}, {7, 1, 2}, {7, 2, 3}, {7, 3, 4}, {7, 4, 5}, {7, 5, 6}, {7, 6, 0}}, ?_, ?_, ?_⟩
  all_goals decide

#print axioms fourteen_le_card_of_double_five_cover
#print axioms exists_singleton_five_mask_of_card_le_twenty
#print axioms exists_fourteen_triple_double_five_cover

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SingletonFiveMask
