/- GID: D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset]
   utility: none
   digest: Double-star grafting with actual induced sets and partial colorings. -/

import D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

/-- Slots are h,u,v,a,b,c,d. Only h belongs to the original graph. -/
def localAdj (x y : Fin 7) : Prop :=
  (x = 0 ∧ y = 3) ∨ (x = 3 ∧ y = 0) ∨
  (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
  (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨
  (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) ∨
  (x = 2 ∧ y = 5) ∨ (x = 5 ∧ y = 2) ∨
  (x = 2 ∧ y = 6) ∨ (x = 6 ∧ y = 2)

/-- Preserve every base edge and attach one double star at each base vertex. -/
def graftGraph {V : Type*} (F : SimpleGraph V) : SimpleGraph (V × Fin 7) where
  Adj p q := (p.2 = 0 ∧ q.2 = 0 ∧ F.Adj p.1 q.1) ∨
    (p.1 = q.1 ∧ localAdj p.2 q.2)
  symm := ⟨by
    intro p q h
    rcases h with h | ⟨h, e⟩
    · exact Or.inl ⟨h.2.1, h.1, F.adj_symm h.2.2⟩
    · refine Or.inr ⟨h.symm, ?_⟩
      rcases e with (⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩ |
        ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩ |
        ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩)
      all_goals simp [e1,e2,localAdj]⟩
  loopless := ⟨by
    intro p h
    rcases h with h | h
    · exact F.loopless.irrefl p.1 h.2.2
    · have e := h.2
      obtain ⟨i,t⟩ := p
      fin_cases t <;> simp [localAdj] at e⟩

noncomputable instance {V : Type*} [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj] :
    DecidableRel (graftGraph F).Adj := fun p q =>
  inferInstanceAs (Decidable ((p.2 = 0 ∧ q.2 = 0 ∧ F.Adj p.1 q.1) ∨
    (p.1 = q.1 ∧ localAdj p.2 q.2)))

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem independent_iff {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (S : Finset W) :
    IsKIndependent G 2 S ↔ ∀ v ∈ S, ∀ a ∈ S, ∀ b ∈ S,
      G.Adj v a → G.Adj v b → a = b := by
  simp only [IsKIndependent, Nat.lt_succ_iff, Finset.card_le_one]
  constructor
  · intro h v hv a ha b hb hva hvb
    exact h v hv a (Finset.mem_filter.mpr ⟨ha,hva⟩) b (Finset.mem_filter.mpr ⟨hb,hvb⟩)
  · intro h v hv a ha b hb
    exact h v hv a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

private theorem gadget_bound (S : Finset (Fin 7)) (hzero : 0 ∉ S)
    (h : ∀ v ∈ S, ∀ a ∈ S, ∀ b ∈ S, localAdj v a → localAdj v b → a = b) :
    S.card ≤ 4 := by
  have forbid (v a b : Fin 7) (hv : v ∈ S) (ha : a ∈ S) (hb : b ∈ S)
      (hva : localAdj v a) (hvb : localAdj v b) (hne : a ≠ b) : False :=
    hne (h v hv a ha b hb hva hvb)
  by_cases hu : 1 ∈ S
  · by_cases hv : 2 ∈ S
    · have h3 : 3 ∉ S := fun h3 => forbid 1 2 3 hu hv h3 (by simp [localAdj]) (by simp [localAdj]) (by decide)
      have h4 : 4 ∉ S := fun h4 => forbid 1 2 4 hu hv h4 (by simp [localAdj]) (by simp [localAdj]) (by decide)
      have h5 : 5 ∉ S := fun h5 => forbid 2 1 5 hv hu h5 (by simp [localAdj]) (by simp [localAdj]) (by decide)
      have h6 : 6 ∉ S := fun h6 => forbid 2 1 6 hv hu h6 (by simp [localAdj]) (by simp [localAdj]) (by decide)
      have hs : S ⊆ {1,2} := by intro t ht; fin_cases t <;> simp_all
      exact (Finset.card_le_card hs).trans (by decide)
    · by_cases ha : 3 ∈ S
      · have hb : 4 ∉ S := fun hb => forbid 1 3 4 hu ha hb (by simp [localAdj]) (by simp [localAdj]) (by decide)
        have hs : S ⊆ {1,3,5,6} := by intro t ht; fin_cases t <;> simp_all
        exact (Finset.card_le_card hs).trans (by decide)
      · have hs : S ⊆ {1,4,5,6} := by intro t ht; fin_cases t <;> simp_all
        exact (Finset.card_le_card hs).trans (by decide)
  · by_cases hv : 2 ∈ S
    · by_cases hc : 5 ∈ S
      · have hd : 6 ∉ S := fun hd => forbid 2 5 6 hv hc hd (by simp [localAdj]) (by simp [localAdj]) (by decide)
        have hs : S ⊆ {2,3,4,5} := by intro t ht; fin_cases t <;> simp_all
        exact (Finset.card_le_card hs).trans (by decide)
      · have hs : S ⊆ {2,3,4,6} := by intro t ht; fin_cases t <;> simp_all
        exact (Finset.card_le_card hs).trans (by decide)
    · have hs : S ⊆ {3,4,5,6} := by intro t ht; fin_cases t <;> simp_all
      exact (Finset.card_le_card hs).trans (by decide)

private def basePart (S : Finset (V × Fin 7)) : Finset V :=
  Finset.univ.filter fun i => (i,0) ∈ S

private def gadgetPart (S : Finset (V × Fin 7)) (i : V) : Finset (Fin 7) :=
  Finset.univ.filter fun t => t ≠ 0 ∧ (i,t) ∈ S

private theorem split_card (S : Finset (V × Fin 7)) :
    S.card = (basePart S).card + ∑ i : V, (gadgetPart S i).card := by
  have hs : S = (basePart S).image (fun i => (i, (0 : Fin 7))) ∪
      Finset.univ.biUnion (fun i => (gadgetPart S i).image (fun t => (i,t))) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ,
      true_and, basePart, gadgetPart, Finset.mem_filter]
    constructor
    · intro hp
      by_cases hz : p.2 = 0
      · left; exact ⟨p.1, by convert hp using 1; exact Prod.ext rfl hz.symm, by ext <;> simp [hz]⟩
      · right; exact ⟨p.1, p.2, ⟨hz,hp⟩, rfl⟩
    · rintro (⟨i,hi,rfl⟩ | ⟨i,t,ht,rfl⟩)
      · exact hi
      · exact ht.2
  conv_lhs => rw [hs]
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective]
  · rw [Finset.card_biUnion]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    · intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨t,ht,hp⟩ := Finset.mem_image.mp hp
      obtain ⟨u,hu,hq⟩ := Finset.mem_image.mp hq
      exact hij (by simpa using congrArg Prod.fst (hp.trans hq.symm))
  · exact fun _ _ h => (Prod.mk.inj h).1
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp ht).2.1 (by simpa using congrArg Prod.snd he)

private theorem independent_upper (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset (V × Fin 7)) (hS : IsKIndependent (graftGraph F) 2 S) :
    S.card ≤ 4 * Fintype.card V + beta F 2 := by
  have h := (independent_iff _ _).mp hS
  have hb : IsKIndependent F 2 (basePart S) := by
    apply (independent_iff _ _).mpr
    intro v hv a ha b hb hva hvb
    exact congrArg Prod.fst (h (v,0) (by simpa [basePart] using hv)
      (a,0) (by simpa [basePart] using ha) (b,0) (by simpa [basePart] using hb)
      (Or.inl ⟨rfl,rfl,hva⟩) (Or.inl ⟨rfl,rfl,hvb⟩))
  have hg (i : V) : (gadgetPart S i).card ≤ 4 := by
    apply gadget_bound _ (by simp [gadgetPart])
    intro v hv a ha b hb hva hvb
    exact congrArg Prod.snd (h (i,v) ((Finset.mem_filter.mp hv).2.2)
      (i,a) (Finset.mem_filter.mp ha).2.2 (i,b) (Finset.mem_filter.mp hb).2.2
      (Or.inr ⟨rfl,hva⟩) (Or.inr ⟨rfl,hvb⟩))
  have hb' : (basePart S).card ≤ beta F 2 :=
    Finset.le_sup (by simp [beta, hb])
  rw [split_card]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset V)) => hg i)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
  omega

private def extendSet (S : Finset V) : Finset (V × Fin 7) :=
  S.image (fun i => (i,(0 : Fin 7))) ∪ Finset.univ.product {1,4,5,6}

private theorem extend_independent (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset V) (hS : IsKIndependent F 2 S) :
    IsKIndependent (graftGraph F) 2 (extendSet S) := by
  have h := (independent_iff _ _).mp hS
  apply (independent_iff _ _).mpr
  intro p hp q hq r hr hpq hpr
  have mem (x : V × Fin 7) : x ∈ extendSet S ↔
      (x.2 = 0 ∧ x.1 ∈ S) ∨ x.2 ∈ ({1,4,5,6} : Finset (Fin 7)) := by
    simp [extendSet, Prod.ext_iff, and_comm, eq_comm]
  have hp' := (mem p).mp hp
  have hq' := (mem q).mp hq
  have hr' := (mem r).mp hr
  change (_ ∨ _) at hpq hpr
  rcases hpq with hpq | ⟨hiq,hpq⟩ <;> rcases hpr with hpr | ⟨hir,hpr⟩
  · have hps := hp'.resolve_right (by simp [hpq.1])
    have hqs := hq'.resolve_right (by simp [hpq.2.1])
    have hrs := hr'.resolve_right (by simp [hpr.2.1])
    exact Prod.ext (h p.1 hps.2 q.1 hqs.2 r.1 hrs.2 hpq.2.2 hpr.2.2)
      (hpq.2.1.trans hpr.2.1.symm)
  · simp only [localAdj] at hpr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq' hr'
    omega
  · simp only [localAdj] at hpq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq' hr'
    omega
  · apply Prod.ext (hiq.symm.trans hir)
    simp only [localAdj, Finset.mem_insert, Finset.mem_singleton] at hpq hpr hp' hq' hr'
    omega

private theorem extend_card (S : Finset V) :
    (extendSet S).card = 4 * Fintype.card V + S.card := by
  rw [extendSet, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      ]
    change S.card + ((Finset.univ : Finset V) ×ˢ
      ({1,4,5,6} : Finset (Fin 7))).card = _
    rw [Finset.card_product]
    have h4 : ({1,4,5,6} : Finset (Fin 7)).card = 4 := by decide
    rw [h4,Finset.card_univ]
    omega
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    simpa using hq

/-- The induced degree-at-most-one maximum of the actual grafted graph. -/
theorem beta_graftGraph (F : SimpleGraph V) [DecidableRel F.Adj] [Nonempty V] :
    beta (graftGraph F) 2 = 4 * Fintype.card V + beta F 2 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    exact independent_upper F S (Finset.mem_filter.mp hS).2
  · obtain ⟨S,hS,hcard⟩ := Finset.exists_mem_eq_sup
      (Finset.univ.powerset.filter (IsKIndependent F 2))
      (by
        refine ⟨{Classical.ofNonempty}, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
        intro v hv
        have hl : (({Classical.ofNonempty} : Finset V).filter (F.Adj v)).card ≤ 1 :=
          (Finset.card_filter_le _ _).trans_eq (Finset.card_singleton _)
        exact Nat.lt_succ_of_le hl) Finset.card
    have hs := (Finset.mem_filter.mp hS).2
    have he := extend_independent F S hs
    have hl : (extendSet S).card ≤ beta (graftGraph F) 2 :=
      Finset.le_sup (by simp [beta,he])
    rw [extend_card] at hl
    change _ = S.card at hcard
    rw [← hcard] at hl
    exact hl


/-- The colored support is exactly the vertices whose value is not `none`. -/
noncomputable def coloredSupport {W C : Type*} [DecidableEq W] [DecidableEq C]
    (c : W → Option C) (S : Finset W) : Finset W := S.filter fun v => c v ≠ none

/-- Only colors actually represented on the support are counted. -/
noncomputable def palette {W C : Type*} [DecidableEq W] [DecidableEq C]
    (c : W → Option C) (S : Finset W) : Finset (Option C) :=
  (coloredSupport c S).image c

/-- Closed-neighborhood majority at a colored vertex, with the center counted once. -/
noncomputable def goodAt {W C : Type*} [DecidableEq W] [DecidableEq C]
    (c : W → Option C) (N : Finset W) (v : W) : Prop :=
  c v ≠ none → 2 * (1 + (N.filter fun w => c w = c v).card) ≥
    1 + (N.filter fun w => c w ≠ none).card

/-- Uncolored neighbors enter neither side of the sub-quorum inequality. -/
noncomputable def IsSubQuorum {W C : Type*} [Fintype W] [DecidableEq W] [DecidableEq C]
    (G : SimpleGraph W) (c : W → Option C) : Prop :=
  ∀ v, goodAt c (Finset.univ.filter (G.Adj v)) v

/-- Maximum actual color count; the empty coloring lawfully attains zero. -/
noncomputable def psiSq {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) : ℕ :=
  Nat.findGreatest (fun n => ∃ c : W → Option ℕ,
    IsSubQuorum G c ∧ (palette c Finset.univ).card = n) (Fintype.card W)

private theorem palette_le {W C : Type*} [DecidableEq W] [DecidableEq C]
    (c : W → Option C) (S : Finset W) : (palette c S).card ≤ S.card :=
  Finset.card_image_le.trans (Finset.card_filter_le _ _)

private theorem erase_duplicate {W C : Type*} [DecidableEq W] [DecidableEq C]
    (S : Finset W) (c : W → C) {x y : W} (hx : x ∈ S) (hxy : x ≠ y)
    (hc : c x = c y) : (S.erase y).image c = S.image c := by
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (Finset.erase_subset _ _)
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    by_cases hwy : w = y
    · subst w; exact Finset.mem_image.mpr ⟨x, by simp [hx,hxy], hc⟩
    · exact Finset.mem_image.mpr ⟨w, by simp [hw,hwy], rfl⟩

private def localNeighbors (v : Fin 7) : Finset (Fin 7) :=
  match v.val with
  | 0 => {3}
  | 1 => {2,3,4}
  | 2 => {1,5,6}
  | 3 => {0,1}
  | 4 => {1}
  | _ => {2}

private theorem mem_localNeighbors (v w : Fin 7) :
    w ∈ localNeighbors v ↔ localAdj v w := by
  fin_cases v <;> fin_cases w <;> simp [localNeighbors,localAdj]

private theorem local_loopless (v : Fin 7) : ¬ localAdj v v := by
  fin_cases v <;> simp [localAdj]

private theorem missing_support {C : Type*} [DecidableEq C]
    (c : Fin 7 → Option C) (hp : 6 ≤ (palette c Finset.univ).card)
    (x : Fin 7) (hx : c x = none) :
    coloredSupport c Finset.univ = Finset.univ.erase x ∧
      Set.InjOn c (coloredSupport c Finset.univ) := by
  have hs : coloredSupport c Finset.univ ⊆ Finset.univ.erase x := by
    intro y hy
    have hn := (Finset.mem_filter.mp hy).2
    exact Finset.mem_erase.mpr ⟨by intro he; subst y; exact hn hx, Finset.mem_univ _⟩
  have hc : (Finset.univ.erase x).card = 6 := by simp
  have hlow := Finset.card_image_le (s := coloredSupport c Finset.univ) (f := c)
  have hu := Finset.card_le_card hs
  have he : coloredSupport c Finset.univ = Finset.univ.erase x :=
    Finset.eq_of_subset_of_card_le hs (by dsimp [palette] at hp; omega)
  refine ⟨he, Finset.injOn_of_card_image_eq ?_⟩
  dsimp [palette] at hp
  omega

private theorem high_palette_all_colored {C : Type*} [DecidableEq C]
    (c : Fin 7 → Option C) (hp : 6 ≤ (palette c Finset.univ).card)
    (hu : goodAt c (localNeighbors 1) 1) (hv : goodAt c (localNeighbors 2) 2) :
    ∀ x, c x ≠ none := by
  intro x hx
  obtain ⟨hs,hi⟩ := missing_support c hp x hx
  have col (y : Fin 7) (hy : y ≠ x) : c y ≠ none := by
    have hym : y ∈ coloredSupport c Finset.univ := by rw [hs]; simp [hy]
    exact (Finset.mem_filter.mp hym).2
  have violate (v a b : Fin 7) (vg : goodAt c (localNeighbors v) v)
      (vx : v ≠ x) (ax : a ≠ x) (bx : b ≠ x) (ab : a ≠ b)
      (va : localAdj v a) (vb : localAdj v b) : False := by
    have cv := col v vx
    have hsame : (localNeighbors v |>.filter fun w => c w = c v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hc
      have cw : c w ≠ none := fun hn => cv (hc.symm.trans hn)
      have eq : w = v := hi (by simp [coloredSupport,cw])
        (by simp [coloredSupport,cv]) hc
      subst w
      exact local_loopless v ((mem_localNeighbors v v).mp hw)
    have htwo : 1 < (localNeighbors v |>.filter fun w => c w ≠ none).card :=
      Finset.one_lt_card.mpr ⟨a, by simp [mem_localNeighbors,va,col a ax],
        b, by simp [mem_localNeighbors,vb,col b bx], ab⟩
    have hg := vg cv
    rw [hsame] at hg
    simp only [Finset.card_empty] at hg
    omega
  fin_cases x
  · exact violate 1 2 3 hu (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])
  · exact violate 2 5 6 hv (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])
  · exact violate 1 3 4 hu (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])
  · exact violate 1 2 4 hu (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])
  · exact violate 1 2 3 hu (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])
  · exact violate 1 2 3 hu (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])
  · exact violate 1 2 3 hu (by decide) (by decide) (by decide) (by decide)
      (by simp [localAdj]) (by simp [localAdj])

private theorem local_palette_bound {C : Type*} [DecidableEq C]
    (c : Fin 7 → Option C) (hu : goodAt c (localNeighbors 1) 1)
    (hv : goodAt c (localNeighbors 2) 2) (ha : goodAt c (localNeighbors 3) 3) :
    (palette c Finset.univ).card ≤ 5 := by
  by_contra hbad
  have hp : 6 ≤ (palette c Finset.univ).card := by omega
  have col := high_palette_all_colored c hp hu hv
  have hs : coloredSupport c Finset.univ = Finset.univ := by
    ext x; simp [coloredSupport,col]
  have hp' : 6 ≤ (Finset.univ.image c).card := by simpa [palette,hs] using hp
  have hn1 : localNeighbors 1 = {2,3,4} := by rfl
  have hn2 : localNeighbors 2 = {1,5,6} := by rfl
  have hn3 : localNeighbors 3 = {0,1} := by rfl
  have match1 : ∃ t ∈ ({2,3,4} : Finset (Fin 7)), c t = c 1 := by
    have hg := hu (col 1)
    rw [hn1] at hg
    have hc : ({2,3,4} : Finset (Fin 7)).filter (fun t => c t ≠ none) = {2,3,4} := by
      ext t; simp [col]
    rw [hc] at hg
    have hpos : 0 < (({2,3,4} : Finset (Fin 7)).filter fun t => c t = c 1).card := by
      have hn : ({2,3,4} : Finset (Fin 7)).card = 3 := by decide
      rw [hn] at hg
      omega
    obtain ⟨t,ht⟩ := Finset.card_pos.mp hpos
    exact ⟨t,(Finset.mem_filter.mp ht).1,(Finset.mem_filter.mp ht).2⟩
  have match2 : ∃ t ∈ ({1,5,6} : Finset (Fin 7)), c t = c 2 := by
    have hg := hv (col 2)
    rw [hn2] at hg
    have hc : ({1,5,6} : Finset (Fin 7)).filter (fun t => c t ≠ none) = {1,5,6} := by
      ext t; simp [col]
    rw [hc] at hg
    have hpos : 0 < (({1,5,6} : Finset (Fin 7)).filter fun t => c t = c 2).card := by
      have hn : ({1,5,6} : Finset (Fin 7)).card = 3 := by decide
      rw [hn] at hg
      omega
    obtain ⟨t,ht⟩ := Finset.card_pos.mp hpos
    exact ⟨t,(Finset.mem_filter.mp ht).1,(Finset.mem_filter.mp ht).2⟩
  have inject_after (x y : Fin 7) (hne : x ≠ y) (he : c x = c y) :
      Set.InjOn c (Finset.univ.erase y) := by
    have him := erase_duplicate Finset.univ c (Finset.mem_univ x) hne he
    apply Finset.injOn_of_card_image_eq
    have hle := Finset.card_image_le (s := Finset.univ.erase y) (f := c)
    rw [him] at hle ⊢
    have hc : (Finset.univ.erase y).card = 6 := by simp
    omega
  by_cases huv : c 1 = c 2
  · have hi := inject_after 1 2 (by decide) huv
    have h31 : c 0 ≠ c 3 := by
      intro he
      have eq := hi (by simp) (by simp) he
      exact (by decide : (0 : Fin 7) ≠ 3) eq
    have h32 : c 1 ≠ c 3 := by
      intro he
      have eq := hi (by simp) (by simp) he
      exact (by decide : (1 : Fin 7) ≠ 3) eq
    have hg := ha (col 3)
    rw [hn3] at hg
    have he : ({0,1} : Finset (Fin 7)).filter (fun w => c w = c 3) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw he
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact h31 he
      · exact h32 he
    rw [he] at hg
    have hc : ({0,1} : Finset (Fin 7)).filter (fun w => c w ≠ none) = {0,1} := by
      ext w; simp [col]
    rw [hc] at hg
    have hn : ({0,1} : Finset (Fin 7)).card = 2 := by decide
    rw [hn] at hg
    simp at hg
  · obtain ⟨x,hx,hcx⟩ := match1
    obtain ⟨y,hy,hcy⟩ := match2
    have hx2 : x ≠ 2 := by intro he; subst x; exact huv hcx.symm
    have hy1 : y ≠ 1 := by intro he; subst y; exact huv hcy
    have hx1 : (1 : Fin 7) ≠ x := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      omega
    have hi := inject_after 1 x hx1 hcx.symm
    have hmem2 : (2 : Fin 7) ∈ Finset.univ.erase x := by simp; omega
    have hmemy : y ∈ Finset.univ.erase x := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      omega
    have eq := hi hmemy hmem2 hcy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    omega

private theorem goodAt_image {W X C : Type*} [DecidableEq W] [DecidableEq X]
    [DecidableEq C] (c : X → Option C) (e : W → X) (he : Function.Injective e)
    (N : Finset W) (v : W) :
    goodAt c (N.image e) (e v) ↔ goodAt (fun w => c (e w)) N v := by
  unfold goodAt
  rw [Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ he, Finset.card_image_of_injective _ he]

private theorem coloring_upper (F : SimpleGraph V) {C : Type*} [DecidableEq C]
    (c : V × Fin 7 → Option C) (hc : IsSubQuorum (graftGraph F) c) :
    (palette c Finset.univ).card ≤ 5 * Fintype.card V := by
  have hlocal (i : V) (t : Fin 7) (ht : t ≠ 0) :
      goodAt (fun s => c (i,s)) (localNeighbors t) t := by
    have hg := hc (i,t)
    have hg' : goodAt c ((localNeighbors t).image (fun s => (i,s))) (i,t) := by
      convert hg using 1
      ext p
      simp [graftGraph,mem_localNeighbors,ht,Prod.ext_iff,eq_comm,and_comm]
    exact (goodAt_image c (fun s => (i,s)) (fun _ _ h => (Prod.mk.inj h).2) _ _).mp hg'
  have he : palette c Finset.univ = Finset.univ.biUnion
      (fun i : V => palette (fun t => c (i,t)) Finset.univ) := by
    ext z
    simp only [palette,coloredSupport,Finset.mem_image,Finset.mem_filter,
      Finset.mem_univ,true_and,Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨i,t⟩,hcol,hc⟩
      exact ⟨i,⟨t,hcol,hc⟩⟩
    · rintro ⟨i,t,hcol,hc⟩
      exact ⟨(i,t),hcol,hc⟩
  rw [he]
  apply Finset.card_biUnion_le.trans
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset V)) =>
    local_palette_bound (fun t => c (i,t)) (hlocal i 1 (by decide))
      (hlocal i 2 (by decide)) (hlocal i 3 (by decide)))
  simpa [mul_comm] using hb

private def leafCode (t : Fin 7) : ℕ := if t = 1 ∨ t = 2 then 0 else t.val - 2

private noncomputable def fiveColoring : V × Fin 7 → Option ℕ := fun p =>
  if p.2 = 0 then none else some (Nat.pair ((Fintype.equivFin V) p.1).val (leafCode p.2))

private theorem fiveColoring_good (F : SimpleGraph V) :
    IsSubQuorum (graftGraph F) (fiveColoring (V := V)) := by
  intro p
  rcases p with ⟨i,t⟩
  by_cases ht : t = 0
  · subst t
    simp [goodAt,fiveColoring]
  · change goodAt _ _ _
    have hg : goodAt (fiveColoring (V := V))
        ((localNeighbors t).image (fun s => (i,s))) (i,t) := by
      apply (goodAt_image _ _ (fun _ _ h => (Prod.mk.inj h).2) _ _).mpr
      fin_cases t <;> norm_num [goodAt,localNeighbors,fiveColoring,leafCode,
        Nat.pair_eq_pair,Fin.ext_iff,Finset.filter_insert,Finset.filter_singleton,
        -Fin.val_eq_zero_iff] <;> simp
    convert hg using 1
    ext p
    simp [graftGraph,mem_localNeighbors,ht,Prod.ext_iff,eq_comm,and_comm]

private theorem fiveColoring_card :
    (palette (fiveColoring (V := V)) Finset.univ).card = 5 * Fintype.card V := by
  let f : V × Fin 5 → Option ℕ := fun p =>
    some (Nat.pair ((Fintype.equivFin V) p.1).val p.2.val)
  have hf : Function.Injective f := by
    intro p q he
    have hpq := Nat.pair_eq_pair.mp (Option.some.inj he)
    apply Prod.ext
    · exact (Fintype.equivFin V).injective (Fin.ext hpq.1)
    · exact Fin.ext hpq.2
  have him : palette (fiveColoring (V := V)) Finset.univ = Finset.univ.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨i,t⟩,ht,rfl⟩ := Finset.mem_image.mp hz
      have ht0 : t ≠ 0 := by
        intro h; subst t; simpa [coloredSupport,fiveColoring] using ht
      have hbound : leafCode t < 5 := by
        fin_cases t <;> simp_all [leafCode]
      exact Finset.mem_image.mpr ⟨(i,⟨leafCode t,hbound⟩),Finset.mem_univ _,by
        simp [f,fiveColoring,ht0]⟩
    · intro hz
      obtain ⟨⟨i,t⟩,_,rfl⟩ := Finset.mem_image.mp hz
      let s : Fin 7 := if t = 0 then 1 else ⟨t.val + 2,by omega⟩
      have hs0 : s ≠ 0 := by
        dsimp [s]
        split_ifs
        · exact (by decide : (1 : Fin 7) ≠ 0)
        · intro he
          have hh := congrArg Fin.val he
          simp only [Fin.val_zero] at hh
          omega
      have hcode : leafCode s = t.val := by
        fin_cases t <;> norm_num [s,leafCode,Fin.ext_iff]
      exact Finset.mem_image.mpr ⟨(i,s),by simp [coloredSupport,fiveColoring,hs0],by
        simp [fiveColoring,hs0,f,hcode]⟩
  rw [him,Finset.card_image_of_injective _ hf]
  simp [mul_comm]

/-- The maximum number of actual sub-quorum colors in every nonempty grafted graph. -/
theorem psiSq_graftGraph (F : SimpleGraph V) [Nonempty V] :
    psiSq (graftGraph F) = 5 * Fintype.card V := by
  let P : ℕ → Prop := fun n => ∃ c : V × Fin 7 → Option ℕ,
    IsSubQuorum (graftGraph F) c ∧ (palette c Finset.univ).card = n
  have h0 : P 0 := ⟨fun _ => none,by simp [IsSubQuorum,goodAt],by simp [palette,coloredSupport]⟩
  have hmax : P (psiSq (graftGraph F)) := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨c,hc,hcard⟩ := hmax
  apply le_antisymm
  · rw [← hcard]
    exact coloring_upper F c hc
  · apply Nat.le_findGreatest
    · rw [← fiveColoring_card (V := V)]
      exact (palette_le (fiveColoring (V := V)) Finset.univ).trans_eq (by simp)
    · exact ⟨fiveColoring,fiveColoring_good F,fiveColoring_card⟩

end D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
