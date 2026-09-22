/- GID: D5/S3/Combinatorics/Graph/DUFLinearRemainder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFLinearRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: A cone with a linear remainder has an exact support compensation and positive surplus. -/

import D5.S3.Combinatorics.Graph.DUFComponents
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFLinearRemainder

open Finset DUFStructure DUFComponents

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The vertices incident with an edge; isolated ground vertices do not contribute. -/
noncomputable def active (G : SimpleGraph V) : Finset V :=
  univ.filter fun x => (G.neighborFinset x).Nonempty

open Classical in
/-- Unordered distinct vertex pairs with a common graph neighbor. -/
noncomputable def twoStepPairs (G : SimpleGraph V) : Finset (Finset V) :=
  pairs.filter fun p => ∃ z, p ⊆ G.neighborFinset z

open Classical in
/-- The diagonal contribution is essential in the two-step support bound. -/
theorem graph_two_step_bound (G : SimpleGraph V) :
    2 * G.edgeFinset.card ≤ (active G).card + 2 * (twoStepPairs G).card := by
  classical
  let A (u : V) := (G.neighborFinset u).biUnion (fun z => G.neighborFinset z)
  let d (u : V) : ℚ := G.degree u
  let R : ℚ := ∑ u, ∑ z ∈ G.neighborFinset u, d z / d u
  have hd (u z : V) (huz : G.Adj u z) : 0 < d u := by
    dsimp [d]
    exact_mod_cast card_pos.mpr ⟨z, (G.mem_neighborFinset _ _).mpr huz⟩
  have havg (u : V) : (∑ z ∈ G.neighborFinset u, d z / d u) ≤ (A u).card := by
    by_cases hn : (G.neighborFinset u).Nonempty
    · obtain ⟨z, hz⟩ := hn
      have hdu := hd u z ((G.mem_neighborFinset _ _).mp hz)
      rw [← sum_div, div_le_iff₀ hdu]
      calc
        ∑ z ∈ G.neighborFinset u, d z ≤
            ∑ _z ∈ G.neighborFinset u, ((A u).card : ℚ) := by
          apply sum_le_sum
          intro z hz
          dsimp [d]
          exact_mod_cast card_le_card (subset_biUnion_of_mem (fun z => G.neighborFinset z) hz)
        _ = (A u).card * d u := by simp [d, mul_comm]
    · rw [not_nonempty_iff_eq_empty.mp hn]
      simp
  have hswap : R = ∑ u, ∑ z ∈ G.neighborFinset u, d u / d z := by
    dsimp [R]
    simp_rw [G.neighborFinset_eq_filter, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro z _
    rw [G.adj_comm]
  have hrat : (∑ u, (G.degree u : ℚ)) ≤ R := by
    have h : 2 * (∑ u, (G.degree u : ℚ)) ≤ R + R := by
      conv_rhs => rhs; rw [hswap]
      rw [← sum_add_distrib]
      calc
        2 * (∑ u, (G.degree u : ℚ)) =
            ∑ u, ∑ _z ∈ G.neighborFinset u, (2 : ℚ) := by
          simp [← mul_sum, mul_comm]
        _ ≤ ∑ u, ((∑ z ∈ G.neighborFinset u, d z / d u) +
            ∑ z ∈ G.neighborFinset u, d u / d z) := by
          apply sum_le_sum
          intro u _
          rw [← sum_add_distrib]
          apply sum_le_sum
          intro z hz
          have hu := hd u z ((G.mem_neighborFinset _ _).mp hz)
          have hz' := hd z u ((G.mem_neighborFinset _ _).mp hz).symm
          apply (le_of_mul_le_mul_right ?_ (mul_pos hu hz'))
          field_simp
          nlinarith [two_mul_le_add_sq (d u) (d z)]
    linarith
  have hsum : (∑ u, G.degree u) ≤ ∑ u, (A u).card := by
    exact_mod_cast hrat.trans (sum_le_sum fun u _ => havg u)
  let K : SimpleGraph V :=
    { Adj := fun u w => u ≠ w ∧ ∃ z, G.Adj u z ∧ G.Adj w z
      symm := ⟨by intro u w h; exact ⟨h.1.symm, by tauto⟩⟩
      loopless := ⟨by intro u h; exact h.1 rfl⟩ }
  have hA (u w : V) : w ∈ A u ↔ ∃ z, G.Adj u z ∧ G.Adj w z := by
    simp only [A, mem_biUnion, SimpleGraph.mem_neighborFinset]
    simp_rw [G.adj_comm (v := w)]
  have hdiag (u : V) : u ∈ A u ↔ (G.neighborFinset u).Nonempty := by
    rw [hA]
    simp only [Finset.Nonempty, SimpleGraph.mem_neighborFinset, and_self]
  have hrow (u : V) : (A u).card = K.degree u +
      if (G.neighborFinset u).Nonempty then 1 else 0 := by
    have he : (A u).erase u = K.neighborFinset u := by
      ext w
      simp [hA, K, ne_comm]
    by_cases hu : u ∈ A u
    · have hcard := card_erase_add_one hu
      rw [he, K.card_neighborFinset_eq_degree] at hcard
      simpa [(hdiag u).mp hu] using hcard.symm
    · rw [erase_eq_of_notMem hu] at he
      simp [he, ← hdiag u]
  have htotal : (∑ u, (A u).card) =
      (active G).card + 2 * K.edgeFinset.card := by
    simp_rw [hrow]
    rw [sum_add_distrib, K.sum_degrees_eq_twice_card_edges]
    rw [active, card_filter]
    omega
  have hK : K.edgeFinset.card = (twoStepPairs G).card := by
    apply card_bij (fun e _ => e.toFinset)
    · intro e he
      induction e using Sym2.ind with | _ u w =>
        have hh : K.Adj u w := by simpa using he
        obtain ⟨huw, z, huz, hwz⟩ := hh
        simp only [twoStepPairs, pairs, mem_filter, mem_powersetCard,
          subset_univ, true_and, Sym2.toFinset_mk_eq]
        refine ⟨by simp [huw], z, ?_⟩
        simp [insert_subset_iff, singleton_subset_iff, huz.symm, hwz.symm]
    · intro e he f hf hef
      apply Sym2.ext
      intro x
      simpa only [Sym2.mem_toFinset] using (congrArg (fun s => x ∈ s) hef).to_iff
    · intro p hp
      obtain ⟨hp, z, hz⟩ := mem_filter.mp hp
      obtain ⟨u, w, huw, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hp).2
      refine ⟨s(u, w), ?_, Sym2.toFinset_mk_eq⟩
      have hu := (G.mem_neighborFinset _ _).mp (hz (by simp : u ∈ ({u, w} : Finset V)))
      have hw := (G.mem_neighborFinset _ _).mp (hz (by simp : w ∈ ({u, w} : Finset V)))
      simpa [K] using And.intro huw ⟨z, hu.symm, hw.symm⟩
  rw [G.sum_degrees_eq_twice_card_edges, htotal, hK] at hsum
  exact hsum

/-- The pair support of a triple family. -/
def support (H : Finset (Finset V)) : Finset (Finset V) :=
  pairs.filter fun p => (neighbors H p).Nonempty

/-- The support of the transposed pair-extension relation. -/
def commonSupport (H : Finset (Finset V)) : Finset (Finset V) :=
  pairs.filter fun p => (common H p).Nonempty

/-- The triples not containing the chosen cone vertex. -/
def remainder (H : Finset (Finset V)) (c : V) : Finset (Finset V) :=
  H.filter fun a => c ∉ a

/-- Every pair lies in at most one member of the family. -/
def Linear (F : Finset (Finset V)) : Prop :=
  ∀ p ∈ (pairs : Finset (Finset V)), ∀ a ∈ F, ∀ b ∈ F,
    p ⊆ a → p ⊆ b → a = b

open Classical in
/-- Exact overlap compensation and an uncapped surplus for a cone with a linear remainder. -/
theorem support_compensation (H : Finset (Finset V))
    (hu : ∀ a ∈ H, a.card = 3) (hd : DUF H) (c : V)
    (hl : Linear (remainder H c)) :
    (support H).card + (commonSupport H).card + (link H c).edgeFinset.card =
        2 * H.card + (active (link H c)).card + (twoStepPairs (link H c)).card +
          (remainder H c).card ∧
    4 * H.card + (active (link H c)).card + 2 * (remainder H c).card ≤
        2 * (support H).card + 2 * (commonSupport H).card ∧
    2 * H.card ≤ (support H).card + (commonSupport H).card := by
  classical
  let F := remainder H c
  let E := pairs.filter fun p => c ∈ neighbors H p
  let B := support F
  let G := link H c
  have hp (p : Finset V) : p ∈ pairs ↔ p.card = 2 := by simp [pairs]
  have hn (J : Finset (Finset V)) (p : Finset V) (x : V) :
      x ∈ neighbors J p ↔ x ∉ p ∧ insert x p ∈ J := by simp [neighbors]
  have hf (a : Finset V) : a ∈ F ↔ a ∈ H ∧ c ∉ a := by simp [F, remainder]
  have he (p : Finset V) : p ∈ E ↔ p.card = 2 ∧ c ∉ p ∧ insert c p ∈ H := by
    simp [E, hp, hn]
  have hlin (p : Finset V) (hp2 : p.card = 2) : (neighbors F p).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    have hxe := (hn F p x).mp hx
    have hye := (hn F p y).mp hy
    exact (insert_inj hxe.1).mp
      (hl p ((hp p).mpr hp2) _ hxe.2 _ hye.2 (subset_insert _ _) (subset_insert _ _))
  have hFc (p : Finset V) (x : V) (hx : x ∈ neighbors F p) : c ∉ p ∧ x ≠ c := by
    have hx' := (hf _).mp ((hn F p x).mp hx).2
    simp only [mem_insert, not_or] at hx'
    exact ⟨hx'.2.2, Ne.symm hx'.2.1⟩
  have hB : B.card = 3 * F.card := by
    have hi := (DUFCounting.incidence_counts F (fun a ha => hu a ((hf a).mp ha).1)).1
    calc
      B.card = ∑ p ∈ pairs, (neighbors F p).card := by
        change (support F).card = _
        rw [support, card_filter]
        apply sum_congr rfl
        intro p hp'
        have hb := hlin p ((hp p).mp hp')
        by_cases hne : (neighbors F p).Nonempty
        · have := card_pos.mpr hne
          simp only [hne, ite_true]
          omega
        · simp [not_nonempty_iff_eq_empty.mp hne]
      _ = 3 * F.card := hi
  have split_pair (p : Finset V) (hp2 : p.card = 2) (hcp : c ∈ p) :
      ∃ x, x ≠ c ∧ p = {c, x} := by
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hp2
    simp only [mem_insert, mem_singleton] at hcp
    rcases hcp with rfl | rfl
    · exact ⟨y, hxy.symm, rfl⟩
    · exact ⟨x, hxy, pair_comm _ _⟩
  have hH : H.card = E.card + F.card := by
    have hE : E.card = (H.filter fun a => c ∈ a).card := by
      apply card_bij (fun p _ => insert c p)
      · intro p hp'
        exact mem_filter.mpr ⟨((he p).mp hp').2.2, mem_insert_self _ _⟩
      · intro p hp' q hq' hpq
        have := congrArg (fun a => a.erase c) hpq
        simpa [((he p).mp hp').2.1, ((he q).mp hq').2.1] using this
      · intro a ha
        obtain ⟨ha, hca⟩ := mem_filter.mp ha
        refine ⟨a.erase c, (he _).mpr ⟨?_, by simp, ?_⟩, insert_erase hca⟩
        · rw [card_erase_of_mem hca, hu a ha]
        · simpa [insert_erase hca] using ha
    rw [hE]
    exact (card_filter_add_card_filter_not (s := H) (fun a => c ∈ a)).symm
  have hEG : E.card = G.edgeFinset.card := by
    symm
    apply card_bij (fun e _ => e.toFinset)
    · intro e he'
      induction e using Sym2.ind with | _ x y =>
        have hxy : G.Adj x y := by simpa using he'
        change x ≠ y ∧ c ∉ ({x, y} : Finset V) ∧ ({c, x, y} : Finset V) ∈ H at hxy
        rw [Sym2.toFinset_mk_eq, he]
        exact ⟨by simp [hxy.1], hxy.2⟩
    · intro e he' f hf' hef
      apply Sym2.ext
      intro x
      simpa only [Sym2.mem_toFinset] using (congrArg (fun s => x ∈ s) hef).to_iff
    · intro p hp'
      obtain ⟨hp2, hcp, hHp⟩ := (he p).mp hp'
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hp2
      refine ⟨s(x, y), ?_, Sym2.toFinset_mk_eq⟩
      have ha : G.Adj x y := ⟨hxy, hcp, hHp⟩
      simpa using ha
  have hNG (x : V) (hxc : x ≠ c) : neighbors H {c, x} = G.neighborFinset x := by
    ext y
    rw [hn, G.mem_neighborFinset]
    change (y ∉ ({c, x} : Finset V) ∧ insert y {c, x} ∈ H) ↔
      (x ≠ y ∧ c ∉ ({x, y} : Finset V) ∧ ({c, x, y} : Finset V) ∈ H)
    have hi : insert y ({c, x} : Finset V) = {c, x, y} := by
      ext z; simp only [mem_insert, mem_singleton]; tauto
    rw [hi]
    simp only [mem_insert, mem_singleton, not_or]
    grind only
  have hactive (x : V) (hx : x ∈ active G) : x ≠ c := by
    obtain ⟨y, hy⟩ := (mem_filter.mp hx).2
    have hy' : G.Adj x y := (G.mem_neighborFinset _ _).mp hy
    exact fun h => hy'.2.1 (by simp [h])
  have hpairinj : Function.Injective (fun x : V => ({c, x} : Finset V)) := by
    intro x y hxy
    change ({c, x} : Finset V) = {c, y} at hxy
    have hx : x ∈ ({c, y} : Finset V) := hxy ▸ (by simp)
    have hy : y ∈ ({c, x} : Finset V) := hxy.symm ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hx hy
    grind only
  have hS : support H = (E ∪ B) ∪ star c (active G) := by
    ext p
    constructor
    · intro hp'
      obtain ⟨hP, x, hx⟩ := mem_filter.mp hp'
      have hp2 := (hp p).mp hP
      obtain ⟨hxp, hHx⟩ := (hn H p x).mp hx
      by_cases hcp : c ∈ p
      · obtain ⟨y, hyc, rfl⟩ := split_pair p hp2 hcp
        apply mem_union_right
        refine mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
        rw [← hNG y hyc]
        exact ⟨x, (hn _ _ _).mpr ⟨hxp, hHx⟩⟩
      · apply mem_union_left
        by_cases hxc : x = c
        · exact mem_union_left _ ((he p).mpr ⟨hp2, hcp, hxc ▸ hHx⟩)
        · apply mem_union_right
          exact mem_filter.mpr ⟨hP, x, (hn F p x).mpr
            ⟨hxp, (hf _).mpr ⟨hHx, by simp [hcp, Ne.symm hxc]⟩⟩⟩
    · intro hp'
      rcases mem_union.mp hp' with hp' | hp'
      · rcases mem_union.mp hp' with hp' | hp'
        · obtain ⟨hp2, hcp, hHp⟩ := (he p).mp hp'
          exact mem_filter.mpr ⟨(hp p).mpr hp2, c, (hn H p c).mpr ⟨hcp, hHp⟩⟩
        · obtain ⟨hP, x, hx⟩ := mem_filter.mp hp'
          have hx' := (hn F p x).mp hx
          exact mem_filter.mpr ⟨hP, x, (hn H p x).mpr ⟨hx'.1, ((hf _).mp hx'.2).1⟩⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hp'
        have hxc := hactive x hx
        refine mem_filter.mpr ⟨(hp _).mpr (by simp [hxc.symm]), ?_⟩
        rw [hNG x hxc]
        exact (mem_filter.mp hx).2
  have hS_count : (support H).card + (E ∩ B).card =
      E.card + 3 * F.card + (active G).card := by
    have hdis : Disjoint (E ∪ B) (star c (active G)) := by
      apply disjoint_left.mpr
      intro p hp' hstar
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hstar
      rcases mem_union.mp hp' with hp' | hp'
      · exact ((he _).mp hp').2.1 (by simp)
      · obtain ⟨_, y, hy⟩ := mem_filter.mp hp'
        exact (hFc _ y hy).1 (by simp)
    rw [hS, card_union_of_disjoint hdis, DUFStructure.star, card_image_of_injective _ hpairinj]
    have hcount := card_union_add_card_inter E B
    rw [hB] at hcount
    omega
  have hTG (q : Finset V) (hq : q ∈ twoStepPairs G) : c ∉ q := by
    obtain ⟨_, z, hz⟩ := mem_filter.mp hq
    intro hcq
    have ha : G.Adj z c := (G.mem_neighborFinset _ _).mp (hz hcq)
    exact ha.2.1 (by simp)
  have hTout (q : Finset V) (hq2 : q.card = 2) (hcq : c ∉ q) :
      q ∈ commonSupport H ↔ q ∈ twoStepPairs G := by
    constructor
    · intro hq
      obtain ⟨_, p, hpq⟩ := mem_filter.mp hq
      obtain ⟨hp', hsub⟩ := mem_filter.mp hpq
      have hp2 := (hp p).mp hp'
      have hcp : c ∈ p := by
        by_contra hcp
        have hsubF : q ⊆ neighbors F p := by
          intro x hx
          have hx' := (hn H p x).mp (hsub hx)
          have hcx : c ≠ x := fun h => hcq (h.symm ▸ hx)
          exact (hn F p x).mpr ⟨hx'.1, (hf _).mpr ⟨hx'.2, by simp [hcx, hcp]⟩⟩
        have := (card_le_card hsubF).trans (hlin p hp2)
        omega
      obtain ⟨z, hzc, rfl⟩ := split_pair p hp2 hcp
      exact mem_filter.mpr ⟨(hp q).mpr hq2, z, by rwa [← hNG z hzc]⟩
    · intro hq
      obtain ⟨_, z, hz⟩ := mem_filter.mp hq
      obtain ⟨x, hx⟩ := card_pos.mp (show 0 < q.card by omega)
      have ha : G.Adj z x := (G.mem_neighborFinset _ _).mp (hz hx)
      have hzc : z ≠ c := fun h => ha.2.1 (by simp [h])
      refine mem_filter.mpr ⟨(hp q).mpr hq2, {c, z}, mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact (hp _).mpr (by simp [hzc.symm])
      · rwa [hNG z hzc]
  have hcommon (x : V) (hxc : x ≠ c) (p : Finset V) :
      p ∈ common H {c, x} ↔ p ∈ E ∧ x ∈ neighbors F p := by
    constructor
    · intro hpc
      obtain ⟨hp', hs⟩ := mem_filter.mp hpc
      have hc := (hn H p c).mp (hs (by simp))
      have hx := (hn H p x).mp (hs (by simp))
      exact ⟨(he p).mpr ⟨(hp p).mp hp', hc⟩,
        (hn F p x).mpr ⟨hx.1, (hf _).mpr ⟨hx.2, by simp [hc.1, hxc.symm]⟩⟩⟩
    · rintro ⟨hp', hx⟩
      have hc := (he p).mp hp'
      have hx' := (hn F p x).mp hx
      refine mem_filter.mpr ⟨(hp p).mpr hc.1, ?_⟩
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨(hn H p c).mpr hc.2, (hn H p x).mpr ⟨hx'.1, ((hf _).mp hx'.2).1⟩⟩
  have unique_completion (x : V) (hxc : x ≠ c) (p q : Finset V)
      (hp' : p ∈ common H {c, x}) (hq' : q ∈ common H {c, x}) : p = q := by
    obtain ⟨y, hyp, hyq⟩ := not_disjoint_iff.mp
      (common_intersecting H hd {c, x} (by simp [hxc.symm]) p hp' q hq')
    have hpF := (hn F p x).mp ((hcommon x hxc p).mp hp').2
    have hqF := (hn F q x).mp ((hcommon x hxc q).mp hq').2
    have hxy : x ≠ y := fun h => hpF.1 (h.symm ▸ hyp)
    have heq := hl {x, y} ((hp _).mpr (by simp [hxy]))
      _ hpF.2 _ hqF.2
      (by simp [insert_subset_iff, singleton_subset_iff, hyp])
      (by simp [insert_subset_iff, singleton_subset_iff, hyq])
    have := congrArg (fun a => a.erase x) heq
    simpa [hpF.1, hqF.1] using this
  let O := univ.filter fun x : V => x ≠ c ∧ (common H {c, x}).Nonempty
  have hO : O.card = (E ∩ B).card := by
    let completion (p : Finset V) (hp' : p ∈ E ∩ B) : V :=
      (mem_filter.mp (mem_inter.mp hp').2).2.choose
    have hc (p : Finset V) (hp' : p ∈ E ∩ B) : completion p hp' ∈ neighbors F p :=
      (mem_filter.mp (mem_inter.mp hp').2).2.choose_spec
    symm
    apply card_bij completion
    · intro p hp'
      have hxc := (hFc p _ (hc p hp')).2
      exact mem_filter.mpr ⟨mem_univ _, hxc, p,
        (hcommon _ hxc p).mpr ⟨(mem_inter.mp hp').1, hc p hp'⟩⟩
    · intro p hp' q hq' heq
      have hxc := (hFc p _ (hc p hp')).2
      apply unique_completion (completion p hp') hxc p q
      · exact (hcommon _ hxc p).mpr ⟨(mem_inter.mp hp').1, hc p hp'⟩
      · exact (hcommon _ hxc q).mpr ⟨(mem_inter.mp hq').1, heq.symm ▸ hc q hq'⟩
    · intro x hx
      obtain ⟨hxc, p, hp'⟩ := (mem_filter.mp hx).2
      obtain ⟨hpE, hxF⟩ := (hcommon x hxc p).mp hp'
      have hpEB : p ∈ E ∩ B := mem_inter.mpr ⟨hpE,
        mem_filter.mpr ⟨(hp p).mpr ((he p).mp hpE).1, x, hxF⟩⟩
      refine ⟨p, hpEB, ?_⟩
      exact card_le_one.mp (hlin p ((he p).mp hpE).1) _ (hc p hpEB) _ hxF
  have hT : commonSupport H = twoStepPairs G ∪ star c O := by
    ext q
    constructor
    · intro hq
      have hq2 := (hp q).mp (mem_filter.mp hq).1
      by_cases hcq : c ∈ q
      · obtain ⟨x, hxc, rfl⟩ := split_pair q hq2 hcq
        apply mem_union_right
        exact mem_image.mpr ⟨x,
          mem_filter.mpr ⟨mem_univ _, hxc, (mem_filter.mp hq).2⟩, rfl⟩
      · exact mem_union_left _ ((hTout q hq2 hcq).mp hq)
    · intro hq
      rcases mem_union.mp hq with hq | hq
      · exact (hTout q ((hp q).mp (mem_filter.mp hq).1) (hTG q hq)).mpr hq
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
        have hx' := (mem_filter.mp hx).2
        exact mem_filter.mpr ⟨(hp _).mpr (by simp [hx'.1.symm]), hx'.2⟩
  have hT_count : (commonSupport H).card = (twoStepPairs G).card + (E ∩ B).card := by
    have hdis : Disjoint (twoStepPairs G) (star c O) := by
      apply disjoint_left.mpr
      intro q hq hstar
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hstar
      exact hTG _ hq (by simp)
    rw [hT, card_union_of_disjoint hdis, DUFStructure.star,
      card_image_of_injective _ hpairinj, hO]
  have hgraph := graph_two_step_bound G
  change (support H).card + (commonSupport H).card + G.edgeFinset.card =
      2 * H.card + (active G).card + (twoStepPairs G).card + F.card ∧
    4 * H.card + (active G).card + 2 * F.card ≤
      2 * (support H).card + 2 * (commonSupport H).card ∧
    2 * H.card ≤ (support H).card + (commonSupport H).card
  omega

end D5.S3.Combinatorics.Graph.DUFLinearRemainder
