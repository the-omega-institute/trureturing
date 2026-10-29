/- GID: D5/S3/Observer/Tomography/InformationallyCompletePairForest
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/InformationallyCompletePairForest
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: IC pairs are exactly injective pairs with acyclic fiber graphs. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax

/-!
# Informationally complete pairs and forests

For finite real random variables, the two pushforward distributions determine every
probability weight precisely when the joint value map is injective and its bipartite
fiber graph is acyclic. Complementarity means injectivity of the joint value map.

A signed trail weight has marginal sums supported at its endpoints. A cycle therefore
produces a nonzero weight with zero marginals; perturbing the uniform probability by
this bounded weight gives two distinct probabilities with the same distributions.
Conversely, the nonzero support of a difference with zero marginals cannot have a leaf,
whereas every nontrivial finite tree has one.

The probability and completeness notions are those of Section 5 of S. Gudder,
*Finite-Dimensional Convex Effect Algebras* (arXiv:1912.05110v1).
-/

noncomputable section
open scoped BigOperators
open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)

namespace D5.S3.Observer.Tomography.InformationallyCompletePairForest

open Classical in
/-- The distribution of a real random variable, evaluated on an arbitrary set. -/
def distribution {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (μ : α → ℝ) (δ : Set ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x ∈ δ), μ x

/-- The two marginal distributions determine every probability weight uniquely. -/
def IsICPair {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℝ) : Prop :=
  ∀ μ ν, Probability μ → Probability ν →
    distribution f μ = distribution f ν → distribution g μ = distribution g ν → μ = ν

/-- A point supplies an edge between its two tagged random-variable values. -/
def fiberGraph {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℝ) : SimpleGraph (ℝ ⊕ ℝ) :=
  SimpleGraph.fromRel (fun v w =>
    Sum.elim (fun a => Sum.elim (fun _ => False)
      (fun b => ∃ x, f x = a ∧ g x = b) w) (fun _ => False) v)

private def supportGraph {α : Type*} [Fintype α] [DecidableEq α]
    (f g w : α → ℝ) : SimpleGraph (ℝ ⊕ ℝ) :=
  SimpleGraph.fromRel (fun v z =>
    Sum.elim (fun a => Sum.elim (fun _ => False)
      (fun b => ∃ x, f x = a ∧ g x = b ∧ w x ≠ 0) z) (fun _ => False) v)

private lemma supportGraph_edge_finite {α : Type*} [Fintype α] [DecidableEq α]
    (f g w : α → ℝ) : (supportGraph f g w).edgeSet.Finite := by
  classical
  apply (Set.finite_range (fun x : α => s(Sum.inl (f x), Sum.inr (g x)))).subset
  intro e he
  induction e using Sym2.inductionOn with
  | _ v z =>
    rw [SimpleGraph.mem_edgeSet] at he
    have he' := (SimpleGraph.fromRel_adj _ _ _).mp he
    rcases he'.2 with hrel | hrel
    · rcases v with a | a
      · rcases z with b | b
        · dsimp only [supportGraph] at *
          simp_all
        · rcases hrel with ⟨x, hfx, hgx, hw⟩
          refine ⟨x, ?_⟩
          simp [hfx, hgx]
      · rcases z with b | b <;> dsimp only [supportGraph] at * <;> simp_all
    · rcases v with a | a
      · rcases z with b | b <;> dsimp only [supportGraph] at * <;> simp_all
      · rcases z with b | b
        · rcases hrel with ⟨x, hfx, hgx, hw⟩
          refine ⟨x, ?_⟩
          simp [hfx, hgx]
        · dsimp only [supportGraph] at *
          simp_all

@[instance_reducible]
private noncomputable def locallyFinite_of_finite_edgeSet {V : Type*} (G : SimpleGraph V)
    [Finite G.edgeSet] : G.LocallyFinite := by
  classical
  intro v
  letI : Fintype (G.incidenceSet v) :=
    ((Set.toFinite G.edgeSet).subset (G.incidenceSet_subset v)).fintype
  exact Fintype.ofEquiv (G.incidenceSet v) (G.incidenceSetEquivNeighborSet v)

private lemma finite_component_edgeSet {V : Type*} (G : SimpleGraph V)
    [Finite G.edgeSet] (C : G.ConnectedComponent) : Finite C.toSimpleGraph.edgeSet := by
  exact Finite.of_injective (SimpleGraph.Embedding.induce C.supp).mapEdgeSet
    (SimpleGraph.Embedding.induce C.supp).mapEdgeSet.injective

private lemma distribution_eq_iff_fiber_sums {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (μ ν : α → ℝ) :
    distribution f μ = distribution f ν ↔
      ∀ a, (∑ x ∈ Finset.univ.filter (fun x => f x = a), μ x) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), ν x := by
  classical
  constructor
  · intro h a
    have ha := congrFun h ({a} : Set ℝ)
    have hμ : distribution f μ ({a} : Set ℝ) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), μ x := by
      unfold distribution
      simp only [Set.mem_singleton_iff]
    have hν : distribution f ν ({a} : Set ℝ) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), ν x := by
      unfold distribution
      simp only [Set.mem_singleton_iff]
    rw [hμ, hν] at ha
    exact ha
  · intro h
    funext δ
    let s : Finset α := Finset.univ.filter (fun x => f x ∈ δ)
    let t : Finset ℝ := s.image f
    have hmap : ∀ x ∈ s, f x ∈ t := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hμ := Finset.sum_fiberwise_of_maps_to hmap μ
    have hν := Finset.sum_fiberwise_of_maps_to hmap ν
    have hfiber (a : ℝ) (ha : a ∈ t) (q : α → ℝ) :
        (∑ x ∈ s with f x = a, q x) =
          ∑ x ∈ Finset.univ.filter (fun x => f x = a), q x := by
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
      have hδa : f x ∈ δ := by simpa [s] using hx
      have hδa' : a ∈ δ := by simpa [hxa] using hδa
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, s]
        constructor
        · rintro ⟨hfd, hfa⟩
          exact hfa
        · intro hfa
          exact ⟨by simpa [hfa] using hδa', hfa⟩
      · intro y hy
        rfl
    calc
      distribution f μ δ = ∑ x ∈ s, μ x := rfl
      _ = ∑ a ∈ t, ∑ x ∈ s with f x = a, μ x := hμ.symm
      _ = ∑ a ∈ t, ∑ x ∈ s with f x = a, ν x := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfiber a ha μ, hfiber a ha ν, h a]
      _ = ∑ x ∈ s, ν x := hν
      _ = distribution f ν δ := rfl

private lemma not_injective_not_ic {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℝ}
    (h : ¬ Function.Injective (fun x => (f x, g x))) : ¬ IsICPair f g := by
  classical
  obtain ⟨x, y, hpair, hxy⟩ := Function.not_injective_iff.mp h
  have hfx : f x = f y := congrArg Prod.fst hpair
  have hgx : g x = g y := congrArg Prod.snd hpair
  intro hic
  have hprob (z : α) : Probability (Pi.single z (1 : ℝ)) := by
    have h : Probability (Convexity.StdSimplex.single (R := ℝ) z).weights :=
      ⟨(Convexity.StdSimplex.single (R := ℝ) z).weights_nonneg,
        (Convexity.StdSimplex.single (R := ℝ) z).total_of_fintype⟩
    simpa only [Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single] using h
  have hf : distribution f (Pi.single x (1 : ℝ)) =
      distribution f (Pi.single y (1 : ℝ)) := by
    funext δ
    unfold distribution
    simp [hfx]
  have hg : distribution g (Pi.single x (1 : ℝ)) =
      distribution g (Pi.single y (1 : ℝ)) := by
    funext δ
    unfold distribution
    simp [hgx]
  have heq := hic _ _ (hprob x) (hprob y) hf hg
  have hneq : (Pi.single x (1 : ℝ) : α → ℝ) ≠ Pi.single y (1 : ℝ) := by
    exact (Pi.single_left_injective (one_ne_zero : (1 : ℝ) ≠ 0)).ne hxy
  exact hneq heq

private lemma walk_weights {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    {u v : ℝ ⊕ ℝ} (p : (fiberGraph f g).Walk u v) (hp : p.IsTrail) :
    ∃ w : α → ℝ,
      (∀ a, (∑ x ∈ Finset.univ.filter (fun x => f x = a), w x) =
        (if u = Sum.inl a then 1 else 0) - (if v = Sum.inl a then 1 else 0)) ∧
      (∀ b, (∑ x ∈ Finset.univ.filter (fun x => g x = b), w x) =
        (if v = Sum.inr b then 1 else 0) - (if u = Sum.inr b then 1 else 0)) ∧
      (∀ x, w x = 0 ↔ s(Sum.inl (f x), Sum.inr (g x)) ∉ p.edges) ∧
      (∀ x, |w x| ≤ 1) := by
  classical
  induction p with
  | nil =>
    refine ⟨0, ?_, ?_, ?_, ?_⟩ <;> simp
  | @cons u v z h p ih =>
    have htail := hp.of_cons
    obtain ⟨w, hwf, hwg, hws, hwb⟩ := ih htail
    have hedge : s(u, v) ∉ p.edges := (SimpleGraph.Walk.isTrail_cons h p).mp hp |>.2
    rcases u with a | a <;> rcases v with b | b
    · unfold fiberGraph at h
      simp at h
    · obtain ⟨x, hfx, hgx⟩ : ∃ x, f x = a ∧ g x = b := by
        unfold fiberGraph at h
        simpa using h
      have hwx : w x = 0 := (hws x).mpr (by simpa [hfx, hgx] using hedge)
      refine ⟨Pi.single x 1 + w, ?_, ?_, ?_, ?_⟩
      · intro c
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [hwf]
        simp [hfx]
        split_ifs <;> ring1
      · intro c
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [hwg]
        simp [hgx]
      · intro y
        by_cases hy : y = x
        · subst y
          simp [hwx, hfx, hgx]
        · have hne : s(Sum.inl (f y), Sum.inr (g y)) ≠ s(Sum.inl a, Sum.inr b) := by
            intro he
            have he' : f y = a ∧ g y = b := by
              rw [Sym2.eq_iff] at he
              simpa using he
            apply hy
            exact hinj (Prod.ext (he'.1.trans hfx.symm) (he'.2.trans hgx.symm))
          simpa [hy, hne] using hws y
      · intro y
        by_cases hy : y = x
        · subst y
          simp [hwx]
        · simpa [hy] using hwb y
    · obtain ⟨x, hfx, hgx⟩ : ∃ x, f x = b ∧ g x = a := by
        unfold fiberGraph at h
        simpa using h
      have hwx : w x = 0 := (hws x).mpr (by simpa [hfx, hgx, Sym2.eq_swap] using hedge)
      refine ⟨Pi.single x (-1) + w, ?_, ?_, ?_, ?_⟩
      · intro c
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [hwf]
        simp [hfx]
        split_ifs <;> ring1
      · intro c
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [hwg]
        simp [hgx]
        split_ifs <;> ring1
      · intro y
        by_cases hy : y = x
        · subst y
          simp [hwx, hfx, hgx, Sym2.eq_swap]
        · have hne : s(Sum.inl (f y), Sum.inr (g y)) ≠ s(Sum.inr a, Sum.inl b) := by
            intro he
            have he' : f y = b ∧ g y = a := by
              rw [Sym2.eq_iff] at he
              simpa using he
            apply hy
            exact hinj (Prod.ext (he'.1.trans hfx.symm) (he'.2.trans hgx.symm))
          simpa [hy, hne] using hws y
      · intro y
        by_cases hy : y = x
        · subst y
          simp [hwx]
        · simpa [hy] using hwb y
    · unfold fiberGraph at h
      simp at h

private lemma zero_fibers_not_ic {α : Type*} [Fintype α] [DecidableEq α]
    {f g w : α → ℝ} (hw : w ≠ 0) (hb : ∀ x, |w x| ≤ 1)
    (hf : ∀ a, (∑ x ∈ Finset.univ.filter (fun x => f x = a), w x) = 0)
    (hg : ∀ b, (∑ x ∈ Finset.univ.filter (fun x => g x = b), w x) = 0) :
    ¬ IsICPair f g := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ 0 := Function.ne_iff.mp hw
  have : Nonempty α := ⟨x⟩
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card α : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have htotal : ∑ x, w x = 0 := by
    have hmap : ∀ x ∈ (Finset.univ : Finset α), f x ∈ Finset.univ.image f := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap w]
    apply Finset.sum_eq_zero
    intro a ha
    exact hf a
  let μ : α → ℝ := fun x => (1 + w x) / n
  let ν : α → ℝ := fun _ => 1 / n
  have hμ : Probability μ := by
    constructor
    · intro z
      have hz := (abs_le.mp (hb z)).1
      exact div_nonneg (by linarith) hn.le
    · change (∑ z, (1 + w z) / n) = 1
      rw [← Finset.sum_div, Finset.sum_add_distrib, htotal]
      simp [n, ne_of_gt hn]
  have hν : Probability ν := by
    constructor
    · intro z
      exact le_of_lt (div_pos zero_lt_one hn)
    · change (∑ _ : α, 1 / n) = 1
      simp [n, ne_of_gt hn]
  have hfd : distribution f μ = distribution f ν := by
    apply (distribution_eq_iff_fiber_sums f μ ν).mpr
    intro a
    dsimp [μ, ν]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hf, add_zero]
    rw [Finset.sum_div]
  have hgd : distribution g μ = distribution g ν := by
    apply (distribution_eq_iff_fiber_sums g μ ν).mpr
    intro b
    dsimp [μ, ν]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hg, add_zero]
    rw [Finset.sum_div]
  intro hic
  have heq := congrFun (hic μ ν hμ hν hfd hgd) x
  have hval : 1 + w x = 1 := (div_left_inj' hn.ne').mp heq
  exact hx (by linarith)

private lemma cycle_not_ic {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    (hcycle : ¬ (fiberGraph f g).IsAcyclic) : ¬ IsICPair f g := by
  classical
  obtain ⟨u, p, hp⟩ : ∃ u, ∃ p : (fiberGraph f g).Walk u u, p.IsCycle := by
    unfold SimpleGraph.IsAcyclic at hcycle
    push Not at hcycle
    exact hcycle
  obtain ⟨w, hwf, hwg, hws, hwb⟩ := walk_weights hinj p hp.isTrail
  have hw : w ≠ 0 := by
    intro hw
    obtain ⟨e, he⟩ := p.edges.exists_mem_of_ne_nil (by simpa using hp.not_nil)
    have hadj := p.edges_subset_edgeSet he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hadj' := (fiberGraph f g).mem_edgeSet.mp hadj
      rcases a with a | a <;> rcases b with b | b
      · unfold fiberGraph at hadj'
        simp at hadj'
      · obtain ⟨x, hfx, hgx⟩ : ∃ x, f x = a ∧ g x = b := by
          unfold fiberGraph at hadj'
          simpa using hadj'
        have hn := (hws x).mp (congrFun hw x)
        exact hn (by simpa [hfx, hgx] using he)
      · obtain ⟨x, hfx, hgx⟩ : ∃ x, f x = b ∧ g x = a := by
          unfold fiberGraph at hadj'
          simpa using hadj'
        have hn := (hws x).mp (congrFun hw x)
        exact hn (by simpa [hfx, hgx, Sym2.eq_swap] using he)
      · unfold fiberGraph at hadj'
        simp at hadj'
  apply zero_fibers_not_ic hw hwb
  · intro a
    simpa using hwf a
  · intro b
    simpa using hwg b

private lemma ic_injective {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℝ}
    (hic : IsICPair f g) : Function.Injective (fun x => (f x, g x)) := by
  by_contra h
  exact not_injective_not_ic h hic

private lemma ic_acyclic {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℝ}
    (hic : IsICPair f g) (hinj : Function.Injective (fun x => (f x, g x))) :
    (fiberGraph f g).IsAcyclic := by
  by_contra h
  exact cycle_not_ic hinj h hic

private lemma injective_acyclic_ic {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    (hacyc : (fiberGraph f g).IsAcyclic) : IsICPair f g := by
  intro μ ν hμ hν hfd hgd
  classical
  by_contra hneq
  let w : α → ℝ := μ - ν
  have hwne : w ≠ 0 := by
    exact sub_ne_zero.mpr hneq
  have hsumf (a : ℝ) :
      ∑ x ∈ Finset.univ.filter (fun x => f x = a), w x = 0 := by
    have heq := (distribution_eq_iff_fiber_sums f μ ν).mp hfd a
    simp [w, Finset.sum_sub_distrib, heq]
  have hsumg (b : ℝ) :
      ∑ x ∈ Finset.univ.filter (fun x => g x = b), w x = 0 := by
    have heq := (distribution_eq_iff_fiber_sums g μ ν).mp hgd b
    simp [w, Finset.sum_sub_distrib, heq]
  let H : SimpleGraph (ℝ ⊕ ℝ) := supportGraph f g w
  have hHsub : H ≤ fiberGraph f g := by
    intro v z hadj
    rcases v with a | a <;> rcases z with b | b
    · dsimp only [H, supportGraph] at hadj
      simp at hadj
    · have hs : ∃ y, f y = a ∧ g y = b ∧ w y ≠ 0 := by
        dsimp only [H, supportGraph] at hadj
        simpa using hadj
      have hs' : ∃ y, f y = a ∧ g y = b := by
        rcases hs with ⟨y, hfy, hgy, hwy⟩
        exact ⟨y, hfy, hgy⟩
      unfold fiberGraph
      simpa only [SimpleGraph.fromRel_adj, Sum.elim_inl, Sum.elim_inr] using
        (show Sum.inl a ≠ Sum.inr b ∧
            ((∃ y, f y = a ∧ g y = b) ∨ False) from
          ⟨Sum.inl_ne_inr, Or.inl hs'⟩)
    · have hs : ∃ y, f y = b ∧ g y = a ∧ w y ≠ 0 := by
        dsimp only [H, supportGraph] at hadj
        simpa using hadj
      have hs' : ∃ y, f y = b ∧ g y = a := by
        rcases hs with ⟨y, hfy, hgy, hwy⟩
        exact ⟨y, hfy, hgy⟩
      unfold fiberGraph
      simpa only [SimpleGraph.fromRel_adj, Sum.elim_inl, Sum.elim_inr] using
        (show Sum.inr a ≠ Sum.inl b ∧
            (False ∨ (∃ y, f y = b ∧ g y = a)) from
          ⟨Sum.inr_ne_inl, Or.inr hs'⟩)
    · dsimp only [H, supportGraph] at hadj
      simp at hadj
  have hHacyc : H.IsAcyclic := hacyc.anti hHsub
  have hfinite : H.edgeSet.Finite := supportGraph_edge_finite f g w
  let : Finite H.edgeSet := hfinite.fintype.finite
  let : H.LocallyFinite := locallyFinite_of_finite_edgeSet H
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ 0 := Function.ne_iff.mp hwne
  have hxe : H.Adj (Sum.inl (f x)) (Sum.inr (g x)) := by
    dsimp only [H, supportGraph]
    rw [SimpleGraph.fromRel_adj]
    exact ⟨Sum.inl_ne_inr, Or.inl ⟨x, rfl, rfl, hx⟩⟩
  let C := H.connectedComponentMk (Sum.inl (f x))
  have hleft : Sum.inl (f x) ∈ C :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hright : Sum.inr (g x) ∈ C := C.mem_supp_of_adj_mem_supp hleft hxe
  have hfiniteC : Finite C.toSimpleGraph.edgeSet := finite_component_edgeSet H C
  let : Finite C.toSimpleGraph.edgeSet := hfiniteC
  let : C.toSimpleGraph.LocallyFinite := locallyFinite_of_finite_edgeSet _
  let : Nontrivial C := ⟨⟨⟨Sum.inl (f x), hleft⟩, ⟨Sum.inr (g x), hright⟩, by
    intro h
    exact Sum.inl_ne_inr (congrArg Subtype.val h)⟩⟩
  have htree : C.toSimpleGraph.IsTree := hHacyc.isTree_connectedComponent C
  obtain ⟨u, v, huv, hu, hv⟩ := htree.exists_ne_and_degree_eq_one
  obtain ⟨q, huq, huq_unique⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu)
  have huqH : H.Adj u.1 q.1 :=
    (C.toSimpleGraph_adj u.2 q.2).mp huq
  have hcontra : False := by
    rcases huval : u.1 with a | a <;> rcases hqval : q.1 with b | b
    · rw [huval, hqval] at huqH
      dsimp only [H, supportGraph] at huqH
      simp at huqH
    · have hy : ∃ y, f y = a ∧ g y = b ∧ w y ≠ 0 := by
        rw [huval, hqval] at huqH
        dsimp only [H, supportGraph] at huqH
        simpa using huqH
      obtain ⟨y, hyf, hyg, hyw⟩ := hy
      have hsum_single :
          ∑ z ∈ Finset.univ.filter (fun z => f z = a), w z = w y := by
        apply Finset.sum_eq_single y
        · intro z hz hzy
          by_contra hwz
          have hzf : f z = a := by simpa using hz
          have hzad : H.Adj (Sum.inl a) (Sum.inr (g z)) := by
            dsimp only [H, supportGraph]
            rw [SimpleGraph.fromRel_adj]
            exact ⟨Sum.inl_ne_inr, Or.inl ⟨z, hzf, rfl, hwz⟩⟩
          have hzmem : Sum.inr (g z) ∈ C :=
            C.mem_supp_of_adj_mem_supp (show Sum.inl a ∈ C from huval ▸ u.2) hzad
          let qz : C := ⟨Sum.inr (g z), hzmem⟩
          have hzadC : C.toSimpleGraph.Adj u qz :=
            (C.toSimpleGraph_adj u.2 qz.2).mpr (by simpa [huval, qz] using hzad)
          have hqeq : qz = q := huq_unique qz hzadC
          have hqeqval := congrArg Subtype.val hqeq
          have hgz : g z = b := by simpa [qz, hqval] using hqeqval
          apply hzy
          apply hinj
          exact Prod.ext (hzf.trans hyf.symm) (hgz.trans hyg.symm)
        · intro hy_not
          exfalso
          apply hy_not
          simp [hyf]
      have hzero := hsumf a
      rw [hsum_single] at hzero
      exact hyw hzero
    · have hy : ∃ y, f y = b ∧ g y = a ∧ w y ≠ 0 := by
        rw [huval, hqval] at huqH
        dsimp only [H, supportGraph] at huqH
        simpa using huqH
      obtain ⟨y, hyf, hyg, hyw⟩ := hy
      have hsum_single :
          ∑ z ∈ Finset.univ.filter (fun z => g z = a), w z = w y := by
        apply Finset.sum_eq_single y
        · intro z hz hzy
          by_contra hwz
          have hzg : g z = a := by simpa using hz
          have hzad : H.Adj (Sum.inr a) (Sum.inl (f z)) := by
            dsimp only [H, supportGraph]
            rw [SimpleGraph.fromRel_adj]
            exact ⟨Sum.inr_ne_inl, Or.inr ⟨z, rfl, hzg, hwz⟩⟩
          have hzmem : Sum.inl (f z) ∈ C :=
            C.mem_supp_of_adj_mem_supp (show Sum.inr a ∈ C from huval ▸ u.2) hzad
          let qz : C := ⟨Sum.inl (f z), hzmem⟩
          have hzadC : C.toSimpleGraph.Adj u qz :=
            (C.toSimpleGraph_adj u.2 qz.2).mpr (by simpa [huval, qz] using hzad)
          have hqeq : qz = q := huq_unique qz hzadC
          have hqeqval := congrArg Subtype.val hqeq
          have hfz : f z = b := by simpa [qz, hqval] using hqeqval
          apply hzy
          apply hinj
          exact Prod.ext (hfz.trans hyf.symm) (hzg.trans hyg.symm)
        · intro hy_not
          exfalso
          apply hy_not
          simp [hyg]
      have hzero := hsumg a
      rw [hsum_single] at hzero
      exact hyw hzero
    · rw [huval, hqval] at huqH
      dsimp only [H, supportGraph] at huqH
      simp at huqH
  exact hcontra.elim

/-- Informational completeness is complementarity together with absence of fiber cycles. -/
theorem result {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℝ) :
    IsICPair f g ↔
      Function.Injective (fun x => (f x, g x)) ∧ (fiberGraph f g).IsAcyclic := by
  constructor
  · intro hic
    exact ⟨ic_injective hic, ic_acyclic hic (ic_injective hic)⟩
  · rintro ⟨hinj, hacyc⟩
    exact injective_acyclic_ic hinj hacyc

end D5.S3.Observer.Tomography.InformationallyCompletePairForest
