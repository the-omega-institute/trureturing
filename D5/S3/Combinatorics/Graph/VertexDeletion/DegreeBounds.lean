/- GID: D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree bounds and positive-target optimistic ratios for exact cuts. -/

import D5.S3.Combinatorics.Graph.Brooks.Coloring
import D5.S3.Combinatorics.Graph.VertexDeletion.TreeTransfer

/-! Degree bounds and positive-target optimistic ratios for exact cuts. -/

set_option autoImplicit false
set_option linter.style.openClassical false

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section DegreeBound

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem survivor_card (D : Finset V) :
    Fintype.card (survivors D) = Fintype.card V - D.card := by
  rw [← Finset.card_compl]
  exact Fintype.card_ofFinset _ (by simp [survivors])

theorem component_card_eq (D : Finset V) :
    (componentSizes G D).card = Fintype.card (survivorGraph G D).ConnectedComponent := by
  simp [componentSizes]

/-- Charge each survivor component other than the root's to an edge from a
deleted vertex, directed away from the surviving root. Every deleted vertex
has a closer neighbor by `BrooksSubcubic.exists_closer_neighbor`, so at most
its degree minus one charges are possible. -/
theorem nc_le_budget_mul_degree_sub_one (hG : G.Connected) (Δ : ℕ)
    (hΔ : G.maxDegree ≤ Δ) (b : ℕ) (D : Finset V) (hD : D.card = b) :
    ncDamage G D ≤ b * (Δ - 1) := by
  by_cases hsurv : Nonempty (survivors D)
  · let root : survivors D := hsurv.some
    let H := survivorGraph G D
    let C₀ := H.connectedComponentMk root
    let A (x : V) := (G.neighborFinset x).filter (fun y =>
      G.dist x root.val < G.dist y root.val)
    have hA (x : V) (hx : x ∈ D) : (A x).card ≤ Δ - 1 := by
      obtain ⟨w, hw, hdRoot⟩ := BrooksSubcubic.exists_closer_neighbor G hG root.val x
        (show x ≠ root.val from fun e => root.property (e ▸ hx))
      have hd : G.dist w root.val < G.dist x root.val := by
        rw [G.dist_comm (u := w) (v := root.val), G.dist_comm (u := x) (v := root.val)]
        exact hdRoot
      have hmem : w ∈ G.neighborFinset x := by simpa only [mem_neighborFinset] using hw
      calc
        (A x).card ≤ ((G.neighborFinset x).erase w).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨hy, hd'⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_erase.mpr ⟨fun e => (hd.not_gt (e ▸ hd')).elim, hy⟩
        _ = G.degree x - 1 := Finset.card_erase_of_mem hmem
        _ ≤ Δ - 1 := Nat.sub_le_sub_right ((G.degree_le_maxDegree x).trans hΔ) 1
    have claim (C : H.ConnectedComponent) (hC : C ≠ C₀) :
        ∃ x ∈ D, ∃ y : survivors D,
          H.connectedComponentMk y = C ∧ y.val ∈ A x := by
      let S : Finset ℕ := C.supp.toFinset.image (fun y => G.dist y.val root.val)
      have hS : S.Nonempty := (Set.toFinset_nonempty.mpr C.nonempty_supp).image _
      obtain ⟨y, hy, hyMin⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
      have hyC : H.connectedComponentMk y = C :=
        by simpa only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] using hy
      have hyRoot : y.val ≠ root.val := by
        intro e
        exact hC (hyC.symm.trans (congrArg H.connectedComponentMk (Subtype.ext e)))
      obtain ⟨x, hx, hdistRoot⟩ :=
        BrooksSubcubic.exists_closer_neighbor G hG root.val y.val hyRoot
      have hdist : G.dist x root.val < G.dist y.val root.val := by
        rw [G.dist_comm (u := x) (v := root.val), G.dist_comm (u := y.val) (v := root.val)]
        exact hdistRoot
      have hxD : x ∈ D := by
        by_contra hn
        let z : survivors D := ⟨x, hn⟩
        have hzC : H.connectedComponentMk z = C :=
          (ConnectedComponent.connectedComponentMk_eq_of_adj
            (show H.Adj z y from hx.symm)).trans hyC
        have hz : G.dist x root.val ∈ S := Finset.mem_image.mpr
          ⟨z, by simpa only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] using hzC, rfl⟩
        have hmin := Finset.min'_le S _ hz
        omega
      exact ⟨x, hxD, y, hyC, Finset.mem_filter.mpr ⟨by simpa only [mem_neighborFinset] using hx.symm, hdist⟩⟩
    let target := D.sigma A
    let domain := (Finset.univ : Finset H.ConnectedComponent).erase C₀
    have witnesses (C : domain) :
        ∃ z : target, ∃ y : survivors D, y.val = z.val.2 ∧ H.connectedComponentMk y = C.val := by
      obtain ⟨x, hx, y, hy, hAxy⟩ := claim C.val (Finset.mem_erase.mp C.property).1
      exact ⟨⟨⟨x, y.val⟩, Finset.mem_sigma.mpr ⟨hx, hAxy⟩⟩, y, rfl, hy⟩
    choose f y hy hf using witnesses
    have hInj : Function.Injective f := by
      intro C E he
      apply Subtype.ext
      rw [← hf C, ← hf E]
      exact congrArg H.connectedComponentMk
        (Subtype.ext ((hy C).trans ((congrArg (fun z : target => z.val.2) he).trans (hy E).symm)))
    have hcards := Fintype.card_le_of_injective f hInj
    rw [Fintype.card_coe, Fintype.card_coe] at hcards
    rw [ncDamage, component_card_eq G, ← Finset.card_univ (α := H.ConnectedComponent),
      ← Finset.card_erase_of_mem (Finset.mem_univ C₀)]
    calc
      domain.card ≤ target.card := hcards
      _ = ∑ x ∈ D, (A x).card := Finset.card_sigma D A
      _ ≤ ∑ _x ∈ D, (Δ - 1) := Finset.sum_le_sum hA
      _ = b * (Δ - 1) := by simp [hD]
  · let : IsEmpty (survivors D) := not_nonempty_iff.mp hsurv
    let : IsEmpty (survivorGraph G D).ConnectedComponent :=
      ⟨fun C => C.nonempty_supp.elim fun v _ => isEmptyElim v⟩
    simp [ncDamage, component_card_eq]

private theorem component_size_pos (D : Finset V)
    (C : (survivorGraph G D).ConnectedComponent) : 0 < C.supp.toFinset.card :=
  Finset.card_pos.mpr (Set.toFinset_nonempty.mpr C.nonempty_supp)

private theorem single_component_scores (b : ℕ) (hb : b < Fintype.card V)
    (D : Finset V) (hD : D.card = b) (hNC : ncDamage G D = 0) :
    pcDamage G D = (Fintype.card V).choose 2 - (Fintype.card V - b).choose 2 ∧
    lccDamage G D = b := by
  let H := survivorGraph G D
  have hSurv : 0 < Fintype.card (survivors D) := by rw [survivor_card, hD]; omega
  let := Fintype.card_pos_iff.mp hSurv
  have hPos : 0 < Fintype.card H.ConnectedComponent := Fintype.card_pos
  have hCount : Fintype.card H.ConnectedComponent = 1 := by
    rw [ncDamage, component_card_eq] at hNC
    change Fintype.card H.ConnectedComponent - 1 = 0 at hNC
    omega
  let C : H.ConnectedComponent := Classical.arbitrary _
  have hUniv : (Finset.univ : Finset H.ConnectedComponent) = {C} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun E _ =>
      (Fintype.card_le_one_iff.mp hCount.le) E C⟩
  have hsum := sum_component_card H
  rw [hUniv, Finset.sum_singleton, survivor_card, hD] at hsum
  have hSize (E : H.ConnectedComponent) : E.supp.toFinset.card = Fintype.card V - b :=
    (Fintype.card_le_one_iff.mp hCount.le) C E ▸ hsum
  obtain ⟨hp, hl⟩ := scores_of_equal_component_sizes G D 1 _ hCount (by decide) hSize
  exact ⟨by simpa using hp, hl.trans (Nat.sub_sub_self hb.le)⟩

private theorem multiple_component_scores (b : ℕ) (D : Finset V)
    (hD : D.card = b) (hnc : 0 < ncDamage G D) :
    (Fintype.card V).choose 2 - (Fintype.card V - b).choose 2 < pcDamage G D ∧
    b < lccDamage G D := by
  let H := survivorGraph G D
  let s := Fintype.card V - b
  let c (C : H.ConnectedComponent) := C.supp.toFinset.card
  have hCount : 1 < Fintype.card H.ConnectedComponent := by
    rw [ncDamage, component_card_eq] at hnc
    change 0 < Fintype.card H.ConnectedComponent - 1 at hnc
    omega
  have hTotal : ∑ C, c C = s := (sum_component_card H).trans ((survivor_card D).trans
    (congrArg (Fintype.card V - ·) hD))
  have each_lt (C : H.ConnectedComponent) : c C < s := by
    have := Fintype.one_lt_card_iff_nontrivial.mp hCount
    obtain ⟨E, hE⟩ := exists_ne C
    have hle := Finset.sum_le_sum_of_subset (f := c)
      (Finset.subset_univ ({C, E} : Finset H.ConnectedComponent))
    rw [Finset.sum_pair (Ne.symm hE), hTotal] at hle
    have hpos := component_size_pos G D E
    change 0 < c E at hpos
    omega
  have hSup : (componentSizes G D).sup ≤ s - 1 := by
    apply Multiset.sup_le.mpr
    intro n hn
    obtain ⟨C, _, rfl⟩ := Multiset.mem_map.mp hn
    exact Nat.le_sub_one_of_lt (each_lt C)
  have hSumSq : ∑ C, c C ^ 2 < s ^ 2 := by
    calc
      _ < ∑ C, s * c C := by
        let : Nonempty H.ConnectedComponent := Fintype.card_pos_iff.mp (by omega)
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun C _ => ?_)
        rw [pow_two]
        exact Nat.mul_lt_mul_of_pos_right (each_lt C) (component_size_pos G D C)
      _ = _ := by rw [← Finset.mul_sum, hTotal, pow_two]
  have hPairs : 2 * (∑ C, (c C).choose 2) + s = ∑ C, c C ^ 2 := by
    rw [← hTotal, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun C _ => twice_choose_two_add (c C))
  have hsPairs := twice_choose_two_add s
  have hChoose : s.choose 2 ≤ (Fintype.card V).choose 2 :=
    Nat.choose_le_choose 2 (Nat.sub_le (Fintype.card V) b)
  have hp := component_profile_score_formulas G D
  change pcDamage G D = _ - ∑ C, (c C).choose 2 at hp
  have hStep : b ≤ Fintype.card V := hD ▸ Finset.card_le_univ D
  have hs : 0 < s := by
    let : Nonempty H.ConnectedComponent := Fintype.card_pos_iff.mp (by omega)
    exact Nat.zero_lt_of_lt (each_lt (Classical.arbitrary _))
  exact ⟨by change _ - s.choose 2 < pcDamage G D; omega,
    by unfold lccDamage; dsimp [s] at *; omega⟩

omit [DecidableEq V] in
private theorem damage_le_maximum (score : Finset V → ℕ)
    (b : ℕ) (D : Finset V) (hD : D.card = b) : score D ≤ damageMaximum score b :=
  Finset.le_sup (f := score) (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD⟩)

omit [DecidableEq V] in
private theorem damage_maximum_attained (score : Finset V → ℕ)
    (b : ℕ) (hb : b ≤ Fintype.card V) :
    ∃ D : Finset V, D.card = b ∧ score D = damageMaximum score b := by
  have hs : ((Finset.univ : Finset V).powersetCard b).Nonempty := by
    rw [Finset.powersetCard_nonempty, Finset.card_univ]
    exact hb
  obtain ⟨D, hD, he⟩ := Finset.exists_mem_eq_sup' hs score
  exact ⟨D, (Finset.mem_powersetCard.mp hD).2, by
    simpa [damageMaximum, Finset.sup'_eq_sup] using he.symm⟩

/-- Every exact PC or LCC optimizer has at least two survivor components when
the NC optimum is positive. -/
private theorem pc_lcc_optimizers_disconnected (b : ℕ) (hb : b < Fintype.card V)
    (hPos : 0 < damageMaximum (ncDamage G) b) (D : Finset V) (hD : D.card = b)
    (hOpt : pcDamage G D = damageMaximum (pcDamage G) b ∨
      lccDamage G D = damageMaximum (lccDamage G) b) :
    ¬ (survivorGraph G D).Connected ∧ 0 < ncDamage G D := by
  obtain ⟨E, hE, hEN⟩ := damage_maximum_attained (ncDamage G) b hb.le
  have hGood := multiple_component_scores G b E hE (hEN ▸ hPos)
  have hNC : 0 < ncDamage G D := by
    by_contra! h
    obtain ⟨hP, hL⟩ := single_component_scores G b hb D hD (Nat.eq_zero_of_le_zero h)
    rcases hOpt with ho | ho
    · exact (hP.trans_lt hGood.1).not_ge
        ((damage_le_maximum (pcDamage G) b E hE).trans_eq ho.symm)
    · exact (hL.trans_lt hGood.2).not_ge
        ((damage_le_maximum (lccDamage G) b E hE).trans_eq ho.symm)
  refine ⟨fun hc => ?_, hNC⟩
  have := hc.preconnected.subsingleton_connectedComponent
  have hcard : Fintype.card (survivorGraph G D).ConnectedComponent ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun _ _ => Subsingleton.elim _ _)
  rw [ncDamage, component_card_eq] at hNC
  omega

/-- The lower bound applies pointwise to all tied source optimizers on the
positive-NC-target domain. -/
theorem bounded_degree_transfers_into_nc (hG : G.Connected) (Δ : ℕ)
    (hΔ : G.maxDegree ≤ Δ) (b : ℕ) (hb : b < Fintype.card V)
    (hPos : 0 < damageMaximum (ncDamage G) b) :
    (∀ D : Finset V, D.card = b → pcDamage G D = damageMaximum (pcDamage G) b →
      1 / (↑(b * (Δ - 1)) : ℝ) ≤ damageRatio (ncDamage G) b D) ∧
    (∀ D : Finset V, D.card = b → lccDamage G D = damageMaximum (lccDamage G) b →
      1 / (↑(b * (Δ - 1)) : ℝ) ≤ damageRatio (ncDamage G) b D) := by
  have hBound : damageMaximum (ncDamage G) b ≤ b * (Δ - 1) := by
    apply Finset.sup_le
    intro E hE
    exact nc_le_budget_mul_degree_sub_one G hG Δ hΔ b E (Finset.mem_powersetCard.mp hE).2
  have hPos' : 0 < (damageMaximum (ncDamage G) b : ℝ) := by exact_mod_cast hPos
  have hBound' : (damageMaximum (ncDamage G) b : ℝ) ≤ (↑(b * (Δ - 1)) : ℝ) := by
    exact_mod_cast hBound
  have pointwise (D : Finset V) (hD : D.card = b)
      (ho : pcDamage G D = damageMaximum (pcDamage G) b ∨
        lccDamage G D = damageMaximum (lccDamage G) b) :
        1 / (↑(b * (Δ - 1)) : ℝ) ≤ damageRatio (ncDamage G) b D := by
    have hN := (pc_lcc_optimizers_disconnected G b hb hPos D hD ho).2
    have h1 : (1 : ℝ) ≤ (ncDamage G D : ℝ) := by exact_mod_cast hN
    exact (one_div_le_one_div_of_le hPos' hBound').trans
      (div_le_div_of_nonneg_right h1 hPos'.le)
  exact ⟨fun D hd h => pointwise D hd (Or.inl h), fun D hd h => pointwise D hd (Or.inr h)⟩

end DegreeBound

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem edge_preserves_reachable {V : Type*} {G : SimpleGraph V}
    (P : V → Prop) (h : ∀ ⦃u v⦄, G.Adj u v → (P u ↔ P v))
    {u v : V} (reach : G.Reachable u v) : P u ↔ P v := by
  have reach' := (G.reachable_iff_reflTransGen u v).mp reach
  clear reach
  induction reach' with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (h edge)

private theorem host_leaf_bridge {p t b k : ℕ} (hub : Fin b → Fin p)
    (a : Fin b × Fin k) :
    (host (t := t) hub).IsBridge s(Sum.inr a, hostHub hub a.1) := by
  rw [isBridge_iff]
  intro reach
  have hNoAdj (w : Vertex p t b k) :
      ¬ ((host (t := t) hub).deleteEdges {s(Sum.inr a, hostHub hub a.1)}).Adj (Sum.inr a) w := by
    rw [deleteEdges_adj]
    rintro ⟨edge, hne⟩
    cases w with
    | inr _ => exact edge
    | inl i =>
      change i = (hub a.1).castAdd t at edge
      subst i
      exact hne (Set.mem_singleton _)
  have h := (component_eq_iff_of_no_adj hNoAdj _).mp (ConnectedComponent.sound reach)
  exact Sum.inr_ne_inl h

private theorem host_spine_bridge {p t b k : ℕ} (hub : Fin b → Fin p)
    {i j : Fin (p + t)} (hij : i.val + 1 = j.val) :
    (host (k := k) hub).IsBridge s(Sum.inl i, Sum.inl j) := by
  rw [isBridge_iff]
  intro reach
  let P (v : Vertex p t b k) := position hub v ≤ i.val
  have forward (x y : Vertex p t b k)
      (h : ((host hub).deleteEdges {s(Sum.inl i, Sum.inl j)}).Adj x y)
      (hx : P x) (hy : ¬ P y) : False := by
    obtain ⟨edge, hne⟩ := deleteEdges_adj.mp h
    have hstep := host_adj_position hub x y edge
    change position hub x ≤ i.val at hx
    change ¬ position hub y ≤ i.val at hy
    have hxs : position hub x = i.val := by omega
    have hys : position hub y = j.val := by omega
    have hnePos : position hub x ≠ position hub y := by omega
    cases x with
    | inr a =>
      cases y with
      | inr _ => exact edge
      | inl v =>
        change v = (hub a.1).castAdd t at edge
        subst v
        exact hnePos rfl
    | inl u =>
      cases y with
      | inr a =>
        change u = (hub a.1).castAdd t at edge
        subst u
        exact hnePos rfl
      | inl v =>
        have hu : u = i := Fin.ext hxs
        have hv : v = j := Fin.ext hys
        exact hne (hu.symm ▸ hv.symm ▸ Set.mem_singleton _)
  have hP := edge_preserves_reachable P
    (fun {x y} e => ⟨fun hx => by_contra (forward x y e hx),
      fun hy => by_contra (forward y x e.symm hy)⟩) reach
  have h := hP.mp (show i.val ≤ i.val from le_rfl)
  change j.val ≤ i.val at h
  omega

private theorem host_isTree {p t b k : ℕ} (hub : Fin b → Fin p) (h : 0 < p + t) :
    (host (t := t) (k := k) hub).IsTree := by
  let f : pathGraph (p + t) →g host (t := t) (k := k) hub := ⟨Sum.inl, id⟩
  let attach (v : Vertex p t b k) : Fin (p + t) :=
    match v with
    | .inl i => i
    | .inr a => (hub a.1).castAdd t
  have reaches (v : Vertex p t b k) : (host hub).Reachable v (f (attach v)) := by
    cases v with
    | inl _ => exact Reachable.rfl
    | inr _ => exact Adj.reachable rfl
  have : Nonempty (Vertex p t b k) := ⟨Sum.inl ⟨0, h⟩⟩
  refine ⟨⟨fun u v => (reaches u).trans (Reachable.trans ?_ (reaches v).symm)⟩, ?_⟩
  · exact ((preconnected_pathGraph _) (attach u) (attach v)).map f
  · apply isAcyclic_iff_forall_adj_isBridge.mpr
    intro u v edge
    cases u with
    | inl i =>
      cases v with
      | inl j =>
        rcases pathGraph_adj.mp edge with hij | hji
        · exact host_spine_bridge hub hij
        · rw [Sym2.eq_swap]
          exact host_spine_bridge hub hji
      | inr a =>
        change i = (hub a.1).castAdd t at edge
        subst i
        rw [Sym2.eq_swap]
        exact host_leaf_bridge hub a
    | inr a =>
      cases v with
      | inl i =>
        change i = (hub a.1).castAdd t at edge
        subst i
        exact host_leaf_bridge hub a
      | inr _ => exact edge.elim

/-- With one leaf per distinct hub, a spine vertex has at most two spine
neighbors and one leaf neighbor. Every leaf has just its hub as a neighbor. -/
private theorem host_maxDegree_one_leaf {p t b : ℕ} (hub : Fin b → Fin p)
    (hinj : Function.Injective hub) :
    (host (t := t) (k := 1) hub).maxDegree ≤ 3 := by
  let H := host (t := t) (k := 1) hub
  apply H.maxDegree_le_of_forall_degree_le
  intro v
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inr a =>
    have eqHub (w : H.neighborSet (Sum.inr a)) : w.val = hostHub hub a.1 := by
      obtain ⟨w, hw⟩ := w
      cases w with
      | inr _ => exact (show False from hw).elim
      | inl j => exact congrArg Sum.inl (show j = (hub a.1).castAdd t from hw)
    have hc : Fintype.card (H.neighborSet (Sum.inr a)) ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun u w => Subtype.ext ((eqHub u).trans (eqHub w).symm))
    exact hc.trans (by decide)
  | inl i =>
    let code : H.neighborSet (Sum.inl i) → Fin 3 := fun w =>
      match w.val with
      | .inl j => if j.val < i.val then 0 else 1
      | .inr _ => 2
    have hi : Function.Injective code := by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ he
      apply Subtype.ext
      cases u with
      | inl j =>
        have hj := pathGraph_adj.mp (show (pathGraph (p + t)).Adj i j from hu)
        cases v with
        | inl l =>
          have hl := pathGraph_adj.mp (show (pathGraph (p + t)).Adj i l from hv)
          change (if j.val < i.val then 0 else 1) = (if l.val < i.val then 0 else 1) at he
          apply congrArg Sum.inl
          apply Fin.ext
          split at he <;> split at he <;> simp_all <;> omega
        | inr a =>
          change (if j.val < i.val then 0 else 1) = (2 : Fin 3) at he
          split at he <;> contradiction
      | inr a =>
        cases v with
        | inl j =>
          change (2 : Fin 3) = (if j.val < i.val then 0 else 1) at he
          split at he <;> contradiction
        | inr z =>
          change i = (hub a.1).castAdd t at hu
          change i = (hub z.1).castAdd t at hv
          have hh : hub a.1 = hub z.1 := Fin.ext (congrArg (Fin.val : Fin (p + t) → ℕ) (hu.symm.trans hv))
          exact congrArg Sum.inr (Prod.ext (hinj hh) (Subsingleton.elim _ _))
    simpa using Fintype.card_le_of_injective code hi

instance instDecidableUniformHostAdj (b k q : ℕ) : DecidableRel (uniformHost b k q).Adj :=
  instDecidableRelVertexAdjHost (uniformHub b)

set_option maxHeartbeats 1500000 in
-- Elaborate the cardinality and reachability comparisons in one proof.
private theorem uniform_one_leaf_tree_maxDegree (b q : ℕ) (hb : 2 ≤ b) :
    (uniformHost b 1 q).IsTree ∧ (uniformHost b 1 q).maxDegree ≤ 3 := by
  change (host (t := uniformTailLength b 1 q) (k := 1) (uniformHub b)).IsTree ∧
    (host (t := uniformTailLength b 1 q) (k := 1) (uniformHub b)).maxDegree ≤ 3
  exact ⟨host_isTree (uniformHub b) (by omega),
    host_maxDegree_one_leaf (uniformHub b) (uniform_hubs_independent b).1⟩

set_option maxHeartbeats 1500000 in
/-- Both transfers out of NC are simultaneously small on degree-three trees.
The three target optima are positive, and every exact NC optimizer qualifies. -/
theorem subcubic_tree_out_of_nc_arbitrarily_small (b : ℕ) (hb : 2 ≤ b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 2 * b * (1 + 2) ≤ q ∧
      (let H : SimpleGraph (UniformVertex b 1 q) := host (uniformHub b)
       H.IsTree ∧ H.maxDegree ≤ 3 ∧ b < Fintype.card (UniformVertex b 1 q) ∧
       (0 < damageMaximum (ncDamage H) b ∧ 0 < damageMaximum (pcDamage H) b ∧
         0 < damageMaximum (lccDamage H) b) ∧
       ∀ D : Finset (UniformVertex b 1 q), D.card = b →
         ncDamage H D = damageMaximum (ncDamage H) b →
         damageRatio (pcDamage H) b D < ε ∧ damageRatio (lccDamage H) b D < ε) := by
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt (12 / ε)
  let q := q₀ + 2 * b * (1 + 2)
  let H : SimpleGraph (UniformVertex b 1 q) := host (uniformHub b)
  have hq : 2 * b * (1 + 2) ≤ q := Nat.le_add_left _ _
  have hqLarge : 12 / ε < (q : ℝ) :=
    hq₀.trans_le (by exact_mod_cast (show q₀ ≤ q from Nat.le_add_right _ _))
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (uniform_prefix_lt_q hb hq).pos
  have hbPos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbLt : b < Fintype.card (UniformVertex b 1 q) := by
    rw [uniform_order hq, Nat.add_comm]
    exact Nat.lt_add_of_pos_right (Nat.mul_pos (by omega) (uniform_prefix_lt_q hb hq).pos)
  have hBound : (↑(4 * (b * (1 + 2)) : ℕ) : ℝ) / (↑(b * q) : ℝ) < ε := by
    push_cast
    apply (div_lt_iff₀ (mul_pos hbPos hqPos)).mpr
    have hh := mul_lt_mul_of_pos_left ((div_lt_iff₀ hε).mp hqLarge) hbPos
    convert hh using 1 <;> ring
  have hK : 1 ≤ (1 : ℕ) := le_rfl
  obtain ⟨⟨_, hP, hL⟩, _, hpos⟩ := uniform_exact_budget_maxima hb hK hq
  obtain ⟨hc, hd⟩ := uniform_one_leaf_tree_maxDegree b q hb
  refine ⟨q, hq, hc, hd, hbLt, hpos, fun D hD hOpt => ?_⟩
  let B := uniformBalancedDeletion hq
  have hB := uniform_balanced_deletion_card hq
  obtain ⟨_, _, eL, eP⟩ := uniform_transfer_identities hb hK hq D B B hD hB hB
    hOpt hP.symm hL.symm
  change damageRatio (pcDamage (host (uniformHub b)) : Finset (UniformVertex b 1 q) → ℕ) b D < ε ∧
    damageRatio (lccDamage (host (uniformHub b)) : Finset (UniformVertex b 1 q) → ℕ) b D < ε
  rw [eP, eL]
  exact ⟨(uniform_pc_transfer_bound hb hq).trans_lt hBound,
    (uniform_lcc_transfer_bound hb hq).trans_lt hBound⟩

/-- With the degree bound removed, the registered uniform witnesses are
trees and make all four transfers small at the same fixed exact budget. -/
theorem uniform_tree_simultaneous_epsilon (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ k q : ℕ, 1 ≤ k ∧ 2 * b * (k + 2) ≤ q ∧
      (let H : SimpleGraph (UniformVertex b k q) := host (uniformHub b)
       H.IsTree ∧ b < Fintype.card (UniformVertex b k q) ∧
       (0 < damageMaximum (ncDamage H) b ∧ 0 < damageMaximum (pcDamage H) b ∧
         0 < damageMaximum (lccDamage H) b) ∧
       ∀ Dn Dp Dl : Finset (UniformVertex b k q), Dn.card = b → Dp.card = b → Dl.card = b →
         ncDamage H Dn = damageMaximum (ncDamage H) b →
         pcDamage H Dp = damageMaximum (pcDamage H) b →
         lccDamage H Dl = damageMaximum (lccDamage H) b →
         damageRatio (ncDamage H) b Dp < ε ∧ damageRatio (ncDamage H) b Dl < ε ∧
           damageRatio (lccDamage H) b Dn < ε ∧ damageRatio (pcDamage H) b Dn < ε) := by
  obtain ⟨k, q, hk, hq, hPos, hSmall⟩ := uniform_simultaneous_epsilon b hb ε hε
  have htree := host_isTree (t := uniformTailLength b k q) (k := k)
    (uniformHub b) (by omega)
  have hcard : b < Fintype.card (UniformVertex b k q) := by
    rw [uniform_order hq, Nat.add_comm]
    exact Nat.lt_add_of_pos_right (Nat.mul_pos (by omega) (uniform_prefix_lt_q hb hq).pos)
  exact ⟨k, q, hk, hq, htree, hcard, hPos, hSmall⟩

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section Optimistic

variable {V : Type*} [Fintype V]

/-- Optimistic source ties maximize the target score among exact source maximizers. -/
noncomputable def optimisticDamageRatio (source target : Finset V → ℕ) (b : ℕ) : ℝ :=
  let choices := ((Finset.univ : Finset V).powersetCard b).filter
    (fun D => source D = damageMaximum source b)
  (↑(choices.sup target : ℕ) : ℝ) / (damageMaximum target b : ℝ)

private theorem optimistic_ratio_attained (source target : Finset V → ℕ)
    (b : ℕ) (hb : b ≤ Fintype.card V) :
    ∃ D : Finset V, D.card = b ∧ source D = damageMaximum source b ∧
      optimisticDamageRatio source target b = damageRatio target b D := by
  let choices := ((Finset.univ : Finset V).powersetCard b).filter
    (fun D => source D = damageMaximum source b)
  obtain ⟨E, hE, hEOpt⟩ := damage_maximum_attained source b hb
  have hne : choices.Nonempty :=
    ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, hE⟩, hEOpt⟩⟩
  obtain ⟨D, hD, hDOpt⟩ := Finset.exists_mem_eq_sup' hne target
  obtain ⟨hCard, hSource⟩ := Finset.mem_filter.mp hD
  refine ⟨D, (Finset.mem_powersetCard.mp hCard).2, hSource, ?_⟩
  change (↑(choices.sup target : ℕ) : ℝ) / (damageMaximum target b : ℝ) =
    (target D : ℝ) / (damageMaximum target b : ℝ)
  rw [← Finset.sup'_eq_sup hne]
  rw [hDOpt]

/-- A common exact maximizer yields optimistic ratio one on the positive-target domain. -/
theorem optimistic_ratio_eq_one_of_common (source target : Finset V → ℕ)
    (b : ℕ) (D : Finset V) (hD : D.card = b)
    (hSource : source D = damageMaximum source b)
    (hTarget : target D = damageMaximum target b)
    (hPos : 0 < damageMaximum target b) :
    optimisticDamageRatio source target b = 1 := by
  let choices := ((Finset.univ : Finset V).powersetCard b).filter
    (fun E => source E = damageMaximum source b)
  have hMem : D ∈ choices :=
    Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ D, hD⟩, hSource⟩
  have hNum : choices.sup target = damageMaximum target b := by
    apply le_antisymm
    · exact Finset.sup_le fun E hE =>
        Finset.le_sup (f := target) (Finset.mem_filter.mp hE).1
    · exact hTarget.symm.trans_le (Finset.le_sup (f := target) hMem)
  have hd : (damageMaximum target b : ℝ) ≠ 0 := by exact_mod_cast hPos.ne'
  unfold optimisticDamageRatio
  change (↑(choices.sup target : ℕ) : ℝ) / (damageMaximum target b : ℝ) = 1
  rw [hNum, div_self hd]

end Optimistic

/-- All optimistic values out of NC on finite subcubic trees, with positivity
required for the selected target alone. -/
noncomputable def subcubicTreeOptimisticOutOfNC (b : ℕ) (pc : Bool) : Set ℝ :=
  {r | ∃ (V : Type) (f : Fintype V) (d : DecidableEq V)
      (H : SimpleGraph V) (a : DecidableRel H.Adj),
    letI := f
    letI := d
    letI := a
    let target := if pc then pcDamage H else lccDamage H
    H.IsTree ∧ H.maxDegree ≤ 3 ∧ b < Fintype.card V ∧
    0 < damageMaximum target b ∧ r = optimisticDamageRatio (ncDamage H) target b}

set_option maxHeartbeats 2000000 in
-- Elaborate the cardinality and reachability comparisons in one proof.
private theorem subcubic_tree_optimistic_out_of_nc_isGLB_zero
    (b : ℕ) (hb : 2 ≤ b) (pc : Bool) :
    IsGLB (subcubicTreeOptimisticOutOfNC b pc) 0 := by
  refine ⟨?_, ?_⟩
  · rintro r ⟨V, f, d, H, a, _, _, _, _, hr⟩
    let := f
    let := d
    let := a
    rw [hr]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro l hl
    by_contra! hn
    obtain ⟨q, _, hTree, hDeg, hcard, hPos, hSmall⟩ :=
      subcubic_tree_out_of_nc_arbitrarily_small b hb l hn
    let H := uniformHost b 1 q
    let target := if pc then pcDamage H else lccDamage H
    obtain ⟨D, hD, hNC, hAtt⟩ := optimistic_ratio_attained (ncDamage H) target b hcard.le
    have hVal : optimisticDamageRatio (ncDamage H) target b ∈
        subcubicTreeOptimisticOutOfNC b pc := by
      refine ⟨UniformVertex b 1 q, inferInstance, inferInstance, H, inferInstance,
        hTree, hDeg, hcard, ?_, rfl⟩
      cases pc
      · exact hPos.2.2
      · exact hPos.2.1
    have hLower := hl hVal
    rw [hAtt] at hLower
    have hUpper : damageRatio target b D < l := by
      cases pc
      · exact (hSmall D hD hNC).2
      · exact (hSmall D hD hNC).1
    exact hUpper.not_ge hLower

theorem subcubic_tree_optimistic_out_of_nc_infimum_zero
    (b : ℕ) (hb : 2 ≤ b) (pc : Bool) :
    sInf (subcubicTreeOptimisticOutOfNC b pc) = 0 := by
  have h := subcubic_tree_optimistic_out_of_nc_isGLB_zero b hb pc
  apply h.csInf_eq
  by_contra he
  have hl : (1 : ℝ) ∈ lowerBounds (subcubicTreeOptimisticOutOfNC b pc) :=
    fun x hx => (he ⟨x, hx⟩).elim
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (h.2 hl)

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem choose_two_support (q c : ℕ) :
    q * c ≤ c.choose 2 + (q + 1).choose 2 := by
  have h1 := twice_choose_two_add c
  have h2 := twice_choose_two_add (q + 1)
  have hnonneg : 0 ≤ ((c : ℤ) - q) * ((c : ℤ) - q - 1) := by
    by_cases h : (c : ℤ) ≤ q
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have he : (c : ℤ) ^ 2 + (q : ℤ) ^ 2 + q -
      (2 * (q : ℤ) * c + c) = ((c : ℤ) - q) * ((c : ℤ) - q - 1) := by ring
  have hi : 2 * (q * c : ℕ) + c + (q + 1) ≤ c ^ 2 + (q + 1) ^ 2 := by
    have hh : (↑(2 * (q * c) + c + (q + 1) : ℕ) : ℤ) ≤
        (↑(c ^ 2 + (q + 1) ^ 2 : ℕ) : ℤ) := by
      push_cast
      nlinarith only [he, hnonneg]
    exact_mod_cast hh
  omega

private theorem choose_two_support_eq (q c : ℕ) (hc : c = q ∨ c = q + 1) :
    q * c = c.choose 2 + (q + 1).choose 2 := by
  have hAdd : (q + 1).choose 2 = q + q.choose 2 := by
    rw [Nat.choose_succ_succ' q 1, Nat.choose_one_right]
  have hQ := twice_choose_two_add q
  rcases hc with rfl | rfl
  · rw [← pow_two]
    omega
  · rw [Nat.mul_add, Nat.mul_one, ← pow_two]
    omega

section BalancedProfiles

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the maximal feasible component count, positive sizes differing by at
most one give a common exact optimizer. This also allows fewer components
in the competing profiles. -/
theorem common_optimizer_of_balanced_maximal_profile
    (b m q : ℕ) (D : Finset V) (hD : D.card = b)
    (hCount : Fintype.card (survivorGraph G D).ConnectedComponent = m)
    (hm : 0 < m)
    (hSizes : ∀ C : (survivorGraph G D).ConnectedComponent,
      C.supp.toFinset.card = q ∨ C.supp.toFinset.card = q + 1)
    (hCap : ∀ E : Finset V, E.card = b →
      Fintype.card (survivorGraph G E).ConnectedComponent ≤ m) :
    ncDamage G D = damageMaximum (ncDamage G) b ∧
    pcDamage G D = damageMaximum (pcDamage G) b ∧
    lccDamage G D = damageMaximum (lccDamage G) b := by
  let s := Fintype.card V - b
  let size (E : Finset V) (C : (survivorGraph G E).ConnectedComponent) :=
    C.supp.toFinset.card
  let cost (E : Finset V) := ∑ C, (size E C).choose 2
  let M (E : Finset V) := (componentSizes G E).sup
  have total (E : Finset V) (hE : E.card = b) : ∑ C, size E C = s :=
    (sum_component_card (survivorGraph G E)).trans (by rw [survivor_card, hE])
  have hP (E : Finset V) : pcDamage G E = (Fintype.card V).choose 2 - cost E :=
    component_profile_score_formulas G E
  have hMax (E : Finset V) (C : (survivorGraph G E).ConnectedComponent) : size E C ≤ M E :=
    Multiset.le_sup (Multiset.mem_map.mpr ⟨C, Finset.mem_univ _, rfl⟩)
  have equalCost : q * s = cost D + m * (q + 1).choose 2 := by
    rw [← total D hD, Finset.mul_sum]
    have hConst : (∑ _C : (survivorGraph G D).ConnectedComponent, (q + 1).choose 2) =
        m * (q + 1).choose 2 := by simp [hCount]
    rw [← hConst]
    unfold cost
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ => choose_two_support_eq q (size D C) (hSizes C)
  have dominates (E : Finset V) (hE : E.card = b) :
      ncDamage G E ≤ ncDamage G D ∧ pcDamage G E ≤ pcDamage G D ∧
        lccDamage G E ≤ lccDamage G D := by
    have hc := hCap E hE
    have hCost : cost D ≤ cost E := by
      have hSupport : q * s ≤ cost E + m * (q + 1).choose 2 := by
        rw [← total E hE, Finset.mul_sum]
        calc
          _ ≤ ∑ C, ((size E C).choose 2 + (q + 1).choose 2) :=
            Finset.sum_le_sum fun C _ => choose_two_support q (size E C)
          _ = cost E + Fintype.card (survivorGraph G E).ConnectedComponent * (q + 1).choose 2 := by
            rw [Finset.sum_add_distrib]
            simp [cost]
          _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _
      omega
    have hM : M D ≤ M E := by
      have hUpper : s ≤ m * M E := by
        calc
          s = ∑ C, size E C := (total E hE).symm
          _ ≤ ∑ _C : (survivorGraph G E).ConnectedComponent, M E :=
            Finset.sum_le_sum fun C _ => hMax E C
          _ = _ * M E := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ hc
      apply Multiset.sup_le.mpr
      intro n hn
      obtain ⟨C, _, rfl⟩ := Multiset.mem_map.mp hn
      change size D C ≤ M E
      have baseSize (C' : (survivorGraph G D).ConnectedComponent) : q ≤ size D C' :=
        (hSizes C').elim (fun h => h.ge) (fun h => h.ge.trans' (Nat.le_succ q))
      rcases hSizes C with he | he
      · change size D C = q at he
        rw [he]
        have hLower : m * q ≤ s := by
          rw [← hCount, ← total D hD]
          simpa using (Finset.sum_le_sum (s := Finset.univ)
            (f := fun _ : (survivorGraph G D).ConnectedComponent => q) (g := size D)
            (fun C' _ => baseSize C'))
        exact (Nat.mul_le_mul_left_iff hm).mp (hLower.trans hUpper)
      · change size D C = q + 1 at he
        rw [he]
        have hLower : m * q < s := by
          rw [← hCount, ← total D hD]
          have hh : (∑ _C : (survivorGraph G D).ConnectedComponent, q) < ∑ C', size D C' :=
            Finset.sum_lt_sum (fun C' _ => baseSize C')
              ⟨C, Finset.mem_univ C, by rw [he]; exact Nat.lt_succ_self _⟩
          simpa using hh
        exact Nat.lt_of_mul_lt_mul_left (hLower.trans_le hUpper)
    refine ⟨?_, ?_, ?_⟩
    · rw [ncDamage, ncDamage, component_card_eq, component_card_eq, hCount]
      exact Nat.sub_le_sub_right hc 1
    · rw [hP E, hP D]
      exact Nat.sub_le_sub_left hCost _
    · exact Nat.sub_le_sub_left hM _
  exact ⟨(damageMaximum_eq_of_dominates (ncDamage G) b D hD (fun E hE => (dominates E hE).1)).symm,
    (damageMaximum_eq_of_dominates (pcDamage G) b D hD (fun E hE => (dominates E hE).2.1)).symm,
    (damageMaximum_eq_of_dominates (lccDamage G) b D hD (fun E hE => (dominates E hE).2.2)).symm⟩

end BalancedProfiles

end Ugurlu33528
