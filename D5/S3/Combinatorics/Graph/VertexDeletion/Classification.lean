/- GID: D5/S3/Combinatorics/Graph/VertexDeletion/Classification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/VertexDeletion/Classification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-budget classification of objective transfers involving NC. -/

import D5.S3.Combinatorics.Graph.VertexDeletion.DegreeBounds

/-! Fixed-budget classification of objective transfers involving NC. -/

set_option autoImplicit false
set_option linter.style.openClassical false

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section DegreeTwoOrder

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem two_neighbors_exhaust {a x y z : V} (hDegree : G.degree a ≤ 2)
    (hx : G.Adj a x) (hy : G.Adj a y) (hne : x ≠ y) (hz : G.Adj a z) :
    z = x ∨ z = y := by
  have hsub : ({x, y} : Finset V) ⊆ G.neighborFinset a := by
    simpa [Finset.insert_subset_iff, mem_neighborFinset] using And.intro hx hy
  have hcard : (G.neighborFinset a).card ≤ ({x, y} : Finset V).card := by
    rw [Finset.card_pair hne]
    exact hDegree
  have hmem : z ∈ ({x, y} : Finset V) := by
    rw [Finset.eq_of_subset_of_card_le hsub hcard]
    simpa only [mem_neighborFinset] using hz
  simpa using hmem

private theorem maximal_path_interior_neighbors {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hΔ : G.maxDegree ≤ 2) {i : ℕ}
    (hi₀ : 0 < i) (hi₁ : i < p.length) {z : V}
    (hz : G.Adj (p.getVert i) z) :
    z = p.getVert (i - 1) ∨ z = p.getVert (i + 1) := by
  have e := p.adj_getVert_succ (i := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at e
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro he
    have := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) he
    omega
  exact two_neighbors_exhaust G ((G.degree_le_maxDegree _).trans hΔ)
    e.symm (p.adj_getVert_succ hi₁) hne hz

/-- A finite connected graph of maximum degree at most two has a linear
ordering with all consecutive edges and with an optional closing edge. -/
private theorem degree_two_linear_order (hG : G.Connected) (hΔ : G.maxDegree ≤ 2) :
    ∃ (e : Fin (Fintype.card V) ≃ V) (closed : Prop), ∀ i j,
      G.Adj (e i) (e j) ↔
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∨
        (closed ∧ ((i.val = 0 ∧ j.val + 1 = Fintype.card V) ∨
          (j.val = 0 ∧ i.val + 1 = Fintype.card V))) := by
  have := hG.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have no_start {z : V} (hz : z ∉ p.support) : ¬ G.Adj u z := by
    intro hadj
    have h := hmax z v (p.cons hadj.symm) ((Walk.cons_isPath_iff _ _).mpr ⟨hp, hz⟩)
    rw [Walk.length_cons] at h
    omega
  have no_end {z : V} (hz : z ∉ p.support) : ¬ G.Adj v z := by
    intro hadj
    have hz' : z ∉ p.reverse.support := by simpa [Walk.support_reverse] using hz
    have h := hmax z u (p.reverse.cons hadj.symm)
      ((Walk.cons_isPath_iff _ _).mpr ⟨hp.reverse, hz'⟩)
    rw [Walk.length_cons, Walk.length_reverse] at h
    omega
  have all_mem (z : V) : z ∈ p.support := by
    by_contra hz
    obtain ⟨w⟩ := hG u z
    obtain ⟨d, _, hd₁, hd₂⟩ := w.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support hz
    obtain ⟨i, he, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hd₁
    have hadj : G.Adj (p.getVert i) d.snd := he.symm ▸ d.adj
    by_cases h0 : i = 0
    · exact no_start hd₂ (by simpa [h0] using hadj)
    by_cases hlast : i = p.length
    · exact no_end hd₂ (by simpa [hlast] using hadj)
    obtain he | he := maximal_path_interior_neighbors G p hp hΔ (by omega) (by omega) hadj
    · exact hd₂ (he ▸ p.getVert_mem_support _)
    · exact hd₂ (he ▸ p.getVert_mem_support _)
  have hlen : p.support.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hp.support_nodup]
    have he : p.support.toFinset = Finset.univ := Finset.eq_univ_of_forall (by simpa using all_mem)
    rw [he, Finset.card_univ]
  let e : Fin (Fintype.card V) ≃ V :=
    (finCongr hlen.symm).trans
      (Equiv.ofBijective p.support.get ⟨fun a z he => Fin.ext (hp.support_nodup.getElem_inj_iff.mp he),
        fun z => List.mem_iff_get.mp (all_mem z)⟩)
  have he (i : Fin (Fintype.card V)) : e i = p.getVert i.val :=
    p.support_getElem_eq_getVert (show i.val < p.support.length by rw [hlen]; exact i.isLt)
  have hn : p.length + 1 = Fintype.card V := p.length_support.symm.trans hlen
  have inj {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
      (hij : p.getVert i = p.getVert j) : i = j := hp.getVert_injOn hi hj hij
  refine ⟨e, G.Adj u v, fun i j => ?_⟩
  have hi := i.isLt
  have hj := j.isLt
  simp only [he]
  constructor
  · intro ha
    by_cases hi' : 0 < i.val ∧ i.val < p.length
    · left
      obtain h | h := maximal_path_interior_neighbors G p hp hΔ hi'.1 hi'.2 ha
      · exact Or.inr (by have := inj (by omega) (by omega) h; omega)
      · exact Or.inl (inj (by omega) (by omega) h).symm
    by_cases hj' : 0 < j.val ∧ j.val < p.length
    · left
      obtain h | h := maximal_path_interior_neighbors G p hp hΔ hj'.1 hj'.2 ha.symm
      · exact Or.inl (by have := inj (by omega) (by omega) h; omega)
      · exact Or.inr (inj (by omega) (by omega) h).symm
    have hne : i.val ≠ j.val := fun hij => ha.ne (congrArg p.getVert hij)
    have ends : (i.val = 0 ∧ j.val = p.length) ∨ (j.val = 0 ∧ i.val = p.length) := by omega
    right
    rcases ends with ⟨hi0, hjEnd⟩ | ⟨hj0, hiEnd⟩
    · exact ⟨by simpa [hi0, hjEnd] using ha, Or.inl ⟨hi0, by omega⟩⟩
    · exact ⟨by simpa [hj0, hiEnd] using ha.symm, Or.inr ⟨hj0, by omega⟩⟩
  · rintro ((h | h) | ⟨h, ⟨hi0, hjEnd⟩ | ⟨hj0, hiEnd⟩⟩)
    · rw [← h]
      exact p.adj_getVert_succ (by omega)
    · rw [← h]
      exact (p.adj_getVert_succ (by omega)).symm
    · rw [hi0, show j.val = p.length by omega, p.getVert_zero, p.getVert_length]
      exact h
    · rw [hj0, show i.val = p.length by omega, p.getVert_zero, p.getVert_length]
      exact h.symm

end DegreeTwoOrder

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private def runStart (q r i : ℕ) := (q + 1) * i + min i r

private def runSize (q r i : ℕ) := q + if i < r then 1 else 0

private theorem runStart_step (q r i : ℕ) :
    runStart q r (i + 1) = runStart q r i + runSize q r i + 1 := by
  unfold runStart runSize
  rw [Nat.mul_succ]
  split <;> omega

private theorem runStart_mono (q r : ℕ) : StrictMono (runStart q r) :=
  strictMono_nat_of_lt_succ fun i => by rw [runStart_step]; omega

private theorem sum_runSize (q r m : ℕ) :
    (∑ i : Fin m, runSize q r i.val) + m = runStart q r m := by
  induction m with
  | zero => simp [runStart]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, runStart_step, ← ih]
    simp only [Fin.val_castSucc, Fin.val_last]
    omega

section Runs

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
local notation "n" => Fintype.card V

private theorem balanced_run_cut (b m : ℕ) (hb : b < n)
    (hm : 0 < m) (hmS : m ≤ n - b)
    (e : Fin n ≃ V) (closed : Prop)
    (hEdge : ∀ i j, G.Adj (e i) (e j) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∨
      (closed ∧ ((i.val = 0 ∧ j.val + 1 = n) ∨
        (j.val = 0 ∧ i.val + 1 = n))))
    (hBudget : m ≤ b + 1) (hCloseBudget : closed → m ≤ b) :
    ∃ D : Finset V, D.card = b ∧
      Fintype.card (survivorGraph G D).ConnectedComponent = m ∧
      ∀ C : (survivorGraph G D).ConnectedComponent,
        C.supp.toFinset.card = (n - b) / m ∨ C.supp.toFinset.card = (n - b) / m + 1 := by
  let s := n - b
  let q := s / m
  let r := s % m
  have hq : 0 < q := Nat.div_pos hmS hm
  have hr : r < m := Nat.mod_lt _ hm
  have hStart : runStart q r m = s + m := by
    unfold runStart
    rw [Nat.add_mul, Nat.one_mul, min_eq_right hr.le]
    have h := Nat.div_add_mod s m
    change m * q + r = s at h
    rw [Nat.mul_comm q m]
    omega
  let W := Σ i : Fin m, Fin (runSize q r i.val)
  let index (w : W) : ℕ := runStart q r w.1.val + w.2.val
  have before_next (w : W) : index w + 1 < runStart q r (w.1.val + 1) := by
    have h := w.2.isLt
    rw [runStart_step]
    change runStart q r w.1.val + w.2.val + 1 < _
    omega
  have gap (a z : W) (h : a.1.val < z.1.val) : index a + 1 < index z := by
    exact (before_next a).trans_le
      (((runStart_mono q r).monotone (show a.1.val + 1 ≤ z.1.val by omega)).trans
        (Nat.le_add_right _ _))
  have in_range (w : W) : index w < n := by
    have h := (before_next w).trans_le
      ((runStart_mono q r).monotone (Nat.succ_le_of_lt w.1.isLt))
    rw [hStart] at h
    dsimp [s] at h
    omega
  have no_wrap (w : W) (hc : closed) : index w + 1 < n := by
    have h := (before_next w).trans_le
      ((runStart_mono q r).monotone (Nat.succ_le_of_lt w.1.isLt))
    rw [hStart] at h
    have hc' := hCloseBudget hc
    dsimp [s] at h
    omega
  let indexFin (w : W) : Fin n := ⟨index w, in_range w⟩
  let enc : W ↪ V := ⟨fun w => e (indexFin w), by
    intro a z he
    have hi := congrArg Fin.val (e.injective he)
    change index a = index z at hi
    have hAZ := gap a z
    have hZA := gap z a
    have h : a.1 = z.1 := Fin.ext (by omega)
    obtain ⟨i, ai⟩ := a
    obtain ⟨j, zi⟩ := z
    change i = j at h
    subst j
    change index ⟨i, ai⟩ = index ⟨i, zi⟩ at hi
    simp only [index] at hi
    rw [show ai = zi from Fin.ext (by omega)]⟩
  let R : Finset V := Finset.univ.map enc
  let D := Rᶜ
  have hR : R.card = s := by
    have hs := sum_runSize q r m
    rw [hStart] at hs
    simp only [R, Finset.card_map, Finset.card_univ, W, Fintype.card_sigma, Fintype.card_fin]
    omega
  have hD : D.card = b := by
    rw [Finset.card_compl, hR]
    omega
  let ev : W ≃ survivors D := Equiv.ofBijective
    (fun w => ⟨enc w, by simp [D, R, survivors]⟩) (by
      constructor
      · intro a z he
        exact enc.injective (congrArg Subtype.val he)
      · rintro ⟨v, hv⟩
        have hvR : v ∈ R := by simpa [D, survivors] using hv
        obtain ⟨w, _, h⟩ := Finset.mem_map.mp hvR
        exact ⟨w, Subtype.ext h⟩)
  let H := survivorGraph G D
  have ev_adj (a z : W) :
      H.Adj (ev a) (ev z) ↔ index a + 1 = index z ∨ index z + 1 = index a := by
    change G.Adj (e (indexFin a)) (e (indexFin z)) ↔ _
    rw [hEdge]
    refine ⟨?_, Or.inl⟩
    rintro (h | ⟨hc, h | h⟩)
    · exact h
    · exact False.elim ((Nat.ne_of_lt (no_wrap z hc)) h.2)
    · exact False.elim ((Nat.ne_of_lt (no_wrap a hc)) h.2)
  have same_index {a z : W} (ha : H.Adj (ev a) (ev z)) : a.1 = z.1 := by
    have hg := gap a z
    have hg' := gap z a
    have he := (ev_adj a z).mp ha
    exact Fin.ext (by omega)
  let label (v : survivors D) : Fin m := (ev.symm v).1
  have reach_label {v w : survivors D} (h : H.Reachable v w) : label v = label w := by
    have hh := (H.reachable_iff_reflTransGen v w).mp h
    clear h
    induction hh with
    | refl => rfl
    | @tail x y _ edge ih =>
      have hEq : label x = label y := same_index (a := ev.symm x) (z := ev.symm y)
        (by simpa only [Equiv.apply_symm_apply] using edge)
      exact ih.trans hEq
  have len_pos (i : Fin m) : 0 < runSize q r i.val :=
    hq.trans_le (Nat.le_add_right _ _)
  let first (i : Fin m) : W := ⟨i, ⟨0, len_pos i⟩⟩
  have reach_first (i : Fin m) (j : Fin (runSize q r i.val)) :
      H.Reachable (ev (first i)) (ev ⟨i, j⟩) := by
    have reach (j : ℕ) (hj : j < runSize q r i.val) :
        H.Reachable (ev (first i)) (ev ⟨i, ⟨j, hj⟩⟩) := by
      induction j with
      | zero => exact Reachable.rfl
      | succ j ih =>
        apply (ih (by omega)).trans
        apply Adj.reachable
        apply (ev_adj _ _).mpr
        exact Or.inl (by simp [index, Nat.add_assoc])
    exact reach j.val j.isLt
  let comp (i : Fin m) := H.connectedComponentMk (ev (first i))
  have comp_eq (w : W) : comp w.1 = H.connectedComponentMk (ev w) :=
    ConnectedComponent.sound (reach_first w.1 w.2)
  let components : Fin m ≃ H.ConnectedComponent := Equiv.ofBijective comp (by
    constructor
    · intro i j he
      have hp := reach_label (ConnectedComponent.exact he)
      simpa [label, first] using hp
    · intro C
      obtain ⟨v, rfl⟩ := Quot.mk_surjective C
      refine ⟨label v, ?_⟩
      change comp (label v) = H.connectedComponentMk v
      simpa [label] using comp_eq (ev.symm v))
  have component_size (i : Fin m) : (comp i).supp.toFinset.card = runSize q r i.val := by
    let E : Fin (runSize q r i.val) ≃ (comp i).supp := Equiv.ofBijective
      (fun j => ⟨ev ⟨i, j⟩, by simpa only [ConnectedComponent.mem_supp_iff] using (comp_eq ⟨i, j⟩).symm⟩) (by
        constructor
        · intro a z he
          have hw := ev.injective (congrArg Subtype.val he)
          exact eq_of_heq (Sigma.mk.inj_iff.mp hw).2
        · rintro ⟨v, hv⟩
          obtain ⟨⟨j, t⟩, rfl⟩ := ev.surjective v
          have h : comp j = comp i := (comp_eq ⟨j, t⟩).trans
            (by simpa only [ConnectedComponent.mem_supp_iff] using hv)
          have hji : j = i := components.injective h
          subst j
          exact ⟨t, rfl⟩)
    rw [Set.toFinset_card, ← Fintype.card_congr E, Fintype.card_fin]
  have hCard : Fintype.card H.ConnectedComponent = m := by
    rw [← Fintype.card_congr components, Fintype.card_fin]
  refine ⟨D, hD, hCard, fun C => ?_⟩
  obtain ⟨i, rfl⟩ := components.surjective C
  change (comp i).supp.toFinset.card = q ∨ (comp i).supp.toFinset.card = q + 1
  rw [component_size]
  unfold runSize
  split <;> omega

end Runs

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section DegreeTwoCommon

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
local notation "n" => Fintype.card V

/-- In a cycle, each positive survivor run starts immediately after a deletion. -/
private theorem closed_order_component_count (e : Fin n ≃ V) (hn : 0 < n)
    (hStep : ∀ (i j : Fin n), i.val + 1 = j.val → G.Adj (e i) (e j))
    (hWrap : G.Adj (e ⟨n - 1, by omega⟩) (e ⟨0, hn⟩))
    (D : Finset V) (hD : D.Nonempty) :
    Fintype.card (survivorGraph G D).ConnectedComponent ≤ D.card := by
  let H := survivorGraph G D
  let zero : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let next (i : Fin n) : Fin n := if hi : i.val + 1 < n then ⟨i.val + 1, hi⟩ else zero
  let inComp (C : H.ConnectedComponent) (i : Fin n) : Prop :=
    ∃ hi : e i ∉ D, H.connectedComponentMk ⟨e i, hi⟩ = C
  have extend {C : H.ConnectedComponent} {i j : Fin n}
      (h : inComp C i) (hj : e j ∉ D) (edge : G.Adj (e i) (e j)) : inComp C j := by
    obtain ⟨hi, he⟩ := h
    exact ⟨hj, (ConnectedComponent.connectedComponentMk_eq_of_adj
      (show H.Adj ⟨e j, hj⟩ ⟨e i, hi⟩ from edge.symm)).trans he⟩
  have start (C : H.ConnectedComponent) :
      ∃ i : Fin n, e i ∈ D ∧ inComp C (next i) := by
    have after {j : Fin n} (hj : 0 < j.val) (hc : inComp C j)
        (hpred : e ⟨j.val - 1, by have := j.isLt; omega⟩ ∈ D) :
        ∃ i : Fin n, e i ∈ D ∧ inComp C (next i) := by
      let p : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hp : p.val + 1 = j.val := by dsimp [p]; omega
      have he : next p = j := by
        simp only [next, hp, dite_eq_left j.isLt]
      exact ⟨p, hpred, he.symm ▸ hc⟩
    let S := Finset.univ.filter (inComp C)
    have hS : S.Nonempty := by
      obtain ⟨v, hv⟩ := C.nonempty_supp
      refine ⟨e.symm v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      obtain ⟨v, hv'⟩ := v
      rw [ConnectedComponent.mem_supp_iff] at hv
      simpa only [inComp, Equiv.apply_symm_apply] using
        (show ∃ hv'' : v ∉ D, H.connectedComponentMk ⟨v, hv''⟩ = C from ⟨hv', hv⟩)
    let j := S.min' hS
    have hj : inComp C j := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    by_cases hj0 : j.val = 0
    · have hZero : inComp C zero := (show j = zero from Fin.ext hj0) ▸ hj
      by_cases hl : e last ∈ D
      · have hNext : next last = zero := by
          have hNot : ¬ last.val + 1 < n := by dsimp [last]; omega
          simp [next, hNot]
        exact ⟨last, hl, hNext.symm ▸ hZero⟩
      · have hLast := extend hZero hl hWrap.symm
        obtain ⟨x, hx⟩ := hD
        let d := e.symm x
        have hd : e d ∈ D := by simpa [d] using hx
        have hdLast : d < last := by
          have hdLt := d.isLt
          have hne : d.val ≠ n - 1 := fun h => hl ((show d = last from Fin.ext h) ▸ hd)
          exact Fin.lt_def.mpr (by dsimp [last]; omega)
        let T := S.filter (fun i => d < i)
        have hT : T.Nonempty := ⟨last, Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLast⟩, hdLast⟩⟩
        let k := T.min' hT
        obtain ⟨hk, hdk⟩ := Finset.mem_filter.mp (Finset.min'_mem T hT)
        have hK := (Finset.mem_filter.mp hk).2
        have hlt : d.val < k.val := hdk
        have hk0 : 0 < k.val := by omega
        let p : Fin n := ⟨k.val - 1, by have := k.isLt; omega⟩
        have hp : p.val + 1 = k.val := by dsimp [p]; omega
        refine after hk0 hK ?_
        change e p ∈ D
        by_cases hdp : d = p
        · exact hdp ▸ hd
        by_contra hnD
        have hdp' : d < p := Fin.lt_def.mpr (by
          have hh : d.val ≠ p.val := fun h => hdp (Fin.ext h)
          omega)
        have hPc := extend hK hnD (hStep p k hp).symm
        have hpT : p ∈ T :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPc⟩, hdp'⟩
        exact (show ¬ k ≤ p from by
          change ¬ k.val ≤ p.val
          omega) (Finset.min'_le T p hpT)
    · have hjp : 0 < j.val := by omega
      let p : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hp : p.val + 1 = j.val := by dsimp [p]; omega
      refine after hjp hj ?_
      change e p ∈ D
      by_contra hnD
      have hPc := extend hj hnD (hStep p j hp).symm
      have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPc⟩
      exact (show ¬ j ≤ p from by change ¬ j.val ≤ p.val; omega) (Finset.min'_le S p hpS)
  choose f hfD hf using start
  let charge (C : H.ConnectedComponent) : D := ⟨e (f C), hfD C⟩
  have hinj : Function.Injective charge := by
    intro C E he
    have hfEq : f C = f E := e.injective (congrArg Subtype.val he)
    obtain ⟨hC, heC⟩ := hf C
    obtain ⟨hE, heE⟩ := hf E
    exact heC.symm.trans (heE ▸ congrArg H.connectedComponentMk
      (Subtype.ext (congrArg (fun i => e (next i)) hfEq)))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective charge hinj

set_option maxHeartbeats 1000000 in
/-- Connected graphs of maximum degree at most two admit a common exact
optimizer of NC, PC, and LCC at all registered budgets. -/
theorem degree_two_common_optimizer (hG : G.Connected) (hDeg : G.maxDegree ≤ 2)
    (b : ℕ) (hb : 2 ≤ b) (hn : b < n) :
    ∃ D : Finset V, D.card = b ∧
      ncDamage G D = damageMaximum (ncDamage G) b ∧
      pcDamage G D = damageMaximum (pcDamage G) b ∧
      lccDamage G D = damageMaximum (lccDamage G) b := by
  obtain ⟨e, closed, hEdge⟩ := degree_two_linear_order G hG hDeg
  let cap := if closed then b else b + 1
  let m := min (n - b) cap
  have hCapPos : 0 < cap := by
    by_cases hc : closed
    · simpa [cap, hc] using (show 0 < b by omega)
    · simp [cap, hc]
  have hm : 0 < m := lt_min (by omega) hCapPos
  have hmS : m ≤ n - b := min_le_left _ _
  have hmB : m ≤ b + 1 := (min_le_right _ _).trans (by by_cases hc : closed <;> simp [cap, hc])
  have hmC (hc : closed) : m ≤ b := (min_le_right _ _).trans (by simp [cap, hc])
  obtain ⟨D, hD, hCount, hSize⟩ := balanced_run_cut G b m hn hm hmS e closed hEdge hmB hmC
  refine ⟨D, hD, common_optimizer_of_balanced_maximal_profile G b m ((n - b) / m) D
    hD hCount hm hSize ?_⟩
  intro E hE
  have hs : Fintype.card (survivorGraph G E).ConnectedComponent ≤ n - b :=
    (Fintype.card_le_of_surjective (survivorGraph G E).connectedComponentMk
      (fun C => Quot.mk_surjective C)).trans_eq (by rw [survivor_card, hE])
  apply le_min hs
  by_cases hc : closed
  · have hn₀ : 0 < n := by omega
    have hne : E.Nonempty := Finset.card_pos.mp (by omega)
    let last : Fin n := ⟨n - 1, by omega⟩
    let zero : Fin n := ⟨0, hn₀⟩
    have hWrap : G.Adj (e last) (e zero) := (hEdge last zero).mpr
      (Or.inr ⟨hc, Or.inr ⟨rfl, by dsimp [last]; omega⟩⟩)
    have h := closed_order_component_count G e hn₀
      (fun i j he => (hEdge i j).mpr (Or.inl (Or.inl he)))
      hWrap E hne
    simpa [cap, hc, hE] using h
  · have h := nc_le_budget_mul_degree_sub_one G hG 2 hDeg b E hE
    rw [ncDamage, component_card_eq] at h
    simp only [cap, ite_eq_right hc]
    omega

/-- The optimistic value is one in every ordered pair of score directions,
with positivity of the chosen target optimum. -/
theorem degree_two_optimistic_transfers_eq_one (hG : G.Connected) (hDeg : G.maxDegree ≤ 2)
    (b : ℕ) (hb : 2 ≤ b) (hn : b < n)
    (source target : Finset V → ℕ)
    (hs : source = ncDamage G ∨ source = pcDamage G ∨ source = lccDamage G)
    (ht : target = ncDamage G ∨ target = pcDamage G ∨ target = lccDamage G)
    (hPos : 0 < damageMaximum target b) :
    optimisticDamageRatio source target b = 1 := by
  obtain ⟨D, hD, hN, hP, hL⟩ := degree_two_common_optimizer G hG hDeg b hb hn
  have h (score : Finset V → ℕ)
      (hh : score = ncDamage G ∨ score = pcDamage G ∨ score = lccDamage G) :
      score D = damageMaximum score b := by
    rcases hh with rfl | rfl | rfl
    · exact hN
    · exact hP
    · exact hL
  exact optimistic_ratio_eq_one_of_common source target b D hD (h source hs) (h target ht) hPos

end DegreeTwoCommon

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph

/-- An attained maximum over deletions of exactly the prescribed cardinality. -/
def ExactOptimizer {V : Type*} [DecidableEq V] [Fintype V]
    (score : Finset V → ℕ) (b : ℕ) (D : Finset V) : Prop :=
  D.card = b ∧ score D = damageMaximum score b

/-- The four NC directions at one fixed budget. The order and positivity
conditions precede the ratios on each graph class. -/
theorem result (b : ℕ) (hb : 2 ≤ b) :
    (∀ ε : ℝ, 0 < ε →
      ∃ k q : ℕ, 1 ≤ k ∧ 2 * b * (k + 2) ≤ q ∧
        (let H := uniformHost b k q
         H.IsTree ∧ b < Fintype.card (UniformVertex b k q) ∧
         0 < damageMaximum (ncDamage H) b ∧
         0 < damageMaximum (pcDamage H) b ∧
         0 < damageMaximum (lccDamage H) b ∧
         ∀ Dn Dp Dl : Finset (UniformVertex b k q),
           ExactOptimizer (ncDamage H) b Dn →
           ExactOptimizer (pcDamage H) b Dp →
           ExactOptimizer (lccDamage H) b Dl →
           damageRatio (ncDamage H) b Dp < ε ∧ damageRatio (ncDamage H) b Dl < ε ∧
           damageRatio (pcDamage H) b Dn < ε ∧ damageRatio (lccDamage H) b Dn < ε)) ∧
    (∀ {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (Δ : ℕ), G.Connected → b < Fintype.card V →
      3 ≤ Δ → G.maxDegree ≤ Δ → 0 < damageMaximum (ncDamage G) b →
      (∀ D : Finset V, ExactOptimizer (pcDamage G) b D →
        1 / (↑(b * (Δ - 1)) : ℝ) ≤ damageRatio (ncDamage G) b D) ∧
      (∀ D : Finset V, ExactOptimizer (lccDamage G) b D →
        1 / (↑(b * (Δ - 1)) : ℝ) ≤ damageRatio (ncDamage G) b D)) ∧
    (∀ pc : Bool, sInf (subcubicTreeOptimisticOutOfNC b pc) = 0) ∧
    (∀ {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → G.maxDegree ≤ 2 → b < Fintype.card V →
      (∃ D : Finset V, ExactOptimizer (ncDamage G) b D ∧
        ExactOptimizer (pcDamage G) b D ∧ ExactOptimizer (lccDamage G) b D) ∧
      ∀ source target : Finset V → ℕ,
        (source = ncDamage G ∨ source = pcDamage G ∨ source = lccDamage G) →
        (target = ncDamage G ∨ target = pcDamage G ∨ target = lccDamage G) →
        0 < damageMaximum target b → optimisticDamageRatio source target b = 1) := by
  refine ⟨?_, ?_, subcubic_tree_optimistic_out_of_nc_infimum_zero b hb, ?_⟩
  · intro ε hε
    obtain ⟨k, q, hk, hq, hTree, hOrder, hPositive, hSmall⟩ :=
      uniform_tree_simultaneous_epsilon b hb ε hε
    refine ⟨k, q, hk, hq, hTree, hOrder, hPositive.1, hPositive.2.1, hPositive.2.2, ?_⟩
    intro Dn Dp Dl hn hp hl
    obtain ⟨hpn, hln, hnl, hnp⟩ := hSmall Dn Dp Dl hn.1 hp.1 hl.1 hn.2 hp.2 hl.2
    exact ⟨hpn, hln, hnp, hnl⟩
  · intro V _ _ G _ Δ hG hOrder hΔ hDegree hPositive
    obtain ⟨hP, hL⟩ :=
      bounded_degree_transfers_into_nc G hG Δ hDegree b hOrder hPositive
    exact ⟨fun D hD => hP D hD.1 hD.2, fun D hD => hL D hD.1 hD.2⟩
  · intro V _ _ G _ hG hDegree hOrder
    obtain ⟨D, hD, hNC, hPC, hLCC⟩ := degree_two_common_optimizer G hG hDegree b hb hOrder
    exact ⟨⟨D, ⟨hD, hNC⟩, ⟨hD, hPC⟩, ⟨hD, hLCC⟩⟩,
      fun source target => degree_two_optimistic_transfers_eq_one G hG hDegree b hb hOrder
        source target⟩

end Ugurlu33528
