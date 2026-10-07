/- GID: D5/S3/Combinatorics/Graph/CapacityPortParityAbsorption
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CapacityPortParityAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph]
   utility: none
   digest: Actual capacity-port components, terminal counts and parity absorption. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption

noncomputable section

open scoped BigOperators
open SimpleGraph

universe u w

variable {V : Type u} {E : Type w}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def endpoint (src dst : E → V) (e : E) (b : Bool) : V :=
  if b then dst e else src e

def degree (src dst : E → V) (v : V) : ℕ :=
  Fintype.card {x : E × Bool // endpoint src dst x.1 x.2 = v}

def Leaf (src dst : E → V) (r : V → ℕ) (v : V) : Prop :=
  r v = 0 ∧ degree src dst v = 1

abbrev Port (src dst : E → V) (r : V → ℕ) :=
  (E × Bool) ⊕ Σ v : V, Fin (2 * r v - degree src dst v)

def portBase (src dst : E → V) (r : V → ℕ) : Port src dst r → V
  | Sum.inl x => endpoint src dst x.1 x.2
  | Sum.inr x => x.1

def realPort (src dst : E → V) (r : V → ℕ) (p : Port src dst r) : Prop :=
  ∃ e b, p = Sum.inl (e, b)

def slackPort (src dst : E → V) (r : V → ℕ) (p : Port src dst r) : Prop :=
  ∃ x, p = Sum.inr x

def lPort (src dst : E → V) (r : V → ℕ) (p : Port src dst r) : Prop :=
  realPort src dst r p ∧ Leaf src dst r (portBase src dst r p)

def rho (src dst : E → V) (r : V → ℕ) : Port src dst r → Port src dst r
  | Sum.inl (e, b) => Sum.inl (e, !b)
  | Sum.inr x => Sum.inr x

def portGraph (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r)
    (hσ : ∀ p, σ (σ p) = p) : SimpleGraph (Port src dst r) := by
  classical
  let adj : Port src dst r → Port src dst r → Prop := fun p q =>
    p ≠ q ∧ (q = rho src dst r p ∨ q = σ p)
  exact {
    Adj := adj
    symm := ⟨by
      intro p q hpq
      rcases hpq with ⟨hpq, hq⟩
      refine ⟨hpq.symm, ?_⟩
      rcases hq with hq | hq
      · left
        subst q
        cases p with
        | inl x =>
            cases x with
            | mk e b => cases b <;> rfl
        | inr x => rfl
      · right
        subst q
        rw [hσ]⟩
    loopless := ⟨by
      intro p hp
      exact hp.1 rfl⟩ }

def leafVertices (src dst : E → V) (r : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (Leaf src dst r)

def slackPorts (src dst : E → V) (r : V → ℕ) : Finset (Port src dst r) := by
  classical
  exact Finset.univ.filter (slackPort src dst r)

def lPorts (src dst : E → V) (r : V → ℕ) : Finset (Port src dst r) := by
  classical
  exact Finset.univ.filter (lPort src dst r)

def componentL (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p)
    (κ : (portGraph src dst r σ hσ).ConnectedComponent) : ℕ := by
  classical
  exact ((lPorts src dst r).filter (fun p => p ∈ κ.supp)).card

def componentH (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p)
    (κ : (portGraph src dst r σ hσ).ConnectedComponent) : ℕ := by
  classical
  exact ((slackPorts src dst r).filter (fun p => p ∈ κ.supp)).card

def componentLength (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p)
    (κ : (portGraph src dst r σ hσ).ConnectedComponent) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : E =>
    (portGraph src dst r σ hσ).connectedComponentMk (Sum.inl (e, false)) = κ)).card

def terminalPort (src dst : E → V) (r : V → ℕ) (p : Port src dst r) : Prop :=
  lPort src dst r p ∨ slackPort src dst r p

noncomputable def componentPathWitness (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p)
    (κ : (portGraph src dst r σ hσ).ConnectedComponent) : Prop := by
  classical
  let G := portGraph src dst r σ hσ
  exact ∃ p t : Port src dst r, ∃ w : G.Walk p t,
    w.IsPath ∧
    (∀ x, x ∈ κ.supp ↔ x ∈ w.support) ∧
    (∀ x y, x ∈ κ.supp → y ∈ κ.supp → G.Adj x y → s(x, y) ∈ w.edges) ∧
    p ≠ t ∧ terminalPort src dst r p ∧ terminalPort src dst r t ∧
    (∀ x, x ∈ κ.supp → terminalPort src dst r x → x = p ∨ x = t) ∧
    (∀ e, e ∈ (Finset.univ : Finset E) →
      e ∈ (Finset.univ.filter (fun e : E =>
        G.connectedComponentMk (Sum.inl (e, false)) = κ)) ↔
      s(Sum.inl (e, false), Sum.inl (e, true)) ∈ w.edges) ∧
    (w.edges.filter (fun z => ∃ e : E,
      z = s(Sum.inl (e, false), Sum.inl (e, true)))).length =
      componentLength src dst r σ hσ κ

def aCount (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p) : ℕ := by
  classical
  let G := portGraph src dst r σ hσ
  exact (Finset.univ.filter (fun κ : G.ConnectedComponent => componentL src dst r σ hσ κ = 2)).card

def bCount (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p) : ℕ := by
  classical
  let G := portGraph src dst r σ hσ
  exact (Finset.univ.filter (fun κ : G.ConnectedComponent => componentH src dst r σ hσ κ = 2)).card

def cCount (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p) : ℕ := by
  classical
  let G := portGraph src dst r σ hσ
  exact (Finset.univ.filter (fun κ : G.ConnectedComponent =>
    componentL src dst r σ hσ κ = 1 ∧ componentH src dst r σ hσ κ = 1)).card

def oddLLCount (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p) : ℕ := by
  classical
  let G := portGraph src dst r σ hσ
  exact (Finset.univ.filter (fun κ : G.ConnectedComponent =>
    componentL src dst r σ hσ κ = 2 ∧ Odd (componentLength src dst r σ hσ κ))).card

noncomputable def capacityPortClaim (src dst : E → V) (r : V → ℕ) (K₀ : ℕ)
    (σ : Port src dst r → Port src dst r)
    (hσ : ∀ p, σ (σ p) = p)
    (_hbase : ∀ p, portBase src dst r (σ p) = portBase src dst r p)
    (_hfix : ∀ p, σ p = p ↔ lPort src dst r p)
    (_hzero : ∀ v, r v = 0 → degree src dst v ≤ 1)
    (_hpos : ∀ v, 0 < r v → degree src dst v ≤ 2 * r v)
    (_hleaf : ∀ e, ¬ (Leaf src dst r (src e) ∧ Leaf src dst r (dst e)))
    (_hK : (leafVertices src dst r).card ≤ K₀) : Prop :=
  let G := portGraph src dst r σ hσ
  let ell := (leafVertices src dst r).card
  let C := Fintype.card E
  let R := ∑ v, r v
  let q : ℤ := (C : ℤ) - (R : ℤ)
  let D : ℤ := (R : ℤ) + (K₀ : ℤ)
  let a := aCount src dst r σ hσ
  let b := bCount src dst r σ hσ
  let c := cCount src dst r σ hσ
  let o := oddLLCount src dst r σ hσ
  (∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ +
      componentH src dst r σ hσ κ > 0 →
      componentPathWitness src dst r σ hσ κ) ∧
    ell = 2 * a + c ∧
    (Finset.sum Finset.univ (fun v => 2 * r v - degree src dst v)) = 2 * b + c ∧
    q = (a : ℤ) - (b : ℤ) ∧
    D ≥ 3 * q + 4 * (b : ℤ) + 2 * (c : ℤ) + (o : ℤ) ∧
    (∀ χ : V → Bool, (∀ e, χ (src e) ≠ χ (dst e)) →
      ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ = 2 →
        ∀ p t : Port src dst r,
          p ≠ t →
          p ∈ κ.supp → t ∈ κ.supp → lPort src dst r p → lPort src dst r t →
          (Odd (componentLength src dst r σ hσ κ) ↔
            χ (portBase src dst r p) ≠ χ (portBase src dst r t)))

def ActualCapacityPortParityAbsorption : Prop :=
  ∀ (V : Type u) (E : Type w) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (r : V → ℕ) (K₀ : ℕ)
    (σ : Port src dst r → Port src dst r),
    (hloop : ∀ e, src e ≠ dst e) →
    (hzero : ∀ v, r v = 0 → degree src dst v ≤ 1) →
    (hpos : ∀ v, 0 < r v → degree src dst v ≤ 2 * r v) →
    (hleaf : ∀ e, ¬ (Leaf src dst r (src e) ∧ Leaf src dst r (dst e))) →
    (hσ : ∀ p, σ (σ p) = p) →
    (hbase : ∀ p, portBase src dst r (σ p) = portBase src dst r p) →
    (hfix : ∀ p, σ p = p ↔ lPort src dst r p) →
    (hK : (leafVertices src dst r).card ≤ K₀) →
    capacityPortClaim src dst r K₀ σ hσ hbase hfix hzero hpos hleaf hK

set_option maxHeartbeats 1500000 in
-- Dependent port-graph elaboration and its finite fiber counts share one proof term.
theorem actual_capacity_port_parity_absorption : ActualCapacityPortParityAbsorption.{u,w} := by
  intro V E _ _ _ _ src dst r K₀ σ hloop hzero hpos hleaf hσ hbase hfix hK
  classical
  let P := Port src dst r
  let G := portGraph src dst r σ hσ
  let ρ := rho src dst r
  let T := terminalPort src dst r
  have hreal : ∀ e b, portBase src dst r (ρ (Sum.inl (e,b))) ≠
      portBase src dst r (Sum.inl (e,b)) := by
    intro e b
    cases b
    · simpa [ρ, rho, portBase, endpoint] using (hloop e).symm
    · simpa [ρ, rho, portBase, endpoint] using hloop e
  have hrhone : ∀ e b, ρ (Sum.inl (e,b)) ≠ Sum.inl (e,b) := by
    intro e b he
    exact hreal e b (congrArg (portBase src dst r) he)
  have hsep : ∀ e b, ρ (Sum.inl (e,b)) ≠ σ (Sum.inl (e,b)) := by
    intro e b he
    exact hreal e b ((congrArg (portBase src dst r) he).trans (hbase _))
  have hHnotL : ∀ x, ¬ lPort src dst r (Sum.inr x) := by
    intro x h
    rcases h.1 with ⟨e,b,h⟩
    cases h
  have hnL : ∀ p : P, lPort src dst r p → G.neighborSet p = {ρ p} := by
    intro p hp
    rcases hp.1 with ⟨e,b,rfl⟩
    have hs := (hfix _).2 hp
    ext q
    change (Sum.inl (e,b) ≠ q ∧ (q = ρ (Sum.inl (e,b)) ∨ q = σ (Sum.inl (e,b)))) ↔ _
    simp only [hs, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hne,h | h⟩
      · exact h
      · exact False.elim (hne h.symm)
    · intro h
      subst q
      exact ⟨(hrhone e b).symm, Or.inl rfl⟩
  have hnH : ∀ x, G.neighborSet (Sum.inr x) = {σ (Sum.inr x)} := by
    intro x
    have hs : σ (Sum.inr x) ≠ Sum.inr x := fun he => hHnotL x ((hfix _).1 he)
    ext q
    change (Sum.inr x ≠ q ∧ (q = Sum.inr x ∨ q = σ (Sum.inr x))) ↔ _
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hne,h | h⟩
      · exact False.elim (hne h.symm)
      · exact h
    · intro h
      subst q
      exact ⟨hs.symm, Or.inr rfl⟩
  have hnI : ∀ e b, ¬ lPort src dst r (Sum.inl (e,b)) →
      G.neighborSet (Sum.inl (e,b)) = {ρ (Sum.inl (e,b)), σ (Sum.inl (e,b))} := by
    intro e b hp
    have hs : σ (Sum.inl (e,b)) ≠ Sum.inl (e,b) := fun he => hp ((hfix _).1 he)
    ext q
    change (Sum.inl (e,b) ≠ q ∧ (q = ρ (Sum.inl (e,b)) ∨ q = σ (Sum.inl (e,b)))) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact And.right
    · rintro (h | h)
      · subst q; exact ⟨(hrhone e b).symm, Or.inl rfl⟩
      · subst q; exact ⟨hs.symm, Or.inr rfl⟩
  have hncard : ∀ p : P, (G.neighborSet p).ncard = if T p then 1 else 2 := by
    intro p
    cases p with
    | inr x =>
      have ht : T (Sum.inr x) := Or.inr ⟨x,rfl⟩
      simp [ht, hnH, T]
    | inl x =>
      rcases x with ⟨e,b⟩
      have hns : ¬ slackPort src dst r (Sum.inl (e,b)) := by
        rintro ⟨x,h⟩; cases h
      by_cases hl : lPort src dst r (Sum.inl (e,b))
      · have ht : T (Sum.inl (e,b)) := Or.inl hl
        rw [if_pos ht, hnL _ hl]; simp
      · have ht : ¬ T (Sum.inl (e,b)) := by simpa [T, terminalPort, hns] using hl
        rw [if_neg ht, hnI e b hl]
        simp [hsep e b]
  have hdegree : ∀ p : P, (G.neighborSet p).ncard ≤ 2 := by
    intro p
    rw [hncard]
    split_ifs <;> omega
  have hterminal : ∀ p : P, T p ↔ (G.neighborSet p).ncard = 1 := by
    intro p; rw [hncard]; split_ifs <;> simp_all
  have hpath : ∀ κ : G.ConnectedComponent, ∀ p : P,
      p ∈ κ.supp → T p →
      ∃ t : P, ∃ w : G.Walk p t, w.IsPath ∧ p ≠ t ∧
        (∀ x, x ∈ κ.supp ↔ x ∈ w.support) ∧
        (∀ x y, x ∈ κ.supp → G.Adj x y → w.toSubgraph.Adj x y) ∧
        T t ∧ (∀ x, x ∈ κ.supp → T x → x = p ∨ x = t) := by
    intro κ p hpk htp
    let A : ℕ → Prop := fun n => ∃ t : P, ∃ w : G.Walk p t, w.IsPath ∧ w.length = n
    have hA0 : A 0 := ⟨p, .nil, by simp, rfl⟩
    obtain ⟨t,w,hw,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card P)) hA0
    have hmax : ∀ t' (w' : G.Walk p t'), w'.IsPath → w'.length ≤ w.length := by
      intro t' w' hw'
      rw [hlen]
      exact Nat.le_findGreatest hw'.length_lt.le ⟨t',w',hw',rfl⟩
    have hncardp : (G.neighborSet p).ncard = 1 := (hterminal p).1 htp
    obtain ⟨z,hz⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (G.neighborSet p).ncard ≠ 0)
    change G.Adj p z at hz
    have hw1 : (Walk.cons hz (.nil : G.Walk z z)).IsPath := by
      simp [Walk.isPath_def, hz.ne]
    have hposw : 0 < w.length := by
      have hm := hmax z (.cons hz .nil) hw1
      have hm1 : 1 ≤ w.length := by simpa [Walk.length_cons, Walk.length_nil] using hm
      omega
    have hnon : ¬ w.Nil := Walk.not_nil_iff_lt_length.mpr hposw
    have hpt : p ≠ t := fun he => hnon (hw.nil_iff_eq.mpr he)
    have hstart : w.toSubgraph.neighborSet p = G.neighborSet p := by
      apply Set.eq_of_subset_of_ncard_le (w.toSubgraph.neighborSet_subset p)
      rw [hncardp, hw.neighborSet_toSubgraph_startpoint hnon]
      simp
    have hint : ∀ x, x ∈ w.support → x ≠ p → x ≠ t →
        w.toSubgraph.neighborSet x = G.neighborSet x := by
      intro x hx hxp hxt
      obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      have hi0 : i ≠ 0 := by intro he; subst i; simp at hi; exact hxp hi.symm
      have hilt : i < w.length := by
        by_contra he
        have heq : i = w.length := by omega
        subst i
        simp at hi
        exact hxt hi.symm
      subst x
      apply Set.eq_of_subset_of_ncard_le (w.toSubgraph.neighborSet_subset _)
      rw [hw.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt]
      exact hdegree _
    have hend : w.toSubgraph.neighborSet t = G.neighborSet t := by
      apply Set.Subset.antisymm (w.toSubgraph.neighborSet_subset t)
      intro x hx
      change G.Adj t x at hx
      have hxs : x ∈ w.support := by
        by_contra h
        have hc := hw.concat h hx
        have hm := hmax x (w.concat hx) hc
        rw [Walk.length_concat] at hm
        omega
      have hxt : x ≠ t := hx.ne.symm
      by_cases hxp : x = p
      · subst x
        have hp : t ∈ w.toSubgraph.neighborSet p := hstart.symm ▸ hx.symm
        exact (show w.toSubgraph.Adj p t from hp).symm
      · have hh := hint x hxs hxp hxt
        have htx : t ∈ w.toSubgraph.neighborSet x := hh.symm ▸ hx.symm
        exact (show w.toSubgraph.Adj x t from htx).symm
    have hsaturated : ∀ x, x ∈ w.support →
        w.toSubgraph.neighborSet x = G.neighborSet x := by
      intro x hx
      by_cases hxp : x = p
      · subst x; exact hstart
      by_cases hxt : x = t
      · subst x; exact hend
      exact hint x hx hxp hxt
    have hclosed : ∀ x ∈ w.toSubgraph.verts, ∀ y, G.Adj x y → w.toSubgraph.Adj x y := by
      intro x hx y hxy
      change y ∈ w.toSubgraph.neighborSet x
      rw [hsaturated x (w.mem_verts_toSubgraph.mp hx)]
      exact hxy
    obtain ⟨κ',hκ'⟩ := w.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
    have hκeq : κ' = κ :=
      ConnectedComponent.eq_of_common_vertex (hκ' ▸ w.start_mem_verts_toSubgraph) hpk
    subst κ'
    have hsupp : ∀ x, x ∈ κ.supp ↔ x ∈ w.support := by
      intro x
      rw [← hκ', w.mem_verts_toSubgraph]
    have htt : T t := by
      apply (hterminal t).2
      rw [← hend, hw.neighborSet_toSubgraph_endpoint hnon]
      simp
    refine ⟨t,w,hw,hpt,hsupp,?_,htt,?_⟩
    · intro x y hx hxy
      exact hclosed x (hκ'.symm ▸ hx) y hxy
    · intro x hx htx
      by_contra he
      have hxp : x ≠ p := fun heq => he (Or.inl heq)
      have hxt : x ≠ t := fun heq => he (Or.inr heq)
      obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp ((hsupp x).1 hx)
      have hi0 : i ≠ 0 := by intro he; subst i; simp at hi; exact hxp hi.symm
      have hilt : i < w.length := by
        by_contra he
        have heq : i = w.length := by omega
        subst i; simp at hi; exact hxt hi.symm
      have hc := hw.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      rw [hi, hint x ((hsupp x).1 hx) hxp hxt, (hterminal x).1 htx] at hc
      omega
  let μ : E → Sym2 P := fun e => s(Sum.inl (e,false), Sum.inl (e,true))
  have hμinj : Function.Injective μ := by
    intro e f hef
    rcases Sym2.eq_iff.mp hef with h | h
    · exact congrArg Prod.fst (Sum.inl.inj h.1)
    · have hb := congrArg Prod.snd (Sum.inl.inj h.1)
      cases hb
  have hρedge : ∀ e, G.Adj (Sum.inl (e,false)) (Sum.inl (e,true)) := by
    intro e
    exact ⟨by simp, Or.inl rfl⟩
  have hactual : ∀ κ : G.ConnectedComponent, ∀ p t : P, ∀ w : G.Walk p t,
      w.IsPath → (∀ x, x ∈ κ.supp ↔ x ∈ w.support) →
      (∀ x y, x ∈ κ.supp → G.Adj x y → w.toSubgraph.Adj x y) →
      (∀ e, G.connectedComponentMk (Sum.inl (e,false)) = κ ↔ μ e ∈ w.edges) ∧
      (w.edges.filter (fun z => ∃ e, z = μ e)).length = componentLength src dst r σ hσ κ := by
    intro κ p t w hw hs hc
    have hequiv : ∀ e, G.connectedComponentMk (Sum.inl (e,false)) = κ ↔ μ e ∈ w.edges := by
      intro e
      constructor
      · intro he
        apply Walk.adj_toSubgraph_iff_mem_edges.mp
        exact hc _ _ ((κ.mem_supp_iff _).2 he) (hρedge e)
      · intro he
        exact (κ.mem_supp_iff _).1 ((hs _).2 (w.fst_mem_support_of_mem_edges he))
    refine ⟨hequiv,?_⟩
    let F : Finset E := Finset.univ.filter (fun e => G.connectedComponentMk (Sum.inl (e,false)) = κ)
    have himage : F.image μ = w.edges.toFinset.filter (fun z => ∃ e, z = μ e) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset, F]
      constructor
      · rintro ⟨e,he,rfl⟩
        exact ⟨(hequiv e).1 he, ⟨e,rfl⟩⟩
      · rintro ⟨hz,e,rfl⟩
        exact ⟨e,(hequiv e).2 hz,rfl⟩
    have hn := List.toFinset_card_of_nodup (hw.isTrail.edges_nodup.filter (fun z => ∃ e, z = μ e))
    rw [← hn, ← List.filter_toFinset, ← himage, Finset.card_image_of_injective F hμinj]
    rfl
  have hcover : ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ +
      componentH src dst r σ hσ κ > 0 → componentPathWitness src dst r σ hσ κ := by
    intro κ hk
    have hex : ∃ p : P, p ∈ κ.supp ∧ T p := by
      have hcL : 0 < componentL src dst r σ hσ κ ∨ 0 < componentH src dst r σ hσ κ := by omega
      rcases hcL with hl | hh
      · obtain ⟨p,hp⟩ := Finset.card_pos.mp hl
        have hp' := Finset.mem_filter.mp hp
        exact ⟨p,hp'.2,Or.inl (Finset.mem_filter.mp hp'.1).2⟩
      · obtain ⟨p,hp⟩ := Finset.card_pos.mp hh
        have hp' := Finset.mem_filter.mp hp
        exact ⟨p,hp'.2,Or.inr (Finset.mem_filter.mp hp'.1).2⟩
    obtain ⟨p,hpk,htp⟩ := hex
    obtain ⟨t,w,hw,hpt,hs,hc,htt,he⟩ := hpath κ p hpk htp
    obtain ⟨ha,hcount⟩ := hactual κ p t w hw hs hc
    refine ⟨p,t,w,hw,hs,?_,hpt,htp,htt,he,?_,?_⟩
    · intro x y hx hy hxy
      exact Walk.adj_toSubgraph_iff_mem_edges.mp (hc x y hx hxy)
    · intro e
      simpa [μ] using ha e
    · simpa [μ] using hcount
  have hLH : ∀ p : P, ¬ (lPort src dst r p ∧ slackPort src dst r p) := by
    rintro p ⟨⟨⟨e,b,he⟩,hl⟩,⟨x,hx⟩⟩
    rw [he] at hx
    cases hx
  have hpart : ∀ κ : G.ConnectedComponent,
      componentL src dst r σ hσ κ + componentH src dst r σ hσ κ = 0 ∨
      componentL src dst r σ hσ κ + componentH src dst r σ hσ κ = 2 := by
    intro κ
    by_cases hh : componentL src dst r σ hσ κ + componentH src dst r σ hσ κ = 0
    · exact Or.inl hh
    right
    obtain ⟨p,t,w,hw,hs,hc,hpt,htp,htt,he,ha,hm⟩ := hcover κ (by omega)
    let FL := (lPorts src dst r).filter (fun x => x ∈ κ.supp)
    let FH := (slackPorts src dst r).filter (fun x => x ∈ κ.supp)
    have hd : Disjoint FL FH := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact hLH x ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2,
        (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2⟩
    have hu : FL ∪ FH = {p,t} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        lPorts, slackPorts, FL, FH, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨hx,hk⟩ | ⟨hx,hk⟩)
        · exact he x hk (Or.inl hx)
        · exact he x hk (Or.inr hx)
      · rintro (rfl | rfl)
        · rcases htp with hl | hh
          · exact Or.inl ⟨hl,(hs _).2 w.start_mem_support⟩
          · exact Or.inr ⟨hh,(hs _).2 w.start_mem_support⟩
        · rcases htt with hl | hh
          · exact Or.inl ⟨hl,(hs _).2 w.end_mem_support⟩
          · exact Or.inr ⟨hh,(hs _).2 w.end_mem_support⟩
    change FL.card + FH.card = 2
    rw [← Finset.card_union_of_disjoint hd, hu]
    simp [hpt]
  have hLunique : ∀ p q : P, lPort src dst r p → lPort src dst r q →
      portBase src dst r p = portBase src dst r q → p = q := by
    intro p q hp hq hb
    rcases hp.1 with ⟨e,b,rfl⟩
    rcases hq.1 with ⟨f,c,rfl⟩
    let v := endpoint src dst e b
    let I := {x : E × Bool // endpoint src dst x.1 x.2 = v}
    have hi : Fintype.card I = 1 := hp.2.2
    have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hi.le
    have heq := hsub.elim (⟨(e,b),rfl⟩ : I) (⟨(f,c),hb.symm⟩ : I)
    exact congrArg Sum.inl (congrArg Subtype.val heq)
  have hLcard : (lPorts src dst r).card = (leafVertices src dst r).card := by
    let f : {p : P // lPort src dst r p} → {v : V // Leaf src dst r v} :=
      fun p => ⟨portBase src dst r p,p.2.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro p q he
        apply Subtype.ext
        exact hLunique p q p.2 q.2 (congrArg Subtype.val he)
      · intro v
        have hi : Fintype.card {x : E × Bool // endpoint src dst x.1 x.2 = v.1} = 1 := v.2.2
        obtain ⟨x,hx⟩ := Fintype.card_eq_one_iff.mp hi
        refine ⟨⟨Sum.inl x.1,⟨⟨x.1.1,x.1.2,rfl⟩,?_⟩⟩,?_⟩
        · change Leaf src dst r (endpoint src dst x.1.1 x.1.2)
          rw [x.2]; exact v.2
        · apply Subtype.ext
          exact x.2
    have hh := Fintype.card_congr (Equiv.ofBijective f hf)
    simpa [Fintype.card_subtype, lPorts, leafVertices] using hh
  have hHcard : (slackPorts src dst r).card = ∑ v, (2*r v - degree src dst v) := by
    let f : (Σ v : V, Fin (2*r v - degree src dst v)) → {p : P // slackPort src dst r p} :=
      fun x => ⟨Sum.inr x,⟨x,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y h
        exact Sum.inr.inj (congrArg Subtype.val h)
      · rintro ⟨p,⟨x,rfl⟩⟩
        exact ⟨x,rfl⟩
    have hh := Fintype.card_congr (Equiv.ofBijective f hf)
    simpa [Fintype.card_subtype, Fintype.card_sigma, slackPorts] using hh.symm
  have hLf : (lPorts src dst r).card = ∑ κ : G.ConnectedComponent, componentL src dst r σ hσ κ := by
    have hf := Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk)
      (s := lPorts src dst r) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    simpa [componentL, ConnectedComponent.mem_supp_iff] using hf
  have hHf : (slackPorts src dst r).card =
      ∑ κ : G.ConnectedComponent, componentH src dst r σ hσ κ := by
    have hf := Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk)
      (s := slackPorts src dst r) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    simpa [componentH, ConnectedComponent.mem_supp_iff] using hf
  have hLrow : ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ =
      2 * (if componentL src dst r σ hσ κ = 2 then 1 else 0) +
      (if componentL src dst r σ hσ κ = 1 ∧ componentH src dst r σ hσ κ = 1 then 1 else 0) := by
    intro κ
    have hh := hpart κ
    split_ifs <;> omega
  have hHrow : ∀ κ : G.ConnectedComponent, componentH src dst r σ hσ κ =
      2 * (if componentH src dst r σ hσ κ = 2 then 1 else 0) +
      (if componentL src dst r σ hσ κ = 1 ∧ componentH src dst r σ hσ κ = 1 then 1 else 0) := by
    intro κ
    have hh := hpart κ
    split_ifs <;> omega
  have hell : (leafVertices src dst r).card = 2*aCount src dst r σ hσ + cCount src dst r σ hσ := by
    rw [← hLcard, hLf]
    rw [Finset.sum_congr rfl (fun κ _ => hLrow κ)]
    simp [Finset.sum_add_distrib, aCount, cCount, Finset.sum_ite, Nat.mul_comm]
    congr 2
  have hslack : (∑ v, (2*r v-degree src dst v)) =
      2*bCount src dst r σ hσ+cCount src dst r σ hσ := by
    rw [← hHcard, hHf]
    rw [Finset.sum_congr rfl (fun κ _ => hHrow κ)]
    simp [Finset.sum_add_distrib, bCount, cCount, Finset.sum_ite, Nat.mul_comm]
    congr 2
  have hdeg : (∑ v, degree src dst v) = 2 * Fintype.card E := by
    have hh := Finset.card_eq_sum_card_fiberwise (f := fun x : E × Bool => endpoint src dst x.1 x.2)
      (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    simpa [degree, Fintype.card_subtype, Fintype.card_prod, Nat.mul_comm] using hh.symm
  have hbalance : 2 * Fintype.card E + (∑ v, (2*r v-degree src dst v)) =
      (leafVertices src dst r).card + 2*(∑ v, r v) := by
    have hv : ∀ v, degree src dst v + (2*r v-degree src dst v) =
        (if Leaf src dst r v then 1 else 0) + 2*r v := by
      intro v
      by_cases hr : r v = 0
      · have hd := hzero v hr
        by_cases hleafv : Leaf src dst r v
        · simp only [if_pos hleafv, hr, mul_zero, zero_tsub, add_zero]
          exact hleafv.2
        · have hd0 : degree src dst v = 0 := by
            have hne : degree src dst v ≠ 1 := fun he => hleafv ⟨hr,he⟩
            omega
          simp [hd0,hr,hleafv]
      · have hd := hpos v (by omega)
        have hnl : ¬ Leaf src dst r v := fun h => hr h.1
        simp only [if_neg hnl, zero_add]
        omega
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun v _ => hv v)
    simpa [Finset.sum_add_distrib, hdeg, ← Finset.mul_sum, Finset.sum_ite, leafVertices] using hs
  have hq : (Fintype.card E : ℤ) - (∑ v, r v) =
      (aCount src dst r σ hσ : ℤ) - (bCount src dst r σ hσ : ℤ) := by
    have hh := hbalance
    rw [hell,hslack] at hh
    omega
  have hEreal : ∀ κ : G.ConnectedComponent, ∀ e b,
      (Sum.inl (e,b) : P) ∈ κ.supp → G.connectedComponentMk (Sum.inl (e,false)) = κ := by
    intro κ e b hp
    apply (κ.mem_supp_iff _).1
    cases b
    · exact hp
    · exact (κ.mem_supp_congr_adj (hρedge e)).2 hp
  have hLlength : ∀ κ : G.ConnectedComponent, 0 < componentL src dst r σ hσ κ →
      1 ≤ componentLength src dst r σ hσ κ := by
    intro κ hl
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hl
    have hp' := Finset.mem_filter.mp hp
    have hpl := (Finset.mem_filter.mp hp'.1).2
    rcases hpl.1 with ⟨e,b,rfl⟩
    have he := hEreal κ e b hp'.2
    apply Finset.card_pos.mpr
    exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ e,he⟩⟩
  have hLLlength : ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ = 2 →
      2 ≤ componentLength src dst r σ hσ κ := by
    intro κ hl
    obtain ⟨p,t,hpt,hF⟩ := Finset.card_eq_two.mp hl
    have hp : p ∈ (lPorts src dst r).filter (fun x => x ∈ κ.supp) := by rw [hF]; simp
    have ht : t ∈ (lPorts src dst r).filter (fun x => x ∈ κ.supp) := by rw [hF]; simp
    have hp' := Finset.mem_filter.mp hp
    have ht' := Finset.mem_filter.mp ht
    have hpl := (Finset.mem_filter.mp hp'.1).2
    have htl := (Finset.mem_filter.mp ht'.1).2
    rcases hpl.1 with ⟨e,b,rfl⟩
    rcases htl.1 with ⟨f,c,rfl⟩
    have hef : e ≠ f := by
      intro he
      subst f
      cases b <;> cases c
      · exact hpt rfl
      · exact hleaf e ⟨by simpa [portBase,endpoint] using hpl.2,
          by simpa [portBase,endpoint] using htl.2⟩
      · exact hleaf e ⟨by simpa [portBase,endpoint] using htl.2,
          by simpa [portBase,endpoint] using hpl.2⟩
      · exact hpt rfl
    let F : Finset E := Finset.univ.filter (fun e => G.connectedComponentMk (Sum.inl (e,false)) = κ)
    have he : e ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hEreal κ e b hp'.2⟩
    have hf : f ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hEreal κ f c ht'.2⟩
    have hsub : ({e,f} : Finset E) ⊆ F := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hh := Finset.card_le_card hsub
    simpa [hef,F,componentLength] using hh
  have hEf : Fintype.card E = ∑ κ : G.ConnectedComponent, componentLength src dst r σ hσ κ := by
    have hf := Finset.card_eq_sum_card_fiberwise
      (f := fun e : E => G.connectedComponentMk (Sum.inl (e,false)))
      (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    simpa [componentLength] using hf
  have hcostrow : ∀ κ : G.ConnectedComponent,
      2*(if componentL src dst r σ hσ κ = 2 then 1 else 0) +
      (if componentL src dst r σ hσ κ = 2 ∧ Odd (componentLength src dst r σ hσ κ) then 1 else 0) +
      (if componentL src dst r σ hσ κ = 1 ∧ componentH src dst r σ hσ κ = 1 then 1 else 0) ≤
      componentLength src dst r σ hσ κ := by
    intro κ
    have hll := hLLlength κ
    have hl := hLlength κ
    split_ifs with h2 ho h1
    all_goals try rcases ho with ⟨hoL,⟨n,hn⟩⟩
    all_goals try rcases h1 with ⟨h1L,h1H⟩
    all_goals omega
  have hC : 2*aCount src dst r σ hσ+oddLLCount src dst r σ hσ+cCount src dst r σ hσ ≤
      Fintype.card E := by
    rw [hEf]
    have hh := Finset.sum_le_sum (fun κ (_ : κ ∈ Finset.univ) => hcostrow κ)
    simpa [Finset.sum_add_distrib,← Finset.mul_sum,aCount,cCount,oddLLCount,
      Finset.sum_ite,Nat.mul_comm] using hh
  have hD : ((∑ v, r v : ℕ) : ℤ) + (K₀ : ℤ) ≥
      3*((Fintype.card E : ℤ)-(∑ v, r v)) + 4*(bCount src dst r σ hσ : ℤ) +
      2*(cCount src dst r σ hσ : ℤ)+(oddLLCount src dst r σ hσ : ℤ) := by
    have hh := hell
    omega
  have hparity : ∀ χ : V → Bool, (∀ e, χ (src e) ≠ χ (dst e)) →
      ∀ κ : G.ConnectedComponent, ∀ p t : P, ∀ w : G.Walk p t,
      w.IsPath → (∀ x, x ∈ κ.supp ↔ x ∈ w.support) →
      (∀ x y, x ∈ κ.supp → G.Adj x y → w.toSubgraph.Adj x y) →
      (Odd (componentLength src dst r σ hσ κ) ↔
        χ (portBase src dst r p) ≠ χ (portBase src dst r t)) := by
    intro χ hχ
    let Q : Sym2 P → Prop := fun z => ∃ e, z = μ e
    have hedge : ∀ p q : P, G.Adj p q →
        (Q s(p,q) ↔ χ (portBase src dst r p) ≠ χ (portBase src dst r q)) := by
      intro p q hpq
      constructor
      · rintro ⟨e,he⟩
        rcases Sym2.eq_iff.mp he with ⟨hp,hq⟩ | ⟨hp,hq⟩
        · subst p; subst q
          simpa [portBase,endpoint] using hχ e
        · subst p; subst q
          simpa [portBase,endpoint] using (hχ e).symm
      · intro hcolor
        rcases hpq with ⟨hne,hq | hq⟩
        · subst q
          cases p with
          | inl x =>
            rcases x with ⟨e,b⟩
            refine ⟨e,?_⟩
            cases b
            · rfl
            · exact Sym2.eq_swap
          | inr x => exact False.elim (hne rfl)
        · subst q
          exact False.elim (hcolor (congrArg χ (hbase p)).symm)
    have hwalk : ∀ p t : P, ∀ w : G.Walk p t,
        Odd ((w.edges.filter Q).length) ↔ χ (portBase src dst r p) ≠ χ (portBase src dst r t) := by
      intro p t w
      induction w with
      | nil => simp
      | @cons p q t hpq w ih =>
        have hc := hedge p q hpq
        by_cases hQ : Q s(p,q)
        · have hne := hc.1 hQ
          simp only [Walk.edges_cons, List.filter_cons, decide_eq_true_eq]
          rw [if_pos hQ, List.length_cons, Nat.odd_add_one, ih]
          cases hp : χ (portBase src dst r p) <;>
            cases hq : χ (portBase src dst r q) <;>
            cases ht : χ (portBase src dst r t) <;>
            simp only [hp,hq,ht] at hne ⊢ <;>
            first | exact False.elim (hne rfl) | decide
        · have heq : χ (portBase src dst r p) = χ (portBase src dst r q) := by
            by_contra hne
            exact hQ (hc.2 hne)
          simp only [Walk.edges_cons, List.filter_cons, decide_eq_true_eq]
          rw [if_neg hQ, ih, heq]
    intro κ p t w hw hs hc
    obtain ⟨_,hcount⟩ := hactual κ p t w hw hs hc
    rw [← hcount]
    exact hwalk p t w
  have hcolor : ∀ χ : V → Bool, (∀ e, χ (src e) ≠ χ (dst e)) →
      ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ = 2 →
        ∀ p t : P, p ≠ t → p ∈ κ.supp → t ∈ κ.supp →
          lPort src dst r p → lPort src dst r t →
          (Odd (componentLength src dst r σ hσ κ) ↔
        χ (portBase src dst r p) ≠ χ (portBase src dst r t)) := by
    intro χ hχ κ hll p t hpt hpk htk hpl htl
    obtain ⟨z,w,hw,hpz,hs,hc,htz,he⟩ := hpath κ p hpk (Or.inl hpl)
    have htz' : t = z := (he t htk (Or.inl htl)).resolve_left hpt.symm
    subst t
    exact hparity χ hχ κ p z w hw hs hc
  exact ⟨hcover,hell,hslack,hq,hD,hcolor⟩

end
end D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
