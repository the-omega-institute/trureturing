/- GID: D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Original multigraph distances control capacity-port absorption without a supplied routing. -/

import D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption

noncomputable section

open scoped BigOperators
open SimpleGraph
open D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption

universe u w

variable {V : Type u} {E : Type w}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Adjacency forgets edge multiplicity, while incidence degrees and edge counts retain it. -/
def originalGraph (src dst : E → V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v t => ∃ e, src e = v ∧ dst e = t)

omit [Fintype V] in
private theorem port_walk_edist (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p)
    (hloop : ∀ e, src e ≠ dst e)
    (hbase : ∀ p, portBase src dst r (σ p) = portBase src dst r p)
    {p t : Port src dst r} (w : (portGraph src dst r σ hσ).Walk p t) :
    (originalGraph src dst).edist (portBase src dst r p) (portBase src dst r t) ≤
      ((w.edges.filter (fun z => ∃ e : E,
        z = s(Sum.inl (e, false), Sum.inl (e, true)))).length : ℕ∞) := by
  classical
  let Q : Sym2 (Port src dst r) → Prop := fun z =>
    ∃ e : E, z = s(Sum.inl (e, false), Sum.inl (e, true))
  change _ ≤ ((w.edges.filter Q).length : ℕ∞)
  induction w with
  | nil => simp
  | @cons p q t hpq w ih =>
    by_cases hQ : Q s(p,q)
    · have hadj : (originalGraph src dst).Adj
          (portBase src dst r p) (portBase src dst r q) := by
        obtain ⟨e,he⟩ := hQ
        rcases Sym2.eq_iff.mp he with ⟨hp,hq⟩ | ⟨hp,hq⟩
        · subst p; subst q
          exact ⟨hloop e, Or.inl ⟨e,rfl,rfl⟩⟩
        · subst p; subst q
          exact ⟨(hloop e).symm, Or.inr ⟨e,rfl,rfl⟩⟩
      simp only [Walk.edges_cons, List.filter_cons, decide_eq_true_eq]
      rw [if_pos hQ, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ (originalGraph src dst).edist (portBase src dst r p)
            (portBase src dst r q) +
            (originalGraph src dst).edist (portBase src dst r q)
              (portBase src dst r t) := SimpleGraph.edist_triangle
        _ ≤ 1 + ((w.edges.filter Q).length : ℕ∞) :=
          add_le_add (by rw [edist_eq_one_iff_adj.mpr hadj]) ih
        _ = _ := add_comm _ _
    · have heq : portBase src dst r p = portBase src dst r q := by
        rcases hpq with ⟨hne,hq | hq⟩
        · subst q
          cases p with
          | inl x =>
            rcases x with ⟨e,b⟩
            exact False.elim (hQ ⟨e,by cases b <;> simp [rho, Sym2.eq_swap]⟩)
          | inr x => exact False.elim (hne rfl)
        · subst q
          exact (hbase p).symm
      simp only [Walk.edges_cons, List.filter_cons, decide_eq_true_eq]
      rw [if_neg hQ, heq]
      exact ih

private theorem ll_component_distance (src dst : E → V) (r : V → ℕ)
    (σ : Port src dst r → Port src dst r) (hσ : ∀ p, σ (σ p) = p)
    (hloop : ∀ e, src e ≠ dst e)
    (hbase : ∀ p, portBase src dst r (σ p) = portBase src dst r p)
    (κ : (portGraph src dst r σ hσ).ConnectedComponent)
    (hll : componentL src dst r σ hσ κ = 2)
    (hpath : componentPathWitness src dst r σ hσ κ) :
    ∃ v t : V, Leaf src dst r v ∧ Leaf src dst r t ∧ v ≠ t ∧
      (originalGraph src dst).Reachable v t ∧
      (originalGraph src dst).edist v t ≤ (componentLength src dst r σ hσ κ : ℕ∞) := by
  classical
  obtain ⟨p,t,w,hw,hs,hc,hpt,htp,htt,he,ha,hlen⟩ := hpath
  obtain ⟨x,y,hxy,hF⟩ := Finset.card_eq_two.mp hll
  have hx : x ∈ (lPorts src dst r).filter (fun z => z ∈ κ.supp) := by rw [hF]; simp
  have hy : y ∈ (lPorts src dst r).filter (fun z => z ∈ κ.supp) := by rw [hF]; simp
  have hxl := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hyl := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
  have hxe := he x (Finset.mem_filter.mp hx).2 (Or.inl hxl)
  have hye := he y (Finset.mem_filter.mp hy).2 (Or.inl hyl)
  have hends : lPort src dst r p ∧ lPort src dst r t := by
    rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact ⟨hxl,hyl⟩
    · exact ⟨hyl,hxl⟩
    · exact False.elim (hxy rfl)
  have hdistinct : portBase src dst r p ≠ portBase src dst r t := by
    intro hb
    rcases hends.1.1 with ⟨e,b,hp⟩
    rcases hends.2.1 with ⟨f,c,ht⟩
    subst p; subst t
    let I := {z : E × Bool // endpoint src dst z.1 z.2 = endpoint src dst e b}
    have hi : Fintype.card I = 1 := hends.1.2.2
    have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hi.le
    have heq := hsub.elim (⟨(e,b),rfl⟩ : I) (⟨(f,c),hb.symm⟩ : I)
    exact hpt (congrArg Sum.inl (congrArg Subtype.val heq))
  have hd := port_walk_edist src dst r σ hσ hloop hbase w
  rw [hlen] at hd
  refine ⟨portBase src dst r p,portBase src dst r t,
    hends.1.2,hends.2.2,hdistinct,?_,hd⟩
  apply reachable_of_edist_ne_top
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd

omit [Fintype V] [DecidableEq E] in
private theorem exists_routing [Finite V] (src dst : E → V) (r : V → ℕ)
    (hzero : ∀ v, r v = 0 → degree src dst v ≤ 1)
    (hpos : ∀ v, 0 < r v → degree src dst v ≤ 2 * r v) :
    ∃ σ : Port src dst r → Port src dst r,
      (∀ p, σ (σ p) = p) ∧
      (∀ p, portBase src dst r (σ p) = portBase src dst r p) ∧
      (∀ p, σ p = p ↔ lPort src dst r p) := by
  classical
  letI := Fintype.ofFinite V
  let P := Port src dst r
  let base : P → V := portBase src dst r
  let U : V → Set P := fun v => {p | base p = v}
  have hcard : ∀ v, Fintype.card (U v) = degree src dst v + (2 * r v - degree src dst v) := by
    intro v
    let eqv : U v ≃ {z : E × Bool // endpoint src dst z.1 z.2 = v} ⊕
        Fin (2 * r v - degree src dst v) :=
      Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaSubtype v))
    calc
      Fintype.card (U v) = Fintype.card
          ({z : E × Bool // endpoint src dst z.1 z.2 = v} ⊕
            Fin (2 * r v - degree src dst v)) := Fintype.card_congr eqv
      _ = Fintype.card {z : E × Bool // endpoint src dst z.1 z.2 = v} +
          Fintype.card (Fin (2 * r v - degree src dst v)) := Fintype.card_sum
      _ = _ := by rw [Fintype.card_fin]; rfl
  have hex : ∀ v : {v : V // 0 < r v},
      ∃ M : (⊤ : SimpleGraph P).Subgraph, M.verts = U v.val ∧ M.IsMatching := by
    intro v
    have hc : (⊤ : SimpleGraph P).IsClique (U v.val) := by
      intro p hp q hq hpq
      exact hpq
    have heven : Even (U v.val).ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, hcard]
      have hd := hpos v.val v.property
      exact ⟨r v.val, by omega⟩
    exact (hc.even_iff_exists_isMatching (Set.toFinite _)).mp heven
  choose M hMverts hMmatch using hex
  have hmem : ∀ (p : P) (hp : 0 < r (base p)), p ∈ (M ⟨base p,hp⟩).verts := by
    intro p hp
    rw [hMverts]
    rfl
  let mate : ∀ (p : P), 0 < r (base p) → P :=
    fun p hp => (hMmatch ⟨base p,hp⟩ (hmem p hp)).choose
  let σ : P → P := fun p => if hp : 0 < r (base p) then mate p hp else p
  have hedge : ∀ p hp, (M ⟨base p,hp⟩).Adj p (σ p) := by
    intro p hp
    dsimp only [σ]
    rw [dif_pos hp]
    exact (hMmatch ⟨base p,hp⟩ (hmem p hp)).choose_spec.1
  have hbase : ∀ p, base (σ p) = base p := by
    intro p
    by_cases hp : 0 < r (base p)
    · have hm := (hedge p hp).snd_mem
      rw [hMverts] at hm
      exact hm
    · simp only [σ, dif_neg hp]
  have hinvol : ∀ p, σ (σ p) = p := by
    intro p
    by_cases hp : 0 < r (base p)
    · have hp' : 0 < r (base (σ p)) := by rw [hbase]; exact hp
      have hi : (⟨base (σ p),hp'⟩ : {v : V // 0 < r v}) =
          ⟨base p,hp⟩ := Subtype.ext (hbase p)
      have he := hedge (σ p) hp'
      rw [hi] at he
      exact (hMmatch ⟨base p,hp⟩).eq_of_adj_left he (hedge p hp).symm
    · have he : σ p = p := by simp only [σ, dif_neg hp]
      rw [he,he]
  have hfix : ∀ p, σ p = p ↔ lPort src dst r p := by
    intro p
    constructor
    · intro he
      have hp : ¬ 0 < r (base p) := by
        intro hp
        exact (hedge p hp).ne he.symm
      have hr : r (base p) = 0 := by omega
      cases p with
      | inl z =>
        rcases z with ⟨e,b⟩
        have hd := hzero (base (Sum.inl (e,b))) hr
        have hdpos : 0 < degree src dst (base (Sum.inl (e,b))) :=
          Fintype.card_pos_iff.mpr ⟨⟨(e,b),rfl⟩⟩
        have hdscalar : degree src dst (endpoint src dst e b) = 1 := by
          change degree src dst (endpoint src dst e b) ≤ 1 at hd
          change 0 < degree src dst (endpoint src dst e b) at hdpos
          omega
        exact ⟨⟨e,b,rfl⟩,hr,hdscalar⟩
      | inr z =>
        rcases z with ⟨v,i⟩
        change r v = 0 at hr
        have hi := i.isLt
        omega
    · intro hp
      have hr : ¬ 0 < r (base p) := by
        have hz := hp.2.1
        change r (base p) = 0 at hz
        omega
      simp only [σ, dif_neg hr]
  exact ⟨σ,hinvol,hbase,hfix⟩

omit [DecidableEq E] in
/-- Separation in the original graph bounds the signed deficit and the rational absorbed mass.
If no two distinct leaves are connected, the signed deficit is nonpositive. -/
theorem actual_capacity_port_separation_absorption (src dst : E → V) (r : V → ℕ) (K : ℕ)
    (hloop : ∀ e, src e ≠ dst e)
    (hzero : ∀ v, r v = 0 → degree src dst v ≤ 1)
    (hpos : ∀ v, 0 < r v → degree src dst v ≤ 2 * r v)
    (hleaf : ∀ e, ¬ (Leaf src dst r (src e) ∧ Leaf src dst r (dst e)))
    (hK : (leafVertices src dst r).card ≤ K) :
    (∀ d : ℕ, 2 ≤ d →
      (∀ v t : V, Leaf src dst r v → Leaf src dst r t → v ≠ t →
        (originalGraph src dst).Reachable v t →
        (d : ℕ∞) ≤ (originalGraph src dst).edist v t) →
      (((∑ v, r v : ℕ) : ℤ) + (K : ℤ) ≥
          ((d : ℤ) + 1) * ((Fintype.card E : ℤ) - ((∑ v, r v : ℕ) : ℤ))) ∧
      (((d : ℚ) + 1) / ((d : ℚ) + 2)) * ((Fintype.card E : ℚ) + (K : ℚ)) ≤
        ((∑ v, r v : ℕ) : ℚ) + (K : ℚ)) ∧
    ((∀ v t : V, Leaf src dst r v → Leaf src dst r t → v ≠ t →
      ¬ (originalGraph src dst).Reachable v t) →
      (Fintype.card E : ℤ) - ((∑ v, r v : ℕ) : ℤ) ≤ 0) := by
  classical
  obtain ⟨σ,hσ,hbase,hfix⟩ := exists_routing src dst r hzero hpos
  have h := actual_capacity_port_parity_absorption V E src dst r K σ
    hloop hzero hpos hleaf hσ hbase hfix hK
  rcases h with ⟨hpath,hell,-,hq,-,-⟩
  let G := portGraph src dst r σ hσ
  have hLL : ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ = 2 →
      ∃ v t : V, Leaf src dst r v ∧ Leaf src dst r t ∧ v ≠ t ∧
        (originalGraph src dst).Reachable v t ∧
        (originalGraph src dst).edist v t ≤ (componentLength src dst r σ hσ κ : ℕ∞) := by
    intro κ hll
    exact ll_component_distance src dst r σ hσ hloop hbase κ hll
      (hpath κ (by rw [hll]; exact Nat.add_pos_left (by decide) _))
  constructor
  · intro d _hd hsep
    have hlength : ∀ κ : G.ConnectedComponent, componentL src dst r σ hσ κ = 2 →
        d ≤ componentLength src dst r σ hσ κ := by
      intro κ hll
      obtain ⟨v,t,hv,ht,hne,hr,he⟩ := hLL κ hll
      exact_mod_cast (hsep v t hv ht hne hr).trans he
    have hEf : Fintype.card E = ∑ κ : G.ConnectedComponent,
        componentLength src dst r σ hσ κ := by
      have hf := Finset.card_eq_sum_card_fiberwise
        (f := fun e : E => G.connectedComponentMk (Sum.inl (e,false)))
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      simpa [componentLength] using hf
    have hC : d * aCount src dst r σ hσ ≤ Fintype.card E := by
      rw [hEf]
      have hr : ∀ κ : G.ConnectedComponent,
          d * (if componentL src dst r σ hσ κ = 2 then 1 else 0) ≤
            componentLength src dst r σ hσ κ := by
        intro κ
        split_ifs with hll
        · simpa using hlength κ hll
        · simp
      have hh := Finset.sum_le_sum (fun κ (_ : κ ∈ Finset.univ) => hr κ)
      simpa [← Finset.mul_sum,aCount,Finset.sum_ite,Nat.mul_comm] using hh
    generalize ha : aCount src dst r σ hσ = a at hell hq hC
    generalize hb : bCount src dst r σ hσ = b at hq
    generalize hc : cCount src dst r σ hσ = c at hell
    clear ha hb hc
    have hCi : (d : ℤ) * (a : ℤ) ≤ (Fintype.card E : ℤ) := by
      exact_mod_cast hC
    have hKi : 2 * (a : ℤ) ≤ (K : ℤ) := by omega
    have hmain : ((∑ v, r v : ℕ) : ℤ) + (K : ℤ) ≥
        ((d : ℤ) + 1) * ((Fintype.card E : ℤ) - ((∑ v, r v : ℕ) : ℤ)) := by
      have hqle : (Fintype.card E : ℤ) - ((∑ v, r v : ℕ) : ℤ) ≤
          (a : ℤ) := by omega
      have hmul := mul_le_mul_of_nonneg_left hqle (by positivity : (0 : ℤ) ≤ (d : ℤ))
      nlinarith
    refine ⟨hmain,?_⟩
    have hrat : ((∑ v, r v : ℕ) : ℚ) + (K : ℚ) ≥
        ((d : ℚ) + 1) * ((Fintype.card E : ℚ) - ((∑ v, r v : ℕ) : ℚ)) := by
      exact_mod_cast hmain
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℚ) < (d : ℚ) + 2)]
    nlinarith
  · intro hnone
    have ha : aCount src dst r σ hσ = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro κ hk
      have hll := (Finset.mem_filter.mp hk).2
      obtain ⟨v,t,hv,ht,hne,hr,_⟩ := hLL κ hll
      exact hnone v t hv ht hne hr
    rw [ha, Nat.cast_zero, zero_sub] at hq
    rw [hq]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

end
end D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption
