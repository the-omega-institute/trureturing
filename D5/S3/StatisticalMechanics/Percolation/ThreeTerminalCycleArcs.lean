/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCycleArcs
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalCycleArcs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed-edge interval cuts identify the full partition of a finite cycle with its three open arcs. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms

/-! Three open-arc events preserve every terminal connectivity relation. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalTriangleArms
set_option backward.isDefEq.respectTransparency.types false

/-- Consecutive vertices on an ordinary simple cycle of length `n+3`. -/
def next {n : ℕ} (e : Fin (n + 3)) : Fin (n + 3) :=
  if h : e.val+1 < n+3 then ⟨e.val+1,h⟩ else 0

/-- Each actual cycle edge has one coordinate; the last edge returns to zero. -/
def cycleEnds (n : ℕ) (e : Fin (n + 3)) : Fin (n + 3) × Fin (n + 3) := (e,next e)

private lemma next_ne {n : ℕ} (e : Fin (n + 3)) : e ≠ next e := by
  intro h
  unfold next at h
  split_ifs at h with hn
  · have hv := congrArg Fin.val h
    change e.val = e.val+1 at hv
    omega
  · have hv := congrArg Fin.val h
    change e.val = 0 at hv
    omega

private lemma cycle_adj {n : ℕ} (ω : Fin (n + 3) → Bool) (e : Fin (n + 3))
    (he : ω e = true) : (openGraph (cycleEnds n) ω).Adj e (next e) := by
  exact ⟨next_ne e,Or.inl ⟨e,he,rfl⟩⟩

/-- A forward arc uses precisely the edge coordinates in a half-open ordinal interval. -/
def arcSupport (n l r : ℕ) : Finset (Fin (n + 3)) :=
  Finset.univ.filter fun e => l ≤ e.val ∧ e.val < r

/-- The effective arc bit is open exactly when every actual edge of that arc is open. -/
def arcBit {n : ℕ} (ω : Fin (n + 3) → Bool) (l r : ℕ) : Bool :=
  decide (∀ e ∈ arcSupport n l r, ω e = true)

private lemma arcBit_iff {n : ℕ} (ω : Fin (n + 3) → Bool) (l r : ℕ) :
    arcBit ω l r = true ↔ ∀ e : Fin (n + 3), l ≤ e.val → e.val < r → ω e = true := by
  simp [arcBit,arcSupport]

private lemma forward_reachable {n : ℕ} (ω : Fin (n + 3) → Bool)
    (l r : Fin (n + 3)) (hlr : l.val ≤ r.val)
    (hopen : ∀ e : Fin (n + 3), l.val ≤ e.val → e.val < r.val → ω e = true) :
    (openGraph (cycleEnds n) ω).Reachable l r := by
  have hr : ∀ m : ℕ, ∀ hm : m < n+3, l.val ≤ m → m ≤ r.val →
      (openGraph (cycleEnds n) ω).Reachable l ⟨m,hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm hl _
      have he : l = ⟨0,hm⟩ := Fin.ext (by change l.val = 0; omega)
      subst l
      exact Reachable.rfl
    | succ m ih =>
      intro hm hl hmr
      by_cases he : l.val = m+1
      · have he' : l = ⟨m+1,hm⟩ := Fin.ext he
        subst l
        exact Reachable.rfl
      · have hm' : m < n+3 := by omega
        have hp := ih hm' (by omega) (by omega)
        have ha := cycle_adj ω (⟨m,hm'⟩ : Fin (n + 3))
          (hopen ⟨m,hm'⟩ (by change l.val ≤ m; omega) (by change m < r.val; omega))
        have hn : next (⟨m,hm'⟩ : Fin (n + 3)) = ⟨m+1,hm⟩ := by
          simp [next,hm]
        rw [hn] at ha
        exact hp.trans ha.reachable
  exact hr r.val r.isLt hlr le_rfl

private lemma closed_cut {n : ℕ} (ω : Fin (n + 3) → Bool)
    (e f : Fin (n + 3)) (hef : e.val < f.val) (he : ω e = false) (hf : ω f = false)
    {x y : Fin (n + 3)} (hxy : (openGraph (cycleEnds n) ω).Reachable x y) :
    (e.val < x.val ∧ x.val ≤ f.val) ↔ (e.val < y.val ∧ y.val ≤ f.val) := by
  have hadj : ∀ {x y : Fin (n + 3)}, (openGraph (cycleEnds n) ω).Adj x y →
      ((e.val < x.val ∧ x.val ≤ f.val) ↔ (e.val < y.val ∧ y.val ≤ f.val)) := by
    intro x y hh
    rcases hh.2 with ⟨i,hi,hends⟩ | ⟨i,hi,hends⟩
    all_goals
      have hie : i ≠ e := by intro h; simpa [h,he] using hi
      have hif : i ≠ f := by intro h; simpa [h,hf] using hi
      have hie' : i.val ≠ e.val := fun h => hie (Fin.ext h)
      have hif' : i.val ≠ f.val := fun h => hif (Fin.ext h)
      have hx := congrArg Prod.fst hends
      have hy := congrArg Prod.snd hends
      dsimp [cycleEnds] at hx hy
      subst_vars
      dsimp [next]
      split_ifs with hn
      · dsimp
        omega
      · simp only [Fin.val_zero]
        omega
  rcases hxy with ⟨p⟩
  induction p with
  | nil => rfl
  | cons h p ih => exact (hadj h).trans ih

/-- Two vertices of a finite cycle are connected exactly when one of their
complementary arcs is entirely open. The proof covers arbitrary configurations. -/
theorem cycle_reachable_iff {n : ℕ} (ω : Fin (n + 3) → Bool)
    (l r : Fin (n + 3)) (hlr : l.val < r.val) :
    (openGraph (cycleEnds n) ω).Reachable l r ↔
      (∀ e : Fin (n + 3), l.val ≤ e.val → e.val < r.val → ω e = true) ∨
      (∀ e : Fin (n + 3), e.val < l.val ∨ r.val ≤ e.val → ω e = true) := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    obtain ⟨⟨e,hle,her,he⟩,f,hf,hwf⟩ := hn
    have he' : ω e = false := Bool.eq_false_iff.mpr he
    have hf' : ω f = false := Bool.eq_false_iff.mpr hwf
    rcases hf with hf | hf
    · have hc := closed_cut ω f e (by omega) hf' he' h
      have hli : f.val < l.val ∧ l.val ≤ e.val := by omega
      exact (show ¬ (f.val < r.val ∧ r.val ≤ e.val) by omega) (hc.mp hli)
    · have hc := closed_cut ω e f (by omega) he' hf' h
      have hri : e.val < r.val ∧ r.val ≤ f.val := by omega
      exact (show ¬ (e.val < l.val ∧ l.val ≤ f.val) by omega) (hc.mpr hri)
  · rintro (h | h)
    · exact forward_reachable ω l r hlr.le h
    · let last : Fin (n + 3) := Fin.last (n + 2)
      have hr : (openGraph (cycleEnds n) ω).Reachable r last :=
        forward_reachable ω r last (by dsimp [last]; omega)
          (fun e hre _ => h e (Or.inr hre))
      have ha := cycle_adj ω last (h last (Or.inr (by dsimp [last]; omega)))
      have hn : next last = 0 := by simp [next,last]
      rw [hn] at ha
      have hl : (openGraph (cycleEnds n) ω).Reachable 0 l :=
        forward_reachable ω 0 l (by simp)
          (fun e _ hel => h e (Or.inl hel))
      exact (hr.trans (ha.reachable.trans hl)).symm

private lemma three_arcs {n : ℕ} (ω : Fin (n + 3) → Bool)
    (i j : Fin (n + 3)) (hi : 0 < i.val) (hij : i.val < j.val) :
    ((openGraph (cycleEnds n) ω).Reachable 0 i ↔
      arcBit ω 0 i.val = true ∨
        arcBit ω i.val j.val = true ∧ arcBit ω j.val (n + 3) = true) ∧
    ((openGraph (cycleEnds n) ω).Reachable i j ↔
      arcBit ω i.val j.val = true ∨
        arcBit ω 0 i.val = true ∧ arcBit ω j.val (n + 3) = true) ∧
    ((openGraph (cycleEnds n) ω).Reachable 0 j ↔
      arcBit ω j.val (n + 3) = true ∨
        arcBit ω 0 i.val = true ∧ arcBit ω i.val j.val = true) := by
  rw [cycle_reachable_iff ω 0 i (by simpa),
    cycle_reachable_iff ω i j hij,
    cycle_reachable_iff ω 0 j (by change 0 < j.val; omega)]
  simp only [arcBit_iff,Fin.val_zero]
  have hsplit : (∀ e : Fin (n + 3), i.val ≤ e.val → ω e = true) ↔
      (∀ e : Fin (n + 3), i.val ≤ e.val → e.val < j.val → ω e = true) ∧
      (∀ e : Fin (n + 3), j.val ≤ e.val → e.val < n+3 → ω e = true) := by
    constructor
    · intro h
      exact ⟨fun e hei _ => h e hei, fun e hej _ => h e (by omega)⟩
    · rintro ⟨h,h'⟩ e hei
      by_cases hej : e.val < j.val
      · exact h e hei hej
      · exact h' e (by omega) e.isLt
  have hsplit' : (∀ e : Fin (n + 3), 0 ≤ e.val → e.val < j.val → ω e = true) ↔
      (∀ e : Fin (n + 3), 0 ≤ e.val → e.val < i.val → ω e = true) ∧
      (∀ e : Fin (n + 3), i.val ≤ e.val → e.val < j.val → ω e = true) := by
    constructor
    · intro h
      exact ⟨fun e he hei => h e he (by omega),fun e _ hej => h e (by omega) hej⟩
    · rintro ⟨h,h'⟩ e he hej
      by_cases hei : e.val < i.val
      · exact h e he hei
      · exact h' e (by omega) hej
  have hcompl : (∀ e : Fin (n + 3), e.val < i.val ∨ j.val ≤ e.val → ω e = true) ↔
      (∀ e : Fin (n + 3), 0 ≤ e.val → e.val < i.val → ω e = true) ∧
      (∀ e : Fin (n + 3), j.val ≤ e.val → e.val < n+3 → ω e = true) := by
    constructor
    · intro h
      exact ⟨fun e _ hei => h e (Or.inl hei),fun e hej _ => h e (Or.inr hej)⟩
    · rintro ⟨h,h'⟩ e (hei | hej)
      · exact h e (by omega) hei
      · exact h' e hej e.isLt
  have hzero (r : Fin (n + 3)) :
      (∀ e : Fin (n + 3), e.val < 0 ∨ r.val ≤ e.val → ω e = true) ↔
      (∀ e : Fin (n + 3), r.val ≤ e.val → ω e = true) := by simp
  rw [hzero i,hzero j,hcompl,hsplit']
  have hlast : (∀ e : Fin (n + 3), j.val ≤ e.val → ω e = true) ↔
      (∀ e : Fin (n + 3), j.val ≤ e.val → e.val < n+3 → ω e = true) :=
    ⟨fun h e he _ => h e he,fun h e he => h e he e.isLt⟩
  rw [hsplit,hlast]
  tauto

theorem core_partition (p q r : Bool) :
    partition triangleArmsEnds 0 1 2 ![p,q,r,true,true,true] =
      if p || (q && r) then
        (if q || (p && r) then .all else .ab)
      else if q || (p && r) then .bc
      else if r || (p && q) then .ac else .separate := by
  rw [arms_partition]
  simp [Bool.and_comm]

/-- All three terminal relations, hence the whole five-mode partition, are
preserved by replacing the three arcs of an arbitrary-length simple cycle
with the corresponding three triangle bits. The pendant bits are constant open. -/
theorem cycle_partition {n : ℕ} (ω : Fin (n + 3) → Bool)
    (i j : Fin (n + 3)) (hi : 0 < i.val) (hij : i.val < j.val) :
    graphMode (openGraph (cycleEnds n) ω) 0 i j =
      partition triangleArmsEnds 0 1 2
        ![arcBit ω 0 i.val,arcBit ω i.val j.val,arcBit ω j.val (n + 3),true,true,true] := by
  classical
  obtain ⟨hab,hbc,hac⟩ := three_arcs ω i j hi hij
  rw [core_partition]
  simp only [graphMode,hab,hbc,hac,Bool.or_eq_true,Bool.and_eq_true]

private lemma map_reachable {U V : Type*} [Nonempty U] (H : SimpleGraph U)
    (f : U ↪ V) (x y : U) :
    (H.map f).Reachable (f x) (f y) ↔ H.Reachable x y := by
  classical
  have hleft (z : U) : Function.invFun f (f z) = z :=
    Function.leftInverse_invFun f.injective z
  let back : H.map f →g H := {
    toFun := Function.invFun f
    map_rel' := by
      intro a b hab
      rcases (SimpleGraph.map_adj f H a b).mp hab with ⟨a',b',h,rfl,rfl⟩
      simpa only [hleft] using h }
  constructor
  · intro h
    simpa only [back,RelHom.coeFn_mk,hleft] using h.map back
  · exact fun h => h.map (SimpleGraph.Embedding.map f H).toHom

private lemma openGraph_map {U V E : Type*} (ends : E → U × U)
    (ω : E → Bool) (f : U ↪ V) :
    openGraph (fun e => (f (ends e).1,f (ends e).2)) ω = (openGraph ends ω).map f := by
  ext a b
  simp only [openGraph,SimpleGraph.fromRel_adj,SimpleGraph.map_adj]
  constructor
  · rintro ⟨hne,⟨e,he,hab⟩ | ⟨e,he,hab⟩⟩
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      refine ⟨(ends e).1,(ends e).2,⟨?_,Or.inl ⟨e,he,by cases ends e; rfl⟩⟩,ha,hb⟩
      exact fun h => hne (ha.symm.trans ((congrArg f h).trans hb))
    · have hb := congrArg Prod.fst hab
      have ha := congrArg Prod.snd hab
      refine ⟨(ends e).2,(ends e).1,⟨?_,Or.inr ⟨e,he,by cases ends e; rfl⟩⟩,ha,hb⟩
      exact fun h => hne (ha.symm.trans ((congrArg f h).trans hb))
  · rintro ⟨x,y,⟨hne,⟨e,he,hab⟩ | ⟨e,he,hab⟩⟩,rfl,rfl⟩
    · refine ⟨f.injective.ne hne,Or.inl ⟨e,he,?_⟩⟩
      simpa only [hab] using congrArg (fun q : U × U => (f q.1,f q.2)) hab
    · refine ⟨f.injective.ne hne,Or.inr ⟨e,he,?_⟩⟩
      simpa only [hab] using congrArg (fun q : U × U => (f q.1,f q.2)) hab

/-- The coordinates of a genuine simple closed walk are distinct before its
final repeated vertex. -/
def cycleVertex {V : Type*} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) {n : ℕ} (hlen : p.length = n + 3) :
    Fin (n + 3) ↪ V where
  toFun e := p.getVert e.val
  inj' := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (by have := i.isLt; simp only [Set.mem_setOf_eq]; omega)
      (by have := j.isLt; simp only [Set.mem_setOf_eq]; omega) h

private lemma cycleVertex_next {V : Type*} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) {n : ℕ} (hlen : p.length = n + 3)
    (e : Fin (n + 3)) : cycleVertex p hp hlen (next e) = p.getVert (e.val+1) := by
  dsimp [cycleVertex,next]
  split_ifs with hn
  · rfl
  · have he : e.val+1 = p.length := by have := e.isLt; omega
    simp [he]

/-- For every actual simple closed walk, every ordered pair of distinct marked
vertices after its basepoint, and every edge configuration, the entire terminal
partition equals that of the triangle of its three all-open arc events. Extra
vertices of the ambient graph are isolated in this cycle-edge network. -/
theorem walk_cycle_partition {V : Type*} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) {n : ℕ} (hlen : p.length = n + 3)
    (ω : Fin (n + 3) → Bool) (i j : Fin (n + 3)) (hi : 0 < i.val) (hij : i.val < j.val) :
    graphMode (openGraph (fun e : Fin (n + 3) =>
      (p.getVert e.val,p.getVert (e.val+1))) ω) a (p.getVert i.val) (p.getVert j.val) =
      partition triangleArmsEnds 0 1 2
        ![arcBit ω 0 i.val,arcBit ω i.val j.val,arcBit ω j.val (n + 3),true,true,true] := by
  classical
  let f := cycleVertex p hp hlen
  have hends : (fun e : Fin (n + 3) => (p.getVert e.val,p.getVert (e.val+1))) =
      (fun e => (f ((cycleEnds n e).1),f ((cycleEnds n e).2))) := by
    funext e
    change (p.getVert e.val,p.getVert (e.val+1)) =
      (cycleVertex p hp hlen e,cycleVertex p hp hlen (next e))
    rw [cycleVertex_next]
    rfl
  rw [hends,openGraph_map]
  have hf0 : f 0 = a := by simp [f,cycleVertex]
  change graphMode ((openGraph (cycleEnds n) ω).map f) a (f i) (f j) = _
  rw [← hf0]
  have hmode : graphMode ((openGraph (cycleEnds n) ω).map f) (f 0) (f i) (f j) =
      graphMode (openGraph (cycleEnds n) ω) 0 i j := by
    simp only [graphMode,map_reachable]
    by_cases h₁ : (openGraph (cycleEnds n) ω).Reachable 0 i <;>
      by_cases h₂ : (openGraph (cycleEnds n) ω).Reachable i j <;>
      by_cases h₃ : (openGraph (cycleEnds n) ω).Reachable 0 j <;> simp_all
  rw [hmode]
  exact cycle_partition ω i j hi hij

/-- A simple cycle's edge coordinates biject with the graph's actual undirected
edge set whenever that graph consists exactly of the cycle's edges. -/
noncomputable def cycleEdgeEquiv {V : Type*} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) {n : ℕ} (hlen : p.length = n + 3)
    (hedges : G.edgeSet = p.edgeSet) : Fin (n + 3) ≃ G.edgeSet := by
  let f : Fin (n + 3) → G.edgeSet := fun e =>
    ⟨s(p.getVert e.val,p.getVert (e.val+1)),
      p.adj_getVert_succ (by have := e.isLt; omega)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    have hi : i.val < p.edges.length := by simpa only [Walk.length_edges,hlen] using i.isLt
    have hj : j.val < p.edges.length := by simpa only [Walk.length_edges,hlen] using j.isLt
    apply Fin.ext
    have hget : p.edges[i.val]'hi = p.edges[j.val]'hj := by
      simpa only [Walk.getElem_edges hi,Walk.getElem_edges hj] using congrArg Subtype.val h
    exact hp.isTrail.edges_nodup.getElem_inj_iff.mp hget
  · rintro ⟨e,he⟩
    have he' : e ∈ p.edges := by simpa only [hedges,Walk.mem_edgeSet] using he
    obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp he'
    refine ⟨⟨i,by simpa only [Walk.length_edges,hlen] using hi⟩,?_⟩
    apply Subtype.ext
    change s(p.getVert i,p.getVert (i+1)) = e
    rw [← Walk.getElem_edges hi]
    exact hei

/-- A graph consisting of one actual simple cycle has the complete five-mode
partition of its three open-arc bits, with the original graph-edge source type.
The graph may include isolated vertices outside the cycle. -/
theorem bond_cycle_partition {V : Type*} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) {n : ℕ} (hlen : p.length = n + 3)
    (hedges : G.edgeSet = p.edgeSet) (ω : G.edgeSet → Bool)
    (i j : Fin (n + 3)) (hi : 0 < i.val) (hij : i.val < j.val) :
    let ξ := fun e => ω (cycleEdgeEquiv p hp hlen hedges e)
    graphMode (bondGraph G ω) a (p.getVert i.val) (p.getVert j.val) =
      partition triangleArmsEnds 0 1 2
        ![arcBit ξ 0 i.val,arcBit ξ i.val j.val,arcBit ξ j.val (n + 3),true,true,true] := by
  classical
  let q := cycleEdgeEquiv p hp hlen hedges
  have hq (e : Fin (n + 3)) : (q e).val = s(p.getVert e.val,p.getVert (e.val+1)) := rfl
  have hgraph : bondGraph G ω = openGraph
      (fun e : Fin (n + 3) => (p.getVert e.val,p.getVert (e.val+1))) (fun e => ω (q e)) := by
    ext x y
    simp only [bondGraph,SimpleGraph.fromEdgeSet_adj,Set.mem_setOf_eq,
      openGraph,SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨⟨e,he,hω⟩,hne⟩
      obtain ⟨i,hie⟩ := q.surjective e
      have hval : s(p.getVert i.val,p.getVert (i.val+1)) = s(x,y) := by
        rw [← hq i,hie,he]
      rcases Sym2.eq_iff.mp hval with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨hne,Or.inl ⟨i,by simpa only [hie] using hω,Prod.ext hx hy⟩⟩
      · exact ⟨hne,Or.inr ⟨i,by simpa only [hie] using hω,Prod.ext hx hy⟩⟩
    · rintro ⟨hne,⟨i,hω,hends⟩ | ⟨i,hω,hends⟩⟩
      · refine ⟨⟨q i,?_,hω⟩,hne⟩
        rw [hq]
        have hx := congrArg Prod.fst hends
        have hy := congrArg Prod.snd hends
        simp only at hx hy
        rw [hx,hy]
      · refine ⟨⟨q i,?_,hω⟩,hne⟩
        rw [hq]
        have hy := congrArg Prod.fst hends
        have hx := congrArg Prod.snd hends
        simp only at hx hy
        rw [hx,hy,Sym2.eq_swap]
  dsimp only
  rw [hgraph]
  exact walk_cycle_partition p hp hlen (fun e => ω (q e)) i j hi hij

/-- Any three distinct marked vertices on a genuine simple cycle admit an
orientation and basepoint with strictly ordered, nonzero coordinates. The
chosen walk uses exactly the original undirected cycle edges. -/
theorem cycle_ordered_coordinates {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (a b c : V)
    (ha : a ∈ p.support) (hb : b ∈ p.support) (hc : c ∈ p.support)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ (q : G.Walk a a) (hq : q.IsCycle) (n : ℕ) (hlen : q.length = n + 3)
      (hedges : q.edgeSet = p.edgeSet) (i j : Fin (n + 3)),
      0 < i.val ∧ i.val < j.val ∧ q.getVert i.val = b ∧ q.getVert j.val = c := by
  classical
  let q := p.rotate a ha
  have hq : q.IsCycle := hp.rotate ha
  have heq : q.edgeSet = p.edgeSet := by
    ext e
    exact (p.rotate_edges a ha).perm.mem_iff
  have hb' : b ∈ q.support := by simpa only [q,Walk.mem_support_rotate_iff] using hb
  have hc' : c ∈ q.support := by simpa only [q,Walk.mem_support_rotate_iff] using hc
  obtain ⟨i,hib,hiL⟩ := Walk.mem_support_iff_exists_getVert.mp hb'
  obtain ⟨j,hjc,hjL⟩ := Walk.mem_support_iff_exists_getVert.mp hc'
  have hi0 : 0 < i := by
    by_contra h
    have he : i = 0 := by omega
    exact hab (by simpa only [he,Walk.getVert_zero] using hib)
  have hj0 : 0 < j := by
    by_contra h
    have he : j = 0 := by omega
    exact hac (by simpa only [he,Walk.getVert_zero] using hjc)
  have hiLt : i < q.length := by
    by_contra h
    have he : i = q.length := by omega
    exact hab (by simpa only [he,Walk.getVert_length] using hib)
  have hjLt : j < q.length := by
    by_contra h
    have he : j = q.length := by omega
    exact hac (by simpa only [he,Walk.getVert_length] using hjc)
  have hij : i ≠ j := by
    intro he
    exact hbc (hib.symm.trans (by simpa only [he] using hjc))
  let n := q.length - 3
  have hlen : q.length = n + 3 := by
    have := hq.three_le_length
    dsimp [n]
    omega
  by_cases hlt : i < j
  · exact ⟨q,hq,n,hlen,heq,⟨i,by omega⟩,⟨j,by omega⟩,hi0,hlt,hib,hjc⟩
  · have hrev : q.reverse.length = n + 3 := by simpa only [Walk.length_reverse] using hlen
    have herev : q.reverse.edgeSet = p.edgeSet := q.edgeSet_reverse.trans heq
    refine ⟨q.reverse,hq.reverse,n,hrev,herev,
      ⟨q.length-i,by omega⟩,⟨q.length-j,by omega⟩,by dsimp; omega,by dsimp; omega,?_,?_⟩
    · change q.reverse.getVert (q.length-i) = b
      rw [Walk.getVert_reverse,show q.length-(q.length-i) = i by omega]
      exact hib
    · change q.reverse.getVert (q.length-j) = c
      rw [Walk.getVert_reverse,show q.length-(q.length-j) = j by omega]
      exact hjc

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycle_reachable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_reachable_iff

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycle_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_partition


/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.walk_cycle_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_cycle_partition

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.bond_cycle_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bond_cycle_partition

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.core_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms core_partition

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycle_ordered_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_ordered_coordinates

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
