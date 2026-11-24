/- GID: D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.claim; result=D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result; claim=D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.claim
   digest: Deleting the first edge of a rooted six-vertex path can destroy inherence. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.FinCases

/-! The rooted six-vertex path remains avoidable in every containing host.
Deleting its first edge lets a four-arm tree confine every copy. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace GurvichLeafRootEdgeDeletionRefutation

open SimpleGraph
open scoped Sym2

variable {V : Type} {G : SimpleGraph V} {n : ℕ}

private def Extension {H : SimpleGraph (Fin n)}
    (f : Copy H G) (s t : Fin n) (x y : V) : Prop :=
  x ∉ Set.range f ∧ y ∉ Set.range f ∧ x ≠ y ∧ G.Adj (f s) x ∧ G.Adj (f t) y

private def Avoidable {H : SimpleGraph (Fin n)} (f : Copy H G) (s t : Fin n) : Prop :=
  ∀ x y, (h : Extension f s t x y) →
    (G.induce (Set.range f)ᶜ).Reachable ⟨x, h.1⟩ ⟨y, h.2.1⟩

private def Inherent (H : SimpleGraph (Fin n)) (s t : Fin n) : Prop :=
  ∀ (m : ℕ) (G : SimpleGraph (Fin m)), Nonempty (Copy H G) → ∃ f : Copy H G, Avoidable f s t

/-- The complete finite statement of Gurvich–Krnc–Milanič–Vyalyi Conjecture 6.4. -/
public noncomputable def claim : Prop := by
  classical
  exact ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (s t u : Fin n),
    H.degree s ≤ H.degree t → s ≠ t → (∀ v, H.Adj s v ↔ v = u) → Inherent H s t →
      Inherent (H.deleteEdges {s(s, u)}) s t

private abbrev Path6 (G : SimpleGraph V) := Copy (pathGraph 6) G

private def pathOfSteps (f : Fin 6 → V) (hf : Function.Injective f)
    (steps : ∀ i : Fin 5, G.Adj (f i.castSucc) (f i.succ)) : Path6 G where
  toHom := {
    toFun := f
    map_rel' := by
      intro i j hij
      rcases pathGraph_adj.mp hij with h | h
      · let k : Fin 5 := ⟨i.val, by omega⟩
        have hi : k.castSucc = i := Fin.ext rfl
        have hj : k.succ = j := Fin.ext h
        simpa only [hi, hj] using steps k
      · let k : Fin 5 := ⟨j.val, by omega⟩
        have hj : k.castSucc = j := Fin.ext rfl
        have hi : k.succ = i := Fin.ext h
        simpa only [hi, hj] using (steps k).symm }
  injective' := hf

private theorem path_step (p : Path6 G) (i : Fin 5) : G.Adj (p i.castSucc) (p i.succ) :=
  p.toHom.map_rel (pathGraph_adj.mpr (Or.inl rfl))

private def reversePath (p : Path6 G) : Path6 G where
  toHom := {
    toFun := fun i => p i.rev
    map_rel' := by
      intro i j hij
      apply p.toHom.map_rel
      have h := pathGraph_adj.mp hij
      rw [pathGraph_adj, Fin.val_rev, Fin.val_rev]
      omega }
  injective' := p.injective.comp Fin.rev_injective

private theorem reverse_range (p : Path6 G) : Set.range (reversePath p) = Set.range p := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by change p i.rev.rev = p i; simp⟩

private def relist {k : ℕ} (p : Path6 G) (new : Fin k → V)
    (hnew : Function.Injective new) (hout : ∀ j, new j ∉ Set.range p)
    (order : Fin 6 ↪ Fin (6 + k))
    (steps : ∀ i : Fin 5, G.Adj (Fin.append p new (order i.castSucc))
      (Fin.append p new (order i.succ))) : Path6 G :=
  pathOfSteps ((Fin.append p new) ∘ order)
    ((Fin.append_injective_iff.mpr ⟨p.injective, hnew,
      fun i j h => hout j ⟨i, h⟩⟩).comp order.injective) steps

private def shift (p : Path6 G) (x : V) (hx : x ∉ Set.range p) (edge : G.Adj (p 5) x) :
    Path6 G :=
  relist p ![x] (Function.injective_of_subsingleton _) (fun j => by
    have : j = 0 := Subsingleton.elim _ _
    subst j
    exact hx)
    ⟨![1, 2, 3, 4, 5, 6], by decide⟩ (by
      intro i
      fin_cases i
      · exact path_step p 1
      · exact path_step p 2
      · exact path_step p 3
      · exact path_step p 4
      · exact edge)

private theorem shift_misses_first (p : Path6 G) (x : V) (hx : x ∉ Set.range p)
    (edge : G.Adj (p 5) x) : p 0 ∉ Set.range (shift p x hx edge) := by
  rintro ⟨i, hi⟩
  fin_cases i
  · exact (by decide : (1 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (2 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (3 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (4 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (5 : Fin 6) ≠ 0) (p.injective hi)
  · exact hx ⟨0, hi.symm⟩

private theorem simplicial_first (p : Path6 G)
    (h : ∀ x, G.Adj (p 0) x → x ∈ Set.range p) : Avoidable p 0 3 :=
  fun x _ e => (e.1 (h x e.2.2.2.1)).elim

private def Away (p : Path6 G) (U : Set V) : Prop := ∀ i, p i ∉ U

private def Boundary (G : SimpleGraph V) (U : Set V) (x : V) : Prop :=
  ∃ a ∈ U, G.Adj x a

private theorem connected_insert {U : Set V} {x a : V} (ha : a ∈ U) (e : G.Adj x a)
    (hU : (G.induce U).Connected) : (G.induce (insert x U)).Connected := by
  let j := (G.induceHomOfLE (Set.subset_insert x U)).toHom
  let anchor : (insert x U : Set V) := j ⟨a, ha⟩
  have toAnchor (v : (insert x U : Set V)) :
      (G.induce (insert x U)).Reachable v anchor := by
    rcases Set.mem_insert_iff.mp v.property with hv | hv
    · exact Adj.reachable (show G.Adj v.val a from hv.symm ▸ e)
    · exact (hU.preconnected ⟨v.val, hv⟩ ⟨a, ha⟩).map j
  exact { preconnected := fun v w => (toAnchor v).trans (toAnchor w).symm
          nonempty := ⟨anchor⟩ }

private theorem crossing_edge (hG : G.Preconnected) {U : Set V} {a b : V}
    (ha : a ∈ U) (hb : b ∉ U) : ∃ x ∈ U, ∃ y ∉ U, G.Adj x y := by
  classical
  by_contra! h
  obtain ⟨w⟩ := hG a b
  have stays {u v : V} (p : G.Walk u v) (hu : u ∈ U) : v ∈ U := by
    induction p with
    | nil => exact hu
    | @cons u v w e next ih =>
        apply ih
        by_contra hv
        exact h u hu v hv e
  exact hb (stays w ha)

private theorem shift_away (p : Path6 G) {U : Set V} (hp : Away p U)
    {x : V} (hx : x ∉ Set.range p) (hxU : x ∉ U) (e : G.Adj (p 5) x) :
    Away (shift p x hx e) U := by
  intro i
  fin_cases i
  · exact hp 1
  · exact hp 2
  · exact hp 3
  · exact hp 4
  · exact hp 5
  · exact hxU

private theorem shift_at (p : Path6 G) {x : V} (hx : x ∉ Set.range p)
    (e : G.Adj (p 5) x) (i : Fin 5) : shift p x hx e i.castSucc = p i.succ := by
  fin_cases i <;> rfl

private theorem outer_endpoints {U : Set V}
    (external : ∀ p : Path6 G, ∃ x ∉ Set.range p, G.Adj (p 0) x)
    (hits : ∀ p : Path6 G, Away p U → ∀ x ∉ U, Boundary G U x → x ∈ Set.range p)
    (p : Path6 G) (hp : Away p U) (hfirst : Boundary G U (p 0)) :
    Boundary G U (p 5) ∧ ∀ x ∉ Set.range p, G.Adj (p 5) x → x ∈ U := by
  classical
  have force (x : V) (hx : x ∉ Set.range p) (edge : G.Adj (p 5) x) : x ∈ U := by
    by_contra hxU
    exact shift_misses_first p x hx edge
      (hits _ (shift_away p hp hx hxU edge) (p 0) (hp 0) hfirst)
  obtain ⟨x, hx, e⟩ := external (reversePath p)
  rw [reverse_range] at hx
  exact ⟨⟨x, force x hx e, e⟩, force⟩

private theorem exists_outer {U : Set V}
    (external : ∀ p : Path6 G, ∃ x ∉ Set.range p, G.Adj (p 0) x)
    (hits : ∀ p : Path6 G, Away p U → ∀ x ∉ U, Boundary G U x → x ∈ Set.range p)
    (p : Path6 G) (hp : Away p U) {b : V} (hb : b ∉ U) (hbB : Boundary G U b) :
    ∃ q : Path6 G, Away q U ∧ Boundary G U (q 0) ∧ Boundary G U (q 5) := by
  classical
  let occurs (k : ℕ) := ∃ q : Path6 G, Away q U ∧ ∃ i : Fin 6, i.val = k ∧ q i = b
  obtain ⟨i, hi⟩ := hits p hp b hb hbB
  have ex : ∃ k, occurs k := ⟨i.val, p, hp, i, rfl, hi⟩
  obtain ⟨q, hq, j, hj, hqj⟩ := Nat.find_spec ex
  by_cases hj0 : j = 0
  · subst j
    have hfirst : Boundary G U (q 0) := hqj ▸ hbB
    exact ⟨q, hq, hfirst, (outer_endpoints external hits q hq hfirst).1⟩
  by_cases hlast : Boundary G U (q 5)
  · let qr := reversePath q
    have hqr : Away qr U := fun i => hq i.rev
    exact ⟨qr, hqr, hlast, (outer_endpoints external hits qr hqr hlast).1⟩
  obtain ⟨x, hx, edge⟩ := external (reversePath q)
  rw [reverse_range] at hx
  have hxU : x ∉ U := fun h => hlast ⟨x, h, edge⟩
  let k : Fin 5 := j.pred hj0
  have heq : k.succ = j := Fin.succ_pred _ _
  have hq' : occurs k.val :=
    ⟨shift q x hx edge, shift_away q hq hx hxU edge, k.castSucc, rfl,
      (shift_at q hx edge k).trans (heq ▸ hqj)⟩
  have hmin := Nat.find_min' ex hq'
  have hval : k.val + 1 = j.val := congrArg Fin.val heq
  omega

private theorem relist_away {k : ℕ} (p : Path6 G) {U : Set V} (hp : Away p U)
    (new : Fin k → V) (hnew : Function.Injective new) (hout : ∀ j, new j ∉ Set.range p)
    (order : Fin 6 ↪ Fin (6 + k))
    (steps : ∀ i : Fin 5, G.Adj (Fin.append p new (order i.castSucc))
      (Fin.append p new (order i.succ)))
    (hnU : ∀ j, new j ∉ U) : Away (relist p new hnew hout order steps) U := by
  intro i
  change (Fin.append p new (order i)) ∉ U
  generalize order i = j
  refine Fin.addCases (fun l => ?_) (fun r => ?_) j
  · simpa only [Fin.append_left] using hp l
  · simpa only [Fin.append_right] using hnU r

private theorem relist_misses {k : ℕ} (p : Path6 G)
    (new : Fin k → V) (hnew : Function.Injective new) (hout : ∀ j, new j ∉ Set.range p)
    (order : Fin 6 ↪ Fin (6 + k))
    (steps : ∀ i : Fin 5, G.Adj (Fin.append p new (order i.castSucc))
      (Fin.append p new (order i.succ)))
    (i : Fin 6) (hi : ∀ j, order j ≠ i.castAdd k) :
    p i ∉ Set.range (relist p new hnew hout order steps) := by
  rintro ⟨j, hj⟩
  apply hi j
  apply Fin.append_injective_iff.mpr
    ⟨p.injective, hnew, fun a b h => hout b ⟨a, h⟩⟩
  change Fin.append p new (order j) = p i at hj
  rwa [Fin.append_left]

private theorem front_no_attachment {U : Set V}
    (external : ∀ p : Path6 G, ∃ x ∉ Set.range p, G.Adj (p 0) x)
    (hits : ∀ p : Path6 G, Away p U → ∀ x ∉ U, Boundary G U x → x ∈ Set.range p)
    (p : Path6 G) (hp : Away p U) (hfirst : Boundary G U (p 0))
    (hlast : Boundary G U (p 5)) {r : V} (hr : r ∉ Set.range p) (hrU : r ∉ U) :
    ¬ G.Adj (p 0) r ∧ ¬ G.Adj (p 1) r := by
  constructor
  · intro e
    have hp' : Away (reversePath p) U := fun i => hp i.rev
    have hr' : r ∉ Set.range (reversePath p) := by rwa [reverse_range]
    exact hrU ((outer_endpoints external hits (reversePath p) hp' hlast).2 r hr' e)
  · intro edge
    let new : Fin 1 → V := ![r]
    have hn : Function.Injective new := Function.injective_of_subsingleton new
    have hout : ∀ j, new j ∉ Set.range p := by
      intro j
      fin_cases j
      exact hr
    let order : Fin 6 ↪ Fin 7 := ⟨![6, 1, 2, 3, 4, 5], by decide⟩
    have steps (i : Fin 5) : G.Adj (Fin.append p new (order i.castSucc))
        (Fin.append p new (order i.succ)) := by
      fin_cases i
      · exact edge.symm
      · exact path_step p 1
      · exact path_step p 2
      · exact path_step p 3
      · exact path_step p 4
    have hnU (j : Fin 1) : new j ∉ U := by
      fin_cases j
      exact hrU
    have hf : ∀ j, order j ≠ (0 : Fin 6).castAdd 1 := by decide
    exact relist_misses p new hn hout order steps 0 hf
      (hits _ (relist_away p hp new hn hout order steps hnU) (p 0) (hp 0) hfirst)

private theorem middle_attachments {U : Set V}
    (external : ∀ p : Path6 G, ∃ x ∉ Set.range p, G.Adj (p 0) x)
    (hits : ∀ p : Path6 G, Away p U → ∀ x ∉ U, Boundary G U x → x ∈ Set.range p)
    (p : Path6 G) (hp : Away p U) (hfirst : Boundary G U (p 0))
    (hlast : Boundary G U (p 5)) {r : V} (hr : r ∉ Set.range p) (hrU : r ∉ U)
    (i : Fin 6) (e : G.Adj (p i) r) : i = 2 ∨ i = 3 := by
  obtain ⟨h0, h1⟩ := front_no_attachment external hits p hp hfirst hlast hr hrU
  have hp' : Away (reversePath p) U := fun i => hp i.rev
  have hr' : r ∉ Set.range (reversePath p) := by rwa [reverse_range]
  obtain ⟨h5, h4⟩ := front_no_attachment external hits (reversePath p) hp' hlast hfirst hr' hrU
  fin_cases i
  · exact (h0 e).elim
  · exact (h1 e).elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (h4 e).elim
  · exact (h5 e).elim

private theorem pair_injective {x y : V} (hxy : x ≠ y) :
    Function.Injective (![x, y] : Fin 2 → V) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hxy h).elim
  · exact (hxy h.symm).elim
  · rfl

private theorem simplicial_from_attachment {U : Set V}
    (external : ∀ p : Path6 G, ∃ x ∉ Set.range p, G.Adj (p 0) x)
    (hits : ∀ p : Path6 G, Away p U → ∀ x ∉ U, Boundary G U x → x ∈ Set.range p)
    (p : Path6 G) (hp : Away p U) (hfirst : Boundary G U (p 0))
    (hlast : Boundary G U (p 5)) {r : V} (hr : r ∉ Set.range p) (hrU : r ∉ U)
    (attach : G.Adj (p 2) r) : ∃ q : Path6 G, Avoidable q 0 3 := by
  have neighbors (z : V) (ez : G.Adj r z) : z = p 2 ∨ z = p 3 := by
    classical
    by_cases hz : z ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hz
      rcases middle_attachments external hits p hp hfirst hlast hr hrU i ez.symm with hi | hi
      · exact Or.inl (congrArg p hi)
      · exact Or.inr (congrArg p hi)
    · exfalso
      have hzU : z ∉ U := fun h => hr (hits p hp r hrU ⟨z, h, ez⟩)
      let new : Fin 2 → V := ![r, z]
      have hn := pair_injective ez.ne
      have hout (j : Fin 2) : new j ∉ Set.range p := by
        fin_cases j
        · exact hr
        · exact hz
      have hnU (j : Fin 2) : new j ∉ U := by
        fin_cases j
        · exact hrU
        · exact hzU
      let order : Fin 6 ↪ Fin 8 := ⟨![7, 6, 2, 3, 4, 5], by decide⟩
      have steps (i : Fin 5) : G.Adj (Fin.append p new (order i.castSucc))
          (Fin.append p new (order i.succ)) := by
        fin_cases i
        · exact ez.symm
        · exact attach.symm
        · exact path_step p 2
        · exact path_step p 3
        · exact path_step p 4
      have hf : ∀ j, order j ≠ (0 : Fin 6).castAdd 2 := by decide
      exact relist_misses p new hn hout order steps 0 hf
        (hits _ (relist_away p hp new hn hout order steps hnU) (p 0) (hp 0) hfirst)
  obtain ⟨u, hu, eu⟩ := hlast
  let new : Fin 2 → V := ![r, u]
  have hn : Function.Injective new := pair_injective (fun h => hrU (h ▸ hu))
  have hout (j : Fin 2) : new j ∉ Set.range p := by
    fin_cases j
    · exact hr
    · rintro ⟨i, hi⟩
      exact hp i (hi.symm ▸ hu)
  let order : Fin 6 ↪ Fin 8 := ⟨![6, 2, 3, 4, 5, 7], by decide⟩
  have steps (i : Fin 5) : G.Adj (Fin.append p new (order i.castSucc))
      (Fin.append p new (order i.succ)) := by
    fin_cases i
    · exact attach.symm
    · exact path_step p 2
    · exact path_step p 3
    · exact path_step p 4
    · exact eu
  let q := relist p new hn hout order steps
  refine ⟨q, simplicial_first q fun z ez => ?_⟩
  rcases neighbors z ez with h | h
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

/-- Lemma 3.4's maximal-complement argument for the six-vertex path. -/
private theorem path6_avoidable_connected [Finite V] (hG : G.Connected) (p : Path6 G) :
    ∃ q : Path6 G, Avoidable q 0 3 := by
  classical
  by_contra none
  have external (q : Path6 G) : ∃ x ∉ Set.range q, G.Adj (q 0) x := by
    by_contra! absent
    exact none ⟨q, simplicial_first q fun x edge => by
      by_contra hx
      exact absent x hx edge⟩
  let good (U : Set V) : Prop := (G.induce U).Connected ∧ ∃ q : Path6 G, Away q U
  obtain ⟨x, hx, _⟩ := external p
  have hgood : good {x} := by
    refine ⟨Connected.of_subsingleton, p, ?_⟩
    intro i hi
    exact hx ⟨i, Set.mem_singleton_iff.mp hi⟩
  obtain ⟨U, hU, maximal⟩ :=
    (Set.toFinite {U : Set V | good U}).exists_maximal ⟨{x}, hgood⟩
  obtain ⟨q, hq⟩ := hU.2
  have hits (p' : Path6 G) (hp' : Away p' U) (b : V)
      (hb : b ∉ U) (hB : Boundary G U b) : b ∈ Set.range p' := by
    by_contra hmiss
    obtain ⟨u, hu, e⟩ := hB
    have hnew : good (insert b U) := by
      refine ⟨connected_insert hu e hU.1, p', fun i hi => ?_⟩
      rcases Set.mem_insert_iff.mp hi with he | he
      · exact hmiss ⟨i, he⟩
      · exact hp' i he
    exact hb (maximal hnew (Set.subset_insert b U) (Set.mem_insert b U))
  obtain ⟨u⟩ := hU.1.nonempty
  obtain ⟨v, hvU, b, hb, evb⟩ := crossing_edge hG.preconnected u.property (hq 0)
  obtain ⟨a, ha, ha0, ha5⟩ := exists_outer external hits q hq hb ⟨v, hvU, evb.symm⟩
  by_cases hcover : ∀ z ∉ U, z ∈ Set.range a
  · refine none ⟨a, fun v w ext => ?_⟩
    have hv : v ∈ U := by
      by_contra hn
      exact ext.1 (hcover v hn)
    have hw : w ∈ U := by
      by_contra hn
      exact ext.2.1 (hcover w hn)
    have hsub : U ⊆ (Set.range a)ᶜ := by
      intro z hz
      rintro ⟨i, rfl⟩
      exact ha i hz
    exact (hU.1.preconnected ⟨v, hv⟩ ⟨w, hw⟩).map (G.induceHomOfLE hsub).toHom
  · push Not at hcover
    obtain ⟨r, hrU, hr⟩ := hcover
    have hrUnion : r ∉ U ∪ Set.range a := fun h => h.elim hrU hr
    obtain ⟨v, hv, z, hz, evz⟩ :=
      crossing_edge hG.preconnected (Set.mem_union_left (Set.range a) u.property) hrUnion
    have hzU : z ∉ U := fun h => hz (Or.inl h)
    have hzrange : z ∉ Set.range a := fun h => hz (Or.inr h)
    rcases hv with hv | ⟨i, rfl⟩
    · exact hzrange (hits a ha z hzU ⟨v, hv, evz.symm⟩)
    · rcases middle_attachments external hits a ha ha0 ha5 hzrange hzU i evz with rfl | rfl
      · exact none (simplicial_from_attachment external hits a ha ha0 ha5 hzrange hzU evz)
      · have ha' : Away (reversePath a) U := fun j => ha j.rev
        have hzrange' : z ∉ Set.range (reversePath a) := by rwa [reverse_range]
        exact none (simplicial_from_attachment external hits (reversePath a) ha' ha5 ha0
          hzrange' hzU evz)

private theorem path6_inherent : Inherent (pathGraph 6) 0 3 := by
  intro m G ⟨p⟩
  let C := G.connectedComponentMk (p 0)
  have hp (i : Fin 6) : p i ∈ C :=
    ConnectedComponent.sound (((preconnected_pathGraph 6) i 0).map p.toHom)
  let pC : Path6 C.toSimpleGraph :=
    ⟨{ toFun := fun i => ⟨p i, hp i⟩, map_rel' := fun e => p.toHom.map_rel e },
      fun _ _ h => p.injective (congrArg Subtype.val h)⟩
  obtain ⟨q, hq⟩ := path6_avoidable_connected C.connected_toSimpleGraph pC
  let f : Path6 G := (Copy.induce G C.supp).comp q
  refine ⟨f, fun x y e => ?_⟩
  let xC : C := ⟨x, C.mem_supp_of_adj_mem_supp (q 0).property e.2.2.2.1⟩
  let yC : C := ⟨y, C.mem_supp_of_adj_mem_supp (q 3).property e.2.2.2.2⟩
  have eC : Extension q 0 3 xC yC :=
    ⟨fun ⟨i, hi⟩ => e.1 ⟨i, congrArg Subtype.val hi⟩,
      fun ⟨i, hi⟩ => e.2.1 ⟨i, congrArg Subtype.val hi⟩,
      fun h => e.2.2.1 (congrArg Subtype.val h), e.2.2.2.1, e.2.2.2.2⟩
  let incl : C.toSimpleGraph.induce (Set.range q)ᶜ →g G.induce (Set.range f)ᶜ :=
    { toFun := fun v => ⟨v.val.val, fun ⟨i, hi⟩ => v.property ⟨i, Subtype.ext hi⟩⟩
      map_rel' := fun h => h }
  exact (hq xC yC eC).map incl

private def deletedPath : SimpleGraph (Fin 6) := (pathGraph 6).deleteEdges {s(0, 1)}

private def midpoint (i : Fin 4) : Fin 9 := ⟨2 * i.val + 1, by omega⟩

private def tip (i : Fin 4) : Fin 9 := ⟨2 * i.val + 2, by omega⟩

private def towardMidpoint (x y : Fin 9) : Prop :=
  ∃ i : Fin 4, y = midpoint i ∧ (x = 0 ∨ x = tip i)

private instance (x y : Fin 9) : Decidable (towardMidpoint x y) :=
  inferInstanceAs (Decidable (∃ i : Fin 4, y = midpoint i ∧ (x = 0 ∨ x = tip i)))

/-- The four two-edge arms with center zero. -/
private def fourArm : SimpleGraph (Fin 9) where
  Adj x y := towardMidpoint x y ∨ towardMidpoint y x
  symm.symm _ _ := Or.symm
  loopless.irrefl x := (by decide : ∀ v : Fin 9, ¬ (towardMidpoint v v ∨ towardMidpoint v v)) x

private instance : DecidableRel fourArm.Adj :=
  fun x y => inferInstanceAs (Decidable (towardMidpoint x y ∨ towardMidpoint y x))

private instance : DecidableRel deletedPath.Adj :=
  fun i j => decidable_of_iff ((pathGraph 6).Adj i j ∧ s(i, j) ≠ s((0 : Fin 6), 1))
    (by simp [deletedPath])

private def displayedCopy : Copy deletedPath fourArm :=
  ⟨{ toFun := ![5, 2, 1, 0, 3, 4]
     map_rel' :=
       (by decide : ∀ (i j : Fin 6), deletedPath.Adj i j →
         fourArm.Adj (![5, 2, 1, 0, 3, 4] i) (![5, 2, 1, 0, 3, 4] j)) },
    by decide⟩

private theorem center_adj (v : Fin 9) :
    fourArm.Adj 0 v ↔ ∃ i : Fin 4, v = midpoint i :=
  (by decide : ∀ v : Fin 9, fourArm.Adj 0 v ↔ ∃ i : Fin 4, v = midpoint i) v

private theorem midpoint_adj (i : Fin 4) (v : Fin 9) :
    fourArm.Adj (midpoint i) v ↔ v = 0 ∨ v = tip i :=
  (by decide : ∀ (i : Fin 4) (v : Fin 9),
    fourArm.Adj (midpoint i) v ↔ v = 0 ∨ v = tip i) i v

private theorem tip_adj (i : Fin 4) (v : Fin 9) : fourArm.Adj (tip i) v ↔ v = midpoint i :=
  (by decide : ∀ (i : Fin 4) (v : Fin 9), fourArm.Adj (tip i) v ↔ v = midpoint i) i v

private theorem vertex_cases (v : Fin 9) :
    v = 0 ∨ ∃ i : Fin 4, v = midpoint i ∨ v = tip i :=
  (by decide : ∀ v : Fin 9, v = 0 ∨ ∃ i : Fin 4, v = midpoint i ∨ v = tip i) v

private theorem arm_distinct (i j : Fin 4) (hij : i ≠ j) :
    midpoint i ≠ midpoint j ∧ midpoint i ≠ tip j ∧
      tip i ≠ midpoint j ∧ tip i ≠ tip j :=
  (by decide : ∀ i j : Fin 4, i ≠ j → midpoint i ≠ midpoint j ∧ midpoint i ≠ tip j ∧
    tip i ≠ midpoint j ∧ tip i ≠ tip j) i j hij

private theorem arm_nonzero (i : Fin 4) : midpoint i ≠ 0 ∧ tip i ≠ 0 :=
  (by decide : ∀ i : Fin 4, midpoint i ≠ 0 ∧ tip i ≠ 0) i

private theorem spare_arm (i j k : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k :=
  (by decide : ∀ i j k : Fin 4, ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k) i j k

/-- The middle of an injective four-edge path must be the center. -/
private theorem fourArm_path_center (f : Copy deletedPath fourArm) : f 3 = 0 := by
  have e12 : fourArm.Adj (f 1) (f 2) := f.toHom.map_rel (by decide : deletedPath.Adj 1 2)
  have e23 : fourArm.Adj (f 2) (f 3) := f.toHom.map_rel (by decide : deletedPath.Adj 2 3)
  have e34 : fourArm.Adj (f 3) (f 4) := f.toHom.map_rel (by decide : deletedPath.Adj 3 4)
  have e45 : fourArm.Adj (f 4) (f 5) := f.toHom.map_rel (by decide : deletedPath.Adj 4 5)
  have distinct {a b : Fin 6} (n : a ≠ b) : f a ≠ f b := fun e => n (f.injective e)
  rcases vertex_cases (f 3) with hc | ⟨i, hmid | htip⟩
  · exact hc
  · have before := (midpoint_adj i (f 2)).mp (hmid ▸ e23.symm)
    have after := (midpoint_adj i (f 4)).mp (hmid ▸ e34)
    rcases before with h2 | h2
    · rcases after with h4 | h4
      · exact (distinct (by decide : (2 : Fin 6) ≠ 4) (h2.trans h4.symm)).elim
      · have h5 := (tip_adj i (f 5)).mp (h4 ▸ e45)
        exact (distinct (by decide : (5 : Fin 6) ≠ 3) (h5.trans hmid.symm)).elim
    · have h1 := (tip_adj i (f 1)).mp (h2 ▸ e12.symm)
      exact (distinct (by decide : (1 : Fin 6) ≠ 3) (h1.trans hmid.symm)).elim
  · have h2 := (tip_adj i (f 2)).mp (htip ▸ e23.symm)
    have h4 := (tip_adj i (f 4)).mp (htip ▸ e34)
    exact (distinct (by decide : (2 : Fin 6) ≠ 4) (h2.trans h4.symm)).elim

/-- The isolated pattern vertex occupies a third arm, opposite the first extension endpoint. -/
private theorem fourArm_obstruction (f : Copy deletedPath fourArm) :
    ∃ (x y : Fin 9) (e : Extension f 0 3 x y),
      (fourArm.induce (Set.range f)ᶜ).IsIsolated ⟨x, e.1⟩ := by
  have h3 := fourArm_path_center f
  have e12 : fourArm.Adj (f 1) (f 2) := f.toHom.map_rel (by decide : deletedPath.Adj 1 2)
  have e23 : fourArm.Adj (f 2) (f 3) := f.toHom.map_rel (by decide : deletedPath.Adj 2 3)
  have e34 : fourArm.Adj (f 3) (f 4) := f.toHom.map_rel (by decide : deletedPath.Adj 3 4)
  have e45 : fourArm.Adj (f 4) (f 5) := f.toHom.map_rel (by decide : deletedPath.Adj 4 5)
  have distinct {a b : Fin 6} (n : a ≠ b) : f a ≠ f b := fun e => n (f.injective e)
  obtain ⟨i, h2⟩ := (center_adj (f 2)).mp (h3 ▸ e23.symm)
  obtain ⟨j, h4⟩ := (center_adj (f 4)).mp (h3 ▸ e34)
  have h1 : f 1 = tip i :=
    ((midpoint_adj i (f 1)).mp (h2 ▸ e12.symm)).resolve_left
      (fun h => distinct (by decide : (1 : Fin 6) ≠ 3) (h.trans h3.symm))
  have h5 : f 5 = tip j :=
    ((midpoint_adj j (f 5)).mp (h4 ▸ e45)).resolve_left
      (fun h => distinct (by decide : (5 : Fin 6) ≠ 3) (h.trans h3.symm))
  obtain ⟨k, hk⟩ := (vertex_cases (f 0)).resolve_left
    (fun h => distinct (by decide : (0 : Fin 6) ≠ 3) (h.trans h3.symm))
  have hki : k ≠ i := by
    rintro rfl
    rcases hk with h | h
    · exact distinct (by decide : (0 : Fin 6) ≠ 2) (h.trans h2.symm)
    · exact distinct (by decide : (0 : Fin 6) ≠ 1) (h.trans h1.symm)
  have hkj : k ≠ j := by
    rintro rfl
    rcases hk with h | h
    · exact distinct (by decide : (0 : Fin 6) ≠ 4) (h.trans h4.symm)
    · exact distinct (by decide : (0 : Fin 6) ≠ 5) (h.trans h5.symm)
  obtain ⟨l, hli, hlj, hlk⟩ := spare_arm i j k
  have arm_off_path (a : Fin 4) (hai : a ≠ i) (haj : a ≠ j)
      {v : Fin 9} (hv : v = midpoint a ∨ v = tip a) (hv0 : v ≠ f 0) :
      v ∉ Set.range f := by
    obtain ⟨ami, ati, tmi, tti⟩ := arm_distinct a i hai
    obtain ⟨amj, atj, tmj, ttj⟩ := arm_distinct a j haj
    obtain ⟨am0, at0⟩ := arm_nonzero a
    rintro ⟨d, hd⟩
    fin_cases d
    · exact hv0 hd.symm
    · rcases hv with rfl | rfl
      · exact ati (hd.symm.trans h1)
      · exact tti (hd.symm.trans h1)
    · rcases hv with rfl | rfl
      · exact ami (hd.symm.trans h2)
      · exact tmi (hd.symm.trans h2)
    · rcases hv with rfl | rfl
      · exact am0 (hd.symm.trans h3)
      · exact at0 (hd.symm.trans h3)
    · rcases hv with rfl | rfl
      · exact amj (hd.symm.trans h4)
      · exact tmj (hd.symm.trans h4)
    · rcases hv with rfl | rfl
      · exact atj (hd.symm.trans h5)
      · exact ttj (hd.symm.trans h5)
  have yRoot : midpoint l ≠ f 0 := by
    rcases hk with h | h
    · exact fun eq => (arm_distinct l k hlk).1 (eq.trans h)
    · exact fun eq => (arm_distinct l k hlk).2.1 (eq.trans h)
  have hy := arm_off_path l hli hlj (Or.inl rfl) yRoot
  have ey : fourArm.Adj (f 3) (midpoint l) := h3 ▸ (center_adj _).mpr ⟨l, rfl⟩
  have other_end :
      ∃ x, (x = midpoint k ∨ x = tip k) ∧ x ≠ f 0 ∧ fourArm.Adj (f 0) x ∧
        ∀ v, fourArm.Adj x v → v = 0 ∨ v = f 0 := by
    rcases hk with h | h
    · have adj := (tip_adj k (midpoint k)).mpr rfl
      refine ⟨tip k, Or.inr rfl, fun eq => adj.ne (eq.trans h), h ▸ adj.symm, ?_⟩
      exact fun v e => Or.inr (((tip_adj k v).mp e).trans h.symm)
    · have adj := (tip_adj k (midpoint k)).mpr rfl
      refine ⟨midpoint k, Or.inl rfl, fun eq => adj.ne (eq.trans h).symm, h ▸ adj, ?_⟩
      exact fun v e => ((midpoint_adj k v).mp e).imp id (fun he => he.trans h.symm)
  obtain ⟨x, hxArm, hxRoot, ex, only⟩ := other_end
  have hx := arm_off_path k hki hkj hxArm hxRoot
  have hxy : x ≠ midpoint l := by
    rcases hxArm with rfl | rfl
    · exact (arm_distinct k l hlk.symm).1
    · exact (arm_distinct k l hlk.symm).2.2.1
  refine ⟨x, midpoint l, ⟨hx, hy, hxy, ex, ey⟩, ?_⟩
  intro v e
  rcases only v.val e with h | h
  · exact v.property ⟨3, h3.trans h.symm⟩
  · exact v.property ⟨0, h.symm⟩

private theorem fourArm_not_avoidable (f : Copy deletedPath fourArm) : ¬ Avoidable f 0 3 := by
  intro h
  obtain ⟨x, y, ext, isolated⟩ := fourArm_obstruction f
  have hne : (⟨x, ext.1⟩ : ((Set.range f)ᶜ : Set (Fin 9))) ≠ ⟨y, ext.2.1⟩ :=
    fun eq => ext.2.2.1 (congrArg Subtype.val eq)
  exact not_reachable_of_neighborSet_left_eq_empty hne isolated.neighborSet_eq_empty (h x y ext)

end GurvichLeafRootEdgeDeletionRefutation
