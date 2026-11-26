/- GID: D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A spine-cut criterion classifies trees formed by one-joining paths. -/

/-
admission_basis: open-problem-resolution
proof_shape: content (oneJoined_iff_spineCut, expanding its consumed directions)
escape_witness: the forward certificate uses actual joins, and the reverse
construction assigns joining labels while recovering exactly the given cut.
Direct frozen dependencies: none. TreePathCuts is a same-delivery dependency.
Preregistration and escape audit: https://github.com/the-omega-institute/trureturing/issues/34504
-/

import D5.S3.Combinatorics.Graph.LinearForests.TreePathCuts
import OmegaBuild.Commands

/-!
# Classification of one-joined path trees

Pinzon, Pragel, Roberts, Marshall and Strain, arXiv:2611.34794v1, §6, p. 9.
The attachment rule is the one in §1 and the cited Definition 1.1.
The minimum block order and the requirement for an actual join are independent.

Preregistration and linked escape-audit issue: https://github.com/the-omega-institute/trureturing/issues/34504.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OneJoinedPathTrees

noncomputable section

open SimpleGraph
open scoped Sym2

universe u
variable {V : Type u} {G : SimpleGraph V}


private def cutNeighbors (G : SimpleGraph V) (C : Set (Sym2 V)) (x : V) : Set V :=
  {y | G.Adj x y ∧ s(x, y) ∈ C}

private theorem incidence_eq_neighbors (C : Set (Sym2 V)) (x : V) :
    cutIncidence G C x = (cutNeighbors G C x).ncard := by
  symm
  apply Set.ncard_congr (fun y _ => s(x, y))
  · intro y hy
    exact ⟨hy.2, (G.mem_incidenceSet x y).mpr hy.1⟩
  · intro y z _ _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  · intro e
    induction e using Sym2.inductionOn with
    | hf y z =>
      rintro ⟨he, hi⟩
      rcases (mk'_mem_incidenceSet_iff (G := G)).mp hi with ⟨hyz, rfl | rfl⟩
      · exact ⟨z, ⟨hyz, he⟩, rfl⟩
      · rw [Sym2.eq_swap] at he ⊢
        exact ⟨y, ⟨hyz.symm, he⟩, rfl⟩

/-- A literal 1-join presentation on the input vertex type.
The fibers of `block` partition every vertex. Each fiber has its own geometric
path coordinates and a separate arbitrary bijection of labels. Labels are
zero-based, so `0` and `Fin.last` encode label 1 and the largest label. -/
structure LabeledChain (G : SimpleGraph V) (k : ℕ) where
  block : V → Fin (k + 1)
  length : Fin (k + 1) → ℕ
  path : ∀ i, pathGraph (length i + 1) ≃g G.induce {x | block x = i}
  label : ∀ i, Fin (length i + 1) ≃ {x // block x = i}
  cross : ∀ x y, block x ≠ block y →
    (G.Adj x y ↔
      ((block x).val + 1 = (block y).val ∧
        x = (label (block x) (Fin.last (length (block x)))).val ∧
        y = (label (block y) 0).val) ∨
      ((block y).val + 1 = (block x).val ∧
        y = (label (block y) (Fin.last (length (block y)))).val ∧
        x = (label (block x) 0).val))

/-- A chain of at least one block, subject to the minimum order and, when
`requireJoin` is true, at least one actual join. -/
def OneJoined (G : SimpleGraph V) (m : ℕ) (requireJoin : Bool) : Prop :=
  ∃ k, ∃ L : LabeledChain G k, (requireJoin = true → 0 < k) ∧
    ∀ i, m ≤ L.length i + 1

private structure OrderedBlocks (G : SimpleGraph V) (k : ℕ) where
  block : V → Fin (k + 1)
  only : ∀ {x y}, G.Adj x y → block x ≠ block y → (pathGraph (k + 1)).Adj (block x) (block y)
  join : ∀ i j : Fin (k + 1), i.val + 1 = j.val →
    ∃ x y, block x = i ∧ block y = j ∧ G.Adj x y
  unique : ∀ {x y x' y'}, G.Adj x y → G.Adj x' y' →
    block x ≠ block y → block x = block x' → block y = block y' → x = x' ∧ y = y'

private def OrderedBlocks.Incoming {k : ℕ} (B : OrderedBlocks G k) (x : V) : Prop :=
  ∃ y, G.Adj x y ∧ (B.block y).val + 1 = (B.block x).val

private def OrderedBlocks.Outgoing {k : ℕ} (B : OrderedBlocks G k) (x : V) : Prop :=
  ∃ y, G.Adj x y ∧ (B.block x).val + 1 = (B.block y).val

private theorem block_degree_bound [Finite V] {k : ℕ} (B : OrderedBlocks G k)
    {C : Set (Sym2 V)} (hC : ∀ x y, G.Adj x y → (s(x, y) ∈ C ↔ B.block x ≠ B.block y))
    (x : V) : cutIncidence G C x ≤ 2 := by
  rw [incidence_eq_neighbors]
  refine (Set.ncard_le_ncard_of_injOn B.block
    (t := (pathGraph (k + 1)).neighborSet (B.block x)) ?_ ?_ (Set.toFinite _)).trans
    (pathGraph_degree_le_two _)
  · intro y hy
    exact B.only hy.1 ((hC x y hy.1).mp hy.2)
  · intro y hy z hz he
    exact (B.unique hy.1 hz.1 ((hC x y hy.1).mp hy.2) rfl he).2

private theorem two_incidence_iff [Finite V] {k : ℕ} (B : OrderedBlocks G k)
    {C : Set (Sym2 V)} (hC : ∀ x y, G.Adj x y → (s(x, y) ∈ C ↔ B.block x ≠ B.block y))
    (x : V) : cutIncidence G C x = 2 ↔ B.Incoming x ∧ B.Outgoing x := by
  constructor
  · intro htwo
    by_contra h
    have hle : (cutNeighbors G C x).ncard ≤ 1 := by
      refine (Set.ncard_le_one (Set.toFinite _)).mpr ?_
      intro y hy z hz
      have hyne := (hC x y hy.1).mp hy.2
      have hzne := (hC x z hz.1).mp hz.2
      rcases pathGraph_adj.mp (B.only hy.1 hyne) with hYo | hYi <;>
        rcases pathGraph_adj.mp (B.only hz.1 hzne) with hZo | hZi
      · exact (B.unique hy.1 hz.1 hyne rfl (Fin.ext (by omega))).2
      · exact (h ⟨⟨z, hz.1, hZi⟩, ⟨y, hy.1, hYo⟩⟩).elim
      · exact (h ⟨⟨y, hy.1, hYi⟩, ⟨z, hz.1, hZo⟩⟩).elim
      · exact (B.unique hy.1 hz.1 hyne rfl (Fin.ext (by omega))).2
    rw [← incidence_eq_neighbors] at hle
    omega
  · rintro ⟨⟨y, hxy, hy⟩, ⟨z, hxz, hz⟩⟩
    have hYZ : y ≠ z := by rintro rfl; omega
    have hyne : B.block x ≠ B.block y := by
      intro he
      have := congrArg Fin.val he
      omega
    have hzne : B.block x ≠ B.block z := by
      intro he
      have := congrArg Fin.val he
      omega
    have hsub : ({y, z} : Set V) ⊆ cutNeighbors G C x := by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨⟨hxy, (hC x y hxy).mpr hyne⟩, ⟨hxz, (hC x z hxz).mpr hzne⟩⟩
    have hlow := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hYZ, ← incidence_eq_neighbors] at hlow
    have := block_degree_bound B hC x
    omega

private theorem block_positive_iff_cut_nonempty {k : ℕ} (B : OrderedBlocks G k)
    {C : Set (Sym2 V)} (hsub : C ⊆ G.edgeSet)
    (hC : ∀ x y, G.Adj x y → (s(x, y) ∈ C ↔ B.block x ≠ B.block y)) :
    0 < k ↔ C.Nonempty := by
  constructor
  · intro hk
    let i : Fin (k + 1) := 0
    let j : Fin (k + 1) := ⟨1, by omega⟩
    obtain ⟨x, y, hx, hy, hadj⟩ := B.join i j rfl
    exact ⟨s(x, y), (hC x y hadj).mpr (by
      rw [hx, hy]
      intro he
      have hv := congrArg Fin.val he
      change 0 = 1 at hv
      omega)⟩
  · rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hadj : G.Adj x y := hsub he
      have hne := (hC x y hadj).mp he
      have h := pathGraph_adj.mp (B.only hadj hne)
      have hx := (B.block x).isLt
      have hy := (B.block y).isLt
      omega

private def LabeledChain.ordered {k : ℕ} (L : LabeledChain G k) : OrderedBlocks G k where
  block := L.block
  only := by
    intro x y hadj hne
    rcases (L.cross x y hne).mp hadj with h | h
    · exact pathGraph_adj.mpr (Or.inl h.1)
    · exact pathGraph_adj.mpr (Or.inr h.1)
  join := by
    intro i j hij
    let x := (L.label i (Fin.last (L.length i))).val
    let y := (L.label j 0).val
    have hx : L.block x = i := (L.label i _).property
    have hy : L.block y = j := (L.label j _).property
    have hne : L.block x ≠ L.block y := by
      rw [hx, hy]
      intro he
      have := congrArg Fin.val he
      omega
    refine ⟨x, y, hx, hy, (L.cross x y hne).mpr (Or.inl ?_)⟩
    exact ⟨by simpa only [hx, hy] using hij, by rw [hx], by rw [hy]⟩
  unique := by
    intro x y x' y' h h' hn hx hy
    have hn' : L.block x' ≠ L.block y' := by rwa [← hx, ← hy]
    have p := (L.cross x y hn).mp h
    have p' := (L.cross x' y' hn').mp h'
    rw [← hx, ← hy] at p'
    rcases p with p | p <;> rcases p' with p' | p'
    · exact ⟨p.2.1.trans p'.2.1.symm, p.2.2.trans p'.2.2.symm⟩
    · omega
    · omega
    · exact ⟨p.2.2.trans p'.2.2.symm, p.2.1.trans p'.2.1.symm⟩

/-- The actual edges between different blocks of a labeled presentation. -/
def LabeledChain.joinEdges {k : ℕ} (L : LabeledChain G k) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ¬(e.map L.block).IsDiag}

theorem LabeledChain.mem_joinEdges {k : ℕ} (L : LabeledChain G k) {x y : V}
    (h : G.Adj x y) : s(x, y) ∈ L.joinEdges ↔ L.block x ≠ L.block y := by
  change (G.Adj x y ∧ ¬s(L.block x, L.block y).IsDiag) ↔ _
  simp [h]

private theorem LabeledChain.joinEdges_subset {k : ℕ} (L : LabeledChain G k) :
    L.joinEdges ⊆ G.edgeSet := fun _ h => h.1

theorem LabeledChain.joinEdges_on_spine {k : ℕ} (L : LabeledChain G k)
    (hG : G.IsTree) : OnSpine G L.joinEdges := by
  let a := (L.label 0 0).val
  let b := (L.label (Fin.last k) 0).val
  have ha : L.block a = 0 := (L.label 0 0).property
  have hb : L.block b = Fin.last k := (L.label (Fin.last k) 0).property
  obtain ⟨p, hp, _⟩ := hG.existsUnique_path a b
  refine ⟨a, b, p, hp, ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hxy : G.Adj x y := L.joinEdges_subset he
    have hn := (L.mem_joinEdges hxy).mp he
    have cross {x y : V} (hxy : G.Adj x y)
        (hs : (L.block x).val + 1 = (L.block y).val) :
        s(x, y) ∈ p.edges := by
      have step : ∀ {v w}, ∀ q : G.Walk v w,
          (L.block v).val ≤ (L.block x).val → (L.block x).val < (L.block w).val →
          s(x, y) ∈ q.edges := by
        intro v w q
        induction q with
        | nil => omega
        | @cons v z w hvz q ih =>
          intro hv hw
          by_cases hz : (L.block z).val ≤ (L.block x).val
          · exact List.mem_cons_of_mem _ (ih hz hw)
          have hn : L.block v ≠ L.block z := by
            intro he
            have := congrArg Fin.val he
            omega
          have hstep := pathGraph_adj.mp (L.ordered.only hvz hn)
          change (L.block v).val + 1 = (L.block z).val ∨
            (L.block z).val + 1 = (L.block v).val at hstep
          have he₁ : L.block x = L.block v := Fin.ext (by omega)
          have he₂ : L.block y = L.block z := Fin.ext (by omega)
          have hxyne : L.block x ≠ L.block y := by
            intro he
            have := congrArg Fin.val he
            omega
          obtain ⟨rfl, rfl⟩ := L.ordered.unique hxy hvz hxyne he₁ he₂
          exact List.mem_cons_self
      refine step p (by rw [ha]; exact Nat.zero_le _) ?_
      rw [hb, Fin.val_last]
      have := (L.block y).isLt
      omega
    rcases pathGraph_adj.mp (L.ordered.only hxy hn) with h | h
    · exact cross hxy h
    · rw [Sym2.eq_swap]
      exact cross hxy.symm h

theorem LabeledChain.residual_adj_iff {k : ℕ} (L : LabeledChain G k) {x y : V} :
    (G.deleteEdges L.joinEdges).Adj x y ↔ G.Adj x y ∧ L.block x = L.block y := by
  rw [deleteEdges_adj]
  exact ⟨fun ⟨h, hc⟩ => ⟨h, by simpa only [L.mem_joinEdges h, not_ne_iff] using hc⟩,
    fun ⟨h, he⟩ => ⟨h, fun hc => (L.mem_joinEdges h).mp hc he⟩⟩

/-- Degree restriction to a fiber that contains every neighbor of its vertices. -/
private theorem degree_induce_fiber {I : Type*} (f : V → I) {i : I}
    (x : {x // f x = i}) (h : ∀ y, G.Adj x.val y → f y = i) :
    degree (G.induce {x | f x = i}) x = degree G x.val := by
  apply Set.ncard_congr (fun y _ => y.val)
  · intro y hy
    exact hy
  · exact fun _ _ _ _ he => Subtype.ext he
  · intro y hy
    exact ⟨⟨y, h y hy⟩, hy, rfl⟩

private theorem LabeledChain.residual_degree {k : ℕ} (L : LabeledChain G k) (x : V) :
    degree (G.deleteEdges L.joinEdges) x =
      degree (pathGraph (L.length (L.block x) + 1))
        ((L.path (L.block x)).symm ⟨x, rfl⟩) := by
  rw [← degree_induce_fiber L.block ⟨x, rfl⟩ (fun y h => (L.residual_adj_iff.mp h).2.symm)]
  have he : (G.deleteEdges L.joinEdges).induce {y | L.block y = L.block x} =
      G.induce {y | L.block y = L.block x} := by
    ext a b
    change (G.deleteEdges L.joinEdges).Adj a.val b.val ↔ G.Adj a.val b.val
    rw [L.residual_adj_iff]
    simp [a.property.trans b.property.symm]
  rw [he]
  exact (degree_iso _ (L.path (L.block x)).symm ⟨x, rfl⟩).symm

private theorem LabeledChain.double_incidence_singleton [Finite V] {k : ℕ} (L : LabeledChain G k)
    {x : V} (h : cutIncidence G L.joinEdges x = 2) : L.length (L.block x) = 0 := by
  obtain ⟨⟨y, hxy, hy⟩, ⟨z, hxz, hz⟩⟩ :=
    (two_incidence_iff L.ordered (fun _ _ => L.mem_joinEdges) x).mp h
  have hyn : L.block x ≠ L.block y := by
    intro he
    have := congrArg Fin.val he
    change (L.block y).val + 1 = (L.block x).val at hy
    omega
  have hzn : L.block x ≠ L.block z := by
    intro he
    have := congrArg Fin.val he
    change (L.block x).val + 1 = (L.block z).val at hz
    omega
  have hp : x = (L.label (L.block x) 0).val := by
    rcases (L.cross x y hyn).mp hxy with h' | h'
    · change (L.block y).val + 1 = (L.block x).val at hy
      omega
    · exact h'.2.2
  have hq : x = (L.label (L.block x) (Fin.last _)).val := by
    rcases (L.cross x z hzn).mp hxz with h' | h'
    · exact h'.2.1
    · change (L.block x).val + 1 = (L.block z).val at hz
      omega
  have he := (L.label (L.block x)).injective (Subtype.ext (hp.symm.trans hq))
  exact (congrArg Fin.val he).symm
/-- The registered conditions at a vertex. The natural-number difference
already has the lower bound zero for minimum order one. -/
def VertexCondition (G : SimpleGraph V) (C : Set (Sym2 V)) (m : ℕ) (x : V) : Prop :=
  degree G x - cutIncidence G C x ≤ 2 ∧
    (m = 1 → cutIncidence G C x = 2 → degree G x = 2) ∧
    (m = 2 → cutIncidence G C x ≤ 1 ∧ 1 ≤ degree G x - cutIncidence G C x)

/-- The degree conditions written on the graph remaining after deletion. -/
def ResidualVertexCondition (G : SimpleGraph V) (C : Set (Sym2 V)) (m : ℕ) (x : V) : Prop :=
  degree (G.deleteEdges C) x ≤ 2 ∧
    (m = 1 → cutIncidence G C x = 2 → degree (G.deleteEdges C) x = 0) ∧
    (m = 2 → cutIncidence G C x ≤ 1 ∧ 1 ≤ degree (G.deleteEdges C) x)

theorem residualVertexCondition_iff [Finite V] (C : Set (Sym2 V)) (m : ℕ) (x : V) :
    ResidualVertexCondition G C m x ↔ VertexCondition G C m x := by
  unfold ResidualVertexCondition VertexCondition
  have hres := residual_eq_degree_sub_incidence (G := G) C x
  have hsum := degree_eq_residual_add_incidence (G := G) C x
  constructor
  · rintro ⟨hdeg, hs, hl⟩
    refine ⟨hres ▸ hdeg, ?_, fun hm => ?_⟩
    · intro hm hc
      have := hs hm hc
      omega
    · simpa only [hres] using hl hm
  · rintro ⟨hdeg, hs, hl⟩
    refine ⟨hres.symm ▸ hdeg, ?_, fun hm => ?_⟩
    · intro hm hc
      have := hs hm hc
      omega
    · simpa only [hres] using hl hm

/-- The preregistered incidence criterion for a cut on one simple path. -/
def SpineCut (G : SimpleGraph V) (m : ℕ) (requireJoin : Bool) : Prop :=
  ∃ C : Set (Sym2 V), OnSpine G C ∧ (requireJoin = true → C.Nonempty) ∧
    ∀ x, VertexCondition G C m x

/-- The same spine cut, with conditions on the residual degrees. -/
def ResidualSpineCut (G : SimpleGraph V) (m : ℕ) (requireJoin : Bool) : Prop :=
  ∃ C : Set (Sym2 V), OnSpine G C ∧ (requireJoin = true → C.Nonempty) ∧
    ∀ x, ResidualVertexCondition G C m x

theorem residualSpineCut_iff_spineCut [Finite V] (m : ℕ) (requireJoin : Bool) :
    ResidualSpineCut G m requireJoin ↔ SpineCut G m requireJoin :=
  exists_congr fun C => and_congr_right fun _ => and_congr_right fun _ =>
    forall_congr' (residualVertexCondition_iff C m)

/-- The witnessing cut consists of the actual joins in the supplied presentation. -/
private def orderedBlocksOfComponents (hG : G.IsAcyclic) {C : Set (Sym2 V)} {k : ℕ}
    (e : componentGraph G C ≃g pathGraph (k + 1)) : OrderedBlocks G k where
  block := fun x => e (component G C x)
  only := by
    intro x y hadj hne
    have hc : s(x, y) ∈ C := by
      by_contra h
      exact hne (congrArg e (same_component_of_uncut hadj h))
    exact e.map_rel_iff.mpr (componentGraph_adj hG hadj hc)
  join := by
    intro i j hij
    have h := e.symm.map_rel_iff.mpr (pathGraph_adj.mpr (Or.inl hij))
    obtain ⟨_, x, y, hadj, _, hx, hy⟩ := h
    exact ⟨x, y, by rw [hx, e.apply_symm_apply], by rw [hy, e.apply_symm_apply], hadj⟩
  unique := by
    intro x y x' y' hadj hadj' hne hx hy
    have hc : s(x, y) ∈ C := by
      by_contra h
      exact hne (congrArg e (same_component_of_uncut hadj h))
    exact cutEndpoints_unique hG hadj hc hadj' (e.injective hx) (e.injective hy)

private theorem orderedBlocksOfComponents_cut_iff (hG : G.IsAcyclic) {C : Set (Sym2 V)} {k : ℕ}
    (e : componentGraph G C ≃g pathGraph (k + 1)) {x y : V} (hadj : G.Adj x y) :
    s(x, y) ∈ C ↔ (orderedBlocksOfComponents hG e).block x ≠
      (orderedBlocksOfComponents hG e).block y := by
  refine ⟨fun h hn => cut_separates hG hadj h (e.injective hn), fun hn => ?_⟩
  by_contra h
  exact hn (congrArg e (same_component_of_uncut hadj h))


/-- Every cut on a tree path has at most two incidences at each vertex. -/
theorem OnSpine.incidence_le_two [Finite V] (hG : G.IsTree) {C : Set (Sym2 V)}
    (hs : OnSpine G C) (x : V) : cutIncidence G C x ≤ 2 := by
  obtain ⟨k, ⟨e⟩⟩ := componentGraph_path hG hs
  let B := orderedBlocksOfComponents hG.isAcyclic e.symm
  exact block_degree_bound B
    (fun _ _ => orderedBlocksOfComponents_cut_iff hG.isAcyclic e.symm) x


/-- The witnessing cut consists of the actual joins in the supplied presentation. -/
theorem LabeledChain.joinEdges_certificate [Finite V] (hG : G.IsTree) {k m : ℕ}
    (L : LabeledChain G k) (hmin : ∀ i, m ≤ L.length i + 1) :
    OnSpine G L.joinEdges ∧ (0 < k ↔ L.joinEdges.Nonempty) ∧
    ∀ x, ResidualVertexCondition G L.joinEdges m x := by
  have hc : ∀ x y, G.Adj x y → (s(x, y) ∈ L.joinEdges ↔ L.ordered.block x ≠ L.ordered.block y) :=
    fun _ _ => L.mem_joinEdges
  have hpos := block_positive_iff_cut_nonempty L.ordered L.joinEdges_subset hc
  refine ⟨L.joinEdges_on_spine hG, hpos, fun x => ?_⟩
  unfold ResidualVertexCondition
  rw [L.residual_degree x]
  refine ⟨pathGraph_degree_le_two _, ?_, ?_⟩
  · intro _ htwo
    exact pathGraph_one_degree_zero (L.double_incidence_singleton htwo) _
  · intro hm
    have hn := hmin (L.block x)
    have hpos : 0 < L.length (L.block x) := by omega
    have hmax := (L.joinEdges_on_spine hG).incidence_le_two hG x
    have hne : cutIncidence G L.joinEdges x ≠ 2 :=
      fun he => (Nat.ne_of_gt hpos) (L.double_incidence_singleton he)
    exact ⟨by omega, pathGraph_degree_pos hpos _⟩

theorem oneJoined_to_spineCut [Finite V] (hG : G.IsTree) {m : ℕ} {requireJoin : Bool} :
    OneJoined G m requireJoin → SpineCut G m requireJoin := by
  rintro ⟨k, L, hrequire, hmin⟩
  obtain ⟨hs, hpos, hlocal⟩ := L.joinEdges_certificate hG hmin
  exact (residualSpineCut_iff_spineCut m requireJoin).mp
    ⟨L.joinEdges, hs, fun h => hpos.mp (hrequire h), hlocal⟩

private theorem residual_induce_eq_of_blocks {k : ℕ} (B : OrderedBlocks G k) {C : Set (Sym2 V)}
    (hC : ∀ x y, G.Adj x y → (s(x, y) ∈ C ↔ B.block x ≠ B.block y)) (i : Fin (k + 1)) :
    (G.deleteEdges C).induce {x | B.block x = i} = G.induce {x | B.block x = i} := by
  ext x y
  change (G.deleteEdges C).Adj x.val y.val ↔ G.Adj x.val y.val
  rw [deleteEdges_adj]
  exact ⟨And.left, fun h => ⟨h, fun hc => (hC _ _ h).mp hc (x.property.trans y.property.symm)⟩⟩

private theorem residual_degree_on_block {k : ℕ} (B : OrderedBlocks G k) {C : Set (Sym2 V)}
    (hC : ∀ x y, G.Adj x y → (s(x, y) ∈ C ↔ B.block x ≠ B.block y)) {i : Fin (k + 1)}
    (x : {x // B.block x = i}) : degree (G.induce {x | B.block x = i}) x =
      degree (G.deleteEdges C) x.val := by
  rw [← residual_induce_eq_of_blocks B hC]
  apply degree_induce_fiber
  intro y hadj
  obtain ⟨hadj, hn⟩ := deleteEdges_adj.mp hadj
  exact (not_ne_iff.mp (fun h => hn ((hC x.val y hadj).mpr h))).symm.trans x.property

private theorem orderedBlocksOfComponents_tree (hG : G.IsAcyclic) {C : Set (Sym2 V)} {k : ℕ}
    (e : componentGraph G C ≃g pathGraph (k + 1)) (i : Fin (k + 1)) :
    (G.induce {x | (orderedBlocksOfComponents hG e).block x = i}).IsTree := by
  let B := orderedBlocksOfComponents hG e
  change (G.induce {x | B.block x = i}).IsTree
  rw [← residual_induce_eq_of_blocks B (fun _ _ => orderedBlocksOfComponents_cut_iff hG e)]
  let cc := e.symm i
  have he : {x | B.block x = i} = cc.supp := by
    ext x
    rw [ConnectedComponent.mem_supp_iff]
    change e (component G C x) = i ↔ component G C x = e.symm i
    exact ⟨fun h => e.injective (h.trans (e.apply_symm_apply i).symm),
      fun h => by rw [h, e.apply_symm_apply]⟩
  rw [he]
  exact ⟨cc.connected_toSimpleGraph, (hG.anti (deleteEdges_le C)).induce _⟩

private theorem OrderedBlocks.incoming_unique {k : ℕ} (B : OrderedBlocks G k) {x x' : V}
    (h : B.Incoming x) (h' : B.Incoming x') (he : B.block x = B.block x') :
    x = x' := by
  obtain ⟨y, hxy, hi⟩ := h
  obtain ⟨y', hxy', hi'⟩ := h'
  have he' : (B.block x).val = (B.block x').val := congrArg Fin.val he
  have hn : B.block x ≠ B.block y := by
    intro h
    have := congrArg Fin.val h
    omega
  exact (B.unique hxy hxy' hn he (Fin.ext (by omega))).1

private theorem OrderedBlocks.outgoing_unique {k : ℕ} (B : OrderedBlocks G k) {x x' : V}
    (h : B.Outgoing x) (h' : B.Outgoing x') (he : B.block x = B.block x') :
    x = x' := by
  obtain ⟨y, hxy, hi⟩ := h
  obtain ⟨y', hxy', hi'⟩ := h'
  have he' : (B.block x).val = (B.block x').val := congrArg Fin.val he
  have hn : B.block x ≠ B.block y := by
    intro h
    have := congrArg Fin.val h
    omega
  exact (B.unique hxy hxy' hn he (Fin.ext (by omega))).1

/-- Prescribe up to two label positions. The only permitted collision of the
requested ports is on a singleton, where the two positions coincide. -/
private theorem labels_for_ports {W : Type*} {n : ℕ} (e : Fin (n + 1) ≃ W)
    (I O : W → Prop) (hi : ∀ a b, I a → I b → a = b)
    (ho : ∀ a b, O a → O b → a = b)
    (hd : ∀ a, I a → O a → n = 0) :
    ∃ l : Fin (n + 1) ≃ W,
      (∀ a, I a → a = l 0) ∧ (∀ b, O b → b = l (Fin.last n)) := by
  classical
  by_cases hn : n = 0
  · subst n
    have same (i j : Fin (0 + 1)) : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    have fixed (a : W) (i : Fin (0 + 1)) : a = e i :=
      (e.apply_symm_apply a).symm.trans (congrArg e (same (e.symm a) i))
    exact ⟨e, fun a _ => fixed a _, fun b _ => fixed b _⟩
  have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro he
    have hval := congrArg Fin.val he
    change 0 = n at hval
    exact hn hval.symm
  by_cases hI : ∃ a, I a
  · obtain ⟨a, ha⟩ := hI
    let f := e.trans (Equiv.swap (e 0) a)
    have hf : f 0 = a := by simp [f]
    have hfne : f 0 ≠ f (Fin.last n) := fun he => h0 (f.injective he)
    by_cases hO : ∃ b, O b
    · obtain ⟨b, hb⟩ := hO
      have hab : a ≠ b := by
        intro he
        exact hn (hd a ha (he.symm ▸ hb))
      let l := f.trans (Equiv.swap (f (Fin.last n)) b)
      have hl₀ : l 0 = a := by
        change Equiv.swap _ _ (f 0) = a
        rw [Equiv.swap_apply_of_ne_of_ne hfne (by simpa only [hf] using hab), hf]
      have hl₁ : l (Fin.last n) = b := by simp [l]
      exact ⟨l, fun x hx => (hi x a hx ha).trans hl₀.symm,
        fun x hx => (ho x b hx hb).trans hl₁.symm⟩
    · exact ⟨f, fun x hx => (hi x a hx ha).trans hf.symm,
        fun x hx => (hO ⟨x, hx⟩).elim⟩
  · by_cases hO : ∃ b, O b
    · obtain ⟨b, hb⟩ := hO
      let l := e.trans (Equiv.swap (e (Fin.last n)) b)
      have hl : l (Fin.last n) = b := by simp [l]
      exact ⟨l, fun x hx => (hI ⟨x, hx⟩).elim, fun x hx => (ho x b hx hb).trans hl.symm⟩
    · exact ⟨e, fun x hx => (hI ⟨x, hx⟩).elim, fun x hx => (hO ⟨x, hx⟩).elim⟩

/-- A spine cut satisfying the degree conditions is realized by a labeled chain
whose set of actual interblock joins is exactly the supplied cut. -/
theorem realizes_spine_cut [Finite V] (hG : G.IsTree) {m : ℕ} (hm : m = 1 ∨ m = 2)
    (C : Set (Sym2 V)) (hs : OnSpine G C)
    (hlocal : ∀ x, ResidualVertexCondition G C m x) :
    ∃ k, ∃ L : LabeledChain G k, L.joinEdges = C ∧
      (0 < k ↔ C.Nonempty) ∧ ∀ i, m ≤ L.length i + 1 := by
  classical
  obtain ⟨k, ⟨e⟩⟩ := componentGraph_path hG hs
  let B := orderedBlocksOfComponents hG.isAcyclic e.symm
  have hC (x y : V) (hxy : G.Adj x y) : s(x, y) ∈ C ↔ B.block x ≠ B.block y :=
    orderedBlocksOfComponents_cut_iff hG.isAcyclic e.symm hxy
  let Fiber (i : Fin (k + 1)) := {x // B.block x = i}
  have hpaths (i : Fin (k + 1)) :
      ∃ n, Nonempty (pathGraph (n + 1) ≃g G.induce {x | B.block x = i}) :=
    path_of_degree_le_two (orderedBlocksOfComponents_tree hG.isAcyclic e.symm i)
      (fun x => (residual_degree_on_block B hC x).trans_le (hlocal x.val).1)
  choose n hp using hpaths
  let path (i : Fin (k + 1)) := (hp i).some
  have hdegree (i : Fin (k + 1)) (x : Fiber i) :
      degree (G.deleteEdges C) x.val = degree (pathGraph (n i + 1)) ((path i).symm x) :=
    (residual_degree_on_block B hC x).symm.trans (degree_iso _ (path i).symm x).symm
  have hports (i : Fin (k + 1)) :
      ∃ l : Fin (n i + 1) ≃ Fiber i,
        (∀ a : Fiber i, B.Incoming a.val → a = l 0) ∧
        (∀ b : Fiber i, B.Outgoing b.val → b = l (Fin.last (n i))) := by
    apply labels_for_ports (path i).toEquiv (fun a => B.Incoming a.val) (fun a => B.Outgoing a.val)
    · intro a b ha hb
      exact Subtype.ext (B.incoming_unique ha hb (a.property.trans b.property.symm))
    · intro a b ha hb
      exact Subtype.ext (B.outgoing_unique ha hb (a.property.trans b.property.symm))
    · intro a ha hb
      have htwo := (two_incidence_iff B hC a.val).mpr ⟨ha, hb⟩
      rcases hm with hm | hm
      · have hz := (hlocal a.val).2.1 hm htwo
        rw [hdegree i a] at hz
        by_contra hn
        have hh := pathGraph_degree_pos (Nat.pos_of_ne_zero hn) ((path i).symm a)
        omega
      · have hh := ((hlocal a.val).2.2 hm).1
        omega
  choose labels hl using hports
  have entry (x : V) (h : B.Incoming x) : x = (labels (B.block x) 0).val :=
    congrArg Subtype.val ((hl (B.block x)).1 ⟨x, rfl⟩ h)
  have exit (x : V) (h : B.Outgoing x) :
      x = (labels (B.block x) (Fin.last (n (B.block x)))).val :=
    congrArg Subtype.val ((hl (B.block x)).2 ⟨x, rfl⟩ h)
  have ports_adj (x y : V) (h : (B.block x).val + 1 = (B.block y).val)
      (hx : x = (labels (B.block x) (Fin.last (n (B.block x)))).val)
      (hy : y = (labels (B.block y) 0).val) : G.Adj x y := by
    obtain ⟨a, b, ha, hb, hab⟩ := B.join (B.block x) (B.block y) h
    have hab' : (B.block a).val + 1 = (B.block b).val := by rwa [ha, hb]
    have hax := exit a ⟨b, hab, hab'⟩
    have hby := entry b ⟨a, hab.symm, hab'⟩
    rw [ha, ← hx] at hax
    rw [hb, ← hy] at hby
    simpa only [hax, hby] using hab
  let L : LabeledChain G k :=
    { block := B.block
      length := n
      path := path
      label := labels
      cross := by
        intro x y hne
        constructor
        · intro hxy
          rcases pathGraph_adj.mp (B.only hxy hne) with h | h
          · exact Or.inl ⟨h, exit x ⟨y, hxy, h⟩, entry y ⟨x, hxy.symm, h⟩⟩
          · exact Or.inr ⟨h, exit y ⟨x, hxy.symm, h⟩, entry x ⟨y, hxy, h⟩⟩
        · rintro (⟨h, hx, hy⟩ | ⟨h, hy, hx⟩)
          · exact ports_adj x y h hx hy
          · exact (ports_adj y x h hy hx).symm }
  refine ⟨k, L, ?_, block_positive_iff_cut_nonempty B hs.subset_edgeSet hC, ?_⟩
  · ext f
    induction f using Sym2.inductionOn with
    | hf x y =>
      by_cases hxy : G.Adj x y
      · exact (L.mem_joinEdges hxy).trans (hC x y hxy).symm
      · exact iff_of_false (fun h => hxy (L.joinEdges_subset h))
          (fun h => hxy (hs.subset_edgeSet h))
  · intro i
    change m ≤ n i + 1
    rcases hm with hm | hm
    · omega
    · by_contra h
      have hn : n i = 0 := by omega
      let x := path i 0
      have hpos := ((hlocal x.val).2.2 hm).2
      rw [hdegree i x, pathGraph_one_degree_zero hn] at hpos
      omega

theorem spineCut_to_oneJoined [Finite V] (hG : G.IsTree) {m : ℕ} (hm : m = 1 ∨ m = 2)
    {requireJoin : Bool} : SpineCut G m requireJoin → OneJoined G m requireJoin := by
  intro h
  obtain ⟨C, hs, hpos, hlocal⟩ := (residualSpineCut_iff_spineCut m requireJoin).mpr h
  obtain ⟨k, L, _, hk, hmin⟩ := realizes_spine_cut hG hm C hs hlocal
  exact ⟨k, L, fun h => hk.mpr (hpos h), hmin⟩

/-- Classification of 1-joined path trees for both minimum block sizes and
both conventions on the presence of an actual join. A tree is connected and
therefore has a nonempty vertex type. -/
theorem oneJoined_iff_spineCut [Finite V] (hG : G.IsTree) {m : ℕ} (hm : m = 1 ∨ m = 2)
    (requireJoin : Bool) : OneJoined G m requireJoin ↔ SpineCut G m requireJoin :=
  ⟨oneJoined_to_spineCut hG, spineCut_to_oneJoined hG hm⟩

end

end OneJoinedPathTrees
