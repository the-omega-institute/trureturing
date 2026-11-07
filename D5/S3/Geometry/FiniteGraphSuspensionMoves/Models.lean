/- GID: D5/S3/Geometry/FiniteGraphSuspensionMoves/Models
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSuspensionMoves/Models
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Subgraph]
   utility: none
   digest: Exact local edge subgraphs and their maximal independent sets. -/
import D5.S3.Geometry.FiniteGraphSubgraphSuspension

/-!
# Finite local subgraphs and maximal independent sets

An injective graph map specifies precisely the model edges, including when
extra ambient edges join vertices in its range. Maximal independent sets
are transported through the resulting local graph isomorphism. The edge,
two-edge matching and nonempty star models have explicit maximal-set
classifications used by the suspension moves.
-/

noncomputable section

namespace D5.S3.Geometry.FiniteGraphSuspensionMoves

open FiniteGraphSubgraphSuspension

variable {A B V : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype V] [DecidableEq V]

/-- Relabel a maximal independent set, preserving inclusion maximality. -/
def mapMax {T : SimpleGraph A} {S : SimpleGraph B} (e : T ≃g S)
    (M : MaxIndependent T) : MaxIndependent S := by
  classical
  refine ⟨M.val.image e, ?_, ?_⟩
  · intro x hx y hy hxy h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact M.property.1 ha hb (fun hab => hxy (congrArg e hab))
      (e.map_adj_iff.mp h)
  · intro N hN hMN x hx
    have hpre : T.IsIndepSet ((N.image e.symm : Finset A) : Set A) := by
      intro a ha b hb hab h
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      exact hN hx hy (fun hxy => hab (congrArg e.symm hxy))
        (e.symm.map_adj_iff.mp h)
    have hsub : M.val ⊆ N.image e.symm := by
      intro a ha
      exact Finset.mem_image.mpr ⟨e a,
        hMN (Finset.mem_image.mpr ⟨a, ha, rfl⟩), e.symm_apply_apply a⟩
    have ha := M.property.2 _ hpre hsub
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    exact Finset.mem_image.mpr ⟨e.symm x, ha, e.apply_symm_apply x⟩

def maxEquiv {T : SimpleGraph A} {S : SimpleGraph B} (e : T ≃g S) :
    MaxIndependent T ≃ MaxIndependent S where
  toFun := mapMax e
  invFun := mapMax e.symm
  left_inv M := by
    apply Subtype.ext
    simp [mapMax, Finset.image_image, Function.comp_def]
  right_inv M := by
    apply Subtype.ext
    simp [mapMax, Finset.image_image, Function.comp_def]

/-- Only the specified model edges are inserted, even when G has extra edges
between vertices in the image. In particular this is NOT an induced subgraph. -/
def embeddedSubgraph (G : SimpleGraph V) (T : SimpleGraph A) (e : A ↪ V)
    (he : ∀ x y, T.Adj x y → G.Adj (e x) (e y)) : G.Subgraph where
  verts := Set.range e
  Adj x y := ∃ a b, T.Adj a b ∧ e a = x ∧ e b = y
  adj_sub := by rintro x y ⟨a, b, h, rfl, rfl⟩; exact he a b h
  edge_vert := by rintro x y ⟨a, b, h, rfl, rfl⟩; exact ⟨a, rfl⟩
  symm.symm := by
    rintro x y ⟨a, b, h, ha, hb⟩
    exact ⟨b, a, T.adj_symm h, hb, ha⟩

def rangeEquiv (e : A ↪ V) : A ≃ Set.range e where
  toFun a := ⟨e a, a, rfl⟩
  invFun x := Classical.choose x.property
  left_inv a := e.injective (Classical.choose_spec (show e a ∈ Set.range e from ⟨a, rfl⟩))
  right_inv x := Subtype.ext (Classical.choose_spec x.property)

instance embeddedFintype (G : SimpleGraph V) (T : SimpleGraph A) (e : A ↪ V)
    (he : ∀ x y, T.Adj x y → G.Adj (e x) (e y)) :
    Fintype (embeddedSubgraph G T e he).verts :=
  Fintype.ofEquiv A (rangeEquiv e)

def embeddedIso (G : SimpleGraph V) (T : SimpleGraph A) (e : A ↪ V)
    (he : ∀ x y, T.Adj x y → G.Adj (e x) (e y)) :
    T ≃g (embeddedSubgraph G T e he).coe where
  toEquiv := rangeEquiv e
  map_rel_iff' := by
    intro a b
    change (∃ x y, T.Adj x y ∧ e x = e a ∧ e y = e b) ↔ T.Adj a b
    constructor
    · rintro ⟨x, y, h, hx, hy⟩
      exact (e.injective hx) ▸ (e.injective hy) ▸ h
    · intro h; exact ⟨a, b, h, rfl, rfl⟩

/-- Actual complement membership, including the local vertex restriction. -/
theorem embedded_complement (G : SimpleGraph V) (T : SimpleGraph A) (e : A ↪ V)
    (he : ∀ x y, T.Adj x y → G.Adj (e x) (e y))
    (M : MaxIndependent T) (x : V) :
    (x ∈ (embeddedSubgraph G T e he).verts ∧
      x ∉ (mapMax (embeddedIso G T e he) M).val.image Subtype.val) ↔
      ∃ a, e a = x ∧ a ∉ M.val := by
  classical
  have himage : (mapMax (embeddedIso G T e he) M).val.image Subtype.val =
      M.val.image e := by
    change (M.val.image (embeddedIso G T e he)).image Subtype.val = _
    rw [Finset.image_image]
    rfl
  rw [himage]
  constructor
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, rfl, fun h => ha (Finset.mem_image.mpr ⟨a, h, rfl⟩)⟩
  · rintro ⟨a, rfl, ha⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    rintro hx
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hx
    exact ha (e.injective hba ▸ hb)

/-- The single edge on two labeled endpoints. -/
def edgeModel : SimpleGraph Bool := ⊤

instance : DecidableRel edgeModel.Adj := by
  unfold edgeModel
  infer_instance

def edgeSet (b : Bool) : Finset Bool := {!b}

private theorem edgeSet_maximal (b : Bool) :
    edgeModel.IsIndepSet (edgeSet b : Set Bool) ∧
      ∀ N : Finset Bool, edgeModel.IsIndepSet (N : Set Bool) →
        edgeSet b ⊆ N → N ⊆ edgeSet b := by
  cases b <;> decide

def edgeMax (b : Bool) : MaxIndependent edgeModel :=
  ⟨edgeSet b, edgeSet_maximal b⟩

/-- Exhaustive inclusion-maximal classification, proved by kernel reduction
on the two-vertex graph, not by a native evaluator. -/
theorem edge_max_classification (M : MaxIndependent edgeModel) :
    M.val = edgeSet false ∨ M.val = edgeSet true := by
  have hall : ∀ s : Finset Bool,
      (edgeModel.IsIndepSet (s : Set Bool) ∧
        ∀ N : Finset Bool, edgeModel.IsIndepSet (N : Set Bool) → s ⊆ N → N ⊆ s) →
      s = edgeSet false ∨ s = edgeSet true := by decide
  exact hall M.val M.property

def edgeMaxEquiv : Bool ≃ MaxIndependent edgeModel :=
  Equiv.ofBijective edgeMax ⟨by
    intro a b hab
    have h := congrArg Subtype.val hab
    have hinj : Function.Injective edgeSet := by decide
    exact hinj h, by
    intro M
    rcases edge_max_classification M with h | h
    · exact ⟨false, Subtype.ext h.symm⟩
    · exact ⟨true, Subtype.ext h.symm⟩⟩

/-- The matching has edges (false,false)--(false,true) and
(true,false)--(true,true), regardless of ambient cross edges. -/
def matchingModel : SimpleGraph (Bool × Bool) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm.symm := fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩
  loopless.irrefl := by intro x h; exact h.2 rfl

instance : DecidableRel matchingModel.Adj := by
  change DecidableRel (fun x y : Bool × Bool => x.1 = y.1 ∧ x.2 ≠ y.2)
  infer_instance

def quadrantSet (p : Bool × Bool) : Finset (Bool × Bool) :=
  {(false, !p.1), (true, !p.2)}

private theorem quadrantSet_maximal (p : Bool × Bool) :
    matchingModel.IsIndepSet (quadrantSet p : Set (Bool × Bool)) ∧
      ∀ N : Finset (Bool × Bool), matchingModel.IsIndepSet (N : Set (Bool × Bool)) →
        quadrantSet p ⊆ N → N ⊆ quadrantSet p := by
  rcases p with ⟨s, t⟩
  cases s <;> cases t <;> decide

def quadrantMax (p : Bool × Bool) : MaxIndependent matchingModel :=
  ⟨quadrantSet p, quadrantSet_maximal p⟩

/-- Exactly the four choices of one endpoint on each edge. -/
theorem matching_max_classification (M : MaxIndependent matchingModel) :
    M.val = quadrantSet (false, false) ∨ M.val = quadrantSet (false, true) ∨
      M.val = quadrantSet (true, false) ∨ M.val = quadrantSet (true, true) := by
  have hall : ∀ s : Finset (Bool × Bool),
      (matchingModel.IsIndepSet (s : Set (Bool × Bool)) ∧
        ∀ N : Finset (Bool × Bool), matchingModel.IsIndepSet (N : Set (Bool × Bool)) →
          s ⊆ N → N ⊆ s) →
      s = quadrantSet (false, false) ∨ s = quadrantSet (false, true) ∨
        s = quadrantSet (true, false) ∨ s = quadrantSet (true, true) := by decide
  exact hall M.val M.property

def quadrantMaxEquiv : (Bool × Bool) ≃ MaxIndependent matchingModel :=
  Equiv.ofBijective quadrantMax ⟨by
    intro a b hab
    have hinj : Function.Injective quadrantSet := by decide
    exact hinj (congrArg Subtype.val hab), by
    intro M
    rcases matching_max_classification M with h | h | h | h
    · exact ⟨(false, false), Subtype.ext h.symm⟩
    · exact ⟨(false, true), Subtype.ext h.symm⟩
    · exact ⟨(true, false), Subtype.ext h.symm⟩
    · exact ⟨(true, true), Subtype.ext h.symm⟩⟩

section Star

variable (L : Type) [Fintype L] [DecidableEq L]

def starModel : SimpleGraph (Option L) where
  Adj x y := match x, y with
    | none, some _ => True
    | some _, none => True
    | _, _ => False
  symm.symm := by intro x y; cases x <;> cases y <;> simp
  loopless.irrefl := by intro x; cases x <;> simp

def leaves : Finset (Option L) := Finset.univ.image some

@[simp] theorem mem_leaves (x : Option L) : x ∈ leaves L ↔ x ≠ none := by
  cases x <;> simp [leaves]

private theorem leaves_independent : (starModel L).IsIndepSet (leaves L : Set (Option L)) := by
  intro x hx y hy _ h
  have hx' := (mem_leaves L x).mp hx
  have hy' := (mem_leaves L y).mp hy
  cases x <;> cases y <;> simp_all [starModel]

private theorem center_independent :
    (starModel L).IsIndepSet ({none} : Set (Option L)) := by
  intro x hx y hy hxy _
  simp only [Set.mem_singleton_iff] at hx hy
  exact hxy (hx.trans hy.symm)

private theorem center_maximal :
    ∀ N : Finset (Option L), (starModel L).IsIndepSet (N : Set (Option L)) →
      {none} ⊆ N → N ⊆ {none} := by
  intro N hN hsub x hx
  cases x with
  | none => simp
  | some x =>
    have hnone : (none : Option L) ∈ N := hsub (Finset.mem_singleton_self _)
    exact False.elim (hN hnone hx (by simp) (by trivial))

private theorem leaves_maximal [Nonempty L] :
    ∀ N : Finset (Option L), (starModel L).IsIndepSet (N : Set (Option L)) →
      leaves L ⊆ N → N ⊆ leaves L := by
  intro N hN hsub x hx
  cases x with
  | none =>
    let l : L := Classical.choice inferInstance
    exact False.elim (hN hx (hsub (by simp : some l ∈ leaves L))
      (by simp) (by trivial))
  | some x => simp

def starMax [Nonempty L] (b : Bool) : MaxIndependent (starModel L) :=
  if b then ⟨leaves L, leaves_independent L, leaves_maximal L⟩
  else ⟨{none}, by simpa only [Finset.coe_singleton] using center_independent L,
    center_maximal L⟩

/-- A nonempty star has exactly {center} and the full leaf set as its maximal
independent sets. Edges in an ambient graph between leaves play no role. -/
theorem star_max_classification [Nonempty L] (M : MaxIndependent (starModel L)) :
    M.val = {none} ∨ M.val = leaves L := by
  by_cases hc : none ∈ M.val
  · left
    apply Finset.Subset.antisymm
    · intro x hx
      cases x with
      | none => simp
      | some x => exact False.elim (M.property.1 hc hx (by simp) (by trivial))
    · simpa using hc
  · right
    have hs : M.val ⊆ leaves L := by
      intro x hx
      exact (mem_leaves L x).mpr (fun h => hc (h ▸ hx))
    exact Finset.Subset.antisymm hs (M.property.2 _ (leaves_independent L) hs)

def starMaxEquiv [Nonempty L] : Bool ≃ MaxIndependent (starModel L) :=
  Equiv.ofBijective (starMax L) ⟨by
    intro a b hab
    cases a <;> cases b <;> try rfl
    all_goals
      have h := congrArg (fun M : MaxIndependent (starModel L) => none ∈ M.val) hab
      simp [starMax] at h, by
    intro M
    rcases star_max_classification L M with h | h
    · exact ⟨false, Subtype.ext h.symm⟩
    · exact ⟨true, Subtype.ext h.symm⟩⟩

end Star

/- The supplier's local adjacency is private. These definitional equations
expose only its public graph and do not alter or duplicate the supplier. -/
section LocalEquations
variable (G : SimpleGraph V) (H : G.Subgraph)

@[simp] theorem local_old_old (x y : V) :
    (localSuspensionGraph G H).Adj (.inl x) (.inl y) ↔ G.Adj x y ∧ ¬ H.Adj x y := Iff.rfl
@[simp] theorem local_old_hub (x : V) :
    ¬ (localSuspensionGraph G H).Adj (.inl x) (.inr none) := id
@[simp] theorem local_hub_old (x : V) :
    ¬ (localSuspensionGraph G H).Adj (.inr none) (.inl x) := id
@[simp] theorem local_old_apex (x : V) (M : MaxIndependent H.coe) :
    (localSuspensionGraph G H).Adj (.inl x) (.inr (some M)) ↔
      x ∈ H.verts ∧ x ∉ M.val.image Subtype.val := Iff.rfl
@[simp] theorem local_apex_old (x : V) (M : MaxIndependent H.coe) :
    (localSuspensionGraph G H).Adj (.inr (some M)) (.inl x) ↔
      x ∈ H.verts ∧ x ∉ M.val.image Subtype.val := Iff.rfl
@[simp] theorem local_hub_hub :
    ¬ (localSuspensionGraph G H).Adj (.inr none) (.inr none) := id
@[simp] theorem local_hub_apex (M : MaxIndependent H.coe) :
    (localSuspensionGraph G H).Adj (.inr none) (.inr (some M)) := trivial
@[simp] theorem local_apex_hub (M : MaxIndependent H.coe) :
    (localSuspensionGraph G H).Adj (.inr (some M)) (.inr none) := trivial
@[simp] theorem local_apex_apex (M N : MaxIndependent H.coe) :
    ¬ (localSuspensionGraph G H).Adj (.inr (some M)) (.inr (some N)) := id
end LocalEquations

end D5.S3.Geometry.FiniteGraphSuspensionMoves
