/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: The cycle with two pendant paths and a bridged triangle in Question 1.9. -/

import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph
import D5.S3.Combinatorics.Graph.ZeroForcing.CycleConnectedForcing
import D5.S3.Combinatorics.Graph.ZeroForcing.PathConnectedForcing

/-! The support and tree configurations for the fixed graph in the counterexample to
Question 1.9 of Cambie, Jooken and Wagner (arXiv:2508.20593v2). -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

open SimpleGraph

open private arc mem_arc arc_connected eq_arc_of_connected card_arc arc_injective from
  D5.S3.Combinatorics.Graph.ZeroForcing.CycleConnectedForcing
open private interval_connected convex_of_connected from
  D5.S3.Combinatorics.Graph.ZeroForcing.PathConnectedForcing
open scoped BigOperators

/-- The actual tree subgraphs of order k. The vertices are part of each subgraph. -/
abbrev SubtreesOfOrder {V : Type} (G : SimpleGraph V) (k : ℕ) :=
  {H : G.Subgraph // H.coe.IsTree ∧ Nat.card H.verts = k}

/-- The source's subtree count. -/
noncomputable def subtreeCount {V : Type} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card (SubtreesOfOrder G k)

/-- The source's total number of subtrees. -/
noncomputable def totalSubtreeCount {V : Type} (G : SimpleGraph V) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (Nat.card V), subtreeCount G k

/-- The source's sum of orders of subtrees. -/
noncomputable def totalSubtreeOrder {V : Type} (G : SimpleGraph V) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (Nat.card V), k * subtreeCount G k

/-- The subtree mean over the exact rationals. -/
noncomputable def meanSubtreeOrder {V : Type} (G : SimpleGraph V) : ℚ :=
  (totalSubtreeOrder G : ℚ) / (totalSubtreeCount G : ℚ)

/-- Vertex sets whose induced graph is connected. -/
abbrev ConnectedSets {V : Type} (G : SimpleGraph V) :=
  {S : Set V // (G.induce S).Connected}

/-- The mean order of a connected induced vertex set. -/
noncomputable def meanConnectedOrder {V : Type} [Finite V] (G : SimpleGraph V) : ℚ := by
  letI : Fintype (ConnectedSets G) := Fintype.ofFinite _
  exact (↑(∑ S : ConnectedSets G, Nat.card S.val) : ℚ) /
    (Nat.card (ConnectedSets G) : ℚ)

/-- Question 1.9 for every finite simple connected graph. -/
def claim : Prop :=
  ∀ (V : Type) (finiteV : Finite V) (G : SimpleGraph V),
    G.Connected → @meanConnectedOrder V finiteV G ≤ meanSubtreeOrder G

section Intervals

private abbrev cycleArc {m : ℕ} (a : Fin (m + 3)) (i : ℕ) :=
  arc a i

/-- A cycle support is either the whole cycle or a proper arc with nonzero length. -/
abbrev CycleInterval (m : ℕ) := Unit ⊕ (Fin (m + 3) × {l : Fin (m + 3) // 0 < l.val})

def CycleInterval.cycleVertices {m : ℕ} : CycleInterval m → Set (Fin (m + 3))
  | .inl _ => Set.univ
  | .inr (x, l) => cycleArc x l.val.val

def CycleInterval.cycleOrder {m : ℕ} : CycleInterval m → ℕ
  | .inl _ => m + 3
  | .inr (_, l) => l.val.val

private theorem CycleInterval.connected {m : ℕ} (c : CycleInterval m) :
    ((cycleGraph (m + 3)).induce c.cycleVertices).Connected := by
  rcases c with _ | ⟨x, l⟩
  · exact ((induceUnivIso _).connected_iff).mpr connected_cycleGraph_add_one
  · exact arc_connected x l.val.val l.property

private theorem CycleInterval.card_vertices {m : ℕ} (c : CycleInterval m) :
    Nat.card c.cycleVertices = c.cycleOrder := by
  rcases c with _ | ⟨x, l⟩
  · simp [CycleInterval.cycleVertices, CycleInterval.cycleOrder, Nat.card_eq_fintype_card]
  · change Nat.card ↥(↑(cycleArc x l.val.val) : Set (Fin (m + 3))) = l.val.val
    rw [show Nat.card ↥(↑(cycleArc x l.val.val) : Set (Fin (m + 3))) =
        (cycleArc x l.val.val).card from
      (Nat.card_eq_fintype_card (α := ↥(cycleArc x l.val.val))).trans (Fintype.card_coe _),
      card_arc, min_eq_right l.val.isLt.le]

private theorem CycleInterval.injective_vertices {m : ℕ} :
    Function.Injective (@CycleInterval.cycleVertices m) := by
  intro a b h
  have hc := congrArg (fun s : Set (Fin (m + 3)) => Nat.card s) h
  rw [a.card_vertices, b.card_vertices] at hc
  rcases a with a | ⟨x, l⟩ <;> rcases b with b | ⟨y, k⟩
  · cases a; cases b; rfl
  · exact (k.val.isLt.ne hc.symm).elim
  · exact (l.val.isLt.ne hc).elim
  · have hlk : l = k := Subtype.ext (Fin.ext hc)
    subst k
    have hab : cycleArc x l.val.val = cycleArc y l.val.val :=
      Finset.coe_injective h
    have hxy := arc_injective
      l.val.val l.property l.val.isLt hab
    subst y
    rfl

private theorem CycleInterval.exists_vertices {m : ℕ} (S : Set (Fin (m + 3)))
    (hS : ((cycleGraph (m + 3)).induce S).Connected) :
    ∃ c : CycleInterval m, c.cycleVertices = S := by
  classical
  by_cases hu : S = Set.univ
  · exact ⟨.inl (), hu.symm⟩
  have hmiss : ∃ a, a ∉ S := by simpa [Set.eq_univ_iff_forall] using hu
  obtain ⟨a, ha⟩ := hmiss
  have hc : ((cycleGraph (m + 3)).induce (S.toFinset : Set (Fin (m + 3)))).Connected := by
    rw [Set.coe_toFinset]; exact hS
  obtain ⟨x, l, hl, he⟩ := eq_arc_of_connected
    S.toFinset a (by simpa using ha) hc
  have hlt : l < m + 3 := by
    by_contra hn
    have h := (a - x).isLt
    apply ha
    have : a ∈ S.toFinset := by
      rw [he, mem_arc]
      omega
    simpa using this
  refine ⟨.inr (x, ⟨⟨l, hlt⟩, hl⟩), ?_⟩
  change (cycleArc x l : Set (Fin (m + 3))) = S
  exact (congrArg (fun F : Finset (Fin (m + 3)) => (↑F : Set (Fin (m + 3)))) he.symm).trans
    (Set.coe_toFinset S)

/-- An interval in a detached path is specified by its two ordered endpoints. -/
abbrev PathInterval (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

private def PathInterval.pathVertices {n : ℕ} (p : PathInterval n) : Set (Fin n) :=
  Set.Icc p.val.1 p.val.2

def PathInterval.order {n : ℕ} (p : PathInterval n) : ℕ :=
  p.val.2.val + 1 - p.val.1.val

private theorem PathInterval.connected {n : ℕ} (p : PathInterval n) :
    ((pathGraph n).induce p.pathVertices).Connected :=
  interval_connected _ _ p.property

private theorem PathInterval.card_vertices {n : ℕ} (p : PathInterval n) :
    Nat.card p.pathVertices = p.order := by
  classical
  unfold PathInterval.pathVertices
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  simp [PathInterval.order, Set.toFinset_Icc]

private theorem PathInterval.injective_vertices {n : ℕ} :
    Function.Injective (@PathInterval.pathVertices n) := by
  intro p q h
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨c, d⟩, hcd⟩ := q
  change Set.Icc a b = Set.Icc c d at h
  have ha : a ∈ Set.Icc c d := h ▸ Set.left_mem_Icc.mpr hab
  have hb : b ∈ Set.Icc c d := h ▸ Set.right_mem_Icc.mpr hab
  have hc : c ∈ Set.Icc a b := h.symm ▸ Set.left_mem_Icc.mpr hcd
  have hd : d ∈ Set.Icc a b := h.symm ▸ Set.right_mem_Icc.mpr hcd
  exact Subtype.ext (Prod.ext (le_antisymm hc.1 ha.1) (le_antisymm hb.2 hd.2))

private theorem PathInterval.exists_vertices {n : ℕ} (S : Set (Fin n))
    (hS : ((pathGraph n).induce S).Connected) : ∃ p : PathInterval n, p.pathVertices = S := by
  classical
  have h : S.toFinset.Nonempty := by
    obtain ⟨⟨x, hx⟩⟩ := hS.nonempty
    exact ⟨x, by simpa using hx⟩
  let a := S.toFinset.min' h
  let b := S.toFinset.max' h
  have ha : a ∈ S.toFinset := S.toFinset.min'_mem h
  have hb : b ∈ S.toFinset := S.toFinset.max'_mem h
  refine ⟨⟨(a, b), S.toFinset.min'_le _ hb⟩, ?_⟩
  ext x
  constructor
  · exact fun hx => convex_of_connected hS
      (by simpa using ha) (by simpa using hb) hx.1 hx.2
  · intro hx
    have hx' : x ∈ S.toFinset := by simpa using hx
    exact ⟨S.toFinset.min'_le x hx', S.toFinset.le_max' x hx'⟩

end Intervals
section Supports

private def sumSet {A B : Type} (S : Set A) (T : Set B) : Set (A ⊕ B) :=
  fun x => x.elim (· ∈ S) (· ∈ T)

@[simp] private theorem left_sumSet {A B : Type} (S : Set A) (T : Set B) :
    leftSet (sumSet S T) = S := rfl

@[simp] private theorem right_sumSet {A B : Type} (S : Set A) (T : Set B) :
    rightSet (sumSet S T) = T := rfl

@[simp] private theorem sumSet_nonempty {A B : Type} (S : Set A) (T : Set B) :
    (sumSet S T).Nonempty ↔ S.Nonempty ∨ T.Nonempty := by
  constructor
  · rintro ⟨x | x, hx⟩
    · exact .inl ⟨x, hx⟩
    · exact .inr ⟨x, hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨.inl x, hx⟩
    · exact ⟨.inr x, hx⟩

private theorem card_sumSet {A B : Type} [Finite A] [Finite B] (S : Set A) (T : Set B) :
    Nat.card (sumSet S T) = Nat.card S + Nat.card T := by
  exact (Nat.card_congr (Equiv.subtypeSum (p := (· ∈ sumSet S T)))).trans Nat.card_sum

private theorem induced_preconnected_empty {V : Type} (G : SimpleGraph V) :
    (G.induce (∅ : Set V)).Preconnected := fun x => x.property.elim

private theorem induced_connected_nonempty {V : Type} {G : SimpleGraph V} {S : Set V}
    (h : (G.induce S).Connected) : S.Nonempty := Set.nonempty_coe_sort.mp h.nonempty

theorem induced_connected_of_preconnected {V : Type} {G : SimpleGraph V} {S : Set V}
    (h : (G.induce S).Preconnected) (hne : S.Nonempty) : (G.induce S).Connected :=
  @SimpleGraph.Connected.mk _ _ h (Set.nonempty_coe_sort.mpr hne)

private theorem joinAt_connected_sumSet {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    (a : A) (b : B) (S : Set A) (T : Set B) :
    ((joinAt G H a b).induce (sumSet S T)).Connected ↔
      ((G.induce S).Connected ∧ T = ∅) ∨
      (S = ∅ ∧ (H.induce T).Connected) ∨
      ((G.induce S).Connected ∧ (H.induce T).Connected ∧ a ∈ S ∧ b ∈ T) := by
  rw [joinAt_induce_connected, sumSet_nonempty, left_sumSet, right_sumSet]
  constructor
  · rintro ⟨hn, hl, hr, hc⟩
    by_cases hs : S.Nonempty
    · have hcs := induced_connected_of_preconnected hl hs
      by_cases ht : T.Nonempty
      · exact .inr (.inr ⟨hcs, induced_connected_of_preconnected hr ht, hc hs ht⟩)
      · exact .inl ⟨hcs, Set.not_nonempty_iff_eq_empty.mp ht⟩
    · exact .inr (.inl ⟨Set.not_nonempty_iff_eq_empty.mp hs,
        induced_connected_of_preconnected hr (hn.resolve_left hs)⟩)
  · rintro (⟨hS, rfl⟩ | ⟨rfl, hT⟩ | ⟨hS, hT, ha, hb⟩)
    · exact ⟨.inl (induced_connected_nonempty hS), hS.preconnected,
        induced_preconnected_empty _, fun _ ht => (Set.not_nonempty_empty ht).elim⟩
    · exact ⟨.inr (induced_connected_nonempty hT), induced_preconnected_empty _, hT.preconnected,
        fun hs => (Set.not_nonempty_empty hs).elim⟩
    · exact ⟨.inl (induced_connected_nonempty hS), hS.preconnected, hT.preconnected,
        fun _ _ => ⟨ha, hb⟩⟩

abbrev PathPrefix (S : Set (Fin 5000)) (mark : Fin 5000) :=
  {l : Fin 501 // 0 < l.val → mark ∈ S}

private def prefixVertices (l : Fin 501) : Set (Fin 500) := {x | x.val < l.val}

private theorem prefix_card (l : Fin 501) : Nat.card (prefixVertices l) = l.val := by
  classical
  have h : (prefixVertices l).toFinset = Finset.univ.filter (fun x => x.val < l.val) := by
    ext x
    rw [Set.mem_toFinset, Finset.mem_filter]
    simp [prefixVertices]
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card, h, Fin.card_filter_val_lt,
    min_eq_right (by have := l.isLt; omega)]

private theorem prefix_empty : prefixVertices 0 = ∅ := by
  ext x; simp [prefixVertices]

private theorem prefix_connected {l : Fin 501} (hl : 0 < l.val) :
    ((pathGraph 500).induce (prefixVertices l)).Connected := by
  let b : Fin 500 := ⟨l.val - 1, by have := l.isLt; omega⟩
  have h : prefixVertices l = Set.Icc 0 b := by
    ext x
    change x.val < l.val ↔ 0 ≤ x.val ∧ x.val ≤ l.val - 1
    omega
  rw [h]
  exact interval_connected 0 b (Fin.zero_le _)

private theorem exists_prefix {S : Set (Fin 500)}
    (hS : ((pathGraph 500).induce S).Connected) (h0 : 0 ∈ S) :
    ∃ l : Fin 501, 0 < l.val ∧ prefixVertices l = S := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, h⟩ := PathInterval.exists_vertices S hS
  change Set.Icc a b = S at h
  have ha := (h.symm ▸ h0 : (0 : Fin 500) ∈ Set.Icc a b).1
  have hea : a = 0 := le_antisymm ha (Fin.zero_le _)
  subst a
  refine ⟨⟨b.val + 1, by have := b.isLt; omega⟩, by simp, ?_⟩
  rw [← h]
  ext x
  change x.val < b.val + 1 ↔ 0 ≤ x.val ∧ x.val ≤ b.val
  omega

abbrev TriangleExtension (S : Set (Fin 5000)) :=
  {t : Finset (Fin 3) // t.Nonempty → (500 : Fin 5000) ∈ S ∧ (0 : Fin 3) ∈ t}

/-- The four ways a connected support can meet the blocks of the witness graph. -/
inductive Configuration
  | onCore (c : CycleInterval 4997) (p : PathPrefix c.cycleVertices 0)
      (q : PathPrefix c.cycleVertices 1000) (t : TriangleExtension c.cycleVertices)
  | firstOnly (p : PathInterval 500)
  | secondOnly (p : PathInterval 500)
  | triangleOnly (t : {t : Finset (Fin 3) // t.Nonempty})

private def pack (C : Set (Fin 5000)) (P Q : Set (Fin 500)) (T : Set (Fin 3)) : Set Vertex :=
  sumSet (sumSet (sumSet C P) Q) T

abbrev coreSet (S : Set Vertex) : Set (Fin 5000) := core ⁻¹' S
private abbrev firstSet (S : Set Vertex) : Set (Fin 500) := firstPath ⁻¹' S
private abbrev secondSet (S : Set Vertex) : Set (Fin 500) := secondPath ⁻¹' S
abbrev triangleSet (S : Set Vertex) : Set (Fin 3) := triangle ⁻¹' S

private theorem pack_restrictions (S : Set Vertex) :
    pack (coreSet S) (firstSet S) (secondSet S) (triangleSet S) = S := by
  ext (((x | x) | x) | x) <;> rfl

private theorem pack_inj {C C' : Set (Fin 5000)} {P P' Q Q' : Set (Fin 500)} {T T' : Set (Fin 3)}
    (h : pack C P Q T = pack C' P' Q' T') : C = C' ∧ P = P' ∧ Q = Q' ∧ T = T' :=
  ⟨congrArg coreSet h, congrArg firstSet h, congrArg secondSet h, congrArg triangleSet h⟩

/-- Decode the interval and attachment choices as actual vertices of the host graph. -/
def Configuration.vertices : Configuration → Set Vertex
  | .onCore c p q t => pack c.cycleVertices (prefixVertices p.val) (prefixVertices q.val) t.val
  | .firstOnly p => pack ∅ p.pathVertices ∅ ∅
  | .secondOnly p => pack ∅ ∅ p.pathVertices ∅
  | .triangleOnly t => pack ∅ ∅ ∅ t.val

/-- The order from the interval lengths and triangle multiplicities. -/
def Configuration.vertexOrder : Configuration → ℕ
  | .onCore c p q t => c.cycleOrder + p.val.val + q.val.val + t.val.card
  | .firstOnly p => p.order
  | .secondOnly p => p.order
  | .triangleOnly t => t.val.card

private theorem pack_connected {C : Set (Fin 5000)} {P Q : Set (Fin 500)}
    {T : Set (Fin 3)} :
    (G500.induce (pack C P Q T)).Connected ↔
      (((cycleGraph 5000).induce C).Connected ∧
        (P = ∅ ∨ (((pathGraph 500).induce P).Connected ∧ 0 ∈ C ∧ 0 ∈ P)) ∧
        (Q = ∅ ∨ (((pathGraph 500).induce Q).Connected ∧ 1000 ∈ C ∧ 0 ∈ Q)) ∧
        (T = ∅ ∨ (((cycleGraph 3).induce T).Connected ∧ 500 ∈ C ∧ 0 ∈ T))) ∨
      (C = ∅ ∧ P = ∅ ∧ Q = ∅ ∧ ((cycleGraph 3).induce T).Connected) ∨
      (C = ∅ ∧ P = ∅ ∧ ((pathGraph 500).induce Q).Connected ∧ T = ∅) ∨
      (C = ∅ ∧ ((pathGraph 500).induce P).Connected ∧ Q = ∅ ∧ T = ∅) := by
  simp only [G500, pack, joinAt_connected_sumSet]
  have j₁ : ∀ S : Set (Fin 5000), ∀ U : Set (Fin 500),
      sumSet S U = ∅ ↔ S = ∅ ∧ U = ∅ := by
    intro S U
    rw [← not_iff_not, ← Set.not_nonempty_iff_eq_empty,
      sumSet_nonempty, not_or, Set.not_nonempty_iff_eq_empty, Set.not_nonempty_iff_eq_empty]
  have j₂ : sumSet (sumSet C P) Q = ∅ ↔ C = ∅ ∧ P = ∅ ∧ Q = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty, sumSet_nonempty, not_or,
      Set.not_nonempty_iff_eq_empty, j₁, Set.not_nonempty_iff_eq_empty, and_assoc]
  simp only [j₁, j₂]
  change _ ↔ _
  have h1000 : (Sum.inl (1000 : Fin 5000) ∈ sumSet C P) ↔ (1000 : Fin 5000) ∈ C := Iff.rfl
  have h500 : (Sum.inl (Sum.inl (500 : Fin 5000)) ∈ sumSet (sumSet C P) Q) ↔
      (500 : Fin 5000) ∈ C := Iff.rfl
  rw [h1000, h500]
  have no500 : C = ∅ → (500 : Fin 5000) ∉ C := fun h => h.symm ▸ Set.notMem_empty _
  have no1000 : C = ∅ → (1000 : Fin 5000) ∉ C := fun h => h.symm ▸ Set.notMem_empty _
  constructor
  · rintro (⟨⟨⟨hc, hp⟩ | ⟨hc, hp⟩ | ⟨hc, hp, h0, hp0⟩, hq⟩ |
      ⟨⟨hc, hp⟩, hq⟩ |
      ⟨⟨hc, hp⟩ | ⟨hc, hp⟩ | ⟨hc, hp, h0, hp0⟩, hq, h1000, hq0⟩, ht⟩ |
      ⟨⟨hc, hp, hq⟩, ht⟩ |
      ⟨⟨⟨hc, hp⟩ | ⟨hc, hp⟩ | ⟨hc, hp, h0, hp0⟩, hq⟩ |
      ⟨⟨hc, hp⟩, hq⟩ |
      ⟨⟨hc, hp⟩ | ⟨hc, hp⟩ | ⟨hc, hp, h0, hp0⟩, hq, h1000, hq0⟩, ht, h500, ht0⟩)
    · exact .inl ⟨hc, .inl hp, .inl hq, .inl ht⟩
    · exact .inr (.inr (.inr ⟨hc, hp, hq, ht⟩))
    · exact .inl ⟨hc, .inr ⟨hp, h0, hp0⟩, .inl hq, .inl ht⟩
    · exact .inr (.inr (.inl ⟨hc, hp, hq, ht⟩))
    · exact .inl ⟨hc, .inl hp, .inr ⟨hq, h1000, hq0⟩, .inl ht⟩
    · exact (no1000 hc h1000).elim
    · exact .inl ⟨hc, .inr ⟨hp, h0, hp0⟩, .inr ⟨hq, h1000, hq0⟩, .inl ht⟩
    · exact .inr (.inl ⟨hc, hp, hq, ht⟩)
    · exact .inl ⟨hc, .inl hp, .inl hq, .inr ⟨ht, h500, ht0⟩⟩
    · exact (no500 hc h500).elim
    · exact .inl ⟨hc, .inr ⟨hp, h0, hp0⟩, .inl hq, .inr ⟨ht, h500, ht0⟩⟩
    · exact (no500 hc h500).elim
    · exact .inl ⟨hc, .inl hp, .inr ⟨hq, h1000, hq0⟩, .inr ⟨ht, h500, ht0⟩⟩
    · exact (no1000 hc h1000).elim
    · exact .inl ⟨hc, .inr ⟨hp, h0, hp0⟩, .inr ⟨hq, h1000, hq0⟩, .inr ⟨ht, h500, ht0⟩⟩
  · rintro (⟨hc, hp, hq, ht⟩ | ⟨hc, hp, hq, ht⟩ | ⟨hc, hp, hq, ht⟩ | ⟨hc, hp, hq, ht⟩)
    · rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases ht with ht | ht
      · exact .inl ⟨.inl ⟨.inl ⟨hc, hp⟩, hq⟩, ht⟩
      · exact .inr (.inr ⟨.inl ⟨.inl ⟨hc, hp⟩, hq⟩, ht⟩)
      · exact .inl ⟨.inr (.inr ⟨.inl ⟨hc, hp⟩, hq⟩), ht⟩
      · exact .inr (.inr ⟨.inr (.inr ⟨.inl ⟨hc, hp⟩, hq⟩), ht⟩)
      · exact .inl ⟨.inl ⟨.inr (.inr ⟨hc, hp⟩), hq⟩, ht⟩
      · exact .inr (.inr ⟨.inl ⟨.inr (.inr ⟨hc, hp⟩), hq⟩, ht⟩)
      · exact .inl ⟨.inr (.inr ⟨.inr (.inr ⟨hc, hp⟩), hq⟩), ht⟩
      · exact .inr (.inr ⟨.inr (.inr ⟨.inr (.inr ⟨hc, hp⟩), hq⟩), ht⟩)
    · exact .inr (.inl ⟨⟨hc, hp, hq⟩, ht⟩)
    · exact .inl ⟨.inr (.inl ⟨⟨hc, hp⟩, hq⟩), ht⟩
    · exact .inl ⟨.inl ⟨.inr (.inl ⟨hc, hp⟩), hq⟩, ht⟩

private theorem triangle_connected (T : Finset (Fin 3)) (h : T.Nonempty) :
    ((cycleGraph 3).induce (T : Set (Fin 3))).Connected := by
  apply induced_connected_of_preconnected _ (by simpa using h)
  have ht : (cycleGraph 3).induce (T : Set (Fin 3)) = ⊤ := by
    rw [cycleGraph_three_eq_top]
    ext x y
    exact not_congr Subtype.ext_iff.symm
  rw [ht]
  exact preconnected_top

theorem Configuration.supportConnected (c : Configuration) : (G500.induce c.vertices).Connected := by
  cases c with
  | onCore c p q t =>
    apply pack_connected.mpr
    refine .inl ⟨c.connected, ?_, ?_, ?_⟩
    · by_cases hp : p.val.val = 0
      · exact .inl ((Fin.ext hp : p.val = 0) ▸ prefix_empty)
      · exact .inr ⟨prefix_connected (Nat.pos_of_ne_zero hp),
          p.property (Nat.pos_of_ne_zero hp), Nat.pos_of_ne_zero hp⟩
    · by_cases hq : q.val.val = 0
      · exact .inl ((Fin.ext hq : q.val = 0) ▸ prefix_empty)
      · exact .inr ⟨prefix_connected (Nat.pos_of_ne_zero hq),
          q.property (Nat.pos_of_ne_zero hq), Nat.pos_of_ne_zero hq⟩
    · by_cases ht : t.val.Nonempty
      · exact .inr ⟨triangle_connected _ ht, (t.property ht).1, (t.property ht).2⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
        exact .inl Finset.coe_empty
  | firstOnly p => exact pack_connected.mpr (.inr (.inr (.inr ⟨rfl, p.connected, rfl, rfl⟩)))
  | secondOnly p => exact pack_connected.mpr (.inr (.inr (.inl ⟨rfl, rfl, p.connected, rfl⟩)))
  | triangleOnly t =>
    exact pack_connected.mpr (.inr (.inl ⟨rfl, rfl, rfl, triangle_connected _ t.property⟩))

private theorem Configuration.exists_vertices (S : Set Vertex) (h : (G500.induce S).Connected) :
    ∃ c : Configuration, c.vertices = S := by
  classical
  generalize hC : coreSet S = C
  generalize hP : firstSet S = P
  generalize hQ : secondSet S = Q
  generalize hT : triangleSet S = T
  have hs : pack C P Q T = S := by
    rw [← hC, ← hP, ← hQ, ← hT, pack_restrictions]
  rw [← hs] at h
  rcases pack_connected.mp h with ⟨hC, hP, hQ, hT⟩ | ⟨rfl, rfl, rfl, hT⟩ |
    ⟨rfl, rfl, hQ, rfl⟩ | ⟨rfl, hP, rfl, rfl⟩
  · obtain ⟨c, rfl⟩ := CycleInterval.exists_vertices C hC
    have getPrefix (U : Set (Fin 500)) (m : Fin 5000)
        (hU : U = ∅ ∨ (((pathGraph 500).induce U).Connected ∧ m ∈ c.cycleVertices ∧ 0 ∈ U)) :
        ∃ p : PathPrefix c.cycleVertices m, prefixVertices p.val = U := by
      rcases hU with rfl | ⟨hconn, hm, h0⟩
      · exact ⟨⟨0, fun h => (Nat.lt_irrefl 0 h).elim⟩, prefix_empty⟩
      · obtain ⟨l, _, hl⟩ := exists_prefix hconn h0
        exact ⟨⟨l, fun _ => hm⟩, hl⟩
    obtain ⟨p, hp⟩ := getPrefix P 0 hP
    obtain ⟨q, hq⟩ := getPrefix Q 1000 hQ
    have root : T.toFinset.Nonempty → 500 ∈ c.cycleVertices ∧ 0 ∈ T.toFinset := by
      intro hne
      rcases hT with rfl | ⟨_, hm, h0⟩
      · simp at hne
      · exact ⟨hm, by simpa using h0⟩
    exact ⟨.onCore c p q ⟨T.toFinset, root⟩, by
      simpa [Configuration.vertices, hp, hq] using hs⟩
  · have ht : T.toFinset.Nonempty := by
      simpa using induced_connected_nonempty hT
    exact ⟨.triangleOnly ⟨T.toFinset, ht⟩, by simpa [Configuration.vertices] using hs⟩
  · obtain ⟨q, hq⟩ := PathInterval.exists_vertices Q hQ
    exact ⟨.secondOnly q, by simpa [Configuration.vertices, hq] using hs⟩
  · obtain ⟨p, hp⟩ := PathInterval.exists_vertices P hP
    exact ⟨.firstOnly p, by simpa [Configuration.vertices, hp] using hs⟩

private theorem Configuration.injective_vertices : Function.Injective Configuration.vertices := by
  intro a b h
  have pc {n} (p : PathInterval n) : p.pathVertices ≠ ∅ :=
    (induced_connected_nonempty p.connected).ne_empty
  have cc {m} (c : CycleInterval m) : c.cycleVertices ≠ ∅ :=
    (induced_connected_nonempty c.connected).ne_empty
  cases a <;> cases b <;> obtain ⟨hC, hP, hQ, hT⟩ := pack_inj h
  all_goals try first
    | exact (cc _ hC).elim | exact (cc _ hC.symm).elim
    | exact (pc _ hP).elim | exact (pc _ hP.symm).elim
    | exact (pc _ hQ).elim | exact (pc _ hQ.symm).elim
  · cases CycleInterval.injective_vertices hC
    have hp := congrArg (fun s : Set (Fin 500) => Nat.card s) hP
    have hq := congrArg (fun s : Set (Fin 500) => Nat.card s) hQ
    rw [prefix_card, prefix_card] at hp hq
    cases Subtype.ext (Fin.ext hp)
    cases Subtype.ext (Fin.ext hq)
    cases Subtype.ext (Finset.coe_injective hT)
    rfl
  · cases PathInterval.injective_vertices hP; rfl
  · cases PathInterval.injective_vertices hQ; rfl
  · cases Subtype.ext (Finset.coe_injective hT); rfl

/-- Actual connected induced supports are equivalent to interval-and-attachment configurations. -/
noncomputable def supportEquiv : ConnectedSets G500 ≃ Configuration :=
  (Equiv.ofBijective (fun (c : Configuration) => (⟨c.vertices, c.supportConnected⟩ : ConnectedSets G500))
    ⟨fun a b h => Configuration.injective_vertices (congrArg Subtype.val h), fun ⟨s, hs⟩ => by
      obtain ⟨c, hc⟩ := Configuration.exists_vertices s hs
      exact ⟨c, Subtype.ext hc⟩⟩).symm

@[simp] theorem supportEquiv_symm_verts (c : Configuration) :
    (supportEquiv.symm c).val = c.vertices := rfl

/-- The support equivalence preserves vertex order pointwise. -/
theorem supportEquiv_order (c : Configuration) :
    Nat.card (supportEquiv.symm c).val = c.vertexOrder := by
  rw [supportEquiv_symm_verts]
  have h (t : Finset (Fin 3)) : Nat.card (t : Set (Fin 3)) = t.card := by
    exact (Nat.card_eq_fintype_card (α := ↥t)).trans (Fintype.card_coe t)
  have he {n : ℕ} : Nat.card (∅ : Set (Fin n)) = 0 := by simp
  cases c <;> simp only [Configuration.vertices, Configuration.vertexOrder, pack, card_sumSet,
    CycleInterval.card_vertices, PathInterval.card_vertices, prefix_card, h, he,
    Nat.zero_add, Nat.add_zero]

#print axioms supportEquiv
#print axioms supportEquiv_order

end Supports

end D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
