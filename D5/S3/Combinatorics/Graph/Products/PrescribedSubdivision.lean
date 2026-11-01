/- GID: D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/PrescribedSubdivision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: none
   digest: Fresh indexed subdivision paths have an exact edge inventory and finite cardinalities. -/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.Products.PrescribedSubdivision

universe u v

/-- Positive subdivision multiplicities suffice for the consumed routing data.
`k e` triple subdivisions give `3*k e` fresh vertices and `3*k e+1` edges.
Original vertex labels are arbitrary: they are not silently replaced by `Fin (card V)`.
The actual data have `k e ≥ 5`. Parallel endpoint pairs are not required here;
the concrete module separately identifies its simple base graph exactly. -/
structure Data (V : Type u) (E : Type v) where
  left : E → V
  right : E → V
  k : E → ℕ
  positive : ∀ e, 0 < k e
  different : ∀ e, left e ≠ right e

variable {V : Type u} {E : Type v} (D : Data V E)

namespace Data

abbrev Vertex := V ⊕ (Σ e : E, Fin (3 * D.k e))
abbrev Slot := Σ e : E, Fin (3 * D.k e + 1)

@[simp] theorem inner_eq_iff (e f : E) (i : Fin (3 * D.k e)) (j : Fin (3 * D.k f)) :
    (Sum.inr ⟨e, i⟩ : D.Vertex) = Sum.inr ⟨f, j⟩ ↔ e = f ∧ i.val = j.val := by
  constructor
  · intro h
    have hs := Sum.inr.inj h
    exact ⟨congrArg Sigma.fst hs, congrArg (fun x : Σ e : E, Fin (3 * D.k e) => x.2.val) hs⟩
  · rintro ⟨rfl, h⟩
    have hij : i = j := Fin.ext h
    subst j
    rfl

/-- The interior index `i` denotes path position `i+1`. -/
def Arc : D.Vertex → D.Vertex → Prop
  | .inl a, .inr ⟨e, i⟩ => a = D.left e ∧ i.val = 0
  | .inr ⟨e, i⟩, .inl a => a = D.right e ∧ i.val + 1 = 3 * D.k e
  | .inr ⟨e, i⟩, .inr ⟨f, j⟩ => e = f ∧ i.val + 1 = j.val
  | .inl _, .inl _ => False

theorem arc_asymmetric (a b : D.Vertex) : D.Arc a b → ¬ D.Arc b a := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [Arc]
    | inr b =>
      rcases b with ⟨e, i⟩
      have hp := D.positive e
      simp only [Arc]
      omega
  | inr a =>
    rcases a with ⟨e, i⟩
    cases b with
    | inl b =>
      have hp := D.positive e
      simp only [Arc]
      omega
    | inr b =>
      rcases b with ⟨f, j⟩
      simp only [Arc]
      omega

def graph : SimpleGraph D.Vertex where
  Adj a b := D.Arc a b ∨ D.Arc b a
  symm.symm _ _ h := h.symm
  loopless.irrefl a h := by
    have h' : D.Arc a a := h.elim id id
    exact D.arc_asymmetric a a h' h'

instance [DecidableEq V] [DecidableEq E] : DecidableRel D.Arc := by
  intro a b
  cases a <;> cases b <;> simp only [Arc] <;> infer_instance

instance [DecidableEq V] [DecidableEq E] : DecidableRel D.graph.Adj :=
  fun a b => inferInstanceAs (Decidable (D.Arc a b ∨ D.Arc b a))

/-- Path positions include both old endpoints, numbered `0,...,3*k e+1`. -/
def pathVertex (e : E) (i : Fin (3 * D.k e + 2)) : D.Vertex :=
  if h0 : i.val = 0 then .inl (D.left e)
  else if hL : i.val = 3 * D.k e + 1 then .inl (D.right e)
  else .inr ⟨e, ⟨i.val - 1, by omega⟩⟩

@[simp] theorem pathVertex_zero (e : E) :
    D.pathVertex e ⟨0, by omega⟩ = .inl (D.left e) := by simp [pathVertex]

@[simp] theorem pathVertex_last (e : E) :
    D.pathVertex e ⟨3 * D.k e + 1, by omega⟩ = .inl (D.right e) := by
  simp [pathVertex]

@[simp] theorem pathVertex_inner (e : E) (i : Fin (3 * D.k e)) :
    D.pathVertex e ⟨i.val + 1, by omega⟩ = .inr ⟨e, i⟩ := by
  have hi := i.isLt
  simp [pathVertex, show i.val ≠ 3 * D.k e by omega]

/-- All path vertices are distinct, including the old endpoints. -/
theorem pathVertex_injective (e : E) : Function.Injective (D.pathVertex e) := by
  intro i j h
  have hd := D.different e
  have hi := i.isLt
  have hj := j.isLt
  unfold pathVertex at h
  split_ifs at h <;> simp_all [inner_eq_iff] <;> apply Fin.ext <;> omega

/-- An oriented successor edge, with no quotient or implicit fresh-vertex identification. -/
def edgePair (s : D.Slot) : D.Vertex × D.Vertex :=
  match s with
  | ⟨e, i⟩ =>
    ((if h0 : i.val = 0 then .inl (D.left e)
      else .inr ⟨e, ⟨i.val - 1, by have := i.isLt; omega⟩⟩),
     (if hL : i.val = 3 * D.k e then .inl (D.right e)
      else .inr ⟨e, ⟨i.val, by have := i.isLt; omega⟩⟩))

theorem edgePair_path (s : D.Slot) :
    D.edgePair s =
      (D.pathVertex s.1 ⟨s.2.val, by have := s.2.isLt; omega⟩,
       D.pathVertex s.1 ⟨s.2.val + 1, by have := s.2.isLt; omega⟩) := by
  rcases s with ⟨e, i⟩
  have hi := i.isLt
  have hp := D.positive e
  unfold edgePair pathVertex
  dsimp
  split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq,
    inner_eq_iff, Sum.inl_ne_inr, Sum.inr_ne_inl] <;> omega

theorem arc_edgePair (s : D.Slot) : D.Arc (D.edgePair s).1 (D.edgePair s).2 := by
  simp only [D.edgePair_path]
  rcases s with ⟨e, i⟩
  have hi := i.isLt
  have hp := D.positive e
  unfold pathVertex
  dsimp
  split_ifs <;> simp_all [Arc] <;> omega

theorem arc_iff_slot (a b : D.Vertex) :
    D.Arc a b ↔ ∃ s : D.Slot, D.edgePair s = (a, b) := by
  constructor
  · intro h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact False.elim h
      | inr b =>
        rcases b with ⟨e, i⟩
        have hib := i.isLt
        rcases h with ⟨ha, hi⟩
        refine ⟨⟨e, ⟨0, by omega⟩⟩, ?_⟩
        have hp := D.positive e
        simp only [edgePair, ha]
        dsimp
        split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    | inr a =>
      rcases a with ⟨e, i⟩
      have hib := i.isLt
      cases b with
      | inl b =>
        rcases h with ⟨hb, hi⟩
        have hp := D.positive e
        refine ⟨⟨e, ⟨3 * D.k e, by omega⟩⟩, ?_⟩
        simp only [edgePair, hb]
        dsimp
        split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      | inr b =>
        rcases b with ⟨f, j⟩
        rcases h with ⟨hef, hij⟩
        subst f
        have hi := i.isLt
        have hj := j.isLt
        refine ⟨⟨e, ⟨i.val + 1, by omega⟩⟩, ?_⟩
        unfold edgePair
        dsimp
        split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq,
          inner_eq_iff, Sum.inl_ne_inr, Sum.inr_ne_inl] <;> omega
  · rintro ⟨s, hs⟩
    have h := D.arc_edgePair s
    rw [hs] at h
    exact h

theorem edgePair_injective : Function.Injective D.edgePair := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  have hp := D.positive e
  have hq := D.positive f
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · have hef : e = f := by
        have he0 : (0 : ℕ) ≠ 3 * D.k e := by omega
        have hf0 : (0 : ℕ) ≠ 3 * D.k f := by omega
        have hh : e = f ∧ (0 : ℕ) = 0 := by
          simpa only [edgePair, hi0, hj0, he0, hf0, ↓reduceDIte, inner_eq_iff] using hs
        exact hh.1
      subst f
      congr 1
      exact Fin.ext (by omega)
    · simp only [edgePair, hi0, hj0, ↓reduceDIte] at hf
      cases hf
  · by_cases hj0 : j.val = 0
    · simp only [edgePair, hi0, hj0, ↓reduceDIte] at hf
      cases hf
    · have hef : e = f := by
        have hh : e = f ∧ i.val - 1 = j.val - 1 := by
          simpa only [edgePair, hi0, hj0, ↓reduceDIte, inner_eq_iff] using hf
        exact hh.1
      subst f
      have hpath :
          D.pathVertex e ⟨i.val, by omega⟩ =
            D.pathVertex e ⟨j.val, by omega⟩ := by
        simpa only [D.edgePair_path] using hf
      have hpos := D.pathVertex_injective e hpath
      congr 1
      exact Fin.ext (congrArg (fun p : Fin (3 * D.k e + 2) => p.val) hpos)

def edge (s : D.Slot) : Sym2 D.Vertex := s((D.edgePair s).1, (D.edgePair s).2)

theorem edge_injective : Function.Injective D.edge := by
  intro s t h
  have hs := D.arc_edgePair s
  have ht := D.arc_edgePair t
  rcases Sym2.eq_iff.mp h with h | h
  · apply D.edgePair_injective
    exact Prod.ext h.1 h.2
  · exfalso
    have hts : D.Arc (D.edgePair s).2 (D.edgePair s).1 := by
      simpa only [h.1, h.2] using ht
    exact D.arc_asymmetric _ _ hs hts

section Enumeration
variable (vs : List V) (es : List E)

def vertices : List D.Vertex :=
  vs.map Sum.inl ++
    (es.flatMap fun e =>
      (List.finRange (3 * D.k e)).map fun i => Sum.inr ⟨e, i⟩)

theorem mem_vertices (hvs : ∀ a, a ∈ vs) (hes : ∀ e, e ∈ es)
    (a : D.Vertex) : a ∈ D.vertices vs es := by
  cases a with
  | inl a => simp [vertices, hvs a]
  | inr a =>
    rcases a with ⟨e, i⟩
    simp only [vertices, List.mem_append, List.mem_map, List.mem_flatMap]
    exact Or.inr ⟨e, hes e, i, by simp, rfl⟩

def slots : List D.Slot :=
  es.flatMap fun e =>
    (List.finRange (3 * D.k e + 1)).map fun i => ⟨e, i⟩

theorem mem_slots (hes : ∀ e, e ∈ es) (s : D.Slot) : s ∈ D.slots es := by
  rcases s with ⟨e, i⟩
  simp only [slots, List.mem_flatMap, List.mem_map]
  exact ⟨e, hes e, i, by simp, rfl⟩

def edgePairs : List (D.Vertex × D.Vertex) := (D.slots es).map D.edgePair

theorem adj_iff_edgePairs (hes : ∀ e, e ∈ es) (a b : D.Vertex) :
    D.graph.Adj a b ↔ (a, b) ∈ D.edgePairs es ∨ (b, a) ∈ D.edgePairs es := by
  simp only [graph, edgePairs, List.mem_map]
  constructor
  · rintro (h | h)
    · obtain ⟨s, hs⟩ := (D.arc_iff_slot a b).mp h
      exact Or.inl ⟨s, D.mem_slots es hes s, hs⟩
    · obtain ⟨s, hs⟩ := (D.arc_iff_slot b a).mp h
      exact Or.inr ⟨s, D.mem_slots es hes s, hs⟩
  · rintro (⟨s, _, hs⟩ | ⟨s, _, hs⟩)
    · exact Or.inl ((D.arc_iff_slot a b).mpr ⟨s, hs⟩)
    · exact Or.inr ((D.arc_iff_slot b a).mpr ⟨s, hs⟩)

end Enumeration

/-- A proof-free computational tag for an actual indexed vertex. -/
abbrev RawVertex := V ⊕ (E × ℕ)

def code : D.Vertex → RawVertex (V := V) (E := E)
  | .inl a => .inl a
  | .inr ⟨e, i⟩ => .inr (e, i.val)

theorem code_injective : Function.Injective D.code := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a =>
    rcases a with ⟨e, i⟩
    cases b with
    | inl b => cases h
    | inr b =>
      rcases b with ⟨f, j⟩
      apply (D.inner_eq_iff e f i j).mpr
      exact ⟨congrArg Prod.fst (Sum.inr.inj h), congrArg Prod.snd (Sum.inr.inj h)⟩

def RawArc : RawVertex (V := V) (E := E) → RawVertex (V := V) (E := E) → Prop
  | .inl a, .inr (e, i) => a = D.left e ∧ i = 0
  | .inr (e, i), .inl a => a = D.right e ∧ i + 1 = 3 * D.k e
  | .inr (e, i), .inr (f, j) => e = f ∧ i + 1 = j
  | .inl _, .inl _ => False

theorem raw_arc_asymmetric (a b : RawVertex (V := V) (E := E)) :
    D.RawArc a b → ¬ D.RawArc b a := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [RawArc]
    | inr b =>
      rcases b with ⟨e, i⟩
      have hp := D.positive e
      simp only [RawArc]
      omega
  | inr a =>
    rcases a with ⟨e, i⟩
    cases b with
    | inl b =>
      have hp := D.positive e
      simp only [RawArc]
      omega
    | inr b =>
      rcases b with ⟨f, j⟩
      simp only [RawArc]
      omega

def rawGraph : SimpleGraph (RawVertex (V := V) (E := E)) where
  Adj a b := D.RawArc a b ∨ D.RawArc b a
  symm.symm _ _ h := h.symm
  loopless.irrefl a h := by
    have h' : D.RawArc a a := h.elim id id
    exact D.raw_arc_asymmetric a a h' h'

instance [DecidableEq V] [DecidableEq E] : DecidableRel D.RawArc :=
  fun a b => match a, b with
  | .inl _, .inl _ => inferInstanceAs (Decidable False)
  | .inl a, .inr (e, i) => inferInstanceAs (Decidable (a = D.left e ∧ i = 0))
  | .inr (e, i), .inl a => inferInstanceAs (Decidable (a = D.right e ∧ i + 1 = 3 * D.k e))
  | .inr (e, i), .inr (f, j) => inferInstanceAs (Decidable (e = f ∧ i + 1 = j))

instance [DecidableEq V] [DecidableEq E] : DecidableRel D.rawGraph.Adj :=
  fun a b => inferInstanceAs (Decidable (D.RawArc a b ∨ D.RawArc b a))

theorem raw_graph_code_iff (a b : D.Vertex) :
    D.rawGraph.Adj (D.code a) (D.code b) ↔ D.graph.Adj a b := by
  cases a with
  | inl a => cases b <;> rfl
  | inr a => rcases a with ⟨e, i⟩; cases b <;> rfl

def rawEdgePair (e : E) (i : ℕ) :
    RawVertex (V := V) (E := E) × RawVertex (V := V) (E := E) :=
  ((if i = 0 then .inl (D.left e) else .inr (e, i - 1)),
   (if i = 3 * D.k e then .inl (D.right e) else .inr (e, i)))

theorem raw_edge_pair (s : D.Slot) :
    D.rawEdgePair s.1 s.2.val = (D.code (D.edgePair s).1, D.code (D.edgePair s).2) := by
  rcases s with ⟨e, i⟩
  unfold rawEdgePair edgePair
  dsimp
  split_ifs <;> rfl

section RawEnumeration
variable (vs : List V) (es : List E)

def rawVertices : List (RawVertex (V := V) (E := E)) :=
  vs.map Sum.inl ++ (es.flatMap fun e => (List.range (3 * D.k e)).map fun i => Sum.inr (e, i))

theorem mem_raw_vertices (hvs : ∀ a, a ∈ vs) (hes : ∀ e, e ∈ es)
    (a : D.Vertex) : D.code a ∈ D.rawVertices vs es := by
  cases a with
  | inl a => simp [rawVertices, code, hvs a]
  | inr a =>
    rcases a with ⟨e, i⟩
    simp only [rawVertices, code, List.mem_append, List.mem_map, List.mem_flatMap]
    exact Or.inr ⟨e, hes e, i.val, List.mem_range.mpr i.isLt, rfl⟩

def rawEdgePairs : List (RawVertex (V := V) (E := E) × RawVertex (V := V) (E := E)) :=
  es.flatMap fun e => (List.range (3 * D.k e + 1)).map (D.rawEdgePair e)

theorem mem_raw_edge_pairs_iff (a b : D.Vertex) :
    (D.code a, D.code b) ∈ D.rawEdgePairs es ↔ (a, b) ∈ D.edgePairs es := by
  constructor
  · intro h
    obtain ⟨e, he, h⟩ := List.mem_flatMap.mp h
    obtain ⟨i, hi, hp⟩ := List.mem_map.mp h
    let s : D.Slot := ⟨e, ⟨i, List.mem_range.mp hi⟩⟩
    have hs : s ∈ D.slots es :=
      List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨s.2, List.mem_finRange _, rfl⟩⟩
    apply List.mem_map.mpr
    refine ⟨s, hs, ?_⟩
    have heq : (D.code (D.edgePair s).1, D.code (D.edgePair s).2) = (D.code a, D.code b) :=
      (D.raw_edge_pair s).symm.trans hp
    exact Prod.ext (D.code_injective (congrArg Prod.fst heq))
      (D.code_injective (congrArg Prod.snd heq))
  · intro h
    obtain ⟨s, hs, hp⟩ := List.mem_map.mp h
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨i, _, hs⟩ := List.mem_map.mp hs
    subst s
    apply List.mem_flatMap.mpr
    refine ⟨e, he, List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩⟩
    exact (D.raw_edge_pair ⟨e, i⟩).trans
      (congrArg (fun p : D.Vertex × D.Vertex => (D.code p.1, D.code p.2)) hp)

theorem adj_iff_raw_edge_pairs (hes : ∀ e, e ∈ es) (a b : D.Vertex) :
    D.graph.Adj a b ↔ (D.code a, D.code b) ∈ D.rawEdgePairs es ∨
      (D.code b, D.code a) ∈ D.rawEdgePairs es := by
  rw [D.mem_raw_edge_pairs_iff es, D.mem_raw_edge_pairs_iff es]
  exact D.adj_iff_edgePairs es hes a b

end RawEnumeration

section Finite
variable [Fintype V] [Fintype E]

theorem card_vertices : Fintype.card D.Vertex = Fintype.card V + ∑ e, 3 * D.k e := by
  simp [Vertex, Fintype.card_sum, Fintype.card_sigma]

variable [DecidableEq V] [DecidableEq E]

theorem edgeFinset_eq : D.graph.edgeFinset = Finset.univ.image D.edge := by
  ext z
  induction z using Sym2.inductionOn with
  | hf a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change (D.Arc a b ∨ D.Arc b a) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, edge]
    constructor
    · rintro (h | h)
      · obtain ⟨s, hs⟩ := (D.arc_iff_slot a b).mp h
        exact ⟨s, by rw [hs]⟩
      · obtain ⟨s, hs⟩ := (D.arc_iff_slot b a).mp h
        exact ⟨s, by rw [hs]; exact Sym2.eq_swap⟩
    · rintro ⟨s, hs⟩
      rcases Sym2.eq_iff.mp hs with hs | hs
      · left
        simpa only [hs.1, hs.2] using D.arc_edgePair s
      · right
        simpa only [hs.1, hs.2] using D.arc_edgePair s

theorem card_edges : D.graph.edgeFinset.card = ∑ e, (3 * D.k e + 1) := by
  rw [D.edgeFinset_eq, Finset.card_image_of_injective _ D.edge_injective]
  simp only [Finset.card_univ, Slot, Fintype.card_sigma, Fintype.card_fin]

/-- Arithmetic count of the exact fresh vertices added by these prescribed paths. -/
theorem subdivision_count : (∑ e, 3 * D.k e) = 3 * ∑ e, D.k e := by
  rw [Finset.mul_sum]

end Finite
end Data
end D5.S3.Combinatorics.Graph.Products.PrescribedSubdivision
