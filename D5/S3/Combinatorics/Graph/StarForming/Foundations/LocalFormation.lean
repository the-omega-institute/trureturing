/- GID: D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Local star witnesses and deletion minimality for arbitrary simple graphs. -/

import D5.S3.Combinatorics.Graph.StarForming.Foundations.Invariants

/-! Local proof bodies from subquorum-colorings revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/Amplification.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.StarForming.Amplification

def TwoAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop :=
  (∃ first ∈ S, ∃ second ∈ S,
    first ≠ second ∧ G.Adj x first ∧ G.Adj x second) ∨
  (∃ center ∈ S, G.Adj x center ∧ ∃ leaf ∈ S, G.Adj center leaf)

def Forms {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x, x ∉ S → TwoAt G S x

def Minimal {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  Forms G S ∧ ∀ T : Set V, T ⊂ S → ¬ Forms G T

def LiteralAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop :=
  ∃ center first second,
    center ≠ first ∧ center ≠ second ∧ first ≠ second ∧
    center ∈ insert x S ∧ first ∈ insert x S ∧ second ∈ insert x S ∧
    G.Adj center first ∧ G.Adj center second ∧
    (x = center ∨ x = first ∨ x = second)

theorem literal_iff_local {V : Type*} (G : SimpleGraph V) (S : Set V)
    (x : V) (hx : x ∉ S) : LiteralAt G S x ↔ TwoAt G S x := by
  constructor
  · rintro ⟨center, first, second, hcf, hcs, hfs, hc, hf, hs, hadjf, hadjs, hxin⟩
    simp only [Set.mem_insert_iff] at hc hf hs
    rcases hxin with rfl | rfl | rfl
    · exact Or.inl ⟨first, hf.resolve_left (Ne.symm hcf), second,
        hs.resolve_left (Ne.symm hcs), hfs, hadjf, hadjs⟩
    · exact Or.inr ⟨center, hc.resolve_left hcf, G.adj_symm hadjf,
        second, hs.resolve_left (Ne.symm hfs), hadjs⟩
    · exact Or.inr ⟨center, hc.resolve_left hcs, G.adj_symm hadjs,
        first, hf.resolve_left hfs, hadjf⟩
  · rintro (⟨first, hf, second, hs, hfs, hadjf, hadjs⟩ |
      ⟨center, hc, hadj, leaf, hl, hleaf⟩)
    · exact ⟨x, first, second, (fun heq => hx (heq ▸ hf)),
        (fun heq => hx (heq ▸ hs)), hfs, Set.mem_insert x S,
        Set.mem_insert_of_mem x hf, Set.mem_insert_of_mem x hs,
        hadjf, hadjs, Or.inl rfl⟩
    · exact ⟨center, x, leaf, (fun heq => G.irrefl (heq ▸ G.adj_symm hadj)),
        (fun heq => G.irrefl (heq ▸ hleaf)), (fun heq => hx (heq ▸ hl)),
        Set.mem_insert_of_mem x hc, Set.mem_insert x S,
        Set.mem_insert_of_mem x hl, G.adj_symm hadj, hleaf, Or.inr (Or.inl rfl)⟩

theorem twoAt_mono {V : Type*} (G : SimpleGraph V) {S T : Set V}
    (hST : S ⊆ T) {x : V} : TwoAt G S x → TwoAt G T x := by
  rintro (⟨first, hf, second, hs, hfs, hadjf, hadjs⟩ |
    ⟨center, hc, hadj, leaf, hl, hleaf⟩)
  · exact Or.inl ⟨first, hST hf, second, hST hs, hfs, hadjf, hadjs⟩
  · exact Or.inr ⟨center, hST hc, hadj, leaf, hST hl, hleaf⟩

theorem minimal_of_deletion_failures {V : Type*} (G : SimpleGraph V)
    (S : Set V) (hforms : Forms G S)
    (hfail : ∀ selected ∈ S, ∃ x, x ∉ S \ {selected} ∧
      ¬ TwoAt G (S \ {selected}) x) : Minimal G S := by
  refine ⟨hforms, ?_⟩
  intro T hT hformsT
  obtain ⟨selected, hs, hnot⟩ := Set.exists_of_ssubset hT
  obtain ⟨x, hx, hfailx⟩ := hfail selected hs
  have hsub : T ⊆ S \ {selected} := by
    intro vertex hv
    refine ⟨hT.subset hv, ?_⟩
    intro heq
    have heq' : vertex = selected := Set.mem_singleton_iff.mp heq
    exact hnot (heq' ▸ hv)
  exact hfailx (twoAt_mono G hsub (hformsT x (fun hxt => hx (hsub hxt))))

end D5.S3.Combinatorics.Graph.StarForming.Amplification
