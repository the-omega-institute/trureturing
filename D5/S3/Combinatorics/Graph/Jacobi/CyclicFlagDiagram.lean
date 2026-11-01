/- GID: D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram
   mirror-E: none(waiver:consumed-graph-carrier)
   anchors: []
   utility: none
   digest: Finite cyclic flags and geometric AS, IHX, and ordinary CL relations. -/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-! Finite cyclic-flag diagrams with ordinary leaves, numbered anchors, and geometric relations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi


inductive Color
  | red | blue
  deriving DecidableEq

/-- Ordinary colored leaves are distinguished from true numbered anchors. -/
inductive LeafLabel
  | ordinary : Color → LeafLabel
  | anchor : ℕ → LeafLabel
  deriving DecidableEq

/-- Pairing and actual cyclic vertex permutation on finite flags. Fixed cyclic
flags, and only those flags, are labeled univalent vertices. -/
structure FlagGraph (F : Type) where
  edge : F → F
  edge_involutive : Function.Involutive edge
  edge_ne : ∀ f, edge f ≠ f
  next : F → F
  next_cube : ∀ f, next (next (next f)) = f
  color : F → Option LeafLabel
  color_none_iff : ∀ f, color f = none ↔ next f ≠ f

/-- Finite actual graph carrier. No simplicity, genus or connectivity restriction
is needed for the local graph relations. -/
structure Diagram where
  Flag : Type
  finiteFlag : Finite Flag
  graph : FlagGraph Flag

attribute [instance] Diagram.finiteFlag

abbrev pack {F : Type} [Finite F] (G : FlagGraph F) : Diagram := ⟨F, inferInstance, G⟩

structure FlagIso {F K : Type} (G : FlagGraph F) (H : FlagGraph K) where
  flagEquiv : F ≃ K
  edge_eq : ∀ f, H.edge (flagEquiv f) = flagEquiv (G.edge f)
  next_eq : ∀ f, H.next (flagEquiv f) = flagEquiv (G.next f)
  color_eq : ∀ f, H.color (flagEquiv f) = G.color f

namespace FlagGraph

theorem next_injective {F : Type} (G : FlagGraph F) : Function.Injective G.next := by
  intro a b h
  have := congrArg (fun f => G.next (G.next f)) h
  simpa only [G.next_cube] using this

/-- An injectively selected union of cyclic vertices, with its exact local table. -/
structure Patch {F : Type} (G : FlagGraph F) (n : ℕ) where
  flag : Fin n ↪ F
  rotor : Fin n → Fin n
  rotor_cube : ∀ i, rotor (rotor (rotor i)) = i
  rotor_ne : ∀ i, rotor i ≠ i
  next_flag : ∀ i, G.next (flag i) = flag (rotor i)

noncomputable def patchNext {F : Type} {G : FlagGraph F} {n : ℕ}
    (P : Patch G n) (r : Fin n → Fin n) (f : F) : F := by
  classical
  exact if h : ∃ i, P.flag i = f then P.flag (r h.choose) else G.next f

theorem patchNext_flag {F : Type} {G : FlagGraph F} {n : ℕ}
    (P : Patch G n) (r : Fin n → Fin n) (i : Fin n) :
    patchNext P r (P.flag i) = P.flag (r i) := by
  classical
  unfold patchNext
  split
  · rename_i h
    have : h.choose = i := P.flag.injective h.choose_spec
    rw [this]
  · rename_i h
    exact False.elim (h ⟨i, rfl⟩)

theorem next_outside {F : Type} {G : FlagGraph F} {n : ℕ}
    (P : Patch G n) {f : F} (hf : ¬ ∃ i, P.flag i = f) :
    ¬ ∃ i, P.flag i = G.next f := by
  rintro ⟨i, hi⟩
  apply hf
  refine ⟨P.rotor (P.rotor i), ?_⟩
  have h := congrArg (fun x => G.next (G.next x)) hi
  simpa only [P.next_flag, G.next_cube] using h

theorem patchNext_outside {F : Type} {G : FlagGraph F} {n : ℕ}
    (P : Patch G n) (r : Fin n → Fin n) {f : F}
    (hf : ¬ ∃ i, P.flag i = f) : patchNext P r f = G.next f := by
  classical
  simp only [patchNext, dite_eq_right hf]

/-- Replace the selected actual vertex cycles; pairing and colors are untouched. -/
noncomputable def patch {F : Type} {G : FlagGraph F} {n : ℕ}
    (P : Patch G n) (r : Fin n → Fin n)
    (hc : ∀ i, r (r (r i)) = i) (hn : ∀ i, r i ≠ i) : FlagGraph F where
  edge := G.edge
  edge_involutive := G.edge_involutive
  edge_ne := G.edge_ne
  next := patchNext P r
  next_cube f := by
    classical
    by_cases hf : ∃ i, P.flag i = f
    · obtain ⟨i, rfl⟩ := hf
      simp only [patchNext_flag, hc]
    · rw [patchNext_outside P r hf,
        patchNext_outside P r (next_outside P hf),
        patchNext_outside P r (next_outside P (next_outside P hf)), G.next_cube]
  color := G.color
  color_none_iff f := by
    classical
    rw [G.color_none_iff]
    by_cases hf : ∃ i, P.flag i = f
    · obtain ⟨i, rfl⟩ := hf
      rw [P.next_flag, patchNext_flag]
      exact iff_of_true (fun h => P.rotor_ne i (P.flag.injective h))
        (fun h => hn i (P.flag.injective h))
    · rw [patchNext_outside P r hf]

/-- One actual trivalent cyclic orbit. -/
structure Vertex {F : Type} (G : FlagGraph F) where
  flag : Fin 3 ↪ F
  next_flag : ∀ i, G.next (flag i) = flag (finRotate 3 i)

noncomputable def reverseVertex {F : Type} {G : FlagGraph F} (v : Vertex G) :
    FlagGraph F :=
  patch ⟨v.flag, finRotate 3, by decide, by decide, v.next_flag⟩
    ((finRotate 3).symm) (by decide) (by decide)

/-- Literal finite I/H/X cyclic tables on k+,k-,h1,h2,h3,h4. -/
def socketI : Fin 6 → Fin 6 := ![2, 4, 3, 0, 5, 1]
def socketH : Fin 6 → Fin 6 := ![2, 3, 4, 5, 0, 1]
def socketX : Fin 6 → Fin 6 := ![2, 3, 5, 4, 1, 0]

/-- The base graph is the X branch: (k+,h1,h4)|(k-,h2,h3).
All other flag pairings are unrestricted, including port-port pairing. -/
structure Socket {F : Type} (G : FlagGraph F) where
  flag : Fin 6 ↪ F
  next_flag : ∀ i, G.next (flag i) = flag (socketX i)
  central : G.edge (flag 0) = flag 1

noncomputable def Socket.branchI {F : Type} {G : FlagGraph F} (S : Socket G) :
    FlagGraph F :=
  patch ⟨S.flag, socketX, by decide, by decide, S.next_flag⟩ socketI
    (by decide) (by decide)

noncomputable def Socket.branchH {F : Type} {G : FlagGraph F} (S : Socket G) :
    FlagGraph F :=
  patch ⟨S.flag, socketX, by decide, by decide, S.next_flag⟩ socketH
    (by decide) (by decide)

/-- Two actual neighboring ordinary leg insertions. The rotor lists are
(leg,tail,head); the connecting pair joins the first head to the second tail. -/
structure AdjacentLegs {F : Type} (G : FlagGraph F) where
  flag : Fin 6 ↪ F
  leftLeaf : F
  rightLeaf : F
  leaf_ne : leftLeaf ≠ rightLeaf
  next_first : ∀ i : Fin 3,
    G.next (flag (Fin.castAdd 3 i)) = flag (Fin.castAdd 3 (finRotate 3 i))
  next_second : ∀ i : Fin 3,
    G.next (flag (Fin.natAdd 3 i)) = flag (Fin.natAdd 3 (finRotate 3 i))
  first_pair : G.edge (flag 0) = leftLeaf
  second_pair : G.edge (flag 3) = rightLeaf
  connector : G.edge (flag 2) = flag 4
  left_fixed : G.next leftLeaf = leftLeaf
  right_fixed : G.next rightLeaf = rightLeaf
  left_ordinary : ∃ c, G.color leftLeaf = some (.ordinary c)
  right_ordinary : ∃ c, G.color rightLeaf = some (.ordinary c)

open Classical in
noncomputable def exchangeColors {F : Type} {G : FlagGraph F} (L : AdjacentLegs G) :
    FlagGraph F where
  edge := G.edge
  edge_involutive := G.edge_involutive
  edge_ne := G.edge_ne
  next := G.next
  next_cube := G.next_cube
  color f := if f = L.leftLeaf then G.color L.rightLeaf else
    if f = L.rightLeaf then G.color L.leftLeaf else G.color f
  color_none_iff f := by
    classical
    by_cases hl : f = L.leftLeaf
    · subst f
      simp only [ite_eq_left rfl, L.left_fixed, ne_eq, not_true_eq_false, iff_false]
      exact (G.color_none_iff L.rightLeaf).not.mpr (not_not.mpr L.right_fixed)
    · by_cases hr : f = L.rightLeaf
      · subst f
        simp only [ite_eq_right hl, ite_eq_left rfl, L.right_fixed, ne_eq, not_true_eq_false,
          iff_false]
        exact (G.color_none_iff L.leftLeaf).not.mpr (not_not.mpr L.left_fixed)
      · simp only [ite_eq_right hl, ite_eq_right hr, G.color_none_iff]

end FlagGraph

abbrev FreeDiagram := Diagram →₀ ℚ

noncomputable def basis (D : Diagram) : FreeDiagram := Finsupp.single D 1

/-- Only geometric AS/IHX/CL and actual oriented flag isomorphisms generate
relations. In particular the span is not defined by a normalization kernel. -/
inductive ActualRelator : FreeDiagram → Prop
  | iso {F K : Type} [Finite F] [Finite K] {G : FlagGraph F} {H : FlagGraph K}
      (e : FlagIso G H) : ActualRelator (basis (pack G) - basis (pack H))
  | as {F : Type} [Finite F] {G : FlagGraph F} (v : G.Vertex) :
      ActualRelator (basis (pack G) + basis (pack (FlagGraph.reverseVertex v)))
  | ihx {F : Type} [Finite F] {G : FlagGraph F} (S : G.Socket) :
      ActualRelator (basis (pack S.branchI) - basis (pack S.branchH) + basis (pack G))
  | cl {F : Type} [Finite F] {G : FlagGraph F} (L : G.AdjacentLegs) :
      ActualRelator (basis (pack G) - basis (pack (FlagGraph.exchangeColors L)))

noncomputable def relationSpace : Submodule ℚ FreeDiagram :=
  Submodule.span ℚ {r | ActualRelator r}

abbrev JacobiSpace := FreeDiagram ⧸ relationSpace

noncomputable def classOf {F : Type} [Finite F] (G : FlagGraph F) : JacobiSpace :=
  relationSpace.mkQ (basis (pack G))

theorem actual_relator_zero (r : FreeDiagram) (h : ActualRelator r) :
    relationSpace.mkQ r = 0 := by
  apply (Submodule.Quotient.mk_eq_zero relationSpace).mpr
  exact Submodule.subset_span h

end D5.S3.Combinatorics.Graph.Jacobi
