/- GID: D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary subspace degrees and color-preserving reversible deletion. -/

import D5.S3.Combinatorics.Orthogonality.NikandishClique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace D5.S3.Combinatorics.Orthogonality.OrthogonalityDegreeDeletion

open Module
open D5.S3.Combinatorics.Orthogonality.NikandishClique
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

/-- Count every nonzero subspace contained in an arbitrary coordinate subspace.
This is the lattice count consumed by degree and fixed-clique list formulas. -/
theorem below_card (n : ℕ) (X : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {W : Vertex n // W.1 ≤ X} =
      nonzeroSubspaceCount (finrank (ZMod 2) X) := by
  classical
  have nz (W : {W : Vertex n // W.1 ≤ X}) : W.1.1.comap X.subtype ≠ ⊥ := by
    intro h
    apply W.1.2
    have he := congrArg (Submodule.map X.subtype) h
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr W.2] using he
  let f : {W : Vertex n // W.1 ≤ X} → {P : Submodule (ZMod 2) X // P ≠ ⊥} :=
    fun W => ⟨W.1.1.comap X.subtype, nz W⟩
  have fi : Function.Injective f := by
    intro U W h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun P : {P : Submodule (ZMod 2) X // P ≠ ⊥} =>
      P.1.map X.subtype) h
    simpa [f, Submodule.map_comap_subtype, inf_eq_right.mpr U.2,
      inf_eq_right.mpr W.2] using he
  have fs : Function.Surjective f := by
    intro P
    have hp : P.1.map X.subtype ≠ ⊥ := by
      intro h
      apply P.2
      apply Submodule.map_injective_of_injective (show Function.Injective X.subtype from
        Subtype.val_injective)
      simpa using h
    refine ⟨⟨⟨P.1.map X.subtype, hp⟩, Submodule.map_subtype_le X P.1⟩, ?_⟩
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective (show Function.Injective X.subtype from
      Subtype.val_injective) P.1
  let e := Submodule.orderIsoMapComap (Module.finBasis (ZMod 2) X).equivFun
  calc
    _ = Nat.card {P : Submodule (ZMod 2) X // P ≠ ⊥} :=
      Nat.card_congr (Equiv.ofBijective f ⟨fi, fs⟩)
    _ = _ := Nat.card_congr (e.toEquiv.subtypeEquiv (fun P => by simp))

open Classical in
/-- The actual neighbor cardinality, including the exact self-loop subtraction.
The lattice count is the existing cardinal invariant, not an assumed enumeration. -/
theorem degree_card (n : ℕ) (U : Vertex n) :
    Nat.card ((orthogonalityGraph n).neighborSet U) =
      if U.1 ≤ (standardCoordinatePairing (ZMod 2) (Fin n)).orthogonal U.1 then
        nonzeroSubspaceCount (n - finrank (ZMod 2) U.1) - 1
      else nonzeroSubspaceCount (n - finrank (ZMod 2) U.1) := by
  classical
  let : Fintype (Vertex n) := Fintype.ofFinite _
  let B := standardCoordinatePairing (ZMod 2) (Fin n)
  let X := B.orthogonal U.1
  let S := Finset.univ.filter (fun W : Vertex n => W.1 ≤ X)
  have bs : B.IsSymm := ⟨dotProduct_comm⟩
  have bn : B.Nondegenerate := bs.isRefl.nondegenerate_iff_separatingLeft.mpr
    (fun x hx => dotProduct_eq_zero x hx)
  have dimX : finrank (ZMod 2) X = n - finrank (ZMod 2) U.1 := by
    simpa [X] using B.finrank_orthogonal bn U.1
  have count : S.card = nonzeroSubspaceCount (n - finrank (ZMod 2) U.1) := by
    have h := below_card n X
    rw [dimX, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  have neighbors : (orthogonalityGraph n).neighborFinset U = S.erase U := by
    ext W
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_univ, true_and, S]
    constructor
    · intro h
      exact ⟨h.1.symm, fun w hw u hu => h.2 u hu w hw⟩
    · rintro ⟨hne, hle⟩
      exact ⟨hne.symm, fun u hu w hw => hle hw u hu⟩
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    SimpleGraph.degree, neighbors]
  by_cases h : U.1 ≤ X
  · rw [Finset.card_erase_of_mem (by simp [S, h]), count]
    exact (if_pos h).symm
  · rw [Finset.erase_eq_of_notMem (by simp [S, h]), count]
    exact (if_neg h).symm

private theorem extend_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : Finset V) (v : V) (hv : v ∉ D) (k : ℕ)
    (hd : Nat.card (G.neighborSet v) < k)
    (c : (G.induce {w | w ∉ insert v D}).Coloring (Fin k)) :
    ∃ c' : (G.induce {w | w ∉ D}).Coloring (Fin k),
      ∀ w (hw : w ∉ insert v D),
        c' ⟨w, fun h => hw (Finset.mem_insert_of_mem h)⟩ = c ⟨w, hw⟩ := by
  classical
  let T := {w : G.neighborSet v // w.1 ∉ insert v D}
  let used := Finset.univ.image (fun w : T => c ⟨w.1.1, w.2⟩)
  have hcard : used.card < (Finset.univ : Finset (Fin k)).card := by
    have hc : used.card ≤ Fintype.card T := (Finset.card_image_le).trans_eq
      (Finset.card_univ)
    have ht := Fintype.card_subtype_le (fun w : G.neighborSet v =>
      w.1 ∉ insert v D)
    rw [Nat.card_eq_fintype_card] at hd
    simpa using (hc.trans ht).trans_lt hd
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have fresh (w : V) (hw : w ∉ insert v D) (he : G.Adj v w) : a ≠ c ⟨w, hw⟩ := by
    intro h
    apply ha
    exact Finset.mem_image.mpr ⟨⟨⟨w, he⟩, hw⟩, Finset.mem_univ _, h.symm⟩
  let color (w : {w : V // w ∉ D}) : Fin k :=
    if h : w.1 = v then a else c ⟨w.1, by simp [h, w.2]⟩
  have proper : ∀ {x y : {w : V // w ∉ D}},
      (G.induce {w | w ∉ D}).Adj x y → color x ≠ color y := by
    intro x y hxy
    by_cases hx : x.1 = v
    · by_cases hy : y.1 = v
      · exact (G.ne_of_adj hxy (hx.trans hy.symm)).elim
      · simpa [color, hx, hy] using fresh y.1 (by simp [hy, y.2]) (hx ▸ hxy)
    · by_cases hy : y.1 = v
      · have he : G.Adj v x.1 := hy ▸ G.adj_symm hxy
        exact fun h => fresh x.1 (by simp [hx, x.2]) he (by simpa [color, hx, hy] using h.symm)
      · simpa [color, hx, hy] using c.valid (show (G.induce {w | w ∉ insert v D}).Adj
          ⟨x.1, by simp [hx, x.2]⟩ ⟨y.1, by simp [hy, y.2]⟩ from hxy)
  refine ⟨SimpleGraph.Coloring.mk color proper, ?_⟩
  intro w hw
  have hne : w ≠ v := fun h => hw (by simp [h])
  change color ⟨w, _⟩ = c ⟨w, hw⟩
  simp [color, hne]

private theorem extend_deleted {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset V) (k : ℕ) (hd : ∀ v ∈ D, Nat.card (G.neighborSet v) < k)
    (c : (G.induce {v | v ∉ D}).Coloring (Fin k)) :
    ∃ C : G.Coloring (Fin k), ∀ v (hv : v ∉ D), C v = c ⟨v, hv⟩ := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    refine ⟨SimpleGraph.Coloring.mk (fun v => c ⟨v, by simp⟩)
      (fun h => c.valid h), ?_⟩
    intro v hv
    rfl
  | @insert v D hv ih =>
    obtain ⟨c', hc'⟩ := extend_one G D v hv k (hd v (by simp)) c
    obtain ⟨C, hC⟩ := ih (fun w hw => hd w (Finset.mem_insert_of_mem hw)) c'
    refine ⟨C, fun w hw => ?_⟩
    exact (hC w (fun h => hw (Finset.mem_insert_of_mem h))).trans (hc' w hw)

/-- Reversing any finite collection of safe deletions extends every coloring
without changing any retained vertex, in every dimension and for every palette.
In particular all colors on any fixed clique in the retained graph are preserved. -/
theorem result (n k : ℕ) (D : Finset (Vertex n))
    (hd : ∀ U ∈ D, nonzeroSubspaceCount (n - finrank (ZMod 2) U.1) < k)
    (c : ((orthogonalityGraph n).induce {U | U ∉ D}).Coloring (Fin k)) :
    ∃ C : (orthogonalityGraph n).Coloring (Fin k),
      ∀ U (hU : U ∉ D), C U = c ⟨U, hU⟩ := by
  classical
  let : Fintype (Vertex n) := Fintype.ofFinite _
  apply extend_deleted (orthogonalityGraph n) D k _ c
  intro U hU
  rw [degree_card]
  split
  · exact (Nat.sub_le _ _).trans_lt (hd U hU)
  · exact hd U hU

#print axioms degree_card
#print axioms result

end D5.S3.Combinatorics.Orthogonality.OrthogonalityDegreeDeletion
