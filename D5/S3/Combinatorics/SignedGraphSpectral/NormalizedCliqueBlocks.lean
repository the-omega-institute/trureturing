/- GID: D5/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Normalized edge-mass equality decomposes into cliques with rooted zero-sum extensions. -/

import D5.S3.Combinatorics.SignedGraphSpectral.DoublyNonnegativeEdgeMass
import D5.S3.Combinatorics.Graph.Brooks.Cuts

/-!
Normalized edge-mass equality decomposes into cliques with rooted zero-sum extensions.
The support and the normalized equality argument are those used to settle
Hu–Han Problem 6.1, with the clique decomposition of Hu–Liu–Wang, Proposition 4.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy

/-! ### Cut budgets and normalization -/

section

open Finset Matrix SimpleGraph
open scoped Matrix BigOperators

namespace DNN

open Gram

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A partition of the vertices off a single separator into two nonempty sides. -/
private structure Cut (G : SimpleGraph V) where
  c : V
  L : Finset V
  R : Finset V
  left_nonempty : L.Nonempty
  right_nonempty : R.Nonempty
  c_not_left : c ∉ L
  c_not_right : c ∉ R
  disjoint : Disjoint L R
  cover : insert c (L ∪ R) = univ
  no_cross : ∀ i ∈ L, ∀ j ∈ R, ¬ G.Adj i j
  left_connected : (G.induce (↑(insert c L) : Set V)).Connected
  right_connected : (G.induce (↑(insert c R) : Set V)).Connected

variable {G : SimpleGraph V}

private abbrev Cut.left (C : Cut G) : Finset V := insert C.c C.L
private abbrev Cut.right (C : Cut G) : Finset V := insert C.c C.R

private theorem cut_of_not_connected_deleted (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (c : V) (hc : ¬ (deleted G c).Connected) :
    Nonempty (Cut G) := by
  classical
  have hpos : 0 < Fintype.card (({c}ᶜ : Set V)) := by rw [card_deleted]; omega
  have hne := Fintype.card_pos_iff.mp hpos
  have hp : ¬ (deleted G c).Preconnected := fun h => hc ((connected_iff _).mpr ⟨h, hne⟩)
  unfold SimpleGraph.Preconnected at hp
  push Not at hp
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hsep⟩ := hp
  obtain ⟨L, R, hL, hR, hcL, hcR, hdj, hcov, hcross, hl, hr⟩ :=
    BrooksSubcubic.cut_partition_of_unreachable G hG c d e hd he hsep
  exact ⟨⟨c, L, R, hL, hR, hcL, hcR, hdj, hcov, hcross, hl, hr⟩⟩

private theorem Cut.mem_sides (C : Cut G) (i : V) : i = C.c ∨ i ∈ C.L ∨ i ∈ C.R := by
  have h : i ∈ insert C.c (C.L ∪ C.R) := C.cover ▸ mem_univ i
  simpa only [mem_insert, mem_union] using h

private theorem Cut.overlap (C : Cut G) {i : V} (hi : i ∈ C.left) (hj : i ∈ C.right) :
    i = C.c := by
  rcases mem_insert.mp hi with h | h
  · exact h
  · exact (mem_insert.mp hj).resolve_right (Finset.disjoint_left.mp C.disjoint h)

private theorem Cut.edge_sides (C : Cut G) {i j : V} (h : G.Adj i j) :
    (i ∈ C.left ∧ j ∈ C.left) ∨ (i ∈ C.right ∧ j ∈ C.right) := by
  rcases C.mem_sides i with hi | hi | hi <;>
    rcases C.mem_sides j with hj | hj | hj
  all_goals try first
    | exact Or.inl ⟨mem_insert.mpr (Or.inl hi), mem_insert.mpr (Or.inl hj)⟩
    | exact Or.inl ⟨mem_insert.mpr (Or.inl hi), mem_insert_of_mem hj⟩
    | exact Or.inl ⟨mem_insert_of_mem hi, mem_insert.mpr (Or.inl hj)⟩
    | exact Or.inl ⟨mem_insert_of_mem hi, mem_insert_of_mem hj⟩
    | exact Or.inr ⟨mem_insert.mpr (Or.inl hi), mem_insert_of_mem hj⟩
    | exact Or.inr ⟨mem_insert_of_mem hi, mem_insert.mpr (Or.inl hj)⟩
    | exact Or.inr ⟨mem_insert_of_mem hi, mem_insert_of_mem hj⟩
    | exact (C.no_cross i hi j hj h).elim
    | exact (C.no_cross j hj i hi h.symm).elim

private theorem Cut.card_lt (C : Cut G) :
    C.left.card < Fintype.card V ∧ C.right.card < Fintype.card V := by
  obtain ⟨i, hi⟩ := C.left_nonempty
  obtain ⟨j, hj⟩ := C.right_nonempty
  have hnotL : j ∉ C.left := by
    intro hjL
    have h := C.overlap hjL (mem_insert_of_mem hj)
    exact C.c_not_right (h ▸ hj)
  have hnotR : i ∉ C.right := by
    intro hiR
    have h := C.overlap (mem_insert_of_mem hi) hiR
    exact C.c_not_left (h ▸ hi)
  rw [← card_univ]
  exact ⟨card_lt_card (ssubset_iff_of_subset (subset_univ _)
    |>.mpr ⟨j, mem_univ _, hnotL⟩), card_lt_card (ssubset_iff_of_subset (subset_univ _)
    |>.mpr ⟨i, mem_univ _, hnotR⟩)⟩

private theorem map_side_edges (G : SimpleGraph V) (S : Finset V) :
    (G.induce (↑S : Set V)).edgeFinset.map (Function.Embedding.subtype (· ∈ (↑S : Set V))).sym2Map =
      (sideGraph G S).edgeFinset := by
  classical
  have hm := map_edgeFinset_induce (s := (↑S : Set V)) (G := G)
  have hinst : (Subtype.fintype (· ∈ (↑S : Set V)) : Fintype (↑S : Set V)) =
      FinsetCoe.fintype S := Subsingleton.elim _ _
  rw [hinst] at hm
  refine hm.trans ?_
  ext e
  induction e using Sym2.inductionOn with
  | hf i j =>
    simp only [mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mem_sym2_iff, Finset.toFinset_coe]
    change (G.Adj i j ∧ (∀ a ∈ s(i,j), a ∈ S)) ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S
    simp only [Sym2.mem_iff]
    aesop

private theorem side_card_edges (G : SimpleGraph V) (S : Finset V) :
    (G.induce (↑S : Set V)).edgeFinset.card = (sideGraph G S).edgeFinset.card := by
  rw [← map_side_edges, card_map]

private theorem edgeMass_principal_side (G : SimpleGraph V) (S : Finset V) (M : Matrix V V ℝ)
    (hM : M.IsSymm) (hsub : (principal M (↑S : Set V)).IsSymm) :
    edgeMass (G.induce (↑S : Set V)) (principal M (↑S : Set V)) hsub =
      edgeMass (sideGraph G S) M hM := by
  rw [edgeMass_eq_sum, edgeMass_eq_sum, ← map_side_edges, sum_map]
  apply sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | hf i j => rfl

private theorem mass_principal_of_rows (S : Finset V) (M : Matrix V V ℝ)
    (hM : M.IsSymm) (hRow : ∀ i, i ∉ S → ∀ j, M i j = 0) :
    mass (principal M (↑S : Set V)) = mass M := by
  have hm := mass_principal_filter M (↑S : Set V)
  have hinst : (Subtype.fintype (· ∈ (↑S : Set V)) : Fintype (↑S : Set V)) =
      FinsetCoe.fintype S := Subsingleton.elim _ _
  rw [hinst] at hm
  refine hm.trans ?_
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp [hi, hj]
    · simp [hi, hj, ← hM.apply i j, hRow j hj i]
  · simp [hi, hRow i hi j]

private theorem Cut.budget_add (C : Cut G) :
    budget (G.induce (↑C.left : Set V)) + budget (G.induce (↑C.right : Set V)) = budget G := by
  classical
  have hEdge :
      Disjoint (sideGraph G C.left).edgeFinset (sideGraph G C.right).edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | hf i j =>
      have he' : G.Adj i j ∧ i ∈ C.left ∧ j ∈ C.left := (mem_edgeSet (G := sideGraph G C.left)).mp (mem_edgeFinset.mp he)
      have hf' : G.Adj i j ∧ i ∈ C.right ∧ j ∈ C.right := (mem_edgeSet (G := sideGraph G C.right)).mp (mem_edgeFinset.mp hf)
      exact he'.1.ne ((C.overlap he'.2.1 hf'.2.1).trans (C.overlap he'.2.2 hf'.2.2).symm)
  have hUnion : (sideGraph G C.left).edgeFinset ∪ (sideGraph G C.right).edgeFinset =
      G.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf i j =>
      simp only [mem_union, mem_edgeFinset, mem_edgeSet]
      change (G.Adj i j ∧ i ∈ C.left ∧ j ∈ C.left) ∨
        (G.Adj i j ∧ i ∈ C.right ∧ j ∈ C.right) ↔ G.Adj i j
      exact ⟨fun h => h.elim And.left And.left, fun h =>
        (C.edge_sides h).imp (And.intro h) (And.intro h)⟩
  have hM := card_union_of_disjoint hEdge
  rw [hUnion] at hM
  have hV₀ := congrArg Finset.card C.cover
  rw [card_insert_of_notMem (by simp [C.c_not_left, C.c_not_right]),
    card_union_of_disjoint C.disjoint, card_univ] at hV₀
  have hV₁ : C.left.card + C.right.card = Fintype.card V + 1 := by
    rw [Cut.left, Cut.right, card_insert_of_notMem C.c_not_left, card_insert_of_notMem C.c_not_right]
    omega
  have hMc : (G.edgeFinset.card : ℝ) =
      ((sideGraph G C.left).edgeFinset.card : ℝ) + ((sideGraph G C.right).edgeFinset.card : ℝ) := by
    exact_mod_cast hM
  have hVc : (C.left.card : ℝ) + (C.right.card : ℝ) = (Fintype.card V : ℝ) + 1 := by
    exact_mod_cast hV₁
  rw [budget_eq, budget_eq, budget_eq, side_card_edges, side_card_edges]
  have hcL : Fintype.card (↑C.left : Set V) = C.left.card := Fintype.card_coe C.left
  have hcR : Fintype.card (↑C.right : Set V) = C.right.card := Fintype.card_coe C.right
  rw [hcL, hcR]
  linarith only [hMc, hVc]

/-- The ambient split, together with its principal submatrices and exact additive totals. -/
private structure CutSplit (C : Cut G) (M : Matrix V V ℝ) (hM : SupportedDNN G M) where
  N : Matrix V V ℝ
  P : Matrix V V ℝ
  N_supported : SupportedDNN (sideGraph G C.left) N
  P_supported : SupportedDNN (sideGraph G C.right) P
  N_rows : ∀ i, i ∉ C.left → ∀ j, N i j = 0
  P_rows : ∀ i, i ∉ C.right → ∀ j, P i j = 0
  sum_eq : M = N + P
  mass_eq : mass M = mass (principal N (↑C.left : Set V)) + mass (principal P (↑C.right : Set V))
  edge_eq : edgeMass G M hM.symm =
    edgeMass (G.induce (↑C.left : Set V)) (principal N (↑C.left : Set V))
      ((N_supported.psd.submatrix Subtype.val).isHermitian.isSymm) +
    edgeMass (G.induce (↑C.right : Set V)) (principal P (↑C.right : Set V))
      ((P_supported.psd.submatrix Subtype.val).isHermitian.isSymm)

private theorem supported_side_principal (S : Finset V) {M : Matrix V V ℝ}
    (hM : SupportedDNN (sideGraph G S) M) :
    SupportedDNN (G.induce (↑S : Set V)) (principal M (↑S : Set V)) where
  psd := hM.psd.submatrix _
  nonneg i j := hM.nonneg i j
  zero_of_nonedge {i j} hij hn :=
    hM.zero_of_nonedge (fun h => hij (Subtype.ext h)) fun h => hn h.1

private theorem Cut.exists_split (C : Cut G) (M : Matrix V V ℝ) (hM : SupportedDNN G M) :
    Nonempty (CutSplit C M hM) := by
  obtain ⟨N, P, hN, hP, hNr, hPr, hsum, hm, he⟩ :=
    gram_cut_split G M hM C.c C.L C.R C.disjoint C.mem_sides C.no_cross
  refine ⟨⟨N, P, hN, hP, hNr, hPr, hsum, ?_, ?_⟩⟩
  · rwa [mass_principal_of_rows _ N hN.symm hNr, mass_principal_of_rows _ P hP.symm hPr]
  · exact he.trans (congrArg₂ (· + ·)
      (edgeMass_principal_side G C.left N hN.symm _).symm
      (edgeMass_principal_side G C.right P hP.symm _).symm)

private theorem CutSplit.bounded {C : Cut G} {M : Matrix V V ℝ} {hM : SupportedDNN G M}
    (D : CutSplit C M hM)
    (hl : Bounded (G.induce (↑C.left : Set V)) (principal D.N (↑C.left : Set V))
      (supported_side_principal C.left D.N_supported))
    (hr : Bounded (G.induce (↑C.right : Set V)) (principal D.P (↑C.right : Set V))
      (supported_side_principal C.right D.P_supported)) :
    Bounded G M hM := by
  unfold Bounded
  rw [D.edge_eq, D.mass_eq, ← C.budget_add]
  exact cut_scalar_bound (budget_nonneg C.left_connected) (budget_nonneg C.right_connected)
    (mass_nonneg (M := principal D.N (↑C.left : Set V)) fun i j => D.N_supported.nonneg i j)
    (mass_nonneg (M := principal D.P (↑C.right : Set V)) fun i j => D.P_supported.nonneg i j) hl hr
    (add_nonneg (edgeMass_nonneg _ _ _) (edgeMass_nonneg _ _ _))

private theorem CutSplit.normalized {C : Cut G} {M : Matrix V V ℝ} {hM : SupportedDNN G M}
    (D : CutSplit C M hM)
    (hl : Bounded (G.induce (↑C.left : Set V)) (principal D.N (↑C.left : Set V))
      (supported_side_principal C.left D.N_supported))
    (hr : Bounded (G.induce (↑C.right : Set V)) (principal D.P (↑C.right : Set V))
      (supported_side_principal C.right D.P_supported))
    (he : Normalized G M hM) :
    Normalized (G.induce (↑C.left : Set V)) (principal D.N (↑C.left : Set V))
      (supported_side_principal C.left D.N_supported) ∧
    Normalized (G.induce (↑C.right : Set V)) (principal D.P (↑C.right : Set V))
      (supported_side_principal C.right D.P_supported) := by
  have ht : _ = _ := D.mass_eq.symm.trans (he.1.trans C.budget_add.symm)
  have hs := (congrArg (fun t : ℝ => 2 * t) D.edge_eq).symm.trans (he.2.trans C.budget_add.symm)
  obtain ⟨hNl, hNl', hPr, hPr'⟩ := cut_scalar_normalized
    (budget_nonneg C.left_connected) (budget_nonneg C.right_connected)
    (mass_nonneg (M := principal D.N (↑C.left : Set V)) fun i j => D.N_supported.nonneg i j)
    (mass_nonneg (M := principal D.P (↑C.right : Set V)) fun i j => D.P_supported.nonneg i j) hl hr ht hs
  exact ⟨⟨hNl, hNl'⟩, ⟨hPr, hPr'⟩⟩

end DNN

end

/-! ### Inductive edge-mass bound -/

section

open Finset Matrix SimpleGraph
open scoped Matrix BigOperators

namespace DNN

open Gram

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem supported_bound (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : SupportedDNN G M) (hG : G.Connected) : Bounded G M hM := by
  suffices h : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      Fintype.card W = n → ∀ (H : SimpleGraph W) (X : Matrix W W ℝ)
      (hX : SupportedDNN H X), H.Connected → Bounded H X hX from
    h (Fintype.card V) V rfl G M hM hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ hW H X hX hH
    have hne := hH.nonempty
    have hn : 0 < Fintype.card W := Fintype.card_pos
    by_cases hn₁ : Fintype.card W = 1
    · exact singleton_bound H X hX hn₁
    by_cases hn₂ : Fintype.card W = 2
    · exact two_bound H X hX hH hn₂
    have hn₃ : 3 ≤ Fintype.card W := by omega
    by_cases hall : ∀ v, (deleted H v).Connected
    · apply noCut_bound H X hX hn₃ hall
      intro v
      have hlt : Fintype.card (↑({v}ᶜ : Set W)) < n := by
        rw [card_deleted]
        omega
      exact ih _ hlt _ rfl _ _ _ (hall v)
    · push Not at hall
      obtain ⟨v, hv⟩ := hall
      obtain ⟨C⟩ := cut_of_not_connected_deleted hH (by omega) v hv
      obtain ⟨D⟩ := C.exists_split X hX
      have hl : Fintype.card (↑C.left : Set W) < n := by
        rw [show Fintype.card (↑C.left : Set W) = C.left.card from Fintype.card_coe C.left, ← hW]
        exact C.card_lt.1
      have hr : Fintype.card (↑C.right : Set W) < n := by
        rw [show Fintype.card (↑C.right : Set W) = C.right.card from Fintype.card_coe C.right, ← hW]
        exact C.card_lt.2
      exact D.bounded (ih _ hl _ rfl _ _ _ C.left_connected)
        (ih _ hr _ rfl _ _ _ C.right_connected)

/-- Once the connected edge-mass bound is established, this checks the no-cut
rigidity without any user-supplied inequality on the vertex deletions. -/
private theorem leaf_normalized (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : SupportedDNN G M) (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hNoCut : ∀ v, (deleted G v).Connected) (he : Normalized G M hM) :
    G = ⊤ ∧ M = blockMatrix (univ : Finset V) := by
  by_cases hn₂ : Fintype.card V = 2
  · exact two_normalized G M hM hG hn₂ he
  exact noCut_normalized G M hM hG (by omega) hNoCut
    (fun v => supported_bound _ _ _ (hNoCut v)) he

end DNN

end

/-! ### Normalized clique decomposition -/

section

open Finset Matrix SimpleGraph
open scoped Matrix BigOperators

namespace DNN

open Gram

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The literal matrix sum and the graph incidence data consumed at the signed endpoint. -/
structure BlockDecomposition (G : SimpleGraph V) (M : Matrix V V ℝ)
    (blocks : Finset (Finset V)) : Prop where
  size : ∀ B ∈ blocks, 2 ≤ B.card
  clique : ∀ B ∈ blocks, G.IsClique (B : Set V)
  edge : ∀ i j, G.Adj i j → ∃! B, B ∈ blocks ∧ i ∈ B ∧ j ∈ B
  clique_cover : ∀ A : Finset V, G.IsClique (A : Set V) → 2 ≤ A.card →
    ∃ B ∈ blocks, A ⊆ B
  matrix_eq : M = ∑ B ∈ blocks, blockMatrix B

variable {G : SimpleGraph V}

private def liftBlock (S : Finset V) : Finset (↑S : Set V) ↪ Finset V :=
  (Finset.mapEmbedding (Function.Embedding.subtype (· ∈ (↑S : Set V)))).toEmbedding

private theorem liftBlock_subset (S : Finset V) (B : Finset (↑S : Set V)) :
    liftBlock S B ⊆ S := by
  intro x hx
  obtain ⟨w, _, rfl⟩ := mem_map.mp hx
  exact w.property

private theorem mem_liftBlock (S : Finset V) (B : Finset (↑S : Set V)) (i : (↑S : Set V)) :
    i.val ∈ liftBlock S B ↔ i ∈ B :=
  mem_map' (Function.Embedding.subtype (· ∈ (↑S : Set V)))

private theorem liftBlock_card (S : Finset V) (B : Finset (↑S : Set V)) :
    (liftBlock S B).card = B.card := card_map _

private theorem lift_decomposition (S : Finset V) (M : Matrix V V ℝ)
    (hM : M.IsSymm) (hRow : ∀ i, i ∉ S → ∀ j, M i j = 0)
    (blocks : Finset (Finset (↑S : Set V)))
    (D : BlockDecomposition (G.induce (↑S : Set V)) (principal M (↑S : Set V)) blocks) :
    BlockDecomposition (sideGraph G S) M (blocks.map (liftBlock S)) ∧
      ∀ B ∈ blocks.map (liftBlock S), B ⊆ S := by
  classical
  have hsub : ∀ A ∈ blocks.map (liftBlock S), A ⊆ S := by
    intro A hA
    obtain ⟨B, _, rfl⟩ := mem_map.mp hA
    exact liftBlock_subset S B
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsub⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_map.mp hA
    rw [liftBlock_card]
    exact D.size B hB
  · intro A hA i hi j hj hij
    obtain ⟨B, hB, rfl⟩ := mem_map.mp hA
    let i' : (↑S : Set V) := ⟨i, liftBlock_subset S B hi⟩
    let j' : (↑S : Set V) := ⟨j, liftBlock_subset S B hj⟩
    have hAdj := D.clique B hB ((mem_liftBlock S B i').mp hi)
      ((mem_liftBlock S B j').mp hj) (fun h => hij (congrArg Subtype.val h))
    exact ⟨hAdj, i'.property, j'.property⟩
  · intro i j hij
    let i' : (↑S : Set V) := ⟨i, hij.2.1⟩
    let j' : (↑S : Set V) := ⟨j, hij.2.2⟩
    obtain ⟨B, ⟨hb, hi, hj⟩, hu⟩ := D.edge i' j' hij.1
    refine ⟨liftBlock S B, ⟨mem_map_of_mem _ hb, (mem_liftBlock S B i').mpr hi,
      (mem_liftBlock S B j').mpr hj⟩, ?_⟩
    rintro A ⟨hA, hai, haj⟩
    obtain ⟨Q, hQ, rfl⟩ := mem_map.mp hA
    exact congrArg (liftBlock S) (hu Q ⟨hQ, (mem_liftBlock S Q i').mp hai,
      (mem_liftBlock S Q j').mp haj⟩)
  · intro A hA hSize
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hSize
    have hAS : A ⊆ S := by
      intro k hk
      by_cases hki : k = i
      · subst k
        exact (hA hi hj hij).2.1
      · exact (hA hk hi hki).2.1
    let E := A.subtype (· ∈ (↑S : Set V))
    have hCard : E.card = A.card := by
      rw [Finset.card_subtype]
      exact congrArg Finset.card (filter_eq_self.mpr (fun k hk => show k ∈ (↑S : Set V) from hAS hk))
    have hClique : (G.induce (↑S : Set V)).IsClique (E : Set (↑S : Set V)) := by
      intro x hx y hy hxy
      exact (hA (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
        (fun h => hxy (Subtype.ext h))).1
    obtain ⟨B, hB, hAB⟩ := D.clique_cover E hClique (hCard ▸ hSize)
    refine ⟨liftBlock S B, mem_map_of_mem _ hB, ?_⟩
    intro k hk
    exact (mem_liftBlock S B ⟨k, hAS hk⟩).mpr (hAB (Finset.mem_subtype.mpr hk))
  · ext i j
    simp only [Matrix.sum_apply, sum_map]
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · let i' : (↑S : Set V) := ⟨i, hi⟩
        let j' : (↑S : Set V) := ⟨j, hj⟩
        have he := congrFun (congrFun D.matrix_eq i') j'
        change M i j = _ at he
        rw [he, Matrix.sum_apply]
        refine sum_congr rfl fun B _ => ?_
        simp only [blockMatrix, blockWeight, liftBlock_card]
        exact if_congr (and_congr (mem_liftBlock S B i').symm (mem_liftBlock S B j').symm) rfl rfl
      · rw [← hM.apply i j, hRow j hj]
        symm
        refine sum_eq_zero fun B _ => ?_
        exact if_neg (fun h => hj (liftBlock_subset S B h.2))
    · rw [hRow i hi]
      symm
      refine sum_eq_zero fun B _ => ?_
      exact if_neg (fun h => hi (liftBlock_subset S B h.1))

private theorem Cut.merge_decompositions (C : Cut G) {M N P : Matrix V V ℝ}
    (hSum : M = N + P) {left right : Finset (Finset V)}
    (Dl : BlockDecomposition (sideGraph G C.left) N left)
    (Dr : BlockDecomposition (sideGraph G C.right) P right)
    (Hl : ∀ B ∈ left, B ⊆ C.left) (Hr : ∀ B ∈ right, B ⊆ C.right) :
    BlockDecomposition G M (left ∪ right) := by
  classical
  have hDisj : Disjoint left right := by
    refine Finset.disjoint_left.mpr fun B hB hB' => ?_
    have hsub : B ⊆ {C.c} := fun i hi =>
      mem_singleton.mpr (C.overlap (Hl B hB hi) (Hr B hB' hi))
    have hc := card_le_card hsub
    have hs := Dl.size B hB
    simp only [card_singleton] at hc
    omega
  have hsep {i j : V} (h : G.Adj i j)
      (hi : i ∈ C.left) (hj : j ∈ C.left) (hi' : i ∈ C.right) (hj' : j ∈ C.right) :
      False := h.ne ((C.overlap hi hi').trans (C.overlap hj hj').symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    exact (mem_union.mp hB).elim (Dl.size B) (Dr.size B)
  · intro B hB i hi j hj hij
    rcases mem_union.mp hB with hB | hB
    · exact (Dl.clique B hB hi hj hij).1
    · exact (Dr.clique B hB hi hj hij).1
  · intro i j hij
    rcases C.edge_sides hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · obtain ⟨B, ⟨hB, hBi, hBj⟩, hu⟩ := Dl.edge i j ⟨hij, hi, hj⟩
      refine ⟨B, ⟨mem_union.mpr (Or.inl hB), hBi, hBj⟩, ?_⟩
      rintro A ⟨ha, hai, haj⟩
      rcases mem_union.mp ha with ha | ha
      · exact hu A ⟨ha, hai, haj⟩
      · exact (hsep hij hi hj (Hr A ha hai) (Hr A ha haj)).elim
    · obtain ⟨B, ⟨hB, hBi, hBj⟩, hu⟩ := Dr.edge i j ⟨hij, hi, hj⟩
      refine ⟨B, ⟨mem_union.mpr (Or.inr hB), hBi, hBj⟩, ?_⟩
      rintro A ⟨ha, hai, haj⟩
      rcases mem_union.mp ha with ha | ha
      · exact (hsep hij (Hl A ha hai) (Hl A ha haj) hi hj).elim
      · exact hu A ⟨ha, hai, haj⟩
  · intro A hA hSize
    by_cases hLeft : ∃ i ∈ A, i ∈ C.L
    · obtain ⟨i, hi, hiL⟩ := hLeft
      have hAS : A ⊆ C.left := by
        intro j hj
        rcases C.mem_sides j with h | h | hjR
        · exact mem_insert.mpr (Or.inl h)
        · exact mem_insert_of_mem h
        · have hij : i ≠ j := fun h => (Finset.disjoint_left.mp C.disjoint hiL) (h ▸ hjR)
          exact (C.no_cross i hiL j hjR (hA hi hj hij)).elim
      have ha : (sideGraph G C.left).IsClique (A : Set V) :=
        fun _ hi' _ hj' hij => ⟨hA hi' hj' hij, hAS hi', hAS hj'⟩
      obtain ⟨B, hB, hAB⟩ := Dl.clique_cover A ha hSize
      exact ⟨B, mem_union.mpr (Or.inl hB), hAB⟩
    · have hAS : A ⊆ C.right := by
        intro j hj
        rcases C.mem_sides j with h | hjL | h
        · exact mem_insert.mpr (Or.inl h)
        · exact (hLeft ⟨j, hj, hjL⟩).elim
        · exact mem_insert_of_mem h
      have ha : (sideGraph G C.right).IsClique (A : Set V) :=
        fun _ hi _ hj hij => ⟨hA hi hj hij, hAS hi, hAS hj⟩
      obtain ⟨B, hB, hAB⟩ := Dr.clique_cover A ha hSize
      exact ⟨B, mem_union.mpr (Or.inr hB), hAB⟩
  · rw [hSum, Dl.matrix_eq, Dr.matrix_eq, sum_union hDisj]

private theorem complete_decomposition (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hn : 2 ≤ Fintype.card V) (hG : G = ⊤) (hM : M = blockMatrix (univ : Finset V)) :
    BlockDecomposition G M ({univ} : Finset (Finset V)) := by
  subst G
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    simpa only [mem_singleton.mp hB, card_univ] using hn
  · intro B _ i _ j _ hij
    exact hij
  · intro i j _
    refine ⟨univ, by simp, ?_⟩
    rintro B ⟨hB, _, _⟩
    exact mem_singleton.mp hB
  · intro A _ _
    exact ⟨univ, mem_singleton_self _, subset_univ A⟩
  · simpa using hM

/-- The graph family in the equality decomposition is exactly the family of
maximal cliques of size at least two. -/
theorem BlockDecomposition.mem_iff_maximal {M : Matrix V V ℝ} {blocks : Finset (Finset V)}
    (D : BlockDecomposition G M blocks) (B : Finset V) :
    B ∈ blocks ↔ 2 ≤ B.card ∧ G.IsClique (B : Set V) ∧
      ∀ A : Finset V, G.IsClique (A : Set V) → B ⊆ A → A = B := by
  constructor
  · intro hB
    have hSize := D.size B hB
    have hClique := D.clique B hB
    refine ⟨hSize, hClique, ?_⟩
    intro A hA hBA
    obtain ⟨C, hC, hAC⟩ := D.clique_cover A hA (hSize.trans (card_le_card hBA))
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hSize
    obtain ⟨Q, _, hu⟩ := D.edge i j (hClique hi hj hij)
    have hCB : C = B :=
      (hu C ⟨hC, hAC (hBA hi), hAC (hBA hj)⟩).trans (hu B ⟨hB, hi, hj⟩).symm
    exact Subset.antisymm (hCB ▸ hAC) hBA
  · rintro ⟨hSize, hClique, hMax⟩
    obtain ⟨C, hC, hBC⟩ := D.clique_cover B hClique hSize
    exact hMax C (D.clique C hC) hBC ▸ hC

end DNN

end

/-! ### Extensions of zero-sum data from a root clique -/

section

open Finset SimpleGraph Matrix
open scoped BigOperators

namespace DNN

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
attribute [local instance] Classical.propDecidable

/-- The root vertices are fixed. Distinct fibers have only the original root
edges between them. The coefficients extend any zero-sum data on the root. -/
structure RootExtension (G : SimpleGraph V) (blocks : Finset (Finset V))
    (S B : Finset V) (p : V → V) (a : V → ℝ) : Prop where
  lands : ∀ i ∈ S, p i ∈ B
  fixes : ∀ i ∈ B, p i = i
  edge : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → p i ≠ p j → i ∈ B ∧ j ∈ B
  nonzero : ∀ i ∈ S, a i ≠ 0
  one : ∀ i ∈ B, a i = 1
  zero_sum : ∀ x : V → ℝ, (∑ i ∈ B, x i) = 0 →
    ∀ C ∈ blocks, (∑ i ∈ C, a i * x (p i)) = 0

structure ExtensionsOn (G : SimpleGraph V) (blocks : Finset (Finset V))
    (S : Finset V) : Prop where
  anchored : ∀ c ∈ S, ∃ a : V → ℝ, a c = 1 ∧ (∀ i ∈ S, a i ≠ 0) ∧
    ∀ C ∈ blocks, (∑ i ∈ C, a i) = 0
  rooted : ∀ B ∈ blocks, ∃ p a, RootExtension G blocks S B p a

omit [DecidableEq V] in
private theorem extensions_empty : ExtensionsOn G ∅ (univ : Finset V) :=
  ⟨fun _ _ => ⟨fun _ => 1, rfl, by simp, by simp⟩, by simp⟩

private theorem extensions_complete (h : 2 ≤ Fintype.card V) :
    ExtensionsOn G {univ} (univ : Finset V) := by
  refine ⟨?_, ?_⟩
  · intro c _
    let t : ℝ := (Fintype.card V : ℝ) - 1
    have ht : 0 < t := by
      have h' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast h
      dsimp [t]
      linarith
    let a : V → ℝ := fun i => if i = c then 1 else -1 / t
    have ha : a c = 1 := ite_eq_left rfl
    refine ⟨a, ha, fun i _ => ?_, ?_⟩
    · by_cases hi : i = c <;> simp [a, hi, ht.ne']
    · intro B hB
      rw [mem_singleton.mp hB]
      have hsplit := sum_erase_add (s := (univ : Finset V)) a (mem_univ c)
      rw [ha] at hsplit
      have hc : (∑ i ∈ (univ : Finset V).erase c, a i) = -1 := by
        rw [sum_congr rfl (fun i hi => ite_eq_right (mem_erase.mp hi).1)]
        rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ c), card_univ,
          Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one]
        change t * (-1 / t) = -1
        field_simp
      linarith
  · intro B hB
    rw [mem_singleton.mp hB]
    exact ⟨id, fun _ => 1, ⟨by simp, by simp, by simp, by simp, by simp,
      fun x hx C hC => by simpa [mem_singleton.mp hC] using hx⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem liftBlock_eq_map (S : Finset V) (B : Finset (↑S : Set V)) :
    liftBlock S B = B.map (Function.Embedding.subtype (· ∈ (↑S : Set V))) := rfl

private def extend {T : Type*} (S : Finset V) (d : T) (f : (↑S : Set V) → T) :
    V → T := fun i => if hi : i ∈ S then f ⟨i, hi⟩ else d

omit [Fintype V] in
private theorem lift_extensions (S : Finset V) {blocks : Finset (Finset (↑S : Set V))}
    (E : ExtensionsOn (G.induce (↑S : Set V)) blocks univ) :
    ExtensionsOn G (blocks.map (liftBlock S)) S := by
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨a, ha, hn, hz⟩ := E.anchored ⟨c, hc⟩ (mem_univ _)
    refine ⟨extend S 0 a, by simpa [extend, hc] using ha, ?_, ?_⟩
    · intro i hi
      simpa [extend, hi] using hn ⟨i, hi⟩ (mem_univ _)
    · intro C hC
      obtain ⟨D, hD, rfl⟩ := mem_map.mp hC
      simpa [liftBlock, extend, sum_map, Finset.mem_coe] using hz D hD
  · intro B hB
    obtain ⟨B, hB', rfl⟩ := mem_map.mp hB
    obtain ⟨p, a, E⟩ := E.rooted B hB'
    let q : V → V := fun i => extend S i (Subtype.val ∘ p) i
    let b : V → ℝ := extend S 0 a
    have hq (i : (↑S : Set V)) : q i = (p i).val := by
      simp [q, extend, show i.val ∈ S from i.property]
    have hb (i : (↑S : Set V)) : b i = a i := by
      simp [b, extend, show i.val ∈ S from i.property]
    refine ⟨q, b, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      rw [hq (⟨i, hi⟩ : (↑S : Set V))]
      exact mem_map_of_mem _ (E.lands _ (mem_univ _))
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
      change q j.val = j.val
      rw [hq, E.fixes j hj]
    · intro i hi j hj hij hne
      let i' : (↑S : Set V) := ⟨i, hi⟩
      let j' : (↑S : Set V) := ⟨j, hj⟩
      have hne' : p i' ≠ p j' := by
        intro h
        exact hne ((hq i').trans ((congrArg Subtype.val h).trans (hq j').symm))
      obtain ⟨hiB, hjB⟩ := E.edge i' (mem_univ _) j' (mem_univ _) hij hne'
      exact ⟨mem_map_of_mem _ hiB, mem_map_of_mem _ hjB⟩
    · intro i hi
      rw [hb (⟨i, hi⟩ : (↑S : Set V))]
      exact E.nonzero _ (mem_univ _)
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
      change b j.val = 1
      rw [hb, E.one j hj]
    · intro x hx C hC
      obtain ⟨D, hD, rfl⟩ := mem_map.mp hC
      rw [liftBlock_eq_map, sum_map] at hx ⊢
      change (∑ i ∈ B, x i.val) = 0 at hx
      change (∑ i ∈ D, b i.val * x (q i.val)) = 0
      simpa only [hq, hb, Function.comp_apply] using E.zero_sum (x ∘ Subtype.val) hx D hD

private def Cut.swap (C : Cut G) : Cut G where
  c := C.c
  L := C.R
  R := C.L
  left_nonempty := C.right_nonempty
  right_nonempty := C.left_nonempty
  c_not_left := C.c_not_right
  c_not_right := C.c_not_left
  disjoint := C.disjoint.symm
  cover := by simpa only [union_comm C.R C.L] using C.cover
  no_cross i hi j hj h := C.no_cross j hj i hi h.symm
  left_connected := C.right_connected
  right_connected := C.left_connected

private def splice {T : Type*} (S : Finset V) (f g : V → T) (i : V) : T :=
  if i ∈ S then f i else g i

private theorem splice_left {T : Type*} (C : Cut G) {f g : V → T}
    {i : V} (hi : i ∈ C.left) : splice C.left f g i = f i := ite_eq_left hi

private theorem splice_right {T : Type*} (C : Cut G) {f g : V → T}
    (hc : f C.c = g C.c) {i : V} (hi : i ∈ C.right) :
    splice C.left f g i = g i := by
  by_cases hl : i ∈ C.left
  · rw [splice_left C hl, C.overlap hl hi, hc]
  · exact ite_eq_right hl

private theorem Cut.in_sides (C : Cut G) (i : V) : i ∈ C.left ∨ i ∈ C.right := by
  rcases C.mem_sides i with rfl | hi | hi
  · exact Or.inl (mem_insert_self _ _)
  · exact Or.inl (mem_insert_of_mem hi)
  · exact Or.inr (mem_insert_of_mem hi)

private theorem glue_anchor (C : Cut G) {L R : Finset (Finset V)}
    (EL : ExtensionsOn G L C.left) (ER : ExtensionsOn G R C.right)
    (hL : ∀ B ∈ L, B ⊆ C.left) (hR : ∀ B ∈ R, B ⊆ C.right)
    {w : V} (hw : w ∈ C.left) :
    ∃ a : V → ℝ, a w = 1 ∧ (∀ i : V, a i ≠ 0) ∧
      ∀ D ∈ L ∪ R, (∑ i ∈ D, a i) = 0 := by
  have hlc : C.c ∈ C.left := mem_insert_self _ _
  have hrc : C.c ∈ C.right := mem_insert_self _ _
  obtain ⟨l, hl, hln, hlz⟩ := EL.anchored w hw
  obtain ⟨r, hr, hrn, hrz⟩ := ER.anchored C.c hrc
  let a := splice C.left l (fun i => l C.c * r i)
  have al {i} (hi : i ∈ C.left) : a i = l i := splice_left C hi
  have ar {i} (hi : i ∈ C.right) : a i = l C.c * r i :=
    splice_right C (by simp [hr]) hi
  refine ⟨a, (al hw).trans hl, ?_, ?_⟩
  · intro i
    rcases C.in_sides i with hi | hi
    · rw [al hi]
      exact hln i hi
    · rw [ar hi]
      exact mul_ne_zero (hln C.c hlc) (hrn i hi)
  · intro D hD
    rcases mem_union.mp hD with hD | hD
    · rw [sum_congr rfl (fun i hi => al (hL D hD hi)), hlz D hD]
    · rw [sum_congr rfl (fun i hi => ar (hR D hD hi)), ← mul_sum, hrz D hD, mul_zero]

private theorem glue_root (C : Cut G) {L R : Finset (Finset V)}
    (EL : ExtensionsOn G L C.left) (ER : ExtensionsOn G R C.right)
    (hL : ∀ B ∈ L, B ⊆ C.left) (hR : ∀ B ∈ R, B ⊆ C.right)
    {B : Finset V} (hB : B ∈ L) :
    ∃ p a, RootExtension G (L ∪ R) univ B p a := by
  have hlc : C.c ∈ C.left := mem_insert_self _ _
  have hrc : C.c ∈ C.right := mem_insert_self _ _
  obtain ⟨q, l, e⟩ := EL.rooted B hB
  obtain ⟨r, hr, hrn, hrz⟩ := ER.anchored C.c hrc
  let p := splice C.left q (fun _ => q C.c)
  let a := splice C.left l (fun i => l C.c * r i)
  have pl {i} (hi : i ∈ C.left) : p i = q i := splice_left C hi
  have pr {i} (hi : i ∈ C.right) : p i = q C.c := splice_right C (f := q) (g := fun _ => q C.c) rfl hi
  have al {i} (hi : i ∈ C.left) : a i = l i := splice_left C hi
  have ar {i} (hi : i ∈ C.right) : a i = l C.c * r i :=
    splice_right C (by simp [hr]) hi
  refine ⟨p, a, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i _
    rcases C.in_sides i with hi | hi
    · rw [pl hi]
      exact e.lands i hi
    · rw [pr hi]
      exact e.lands C.c hlc
  · intro i hi
    rw [pl (hL B hB hi), e.fixes i hi]
  · intro i _ j _ hij hn
    rcases C.edge_sides hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [pl hi, pl hj] at hn
      exact e.edge i hi j hj hij hn
    · exact (hn ((pr hi).trans (pr hj).symm)).elim
  · intro i _
    rcases C.in_sides i with hi | hi
    · rw [al hi]
      exact e.nonzero i hi
    · rw [ar hi]
      exact mul_ne_zero (e.nonzero C.c hlc) (hrn i hi)
  · intro i hi
    rw [al (hL B hB hi), e.one i hi]
  · intro x hx D hD
    rcases mem_union.mp hD with hD | hD
    · rw [sum_congr rfl (fun i hi => by rw [pl (hL D hD hi), al (hL D hD hi)])]
      exact e.zero_sum x hx D hD
    · have he : ∀ i ∈ D, a i * x (p i) = (l C.c * x (q C.c)) * r i := by
        intro i hi
        rw [pr (hR D hD hi), ar (hR D hD hi)]
        ring
      rw [sum_congr rfl he, ← mul_sum, hrz D hD, mul_zero]

private theorem glue_extensions (C : Cut G) {L R : Finset (Finset V)}
    (EL : ExtensionsOn G L C.left) (ER : ExtensionsOn G R C.right)
    (hL : ∀ B ∈ L, B ⊆ C.left) (hR : ∀ B ∈ R, B ⊆ C.right) :
    ExtensionsOn G (L ∪ R) univ := by
  refine ⟨?_, ?_⟩
  · intro w _
    rcases C.in_sides w with hw | hw
    · obtain ⟨a, ha, hn, hz⟩ := glue_anchor C EL ER hL hR hw
      exact ⟨a, ha, fun i _ => hn i, hz⟩
    · obtain ⟨a, ha, hn, hz⟩ := glue_anchor C.swap ER EL hR hL hw
      exact ⟨a, ha, fun i _ => hn i, by simpa only [union_comm R L] using hz⟩
  · intro B hB
    rcases mem_union.mp hB with hB | hB
    · exact glue_root C EL ER hL hR hB
    · simpa only [union_comm R L] using glue_root C.swap ER EL hR hL hB

theorem budget_eq_card_sub_one_of_tree (hG : G.IsTree) :
    budget G = (Fintype.card V : ℝ) - 1 := by
  have h := hG.card_edgeFinset
  have hr : (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by exact_mod_cast h
  rw [budget_eq]
  linarith

private theorem tree_of_budget_eq_card_sub_one (hG : G.Connected)
    (h : budget G = (Fintype.card V : ℝ) - 1) : G.IsTree := by
  rw [budget_eq] at h
  have hr : (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by linarith
  have hn : G.edgeFinset.card + 1 = Fintype.card V := by exact_mod_cast hr
  refine isTree_iff_connected_and_card.mpr ⟨hG, ?_⟩
  simpa only [Nat.card_eq_fintype_card, edgeFinset_card] using hn

private theorem cut_join_counts (C : Cut G) :
    Fintype.card (↑C.left : Set V) + Fintype.card (↑C.right : Set V) =
      Fintype.card V + 1 := by
  have h := congrArg Finset.card C.cover
  rw [card_insert_of_notMem (by simp [C.c_not_left, C.c_not_right]),
    card_union_of_disjoint C.disjoint, card_univ] at h
  rw [show Fintype.card (↑C.left : Set V) = C.left.card from Fintype.card_coe C.left,
    show Fintype.card (↑C.right : Set V) = C.right.card from Fintype.card_coe C.right,
    Cut.left, Cut.right,
    card_insert_of_notMem C.c_not_left, card_insert_of_notMem C.c_not_right]
  omega

private theorem top_budget_of_two (h : Fintype.card V = 2) :
    budget (⊤ : SimpleGraph V) = (Fintype.card V : ℝ) - 1 := by
  rw [budget_eq, card_edgeFinset_top_eq_card_choose_two, h]
  norm_num

/-- The normalized clique family has rooted extensions. If every block is an
edge, its decomposition has the budget of a tree. -/
theorem normalized_decomposition_with_extensions (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : Gram.SupportedDNN G M) (hG : G.Connected) (he : Normalized G M hM) :
    ∃ blocks : Finset (Finset V), BlockDecomposition G M blocks ∧
      ExtensionsOn G blocks univ ∧
      ((∀ B ∈ blocks, B.card = 2) → G.IsTree) := by
  suffices h : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      Fintype.card W = n → ∀ (H : SimpleGraph W) (X : Matrix W W ℝ)
      (hX : Gram.SupportedDNN H X), H.Connected → Normalized H X hX →
      ∃ blocks : Finset (Finset W), BlockDecomposition H X blocks ∧
        ExtensionsOn H blocks univ ∧ ((∀ B ∈ blocks, B.card = 2) → H.IsTree) from
    h (Fintype.card V) V rfl G M hM hG he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ hW H X hX hH hN
    have hne := hH.nonempty
    have hn : 0 < Fintype.card W := Fintype.card_pos
    by_cases hn₁ : Fintype.card W = 1
    · have hs := Fintype.card_le_one_iff_subsingleton.mp hn₁.le
      have hbot : H = ⊥ := by
        ext i j
        exact ⟨fun h => (h.ne (hs.elim i j)).elim, False.elim⟩
      refine ⟨∅, ⟨by simp, by simp, fun i j hij => (hij.ne (hs.elim i j)).elim,
        fun B _ hb => (by have h := card_le_univ B; omega), ?_⟩, extensions_empty, ?_⟩
      · simpa using singleton_normalized H X hX hn₁ hN
      · exact fun _ => ⟨hH, hbot ▸ SimpleGraph.isAcyclic_bot⟩
    have complete_case (hn₂ : 2 ≤ Fintype.card W)
        (hTop : H = ⊤) (hX' : X = blockMatrix (univ : Finset W)) :
        ∃ blocks : Finset (Finset W), BlockDecomposition H X blocks ∧
          ExtensionsOn H blocks univ ∧ ((∀ B ∈ blocks, B.card = 2) → H.IsTree) := by
      refine ⟨{univ}, complete_decomposition H X hn₂ hTop hX', extensions_complete hn₂, ?_⟩
      intro small
      have hTwo : Fintype.card W = 2 := by simpa using small univ (mem_singleton_self _)
      exact tree_of_budget_eq_card_sub_one hH (hTop ▸ top_budget_of_two hTwo)
    by_cases hn₂ : Fintype.card W = 2
    · obtain ⟨ht, hb⟩ := two_normalized H X hX hH hn₂ hN
      exact complete_case hn₂.ge ht hb
    by_cases hall : ∀ v, (deleted H v).Connected
    · obtain ⟨ht, hb⟩ := leaf_normalized H X hX hH (by omega) hall hN
      exact complete_case (by omega) ht hb
    · obtain ⟨v, hv⟩ := not_forall.mp hall
      obtain ⟨C⟩ := cut_of_not_connected_deleted hH (by omega) v hv
      obtain ⟨D⟩ := C.exists_split X hX
      obtain ⟨hNl, hNr⟩ := D.normalized (supported_bound _ _ _ C.left_connected)
        (supported_bound _ _ _ C.right_connected) hN
      have hl : Fintype.card (↑C.left : Set W) < n := by
        rw [show Fintype.card (↑C.left : Set W) = C.left.card from Fintype.card_coe C.left, ← hW]
        exact C.card_lt.1
      have hr : Fintype.card (↑C.right : Set W) < n := by
        rw [show Fintype.card (↑C.right : Set W) = C.right.card from Fintype.card_coe C.right, ← hW]
        exact C.card_lt.2
      obtain ⟨L, hL, EL, tl⟩ := ih _ hl _ rfl _ _ _ C.left_connected hNl
      obtain ⟨R, hR, ER, tr⟩ := ih _ hr _ rfl _ _ _ C.right_connected hNr
      obtain ⟨DL, hDL⟩ := lift_decomposition C.left D.N D.N_supported.symm D.N_rows L hL
      obtain ⟨DR, hDR⟩ := lift_decomposition C.right D.P D.P_supported.symm D.P_rows R hR
      refine ⟨_, C.merge_decompositions D.sum_eq DL DR hDL hDR,
        glue_extensions C (lift_extensions C.left EL) (lift_extensions C.right ER) hDL hDR, ?_⟩
      intro small
      have tl' := tl fun B hB => by
        simpa only [liftBlock_eq_map, card_map] using
          small (liftBlock C.left B) (mem_union_left _ (mem_map_of_mem _ hB))
      have tr' := tr fun B hB => by
        simpa only [liftBlock_eq_map, card_map] using
          small (liftBlock C.right B) (mem_union_right _ (mem_map_of_mem _ hB))
      have hc := cut_join_counts C
      have hc' : (Fintype.card (↑C.left : Set W) : ℝ) +
          (Fintype.card (↑C.right : Set W) : ℝ) = (Fintype.card W : ℝ) + 1 := by exact_mod_cast hc
      apply tree_of_budget_eq_card_sub_one hH
      linarith only [budget_eq_card_sub_one_of_tree tl', budget_eq_card_sub_one_of_tree tr',
        C.budget_add, hc']

end DNN

end

end D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy
