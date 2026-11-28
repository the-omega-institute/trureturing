/- GID: D5/S3/Combinatorics/SignedGraphSpectral/DoublyNonnegativeEdgeMass
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedGraphSpectral/DoublyNonnegativeEdgeMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Gram cut splitting and edge-mass bounds for doubly nonnegative matrices. -/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
Gram cut splitting and edge-mass bounds for doubly nonnegative matrices.
The support and the normalized equality argument are those used to settle
Hu–Han Problem 6.1, with the clique decomposition of Hu–Liu–Wang, Proposition 4.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy

/-! ### Gram splitting at a cut vertex -/

section

open Finset Matrix
open scoped Matrix MatrixOrder InnerProductSpace BigOperators

namespace Gram

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- The subgraph induced on `S`, viewed on the original vertex type. -/
def sideGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := h.1.ne rfl

/-- Total entry mass, as in Hu–Han (3.2). -/
def mass (M : Matrix V V ℝ) : ℝ :=
  ∑ u : V, ∑ v : V, M u v

/-- Lift symmetric entries to an unordered pair. -/
def edgeEntry (M : Matrix V V ℝ) (hM : M.IsSymm) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => M u v, fun u v => hM.apply v u⟩

/-- Each unordered edge contributes the square root of its matrix entry. -/
def edgeMass (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : M.IsSymm) : ℝ :=
  ∑ e ∈ G.edgeFinset, Real.sqrt (edgeEntry M hM e)

/-- A real DNN matrix supported on a graph, with the diagonal unrestricted by the graph. -/
structure SupportedDNN (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop where
  psd : M.PosSemidef
  nonneg : ∀ u v, 0 ≤ M u v
  zero_of_nonedge : ∀ {u v}, u ≠ v → ¬ G.Adj u v → M u v = 0

omit [Fintype V] [DecidableEq V] in
theorem SupportedDNN.symm {G : SimpleGraph V} {M : Matrix V V ℝ}
    (hM : SupportedDNN G M) : M.IsSymm := hM.psd.isHermitian.isSymm

private lemma gram_factor {M : Matrix V V ℝ} (hM : M.PosSemidef) :
    ∃ z : V → EuclideanSpace ℝ V, M = gram ℝ z := by
  obtain ⟨Q, hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  refine ⟨fun v => WithLp.toLp 2 (fun i => Q i v), ?_⟩
  rw [hQ]
  ext u v
  simp only [gram_apply, EuclideanSpace.inner_toLp_toLp]
  change (Qᴴ * Q) u v = (fun i => Q i v) ⬝ᵥ star (fun i => Q i u)
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply, dotProduct]
  exact sum_congr rfl fun i _ => by simp [mul_comm]

private lemma edgeMass_side (G : SimpleGraph V) (S : Finset V)
    (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hRow : ∀ u, u ∉ S → ∀ v, M u v = 0) :
    edgeMass (sideGraph G S) M hM = edgeMass G M hM := by
  have hSub : sideGraph G S ≤ G := fun _ _ h => h.1
  unfold edgeMass
  apply sum_subset (SimpleGraph.edgeFinset_mono hSub)
  intro e he hnot
  induction e using Sym2.inductionOn with
  | hf u v =>
    have ha : G.Adj u v := (SimpleGraph.mem_edgeSet (G := G)).mp (SimpleGraph.mem_edgeFinset.mp he)
    have hOut : u ∉ S ∨ v ∉ S := by
      by_contra! h
      exact hnot (SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (G := sideGraph G S)).mpr ⟨ha, h⟩))
    change Real.sqrt (M u v) = 0
    rcases hOut with hu | hv
    · rw [hRow u hu v, Real.sqrt_zero]
    · rw [← hM.apply u v, hRow v hv u, Real.sqrt_zero]

omit [Fintype V] in
private lemma dnn_of_split {G : SimpleGraph V} {M N P : Matrix V V ℝ}
    {S T : Finset V} {c : V} (hM : SupportedDNN G M) (hSum : M = N + P)
    (hN : N.PosSemidef) (hNRow : ∀ u, u ∉ S → ∀ v, N u v = 0)
    (hP : P.IsSymm) (hPRow : ∀ u, u ∉ T → ∀ v, P u v = 0)
    (hOverlap : ∀ i, i ∈ S → i ∈ T → i = c) :
    SupportedDNN (sideGraph G S) N := by
  have hEntry {u v : V} (huv : u ≠ v) (hu : u ∈ S) (hv : v ∈ S) : N u v = M u v := by
    have hp : P u v = 0 := by
      by_cases h : u ∈ T
      · have hvT : v ∉ T := fun hvT => huv ((hOverlap u hu h).trans (hOverlap v hv hvT).symm)
        exact (hP.apply u v).symm.trans (hPRow v hvT u)
      · exact hPRow u h v
    have hEntry := congrFun (congrFun hSum u) v
    simpa [Matrix.add_apply, hp] using hEntry.symm
  refine ⟨hN, ?_, ?_⟩
  · intro u v
    by_cases huv : u = v
    · subst v
      exact hN.diag_nonneg
    · by_cases hu : u ∈ S
      · by_cases hv : v ∈ S
        · rw [hEntry huv hu hv]
          exact hM.nonneg u v
        · rw [← hN.isHermitian.isSymm.apply u v, hNRow v hv u]
      · rw [hNRow u hu v]
  · intro u v huv hnonedge
    by_cases hu : u ∈ S
    · by_cases hv : v ∈ S
      · rw [hEntry huv hu hv]
        exact hM.zero_of_nonedge huv (fun h => hnonedge ⟨h, hu, hv⟩)
      · rw [← hN.isHermitian.isSymm.apply u v, hNRow v hv u]
    · exact hNRow u hu v

/-- Gram split across a cut with separator `c`. The two side matrices occupy
the original vertex set with zeros off their respective sides. This gives the
embedded matrix sum, entry mass additivity, and additivity over unordered edges. -/
theorem gram_cut_split (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (c : V) (L R : Finset V)
    (hDisj : Disjoint L R) (hCover : ∀ i : V, i = c ∨ i ∈ L ∨ i ∈ R)
    (hCross : ∀ u ∈ L, ∀ v ∈ R, ¬ G.Adj u v) :
    ∃ (N P : Matrix V V ℝ)
      (hN : SupportedDNN (sideGraph G (insert c L)) N)
      (hP : SupportedDNN (sideGraph G (insert c R)) P),
      (∀ u, u ∉ insert c L → ∀ v, N u v = 0) ∧
      (∀ u, u ∉ insert c R → ∀ v, P u v = 0) ∧
      M = N + P ∧
      mass M = mass N + mass P ∧
      edgeMass G M hM.symm =
        edgeMass (sideGraph G (insert c L)) N hN.symm +
        edgeMass (sideGraph G (insert c R)) P hP.symm := by
  classical
  obtain ⟨z, hz⟩ := gram_factor hM.psd
  let W := Submodule.span ℝ (z '' (R : Set V))
  let g (i : V) := W.starProjection (z i)
  let f (i : V) := z i - g i
  have hRmem {i : V} (hi : i ∈ R) : z i ∈ W := Submodule.subset_span ⟨i, hi, rfl⟩
  have hfR {i : V} (hi : i ∈ R) : f i = 0 := by
    simp [f, g, Submodule.starProjection_eq_self_iff.mpr (hRmem hi)]
  have hgL {i : V} (hi : i ∈ L) : g i = 0 := by
    apply (W.starProjection_apply_eq_zero_iff).mpr
    apply (W.mem_orthogonal' (z i)).mpr
    intro y hy
    have hSpan : W ≤ (Submodule.span ℝ {z i})ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      have hne : i ≠ j := fun hij => (disjoint_left.mp hDisj hi) (hij ▸ hj)
      simpa [hz] using hM.zero_of_nonedge hne (hCross i hi j hj)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hSpan hy)
  have hOrth (i j : V) : ⟪f i, g j⟫_ℝ = 0 :=
    W.starProjection_inner_eq_zero _ _ (W.starProjection_apply_mem _)
  have hDecomp (i : V) : z i = f i + g i := (sub_add_cancel (z i) (g i)).symm
  let N := gram ℝ f
  let P := gram ℝ g
  have hSum : M = N + P := by
    rw [hz]
    ext u v
    have hOrth' : ⟪g u, f v⟫_ℝ = 0 := (real_inner_comm (f v) (g u)).trans (hOrth v u)
    change ⟪z u, z v⟫_ℝ = ⟪f u, f v⟫_ℝ + ⟪g u, g v⟫_ℝ
    conv_lhs => rw [hDecomp u, hDecomp v]
    simp [inner_add_left, inner_add_right, hOrth, hOrth']
  have hNRow (u : V) (hu : u ∉ insert c L) (v : V) : N u v = 0 := by
    have h : u ∈ R := (hCover u).resolve_left (fun e => hu (mem_insert.mpr (Or.inl e)))
      |>.resolve_left (fun h => hu (mem_insert_of_mem h))
    simp [N, hfR h]
  have hPRow (u : V) (hu : u ∉ insert c R) (v : V) : P u v = 0 := by
    have h : u ∈ L := (hCover u).resolve_left (fun e => hu (mem_insert.mpr (Or.inl e)))
      |>.resolve_right (fun h => hu (mem_insert_of_mem h))
    simp [P, hgL h]
  have hOverlap (i : V) (hi : i ∈ insert c L) (hj : i ∈ insert c R) : i = c := by
    rcases mem_insert.mp hi with h | h
    · exact h
    · exact (mem_insert.mp hj).resolve_right (disjoint_left.mp hDisj h)
  have hN := dnn_of_split hM hSum (posSemidef_gram ℝ f) hNRow
    (isHermitian_gram ℝ g).isSymm hPRow hOverlap
  have hP := dnn_of_split hM (hSum.trans (add_comm N P)) (posSemidef_gram ℝ g) hPRow
    (isHermitian_gram ℝ f).isSymm hNRow (fun i hi hj => hOverlap i hj hi)
  refine ⟨N, P, hN, hP, hNRow, hPRow, hSum, ?_, ?_⟩
  · simp [mass, hSum, Matrix.add_apply, sum_add_distrib]
  · rw [edgeMass_side G _ N hN.symm hNRow, edgeMass_side G _ P hP.symm hPRow]
    unfold edgeMass
    rw [← sum_add_distrib]
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := (SimpleGraph.mem_edgeSet (G := G)).mp (SimpleGraph.mem_edgeFinset.mp he)
      have hOne : N u v = 0 ∨ P u v = 0 := by
        by_cases huL : u ∈ insert c L
        · by_cases hvL : v ∈ insert c L
          · by_cases huR : u ∈ insert c R
            · have hvR : v ∉ insert c R :=
                fun h => huv.ne ((hOverlap u huL huR).trans (hOverlap v hvL h).symm)
              exact Or.inr ((hP.symm.apply u v).symm.trans (hPRow v hvR u))
            · exact Or.inr (hPRow u huR v)
          · exact Or.inl ((hN.symm.apply u v).symm.trans (hNRow v hvL u))
        · exact Or.inl (hNRow u huL v)
      have hEq := congrFun (congrFun hSum u) v
      change M u v = N u v + P u v at hEq
      change Real.sqrt (M u v) = Real.sqrt (N u v) + Real.sqrt (P u v)
      rcases hOne with hzero | hzero <;> simp [hEq, hzero]

end Gram

end

/-! ### Edge mass and the scalar inequality across a cut -/

section

open Finset Matrix SimpleGraph
open scoped Matrix BigOperators

namespace DNN

open Gram

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def budget (G : SimpleGraph V) : ℝ :=
  2 * (Nat.card G.edgeSet : ℝ) - (Fintype.card V : ℝ) + 1

theorem budget_eq (G : SimpleGraph V) [Fintype G.edgeSet] :
    budget G = 2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) + 1 := by
  rw [budget, Nat.card_eq_fintype_card, ← edgeFinset_card]

theorem edgeMass_eq_sum (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : M.IsSymm) :
    edgeMass G M hM = ∑ e ∈ G.edgeFinset, Real.sqrt (edgeEntry M hM e) := rfl

theorem edgeMass_nonneg (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : M.IsSymm) :
    0 ≤ edgeMass G M hM := by
  rw [edgeMass_eq_sum]
  exact sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem mass_nonneg {M : Matrix V V ℝ} (hM : ∀ i j, 0 ≤ M i j) : 0 ≤ mass M :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => hM i j

theorem sum_darts (G : SimpleGraph V) (f : Sym2 V → ℝ) :
    (∑ d : G.Dart, f d.edge) = 2 * ∑ e ∈ G.edgeFinset, f e := by
  classical
  have hm : ∀ d ∈ (univ : Finset G.Dart), d.edge ∈ G.edgeFinset :=
    fun d _ => mem_edgeFinset.mpr d.edge_mem
  rw [← sum_fiberwise_of_maps_to' hm f, Finset.mul_sum]
  exact sum_congr rfl fun e he => by
    rw [sum_const, G.dart_edge_fiber_card e (mem_edgeFinset.mp he), two_nsmul, two_mul]

theorem sum_adj (G : SimpleGraph V) (f : V → V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then f i j else 0) =
      ∑ d : G.Dart, f d.fst d.snd := by
  classical
  let e : G.Dart ≃ {p : V × V // G.Adj p.1 p.2} :=
    { toFun := fun d => ⟨d.toProd, d.adj⟩
      invFun := fun p => ⟨p.val, p.property⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [← Fintype.sum_prod_type (fun p : V × V => if G.Adj p.1 p.2 then f p.1 p.2 else 0)]
  rw [← sum_filter, sum_subtype _ (fun p => mem_filter_univ p)]
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

private theorem mass_trace_edges {G : SimpleGraph V} {M : Matrix V V ℝ}
    (hM : SupportedDNN G M) :
    mass M = M.trace + 2 * ∑ e ∈ G.edgeFinset, edgeEntry M hM.symm e := by
  classical
  have hrow (i : V) : (∑ j : V, M i j) =
      M i i + ∑ j : V, if G.Adj i j then M i j else 0 := by
    rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase
      (f := fun j => if G.Adj i j then M i j else 0) _ (mem_univ i)]
    simp only [G.irrefl, if_false, zero_add]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    by_cases ha : G.Adj i j
    · simp [ha]
    · rw [if_neg ha, hM.zero_of_nonedge (Ne.symm (ne_of_mem_erase hj)) ha]
  simp only [mass, hrow, sum_add_distrib, trace, diag_apply]
  rw [sum_adj G (fun i j => M i j)]
  exact congrArg (fun x => (∑ i : V, M i i) + x) (sum_darts G (edgeEntry M hM.symm))

private theorem edge_flat {G : SimpleGraph V} {M : Matrix V V ℝ} (hM : SupportedDNN G M) :
    (2 * edgeMass G M hM.symm) ^ 2 ≤
      2 * (G.edgeFinset.card : ℝ) * (mass M - M.trace) := by
  rw [edgeMass_eq_sum]
  have h := sq_sum_le_card_mul_sum_sq (s := G.edgeFinset)
    (f := fun e => Real.sqrt (edgeEntry M hM.symm e))
  have hs (e : Sym2 V) : (Real.sqrt (edgeEntry M hM.symm e)) ^ 2 = edgeEntry M hM.symm e :=
    Sym2.inductionOn e fun i j => Real.sq_sqrt (hM.nonneg i j)
  simp_rw [hs] at h
  rw [mass_trace_edges hM]
  nlinarith only [h]

private def pairDeficit (M : Matrix V V ℝ) (i j : V) : ℝ := M i i + M j j - 2 * M i j

private theorem pair_quad {M : Matrix V V ℝ} (hM : M.IsSymm) (i j : V) :
    let v := Pi.single i (1 : ℝ) - Pi.single j 1
    star v ⬝ᵥ (M *ᵥ v) = pairDeficit M i j := by
  dsimp only
  simp only [star_trivial, mulVec_sub, mulVec_single_one, sub_dotProduct, dotProduct_sub,
    single_dotProduct, one_mul, Function.update_self, pairDeficit, col_apply]
  rw [hM.apply i j]
  ring

private theorem sum_pairDeficit (M : Matrix V V ℝ) :
    (∑ i : V, ∑ j : V, pairDeficit M i j) =
      2 * (Fintype.card V : ℝ) * M.trace - 2 * mass M := by
  simp only [pairDeficit, trace, diag_apply, mass, sum_sub_distrib, sum_add_distrib,
    sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  ring

private theorem mass_le_card_trace {M : Matrix V V ℝ} (hM : M.PosSemidef) :
    mass M ≤ (Fintype.card V : ℝ) * M.trace := by
  have hnon (i j : V) : 0 ≤ pairDeficit M i j := by
    rw [← pair_quad hM.isHermitian.isSymm i j]
    simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) - Pi.single j 1)
  have h := sum_nonneg (s := (univ : Finset V)) fun i _ =>
    sum_nonneg (s := (univ : Finset V)) fun j _ => hnon i j
  rw [sum_pairDeficit] at h
  linarith

private theorem constant_of_mass_eq_card_trace {M : Matrix V V ℝ} (hM : M.PosSemidef)
    (hT : mass M = (Fintype.card V : ℝ) * M.trace) :
    ∀ i j, M i j = mass M / (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hnon (i j : V) : 0 ≤ pairDeficit M i j := by
    rw [← pair_quad hM.isHermitian.isSymm i j]
    simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) - Pi.single j 1)
  have hsum : (∑ i : V, ∑ j : V, pairDeficit M i j) = 0 := by
    rw [sum_pairDeficit, hT]
    ring
  have hz (i j : V) : pairDeficit M i j = 0 := by
    have hi := (sum_eq_zero_iff_of_nonneg (fun k _ =>
      sum_nonneg (fun l _ => hnon k l))).mp hsum i (mem_univ i)
    exact (sum_eq_zero_iff_of_nonneg (fun l _ => hnon i l)).mp hi j (mem_univ j)
  have hc (i j k : V) : M k i = M k j := by
    have hq := (pair_quad hM.isHermitian.isSymm i j).trans (hz i j)
    have hv := congrFun (hM.dotProduct_mulVec_zero_iff.mp hq) k
    simpa [mulVec_sub, mulVec_single_one, sub_eq_zero, col_apply] using hv
  intro i j
  have hC : ∀ a b, M a b = M i j := fun a b =>
    (hc b j a).trans ((hM.isHermitian.isSymm.apply j a).trans
      ((hc a i j).trans (hM.isHermitian.isSymm.apply i j)))
  have hT' : mass M = (Fintype.card V : ℝ) ^ 2 * M i j := by
    simp only [mass, hC, sum_const, card_univ, nsmul_eq_mul]
    ring
  haveI : Nonempty V := ⟨i⟩
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
  rw [hT', mul_comm]

theorem budget_nonneg {G : SimpleGraph V} (hG : G.Connected) : 0 ≤ budget G := by
  haveI : Nonempty V := hG.nonempty
  have h := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h
  have hc : (Fintype.card V : ℝ) ≤ (G.edgeFinset.card : ℝ) + 1 := by exact_mod_cast h
  have hm : (0 : ℝ) ≤ G.edgeFinset.card := by positivity
  rw [budget_eq]
  linarith

private theorem budget_pos {G : SimpleGraph V} (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < budget G := by
  have h := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h
  have hc : (Fintype.card V : ℝ) ≤ (G.edgeFinset.card : ℝ) + 1 := by exact_mod_cast h
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  rw [budget_eq]
  linarith

theorem budget_top (hn : 1 ≤ Fintype.card V) :
    budget (⊤ : SimpleGraph V) = ((Fintype.card V : ℝ) - 1) ^ 2 := by
  have h := (⊤ : SimpleGraph V).sum_degrees_eq_twice_card_edges
  change (∑ v : V, (completeGraph V).degree v) = _ at h
  simp only [complete_graph_degree, sum_const, card_univ, nsmul_eq_mul] at h
  have hc : (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) =
      2 * (((⊤ : SimpleGraph V).edgeFinset.card) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_sub hn] at hc
  rw [budget_eq, ← hc]
  push_cast
  ring

private theorem budget_le_top (G : SimpleGraph V) : budget G ≤ budget (⊤ : SimpleGraph V) := by
  have h := card_le_card (edgeFinset_mono (show G ≤ ⊤ from le_top))
  have hc : (G.edgeFinset.card : ℝ) ≤ ((⊤ : SimpleGraph V).edgeFinset.card : ℝ) :=
    by exact_mod_cast h
  rw [budget_eq, budget_eq]
  gcongr

private theorem top_of_budget_eq (G : SimpleGraph V) (h : budget G = budget (⊤ : SimpleGraph V)) :
    G = ⊤ := by
  have hh : (Nat.card G.edgeSet : ℝ) = (Nat.card (⊤ : SimpleGraph V).edgeSet : ℝ) := by
    unfold budget at h
    linarith only [h]
  have hc : (G.edgeFinset.card : ℝ) = ((⊤ : SimpleGraph V).edgeFinset.card : ℝ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, ← edgeFinset_card] at hh
    exact hh
  have he := eq_of_subset_of_card_le (edgeFinset_mono (show G ≤ ⊤ from le_top))
    (show (⊤ : SimpleGraph V).edgeFinset.card ≤ G.edgeFinset.card by exact_mod_cast hc.ge)
  ext i j
  have hm : s(i,j) ∈ G.edgeFinset ↔ s(i,j) ∈ (⊤ : SimpleGraph V).edgeFinset := by rw [he]
  simpa only [mem_edgeFinset, mem_edgeSet] using hm

/-- The two-term scalar inequality used after orthogonal Gram splitting. -/
theorem cut_scalar_bound {q₁ q₂ t₁ t₂ s₁ s₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h₁ : (2 * s₁) ^ 2 ≤ q₁ * t₁) (h₂ : (2 * s₂) ^ 2 ≤ q₂ * t₂)
    (hs : 0 ≤ s₁ + s₂) :
    (2 * (s₁ + s₂)) ^ 2 ≤ (q₁ + q₂) * (t₁ + t₂) := by
  have h₁' : 2 * s₁ ≤ Real.sqrt q₁ * Real.sqrt t₁ := by
    rw [← Real.sqrt_mul hq₁]
    exact Real.le_sqrt_of_sq_le h₁
  have h₂' : 2 * s₂ ≤ Real.sqrt q₂ * Real.sqrt t₂ := by
    rw [← Real.sqrt_mul hq₂]
    exact Real.le_sqrt_of_sq_le h₂
  have hsum : 2 * (s₁ + s₂) ≤ Real.sqrt q₁ * Real.sqrt t₁ +
      Real.sqrt q₂ * Real.sqrt t₂ := by linarith
  have hsq := (sq_le_sq₀ (by linarith : 0 ≤ 2 * (s₁ + s₂))
    (le_trans (by linarith : 0 ≤ 2 * (s₁ + s₂)) hsum)).mpr hsum
  have hx₁ := Real.sq_sqrt hq₁
  have hx₂ := Real.sq_sqrt hq₂
  have hy₁ := Real.sq_sqrt ht₁
  have hy₂ := Real.sq_sqrt ht₂
  calc
    _ ≤ (Real.sqrt q₁ * Real.sqrt t₁ + Real.sqrt q₂ * Real.sqrt t₂) ^ 2 := hsq
    _ ≤ ((Real.sqrt q₁) ^ 2 + (Real.sqrt q₂) ^ 2) *
        ((Real.sqrt t₁) ^ 2 + (Real.sqrt t₂) ^ 2) := by
      nlinarith only [sq_nonneg (Real.sqrt q₁ * Real.sqrt t₂ - Real.sqrt q₂ * Real.sqrt t₁)]
    _ = _ := by rw [hx₁, hx₂, hy₁, hy₂]

/-- Equality and normalization of the two additive totals propagate to each side. -/
theorem cut_scalar_normalized {q₁ q₂ t₁ t₂ s₁ s₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h₁ : (2 * s₁) ^ 2 ≤ q₁ * t₁) (h₂ : (2 * s₂) ^ 2 ≤ q₂ * t₂)
    (ht : t₁ + t₂ = q₁ + q₂) (hs : 2 * (s₁ + s₂) = q₁ + q₂) :
    t₁ = q₁ ∧ 2 * s₁ = q₁ ∧ t₂ = q₂ ∧ 2 * s₂ = q₂ := by
  have hamgm {q t s : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t)
      (h : (2 * s) ^ 2 ≤ q * t) : 4 * s ≤ q + t := by
    by_contra! hn
    have hp : (q + t) ^ 2 < (4 * s) ^ 2 :=
      (sq_lt_sq₀ (add_nonneg hq ht) (le_of_lt (lt_of_le_of_lt (add_nonneg hq ht) hn))).mpr hn
    nlinarith only [hp, h, sq_nonneg (q - t)]
  have h₁' := hamgm hq₁ ht₁ h₁
  have h₂' := hamgm hq₂ ht₂ h₂
  have e₁ : 4 * s₁ = q₁ + t₁ := by linarith
  have e₂ : 4 * s₂ = q₂ + t₂ := by linarith
  have hmass {q t s : ℝ} (e : 4 * s = q + t)
      (h : (2 * s) ^ 2 ≤ q * t) : t = q := by
    have he := congrArg (fun x : ℝ => x ^ 2) e
    have hz : (q - t) ^ 2 ≤ 0 := by nlinarith only [he, h]
    have hz' : (q - t) ^ 2 = 0 := le_antisymm hz (sq_nonneg _)
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hz')).symm
  have ht₁' := hmass e₁ h₁
  have ht₂' := hmass e₂ h₂
  exact ⟨ht₁', by linarith, ht₂', by linarith⟩

end DNN

end

/-! ### Vertex deletion identities -/

section

open Finset Matrix SimpleGraph
open scoped Matrix BigOperators

namespace DNN

open Gram

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def principal (M : Matrix V V ℝ) (S : Set V) : Matrix S S ℝ :=
  M.submatrix Subtype.val Subtype.val

def deleted (G : SimpleGraph V) (v : V) : SimpleGraph (({v}ᶜ : Set V)) :=
  G.induce ({v}ᶜ : Set V)

theorem supported_principal {G : SimpleGraph V} {M : Matrix V V ℝ}
    (hM : SupportedDNN G M) (S : Set V) :
    SupportedDNN (G.induce S) (principal M S) where
  psd := hM.psd.submatrix _
  nonneg i j := hM.nonneg i j
  zero_of_nonedge hne h := hM.zero_of_nonedge (fun hEq => hne (Subtype.ext hEq)) h

theorem card_deleted (v : V) : Fintype.card (({v}ᶜ : Set V)) = Fintype.card V - 1 := by
  classical
  exact (Fintype.card_subtype_compl (fun i => i ∈ ({v} : Set V))).trans (by simp)

private theorem sum_avoid {A : Type*} (s : Finset A) (bad : A → Finset V) (f : A → ℝ) :
    (∑ v : V, ∑ a ∈ s.filter (fun a => v ∉ bad a), f a) =
      ∑ a ∈ s, ((Fintype.card V : ℝ) - (bad a).card) * f a := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  congr 1
  have hf : univ.filter (fun v : V => v ∉ bad a) = univ \ bad a := by
    ext v
    simp
  rw [hf, card_sdiff_of_subset (subset_univ _), card_univ,
    Nat.cast_sub (card_le_univ _)]

private theorem map_edges_deleted (G : SimpleGraph V) (v : V) :
    (deleted G v).edgeFinset.map (Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V))).sym2Map =
      G.edgeFinset.filter (fun e => v ∉ e.toFinset) := by
  classical
  have hm := map_edgeFinset_induce (s := ({v}ᶜ : Set V)) (G := G)
  refine hm.trans ?_
  ext e
  induction e using Sym2.inductionOn with
  | hf i j =>
    simp [Finset.mem_sym2_iff, Sym2.mem_toFinset, eq_comm, not_or]
    aesop

private theorem edgeMass_deleted (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : SupportedDNN G M) (v : V) :
    edgeMass (deleted G v) (principal M ({v}ᶜ : Set V))
        (supported_principal hM _).symm =
      ∑ e ∈ G.edgeFinset.filter (fun e => v ∉ e.toFinset),
        Real.sqrt (edgeEntry M hM.symm e) := by
  rw [edgeMass_eq_sum, ← map_edges_deleted, sum_map]
  apply sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | hf i j => rfl

private theorem sum_edgeMass_deleted (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M) :
    (∑ v : V, edgeMass (deleted G v) (principal M ({v}ᶜ : Set V))
        (supported_principal hM _).symm) =
      ((Fintype.card V : ℝ) - 2) * edgeMass G M hM.symm := by
  simp_rw [edgeMass_deleted G M hM]
  rw [sum_avoid, edgeMass_eq_sum, Finset.mul_sum]
  exact sum_congr rfl fun e he => by
    rw [G.card_toFinset_mem_edgeFinset ⟨e, he⟩]
    norm_num

private theorem sum_budget_deleted (G : SimpleGraph V) (hn : 1 ≤ Fintype.card V) :
    (∑ v : V, budget (deleted G v)) =
      ((Fintype.card V : ℝ) - 2) * (budget G - 1) := by
  classical
  have hcount (v : V) : (deleted G v).edgeFinset.card =
      (G.edgeFinset.filter (fun e => v ∉ e.toFinset)).card := by
    rw [← map_edges_deleted, card_map]
  have hsum : (∑ v : V, ((deleted G v).edgeFinset.card : ℝ)) =
      ((Fintype.card V : ℝ) - 2) * (G.edgeFinset.card : ℝ) := by
    have hones (s : Finset (Sym2 V)) : (s.card : ℝ) = ∑ _ ∈ s, (1 : ℝ) := by simp
    simp_rw [hcount, hones]
    rw [sum_avoid, Finset.mul_sum]
    exact sum_congr rfl fun e he => by
      rw [G.card_toFinset_mem_edgeFinset ⟨e, he⟩]
      norm_num
  simp only [budget_eq, card_deleted, Nat.cast_sub hn, Nat.cast_one,
    sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [hsum]
  ring

theorem mass_principal_filter (M : Matrix V V ℝ) (S : Set V) [DecidablePred (· ∈ S)] :
    mass (principal M S) = ∑ i : V, ∑ j : V, if i ∈ S ∧ j ∈ S then M i j else 0 := by
  classical
  simp only [mass, principal, submatrix_apply]
  rw [← Fintype.sum_prod_type (fun p : S × S => M p.1.val p.2.val)]
  let e : S × S ≃ {p : V × V // p.1 ∈ S ∧ p.2 ∈ S} :=
    { toFun := fun p => ⟨(p.1.val, p.2.val), p.1.property, p.2.property⟩
      invFun := fun p => (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type (fun p : V × V => if p.1 ∈ S ∧ p.2 ∈ S then M p.1 p.2 else 0)]
  rw [← sum_filter, sum_subtype _ (fun p => mem_filter_univ p)]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

private theorem sum_mass_deleted (M : Matrix V V ℝ) :
    (∑ v : V, mass (principal M ({v}ᶜ : Set V))) =
      ((Fintype.card V : ℝ) - 2) * mass M + M.trace := by
  classical
  have hrewrite (v : V) : mass (principal M ({v}ᶜ : Set V)) =
      ∑ p ∈ (univ : Finset (V × V)).filter (fun p => v ∉ ({p.1,p.2} : Finset V)),
        M p.1 p.2 := by
    refine (mass_principal_filter M ({v}ᶜ : Set V)).trans ?_
    rw [sum_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    have hc : i ∈ ({v}ᶜ : Set V) ∧ j ∈ ({v}ᶜ : Set V) ↔ v ∉ ({i,j} : Finset V) := by
      simp [ne_comm]
    exact if_congr hc rfl rfl
  simp_rw [hrewrite]
  rw [sum_avoid, Fintype.sum_prod_type]
  have hentry (i j : V) :
      ((Fintype.card V : ℝ) - (({i,j} : Finset V).card : ℝ)) * M i j =
        ((Fintype.card V : ℝ) - 2) * M i j + if j = i then M i j else 0 := by
    by_cases h : j = i
    · subst j
      simp
      ring
    · rw [card_insert_of_notMem (by simpa [eq_comm] using h), card_singleton]
      simp [h]
  simp only [hentry, sum_add_distrib, ← Finset.mul_sum, sum_ite_eq', mem_univ, ite_true,
    mass, trace, diag_apply]

/-- Averaged inequality for a no-cut leaf, from the bound on each vertex deletion. -/
private theorem edge_averaged (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hn : 3 ≤ Fintype.card V) (hconn : ∀ v, (deleted G v).Connected)
    (hDelete : ∀ v : V,
      (2 * edgeMass (deleted G v) (principal M ({v}ᶜ : Set V))
        (supported_principal hM _).symm) ^ 2 ≤
      budget (deleted G v) * mass (principal M ({v}ᶜ : Set V))) :
    ((Fintype.card V : ℝ) - 2) * (2 * edgeMass G M hM.symm) ^ 2 ≤
      (budget G - 1) * (((Fintype.card V : ℝ) - 2) * mass M + M.trace) := by
  have hn' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hp : 0 < (Fintype.card V : ℝ) - 2 := by linarith
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (univ : Finset V))
    (f := fun v => budget (deleted G v)) (g := fun v => mass (principal M ({v}ᶜ : Set V)))
    (r := fun v => 2 * edgeMass (deleted G v) (principal M ({v}ᶜ : Set V))
      (supported_principal hM _).symm)
    (fun v _ => budget_nonneg (hconn v))
    (fun _ _ => mass_nonneg (fun i j => hM.nonneg i j)) (fun v _ => hDelete v)
  rw [← Finset.mul_sum, sum_edgeMass_deleted G M hM,
    sum_budget_deleted G (by omega), sum_mass_deleted] at h
  apply le_of_mul_le_mul_left _ hp
  convert h using 1 <;> ring

end DNN

end

/-! ### Bounds and equality for graphs without a cut -/

section

open Finset Matrix SimpleGraph
open scoped Matrix BigOperators

namespace DNN

open Gram

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def Bounded (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M) : Prop :=
  (2 * edgeMass G M hM.symm) ^ 2 ≤ budget G * mass M

def Normalized (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M) : Prop :=
  mass M = budget G ∧ 2 * edgeMass G M hM.symm = budget G

def blockWeight (B : Finset V) : ℝ := ((B.card : ℝ) - 1) / B.card

def blockMatrix (B : Finset V) : Matrix V V ℝ :=
  fun i j => if i ∈ B ∧ j ∈ B then blockWeight B ^ 2 else 0

private theorem singleton_scalars (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hn : Fintype.card V = 1) : budget G = 0 ∧ edgeMass G M hM = 0 := by
  have hV : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn.le
  have hG : G = ⊥ := by
    ext i j
    simp [Subsingleton.elim i j]
  subst G
  constructor
  · simp [budget_eq, hn]
  · rw [edgeMass_eq_sum]
    apply sum_eq_zero
    intro e he
    exfalso
    simpa only [mem_edgeFinset, edgeSet_bot, Set.mem_empty_iff_false] using he

theorem singleton_bound (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hn : Fintype.card V = 1) : Bounded G M hM := by
  obtain ⟨hq, hs⟩ := singleton_scalars G M hM.symm hn
  simp [Bounded, hq, hs]

private theorem mass_eq_zero_iff {M : Matrix V V ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    mass M = 0 ↔ M = 0 := by
  constructor
  · intro hT
    have hrow (i : V) : (∑ j : V, M i j) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun k _ => sum_nonneg (fun l _ => hM k l))).mp hT i (mem_univ i)
    ext i j
    exact (sum_eq_zero_iff_of_nonneg (fun l _ => hM i l)).mp (hrow i) j (mem_univ j)
  · rintro rfl
    simp [mass]

theorem singleton_normalized (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hn : Fintype.card V = 1) (he : Normalized G M hM) : M = 0 :=
  (mass_eq_zero_iff hM.nonneg).mp (he.1.trans (singleton_scalars G M hM.symm hn).1)

private theorem budget_two {G : SimpleGraph V} (hG : G.Connected) (hn : Fintype.card V = 2) :
    budget G = 1 ∧ G = ⊤ := by
  have hle := budget_le_top G
  have ht := budget_top (V := V) (show 1 ≤ Fintype.card V by omega)
  rw [hn] at ht
  norm_num at ht
  have hm := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, hn] at hm
  have hm' : (1 : ℝ) ≤ Nat.card G.edgeSet := by exact_mod_cast (show 1 ≤ Nat.card G.edgeSet by omega)
  have hq : 1 ≤ budget G := by
    simp only [budget, hn, Nat.cast_ofNat]
    linarith only [hm']
  have he : budget G = 1 := le_antisymm (ht ▸ hle) hq
  exact ⟨he, top_of_budget_eq G (he.trans ht.symm)⟩

private theorem twice_edges_of_budget (G : SimpleGraph V)
    (hq : budget G = ((Fintype.card V : ℝ) - 1) ^ 2) :
    2 * (G.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
  rw [budget_eq] at hq
  nlinarith only [hq]

private theorem complete_constant (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : SupportedDNN G M) (hn : 2 ≤ Fintype.card V)
    (hq : budget G = ((Fintype.card V : ℝ) - 1) ^ 2)
    (he : (2 * edgeMass G M hM.symm) ^ 2 = budget G * mass M) :
    ∀ i j, M i j = mass M / (Fintype.card V : ℝ) ^ 2 := by
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hp : 0 < (Fintype.card V : ℝ) - 1 := by linarith
  have hf := edge_flat hM
  rw [he, hq, twice_edges_of_budget G hq] at hf
  have hMul : ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) * M.trace) ≤
      ((Fintype.card V : ℝ) - 1) * mass M := by nlinarith only [hf]
  have ht := le_antisymm (mass_le_card_trace hM.psd) (le_of_mul_le_mul_left hMul hp)
  exact constant_of_mass_eq_card_trace hM.psd ht

private theorem complete_normalized (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : SupportedDNN G M) (hn : 2 ≤ Fintype.card V)
    (hq : budget G = ((Fintype.card V : ℝ) - 1) ^ 2)
    (he : Normalized G M hM) :
    M = blockMatrix (univ : Finset V) := by
  have hs : (2 * edgeMass G M hM.symm) ^ 2 = budget G * mass M := by
    rw [he.2, he.1, pow_two]
  ext i j
  simp only [blockMatrix, mem_univ, and_self, ite_true, blockWeight, card_univ,
    complete_constant G M hM hn hq hs i j, he.1, hq]
  rw [div_pow]

/-- The exact two-vertex bound, using the PSD trace inequality. -/
theorem two_bound (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hG : G.Connected) (hn : Fintype.card V = 2) : Bounded G M hM := by
  have hq := (budget_two hG hn).1
  have hcard : 2 * (G.edgeFinset.card : ℝ) = 2 := by
    rw [budget_eq, hn, Nat.cast_ofNat] at hq
    linarith only [hq]
  have hf := edge_flat hM
  rw [hcard] at hf
  have ht := mass_le_card_trace hM.psd
  rw [hn, Nat.cast_ofNat] at ht
  unfold Bounded
  rw [hq, one_mul]
  linarith only [hf, ht]

theorem two_normalized (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hG : G.Connected) (hn : Fintype.card V = 2) (he : Normalized G M hM) :
    G = ⊤ ∧ M = blockMatrix (univ : Finset V) := by
  obtain ⟨hq, hc⟩ := budget_two hG hn
  refine ⟨hc, complete_normalized G M hM hn.ge ?_ he⟩
  norm_num [hn, hq]

/-- The convex combination in Hu–Han (3.15), with its denominator cleared. -/
private theorem noCut_deficit (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hn : 3 ≤ Fintype.card V) (hconn : ∀ v, (deleted G v).Connected)
    (hDelete : ∀ v : V, Bounded (deleted G v) (principal M ({v}ᶜ : Set V))
      (supported_principal hM _)) :
    (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 2) *
        ((2 * edgeMass G M hM.symm) ^ 2 - budget G * mass M) ≤
      (budget G - ((Fintype.card V : ℝ) - 1) ^ 2) * M.trace := by
  have hn' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have ha := edge_averaged G M hM hn hconn hDelete
  have hf := edge_flat hM
  have hc : 2 * (G.edgeFinset.card : ℝ) = budget G + Fintype.card V - 1 := by
    rw [budget_eq]
    ring
  rw [hc] at hf
  have ha' := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ (Fintype.card V : ℝ) - 1 by linarith)
  have hf' := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ (Fintype.card V : ℝ) - 2 by linarith)
  nlinarith only [ha', hf']

theorem noCut_bound (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hn : 3 ≤ Fintype.card V) (hconn : ∀ v, (deleted G v).Connected)
    (hDelete : ∀ v : V, Bounded (deleted G v) (principal M ({v}ᶜ : Set V))
      (supported_principal hM _)) :
    Bounded G M hM := by
  have hn' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hp : 0 < (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 2) :=
    mul_pos (by linarith) (by linarith)
  have hq := budget_le_top G
  rw [budget_top (by omega)] at hq
  have hd := noCut_deficit G M hM hn hconn hDelete
  have hnon := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) hM.psd.trace_nonneg
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right (hd.trans hnon) hp)

private theorem noCut_complete_of_equality (G : SimpleGraph V) (M : Matrix V V ℝ)
    (hM : SupportedDNN G M) (hn : 3 ≤ Fintype.card V)
    (hconn : ∀ v, (deleted G v).Connected)
    (hDelete : ∀ v : V, Bounded (deleted G v) (principal M ({v}ᶜ : Set V))
      (supported_principal hM _))
    (hT : 0 < mass M)
    (he : (2 * edgeMass G M hM.symm) ^ 2 = budget G * mass M) :
    G = ⊤ ∧ ∀ i j, M i j = mass M / (Fintype.card V : ℝ) ^ 2 := by
  have htop := budget_top (V := V) (show 1 ≤ Fintype.card V by omega)
  have hq := budget_le_top G
  rw [htop] at hq
  have htrace : 0 < M.trace :=
    pos_of_mul_pos_right (hT.trans_le (mass_le_card_trace hM.psd)) (by positivity)
  have hd := noCut_deficit G M hM hn hconn hDelete
  rw [he, sub_self, mul_zero] at hd
  have hq' := le_antisymm hq (sub_nonneg.mp (nonneg_of_mul_nonneg_left hd htrace))
  exact ⟨top_of_budget_eq G (hq'.trans htop.symm),
    complete_constant G M hM (by omega) hq' he⟩

theorem noCut_normalized (G : SimpleGraph V) (M : Matrix V V ℝ) (hM : SupportedDNN G M)
    (hG : G.Connected) (hn : 3 ≤ Fintype.card V) (hconn : ∀ v, (deleted G v).Connected)
    (hDelete : ∀ v : V, Bounded (deleted G v) (principal M ({v}ᶜ : Set V))
      (supported_principal hM _)) (he : Normalized G M hM) :
    G = ⊤ ∧ M = blockMatrix (univ : Finset V) := by
  have hT : 0 < mass M := he.1.symm ▸ budget_pos hG (by omega)
  have hs : (2 * edgeMass G M hM.symm) ^ 2 = budget G * mass M := by
    rw [he.2, he.1, pow_two]
  obtain ⟨hTop, _⟩ := noCut_complete_of_equality G M hM hn hconn hDelete hT hs
  have hq := hTop.symm ▸ budget_top (V := V) (show 1 ≤ Fintype.card V by omega)
  exact ⟨hTop, complete_normalized G M hM (by omega) hq he⟩

end DNN

end

end D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy
