/- GID: D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CographDistanceCotree
   mirror-E: none
   anchors: []
   utility: none
   digest: Ordinary cograph distance and its rank-one decomposition on native component cotrees. -/

import D5.S3.Combinatorics.SpectralGraph.NormalizedCographCotree
import D5.S3.QuadraticForms.SymmetricRankOneKernel
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Ring

/-! # Ordinary distance and component cotree matrices -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree

open SimpleGraph Matrix NormalizedCographCotree

/-- Ordinary shortest-path distances on the native vertex carrier. -/
def distanceMatrix {V : Type} (G : SimpleGraph V) : Matrix V V ℝ :=
  Matrix.of fun u v => (G.dist u v : ℝ)

/-- The constant-one matrix, including its diagonal. -/
def ones (V : Type) : Matrix V V ℝ :=
  Matrix.of fun _ _ => 1

/-- At a join node two distinct nonadjacent vertices are in the same child
and have a common neighbor in another child. -/
private theorem dist_two_at_join {V : Type} {G : SimpleGraph V}
    (hc : G.Connected) (t : Cotree G (some true)) {u v : V}
    (hne : u ≠ v) (hnadj : ¬G.Adj u v) : G.dist u v = 2 := by
  cases t with
  | node _ arity _ _ _ =>
    let H := cutGraph G true
    have huv : H.connectedComponentMk u = H.connectedComponentMk v :=
      ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj u v from ⟨hne, hnadj⟩)
    let := arity
    obtain ⟨C, hC⟩ := exists_ne (H.connectedComponentMk u)
    obtain ⟨w, hw⟩ := C.nonempty_supp
    have huw : H.connectedComponentMk u ≠ H.connectedComponentMk w := by
      intro h
      exact hC (hw.symm.trans h.symm)
    have huw' : G.Adj u w := (Cotree.adj_iff_join_of_component_ne true huw).mpr rfl
    have hvw' : G.Adj v w :=
      (Cotree.adj_iff_join_of_component_ne true (huv ▸ huw)).mpr rfl
    have hle := hc.dist_triangle (u := u) (v := w) (w := v)
    rw [dist_eq_one_iff_adj.mpr huw', dist_eq_one_iff_adj.mpr hvw'.symm] at hle
    exact Nat.le_antisymm hle (hc.one_lt_dist_of_ne_of_not_adj hne hnadj)

open Classical in
/-- The ordinary distances of a connected cograph are zero on the diagonal,
one on edges, and two on distinct nonadjacent vertices. -/
theorem dist_eq {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) (u v : V) :
    G.dist u v = if u = v then 0 else if G.Adj u v then 1 else 2 := by
  by_cases he : u = v
  · simp [he]
  by_cases ha : G.Adj u v
  · simp [he, ha, dist_eq_one_iff_adj.mpr ha]
  let : Nontrivial V := ⟨⟨u, v, he⟩⟩
  obtain ⟨t⟩ := Cotree.exists_join_root hc hP
  simpa only [ite_eq_right he, ite_eq_right ha] using dist_two_at_join hc t he ha

open Classical in
/-- The native real distance matrix of a connected cograph is `2J - 2I - A`. -/
theorem distanceMatrix_eq {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) :
    distanceMatrix G = (2 : ℝ) • ones V - (2 : ℝ) • (1 : Matrix V V ℝ) -
      G.adjMatrix ℝ := by
  ext u v
  simp only [distanceMatrix, Matrix.of_apply, dist_eq hc hP, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, ones, Matrix.one_apply, adjMatrix_apply]
  by_cases huv : u = v
  · subst v
    norm_num
  by_cases ha : G.Adj u v <;> norm_num [huv, ha]

open Classical in
/-- The local matrix uses the ambient distance expression, with the parent label
and spectral shift removed. The induced graph may be disconnected. -/
def localMatrix {V : Type} (G : SimpleGraph V) (q x : ℝ) : Matrix V V ℝ :=
  (2 - q) • ones V - (x + 2) • (1 : Matrix V V ℝ) - G.adjMatrix ℝ

open Classical in
/-- At a connected cograph root the local matrix is the shifted ordinary distance matrix. -/
theorem localMatrix_root {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) (x : ℝ) :
    localMatrix G 0 x = distanceMatrix G - x • (1 : Matrix V V ℝ) := by
  rw [distanceMatrix_eq hc hP]
  ext u v
  simp only [localMatrix, sub_zero, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Restricting a local matrix to a subset uses the graph induced on that subset. -/
theorem localMatrix_induce {V : Type} (G : SimpleGraph V) (s : Set V) (q x : ℝ) :
    localMatrix (G.induce s) q x =
      (localMatrix G q x).submatrix (Subtype.val : s → V) Subtype.val := by
  classical
  ext u v
  simp [localMatrix, ones, Matrix.one_apply, Subtype.ext_iff]

/-- Labels of internal vertices are one at joins and two at unions. -/
def label (join : Bool) : ℝ := if join then 1 else 2

/-- The component supports partition a node's native carrier. -/
def componentEquiv {V : Type} (G : SimpleGraph V) (join : Bool) :
    (Σ C : (cutGraph G join).ConnectedComponent, C.supp) ≃ V :=
  Equiv.sigmaFiberEquiv (cutGraph G join).connectedComponentMk

open Classical in
/-- In component coordinates the local matrix is the block sum at child parent
label `label join`, plus one all-ones update. -/
theorem localMatrix_node {V : Type} (G : SimpleGraph V) (join : Bool) (q x : ℝ) :
    Matrix.reindex (componentEquiv G join).symm (componentEquiv G join).symm
        (localMatrix G q x) =
      Matrix.blockDiagonal' (fun C : (cutGraph G join).ConnectedComponent =>
        localMatrix (G.induce C.supp) (label join) x) +
      (label join - q) • ones (Σ C : (cutGraph G join).ConnectedComponent, C.supp) := by
  ext ⟨C, u⟩ ⟨D, v⟩
  change localMatrix G q x u.val v.val =
    Matrix.blockDiagonal'
      (fun C : (cutGraph G join).ConnectedComponent =>
        localMatrix (G.induce C.supp) (label join) x) ⟨C, u⟩ ⟨D, v⟩ + (label join - q) * 1
  by_cases hCD : C = D
  · subst D
    rw [Matrix.blockDiagonal'_apply_eq, localMatrix_induce]
    simp only [localMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, ones, Matrix.of_apply]
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hCD]
    have hm : (cutGraph G join).connectedComponentMk u.val ≠
        (cutGraph G join).connectedComponentMk v.val := by
      rw [show (cutGraph G join).connectedComponentMk u.val = C from u.property,
        show (cutGraph G join).connectedComponentMk v.val = D from v.property]
      exact hCD
    have huv : u.val ≠ v.val := fun h => hm (congrArg _ h)
    have ha := Cotree.adj_iff_join_of_component_ne join hm
    cases join
    · simp_all [localMatrix, label, ones]
    · simp_all [localMatrix, label, ones]
      ring

open D5.S3.QuadraticForms.SymmetricRankOneKernel InnerProductSpace
open scoped RealInnerProductSpace

open Classical in
/-- The local matrix acting on the Euclidean space of native vertex coordinates. -/
abbrev localOperator {V : Type} [Fintype V] (G : SimpleGraph V) (q x : ℝ) :
    EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  (localMatrix G q x).toEuclideanLin

/-- The update direction is the vector whose coordinates are all one. -/
def oneVector (V : Type) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun _ => 1

/-- Pairing with the update direction reads the sum of native vertex coordinates. -/
theorem pairing_oneVector {V : Type} [Fintype V] (y : EuclideanSpace ℝ V) :
    ⟪oneVector V, y⟫ = ∑ v, y v := by
  simp [PiLp.inner_apply, oneVector, RCLike.inner_apply]

theorem localOperator_symmetric {V : Type} [Fintype V] (G : SimpleGraph V) (q x : ℝ) :
    (localOperator G q x).IsSymmetric := by
  classical
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  rw [Matrix.isHermitian_iff_isSymm]
  have hJ : (ones V).IsSymm := by ext; rfl
  exact ((hJ.smul _).sub (Matrix.isSymm_one.smul _)).sub (G.isSymm_adjMatrix)

section Node

variable {V : Type} (G : SimpleGraph V) (join : Bool)
variable [Fintype V] [Fintype (cutGraph G join).ConnectedComponent]
variable [∀ C : (cutGraph G join).ConnectedComponent, Fintype C.supp]

/-- Reindex the native Euclidean coordinates isometrically as Euclidean child blocks. -/
def componentCoordinates :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ]
      PiLp 2 (fun C : (cutGraph G join).ConnectedComponent => EuclideanSpace ℝ C.supp) := by
  let e := componentEquiv G join
  let L : EuclideanSpace ℝ V ≃ₗ[ℝ]
      PiLp 2 (fun C : (cutGraph G join).ConnectedComponent => EuclideanSpace ℝ C.supp) :=
    { toFun := fun y => WithLp.toLp 2 (fun C => WithLp.toLp 2 (fun v => y (e ⟨C, v⟩)))
      invFun := fun y => WithLp.toLp 2 (fun v => y (e.symm v).1 (e.symm v).2)
      left_inv := fun y => by
        apply (WithLp.ext_iff 2).mpr
        funext v
        change y (e (e.symm v)) = y v
        rw [e.apply_symm_apply]
      right_inv := fun y => by
        apply (WithLp.ext_iff 2).mpr
        funext C
        apply (WithLp.ext_iff 2).mpr
        funext v
        change (e.symm (e ⟨C, v⟩)).rec (fun D w => y D w) = y C v
        rw [e.symm_apply_apply]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine L.isometryOfInner (fun y z => ?_)
  simp only [PiLp.inner_apply]
  calc
    _ = ∑ i : (Σ C : (cutGraph G join).ConnectedComponent, C.supp),
        ⟪y (e i), z (e i)⟫ :=
      (Fintype.sum_sigma (fun i => ⟪y (e i), z (e i)⟫)).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The all-ones direction partitions into the all-ones direction of every child. -/
@[simp] theorem componentCoordinates_oneVector :
    componentCoordinates G join (oneVector V) =
      WithLp.toLp 2 (fun C : (cutGraph G join).ConnectedComponent => oneVector C.supp) := rfl

/-- The sum of the local child operators at the parent's label. -/
abbrev childBlocks (x : ℝ) :
    PiLp 2 (fun C : (cutGraph G join).ConnectedComponent => EuclideanSpace ℝ C.supp) →ₗ[ℝ]
      PiLp 2 (fun C : (cutGraph G join).ConnectedComponent => EuclideanSpace ℝ C.supp) :=
  blockDiagonal (fun C => localOperator (G.induce C.supp) (label join) x)

/-- Under the native component isometry the local operator is exactly the
symmetric rank-one update of the child blocks. -/
theorem localOperator_node (q x : ℝ) :
    (componentCoordinates G join).toLinearEquiv.conj (localOperator G q x) =
      update (childBlocks G join x)
        (componentCoordinates G join (oneVector V)) (label join - q) := by
  classical
  ext1 y
  apply (WithLp.ext_iff 2).mpr
  funext C
  apply (WithLp.ext_iff 2).mpr
  funext u
  let e := componentEquiv G join
  let E := componentCoordinates G join
  let B := fun D : (cutGraph G join).ConnectedComponent =>
    localMatrix (G.induce D.supp) (label join) x
  let z : EuclideanSpace ℝ V := E.symm y
  let t := label join - q
  have hz (v : V) : z v = y (e.symm v).1 (e.symm v).2 := rfl
  have hrow :
      (∑ v, localMatrix G q x u.val v * z v) =
        ∑ j : (Σ D : (cutGraph G join).ConnectedComponent, D.supp),
          (Matrix.blockDiagonal' B ⟨C, u⟩ j + t) * y j.1 j.2 := by
    apply Fintype.sum_equiv e.symm
    intro v
    have h := congrFun (congrFun (localMatrix_node G join q x) ⟨C, u⟩) (e.symm v)
    change localMatrix G q x u.val (e (e.symm v)) =
      Matrix.blockDiagonal' B ⟨C, u⟩ (e.symm v) + t * 1 at h
    rw [e.apply_symm_apply, mul_one] at h
    rw [h, hz]
  have hblock :
      (∑ j : (Σ D : (cutGraph G join).ConnectedComponent, D.supp),
          Matrix.blockDiagonal' B ⟨C, u⟩ j * y j.1 j.2) =
        ∑ v : C.supp, B C u v * y C v := by
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single C]
    · simp [Matrix.blockDiagonal'_apply_eq]
    · intro D _ hDC
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hDC.symm]
    · simp
  have hpair : ⟪E (oneVector V), y⟫ = ∑ D, ∑ v, y D v := by
    rw [show E (oneVector V) =
      WithLp.toLp 2 (fun D : (cutGraph G join).ConnectedComponent => oneVector D.supp) from
        componentCoordinates_oneVector G join]
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun D _ => pairing_oneVector (y D)
  simp only [update, LinearMap.add_apply, LinearMap.smul_apply, toLinearMap_rankOne,
    LinearMap.smulRight_apply, smul_smul]
  change (localOperator G q x z) u.val =
    (childBlocks G join x y) C u + (t * ⟪E (oneVector V), y⟫) * 1
  change (∑ v, localMatrix G q x u.val v * z v) =
    (∑ v : C.supp, B C u v * y C v) + (t * ⟪E (oneVector V), y⟫) * 1
  rw [hrow, hpair, mul_one]
  simp only [add_mul, Finset.sum_add_distrib, hblock, ← Finset.mul_sum]
  rw [Fintype.sum_sigma]

end Node

private theorem operator_states_of_conj {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (A : E →ₗ[ℝ] E) (B : F →ₗ[ℝ] F) (u : E)
    (h : e.toLinearEquiv.conj A = B) :
    Module.finrank ℝ (LinearMap.ker A) = Module.finrank ℝ (LinearMap.ker B) ∧
      (HasNonzeroPairing A u ↔ HasNonzeroPairing B (e u)) ∧
      (∀ s, ScalarResponse A u s ↔ ScalarResponse B (e u) s) := by
  have he (z : E) : B (e z) = e (A z) := by
    rw [← h]
    change e (A (e.symm (e z))) = e (A z)
    rw [e.symm_apply_apply]
  have hz (z : E) : e z ∈ LinearMap.ker B ↔ z ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, he, ← e.map_zero, e.injective.eq_iff]
  have hk : (LinearMap.ker A).map e.toLinearEquiv.toLinearMap = LinearMap.ker B := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hz, Submodule.mem_map]
    exact ⟨fun ⟨y, hy, heq⟩ => e.injective heq ▸ hy, fun hw => ⟨w, hw, rfl⟩⟩
  let ek := e.toLinearEquiv.ofSubmodules (LinearMap.ker A) (LinearMap.ker B) hk
  have hp (z : LinearMap.ker A) : ⟪e u, (ek z : F)⟫ = ⟪u, (z : E)⟫ :=
    e.inner_map_map _ _
  have hs (z : E) : B (e z) = e u ↔ A z = u := by rw [he, e.injective.eq_iff]
  refine ⟨ek.finrank_eq, ?_, ?_⟩
  · constructor
    · rintro ⟨z, hz⟩
      exact ⟨ek z, by rwa [hp]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := ek.surjective z
      exact ⟨w, by rwa [hp] at hz⟩
  · intro s
    constructor
    · rintro ⟨⟨y, hy⟩, hresponse⟩
      refine ⟨⟨e y, (hs y).mpr hy⟩, fun z hz => ?_⟩
      obtain ⟨w, rfl⟩ := e.surjective z
      rw [e.inner_map_map]
      exact hresponse w ((hs w).mp hz)
    · rintro ⟨⟨y, hy⟩, hresponse⟩
      obtain ⟨w, rfl⟩ := e.surjective y
      exact ⟨⟨w, (hs w).mp hy⟩, fun z hz =>
        (e.inner_map_map u z).symm.trans (hresponse (e z) ((hs z).mpr hz))⟩

/-- The native nullity, kernel pairing and scalar response survive the
component reindexing used by the symmetric rank-one state APIs. -/
theorem localOperator_node_states {V : Type} [Fintype V] (G : SimpleGraph V) (join : Bool)
    [Fintype (cutGraph G join).ConnectedComponent]
    [∀ C : (cutGraph G join).ConnectedComponent, Fintype C.supp] (q x : ℝ) :
    let e := componentCoordinates G join (oneVector V)
    let B := update (childBlocks G join x) e (label join - q)
    Module.finrank ℝ (LinearMap.ker (localOperator G q x)) = Module.finrank ℝ (LinearMap.ker B) ∧
      (HasNonzeroPairing (localOperator G q x) (oneVector V) ↔ HasNonzeroPairing B e) ∧
      (∀ s, ScalarResponse (localOperator G q x) (oneVector V) s ↔ ScalarResponse B e s) :=
  operator_states_of_conj _ _ _ _ (localOperator_node G join q x)

open Classical in
/-- A leaf has the scalar matrix `[-(x+q)]`. This gives the response and
nullity away from its pole and a one-dimensional flagged kernel at the pole.
In particular a singleton root uses `q = 0`. -/
theorem leaf_states {V : Type} [Fintype V] {G : SimpleGraph V}
    (leaf : Cotree G none) (q x : ℝ) :
    if x + q = 0 then
      Module.finrank ℝ (LinearMap.ker (localOperator G q x)) = 1 ∧
        HasNonzeroPairing (localOperator G q x) (oneVector V)
    else
      Module.finrank ℝ (LinearMap.ker (localOperator G q x)) = 0 ∧
        ScalarResponse (localOperator G q x) (oneVector V) (-1 / (x + q)) := by
  cases leaf with
  | leaf v unique =>
    let : Unique V := ⟨⟨v⟩, unique⟩
    have hInner : ⟪oneVector V, oneVector V⟫ = 1 := by
      rw [pairing_oneVector]
      change (∑ _ : V, (1 : ℝ)) = 1
      simp
    have hA : localMatrix G q x = -(x + q) • (1 : Matrix V V ℝ) := by
      ext u w
      rw [Subsingleton.elim w u]
      simp [localMatrix, ones]
      ring
    have hM : localOperator G q x =
        -(x + q) • (LinearMap.id : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) := by
      rw [localOperator, hA, map_smul, Matrix.toLpLin_one]
    by_cases h : x + q = 0
    · rw [ite_eq_left h, hM, h, neg_zero, zero_smul]
      refine ⟨?_, ⟨⟨oneVector V, LinearMap.mem_ker.mpr rfl⟩, ?_⟩⟩
      · rw [LinearMap.ker_zero, finrank_top, finrank_euclideanSpace, Fintype.card_unique]
      · change ⟪oneVector V, oneVector V⟫ ≠ 0
        rw [hInner]
        exact one_ne_zero
    · have hne : -(x + q) ≠ 0 := neg_ne_zero.mpr h
      rw [ite_eq_right h, hM]
      refine ⟨by rw [LinearMap.ker_smul _ _ hne, LinearMap.ker_id, finrank_bot], ?_⟩
      refine ⟨⟨(-(x + q))⁻¹ • oneVector V, ?_⟩, ?_⟩
      · rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ hne, one_smul]
      · intro y hy
        have hy' : y = (-(x + q))⁻¹ • oneVector V := by
          have hy'' := congrArg (fun w : EuclideanSpace ℝ V => (-(x + q))⁻¹ • w) hy
          simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
            inv_mul_cancel₀ hne, one_smul] using hy''
        rw [hy', real_inner_smul_right, hInner, mul_one, inv_neg, neg_div, one_div]

end D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
