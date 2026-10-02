/- GID: D5/S3/Combinatorics/Graph/DirectedAllMinorsMatrixTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectedAllMinorsMatrixTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Directed forests compute signed complementary minors over commutative rings. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
open Matrix
set_option maxHeartbeats 1200000 in
open Classical in
theorem directed_all_minors_matrix_tree
    {R : Type*} [CommRing R] {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (U W : Finset (Fin n))
    (hU : U.card = k) (hW : W.card = k) (_hk : 1 ≤ k)
    (hcol : ∀ j, ∑ i, M i j = 0) :
    let graph := fun F : Finset (Fin n × Fin n) =>
      SimpleGraph.fromRel (fun i j => (i, j) ∈ F)
    let Forest := {F : Finset (Fin n × Fin n) //
      (∀ edge ∈ F, edge.1 ≠ edge.2) ∧
      (graph F).IsAcyclic ∧
      (∀ v, ∃! u, u ∈ U ∧ (graph F).Reachable v u) ∧
      (∀ v, ∃! w, w ∈ W ∧ (graph F).Reachable v w) ∧
      (∀ i j, (i, j) ∈ F → ∀ u ∈ U, (graph F).Reachable u i →
        (graph F).dist u i < (graph F).dist u j)}
    let row : Fin (n - k) ↪o Fin n := Wᶜ.orderEmbOfFin (by simp [Finset.card_compl, hW])
    let col : Fin (n - k) ↪o Fin n := Uᶜ.orderEmbOfFin (by simp [Finset.card_compl, hU])
    ∃ matching : Forest → Equiv.Perm (Fin k),
      (∀ F a, (graph F.val).Reachable (U.orderEmbOfFin hU a)
        (W.orderEmbOfFin hW (matching F a))) ∧
      (M.submatrix row col).det =
        ∑ F : Forest,
          (((-1 : ℤ) ^ (n + k + (∑ u ∈ U, u.val) + (∑ w ∈ W, w.val)) *
            (Equiv.Perm.sign (matching F) : ℤ) : ℤ) : R) *
          ∏ edge ∈ F.val, M edge.1 edge.2 := by
  classical
  let graph := fun F : Finset (Fin n × Fin n) =>
    SimpleGraph.fromRel (fun i j => (i, j) ∈ F)
  let isForest := fun F : Finset (Fin n × Fin n) =>
    (∀ edge ∈ F, edge.1 ≠ edge.2) ∧
      (graph F).IsAcyclic ∧
      (∀ v, ∃! u, u ∈ U ∧ (graph F).Reachable v u) ∧
      (∀ v, ∃! w, w ∈ W ∧ (graph F).Reachable v w) ∧
      (∀ i j, (i, j) ∈ F → ∀ u ∈ U, (graph F).Reachable u i →
        (graph F).dist u i < (graph F).dist u j)
  let Forest := {F : Finset (Fin n × Fin n) // isForest F}
  let row : Fin (n - k) ↪o Fin n := Wᶜ.orderEmbOfFin (by simp [Finset.card_compl, hW])
  let col : Fin (n - k) ↪o Fin n := Uᶜ.orderEmbOfFin (by simp [Finset.card_compl, hU])
  let roots := U.orderEmbOfFin hU
  let marks := W.orderEmbOfFin hW
  let matchingIndex (F : Forest) (a : Fin k) : Fin k := (W.orderIsoOfFin hW).symm
      ⟨Classical.choose (F.property.2.2.2.1 (roots a)),
        (Classical.choose_spec (F.property.2.2.2.1 (roots a))).1.1⟩
  have matchingIndex_spec (F : Forest) (a : Fin k) :
      (graph F.val).Reachable (roots a) (marks (matchingIndex F a)) := by
    have hw := (Classical.choose_spec (F.property.2.2.2.1 (roots a))).1.2
    simpa [matchingIndex, marks, Finset.orderEmbOfFin] using hw
  have matchingIndex_injective (F : Forest) : Function.Injective (matchingIndex F) := by
    intro a b hab
    have ha := matchingIndex_spec F a
    have hb := matchingIndex_spec F b
    have hab' : (graph F.val).Reachable (roots a) (roots b) := ha.trans (hab ▸ hb.symm)
    apply roots.injective
    have hu := F.property.2.2.1 (roots a)
    exact hu.unique ⟨U.orderEmbOfFin_mem hU a, SimpleGraph.Reachable.refl _⟩
      ⟨U.orderEmbOfFin_mem hU b, hab'⟩
  let matching (F : Forest) : Equiv.Perm (Fin k) := Equiv.ofBijective (matchingIndex F)
      ⟨matchingIndex_injective F,
        Finite.injective_iff_surjective.mp (matchingIndex_injective F)⟩
  have incoming (F : Forest) (v : Fin n) (hv : v ∉ U) : ∃! i, (i, v) ∈ F.val := by
    obtain ⟨u, hu, huniq⟩ := F.property.2.2.1 v
    have huv : u ≠ v := by
      intro heq
      exact hv (heq ▸ hu.1)
    obtain ⟨path, hpath, hlength⟩ := hu.2.symm.exists_path_of_dist
    have hnil : ¬path.Nil := SimpleGraph.Walk.not_nil_of_ne huv
    let predecessor := path.penultimate
    have hadj : (graph F.val).Adj predecessor v := path.adj_penultimate hnil
    have hdepth : (graph F.val).dist u predecessor < (graph F.val).dist u v := by
      have hle := SimpleGraph.dist_le path.dropLast
      have hlen := path.length_dropLast_add_one hnil
      dsimp [predecessor]
      omega
    have hedge : (predecessor, v) ∈ F.val := by
      rcases hadj with ⟨hne, hedge | hedge⟩
      · exact hedge
      · have hbad := F.property.2.2.2.2 v predecessor hedge u hu.1 hu.2.symm
        exact False.elim (Nat.lt_asymm hdepth hbad)
    refine ⟨predecessor, hedge, ?_⟩
    intro other hother
    have hne := F.property.1 (other, v) hother
    have hadj' : (graph F.val).Adj other v := ⟨hne, Or.inl hother⟩
    have hreach : (graph F.val).Reachable u other := hu.2.symm.trans hadj'.symm.reachable
    have hdepth' := F.property.2.2.2.2 other v hother u hu.1 hreach
    have hsupp : other ∈ path.support := by
      by_contra hnmem
      obtain ⟨otherPath, hotherPath, hotherLength⟩ := hreach.exists_path_of_dist
      have hvpath := F.property.2.1.mem_support_of_ne_mem_support_of_adj_of_isPath
        hotherPath hpath hadj' hnmem
      have hle := SimpleGraph.dist_le (otherPath.takeUntil v hvpath)
      have hlen := otherPath.length_takeUntil_le_length hvpath
      omega
    exact F.property.2.1.eq_penultimate_of_adj_end hpath hadj'.symm hsupp
  have no_incoming_root (F : Forest) (v : Fin n) (hv : v ∈ U) :
      ∀ i, (i, v) ∉ F.val := by
    intro i hi
    have hne := F.property.1 (i, v) hi
    have hadj : (graph F.val).Adj v i := ⟨hne.symm, Or.inr hi⟩
    have hbad := F.property.2.2.2.2 i v hi v hv hadj.reachable
    simp only [SimpleGraph.dist_self] at hbad
    exact Nat.not_lt_zero _ hbad
  refine ⟨matching, matchingIndex_spec, ?_⟩
  let Parent := ∀ j : Fin (n - k), {i : Fin n // i ≠ col j}
  let parentEdges (p : Parent) : Finset (Fin n × Fin n) :=
    Finset.univ.image (fun j => ((p j).val, col j))
  have column_nonroot (j : Fin (n - k)) : col j ∉ U :=
    Finset.mem_compl.mp (Uᶜ.orderEmbOfFin_mem (by simp [Finset.card_compl, hU]) j)
  let forestParent (F : Forest) : Parent := fun j =>
    ⟨Classical.choose (incoming F (col j) (column_nonroot j)),
      F.property.1 _ (Classical.choose_spec
        (incoming F (col j) (column_nonroot j))).1⟩
  have forestParent_edge (F : Forest) (j : Fin (n - k)) :
      ((forestParent F j).val, col j) ∈ F.val :=
    (Classical.choose_spec (incoming F (col j) (column_nonroot j))).1
  have parentEdges_forestParent (F : Forest) : parentEdges (forestParent F) = F.val := by
    ext edge
    constructor
    · intro hedge
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hedge
      exact heq ▸ forestParent_edge F j
    · intro hedge
      have hnroot : edge.2 ∉ U := by
        intro hroot
        exact no_incoming_root F edge.2 hroot edge.1 hedge
      let j : Fin (n - k) := (Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
          ⟨edge.2, Finset.mem_compl.mpr hnroot⟩
      have hcolj : col j = edge.2 := by
        simp [col, j, Finset.orderEmbOfFin]
      have hparent : (forestParent F j).val = edge.1 :=
        (incoming F (col j) (column_nonroot j)).unique
          (forestParent_edge F j) (hcolj.symm ▸ hedge)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, Prod.ext hparent hcolj⟩
  have parentEdges_injective : Function.Injective parentEdges := by
    intro p q heq
    funext j
    apply Subtype.ext
    have hedge : ((p j).val, col j) ∈ parentEdges q :=
      heq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨other, hother, hpair⟩ := Finset.mem_image.mp hedge
    have hotherj : other = j := col.injective (congrArg Prod.snd hpair)
    subst other
    exact (congrArg Prod.fst hpair).symm
  let GoodParent := {p : Parent // isForest (parentEdges p)}
  let forestEquiv : GoodParent ≃ Forest :=
    { toFun := fun p => ⟨parentEdges p.val, p.property⟩
      invFun := fun F => ⟨forestParent F, by rw [parentEdges_forestParent]; exact F.property⟩
      left_inv := fun p => Subtype.ext (parentEdges_injective (parentEdges_forestParent _))
      right_inv := fun F => Subtype.ext (parentEdges_forestParent F) }
  have edgeWeight (p : Parent) :
      (∏ edge ∈ parentEdges p, M edge.1 edge.2) = ∏ j, M (p j).val (col j) := by
    apply Finset.prod_image
    intro first hfirst second hsecond heq
    exact col.injective (congrArg Prod.snd heq)
  let root (F : Forest) (v : Fin n) := Classical.choose (F.property.2.2.1 v)
  have root_spec (F : Forest) (v : Fin n) :
      root F v ∈ U ∧ (graph F.val).Reachable v (root F v) :=
    (Classical.choose_spec (F.property.2.2.1 v)).1
  let depth (F : Forest) (v : Fin n) := (graph F.val).dist (root F v) v
  have edge_root_eq (F : Forest) (i j : Fin n) (hij : (i, j) ∈ F.val) :
      root F i = root F j := by
    have hadj : (graph F.val).Adj i j := ⟨F.property.1 _ hij, Or.inl hij⟩
    exact (F.property.2.2.1 i).unique (root_spec F i)
      ⟨(root_spec F j).1, hadj.reachable.trans (root_spec F j).2⟩
  have edge_depth_lt (F : Forest) (i j : Fin n) (hij : (i, j) ∈ F.val) :
      depth F i < depth F j := by
    have hadj : (graph F.val).Adj i j := ⟨F.property.1 _ hij, Or.inl hij⟩
    have hr : (graph F.val).Reachable (root F j) i :=
      (root_spec F j).2.symm.trans hadj.symm.reachable
    have hlt := F.property.2.2.2.2 i j hij (root F j) (root_spec F j).1 hr
    simpa only [depth, edge_root_eq F i j hij] using hlt
  let getParent (F : Forest) (j : Fin n) (hj : j ∉ U) : Fin n :=
    (forestParent F ((Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
      ⟨j, Finset.mem_compl.mpr hj⟩)).val
  have getParent_edge (F : Forest) (j : Fin n) (hj : j ∉ U) :
      (getParent F j hj, j) ∈ F.val := by
    let index : Fin (n - k) := (Uᶜ.orderIsoOfFin
      (by simp [Finset.card_compl, hU])).symm ⟨j, Finset.mem_compl.mpr hj⟩
    have hindex : col index = j := by simp [col, index, Finset.orderEmbOfFin]
    have hedge := forestParent_edge F index
    change (getParent F j hj, col index) ∈ F.val at hedge
    rw [hindex] at hedge
    exact hedge
  let full (F : Forest) : Matrix (Fin n) (Fin n) ℤ :=
    fun i j => if hj : j ∈ U then (if i = j then 1 else 0) else
      (if i = j then 1 else 0) - (if i = getParent F j hj then 1 else 0)
  have full_triangular (F : Forest) : (full F).BlockTriangular (depth F) := by
    intro i j hdepth
    have hij : i ≠ j := by intro heq; subst i; exact Nat.lt_irrefl _ hdepth
    by_cases hj : j ∈ U
    · simp [full, hj, hij]
    · have hparent := edge_depth_lt F _ _ (getParent_edge F j hj)
      have hip : i ≠ getParent F j hj := by
        intro heq
        rw [heq] at hdepth
        exact Nat.lt_asymm hparent hdepth
      simp [full, hj, hij, hip]
  have full_diagonal (F : Forest) (i j : Fin n) (hdepth : depth F i = depth F j) :
      full F i j = if i = j then 1 else 0 := by
    by_cases hj : j ∈ U
    · simp [full, hj]
    · have hparent := edge_depth_lt F _ _ (getParent_edge F j hj)
      have hip : i ≠ getParent F j hj := by
        intro heq
        rw [heq] at hdepth
        exact (Nat.ne_of_lt hparent) hdepth
      simp [full, hj, hip]
  have full_det (F : Forest) : (full F).det = 1 := by
    have hblocks (height : ℕ) : (full F).toSquareBlock (depth F) height = 1 := by
      ext i j
      rw [Matrix.toSquareBlock_def]
      change full F i.val j.val = _
      rw [full_diagonal F i.val j.val (i.property.trans j.property.symm)]
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [(full_triangular F).det]
    simp [hblocks]
  have path_columns (F : Forest) (v : Fin n) : ∃ support : Finset (Fin n),
        (∀ j ∈ support, j ∉ U) ∧
        (∀ j ∈ support, depth F j ≤ depth F v) ∧
        ∀ i, (if i = v then (1 : ℤ) else 0) -
          (if i = root F v then 1 else 0) = ∑ j ∈ support, full F i j := by
    have construction : ∀ height : ℕ, ∀ v : Fin n, depth F v = height →
        ∃ support : Finset (Fin n),
          (∀ j ∈ support, j ∉ U) ∧
          (∀ j ∈ support, depth F j ≤ depth F v) ∧
          ∀ i, (if i = v then (1 : ℤ) else 0) -
            (if i = root F v then 1 else 0) = ∑ j ∈ support, full F i j := by
      intro height
      induction height using Nat.strong_induction_on with
      | h height ih =>
        intro v hv
        by_cases hroot : v ∈ U
        · have hrv : root F v = v := (F.property.2.2.1 v).unique (root_spec F v)
              ⟨hroot, SimpleGraph.Reachable.refl _⟩
          refine ⟨∅, by simp, by simp, ?_⟩
          intro i
          simp [hrv]
        · have hedge := getParent_edge F v hroot
          have hlt := edge_depth_lt F _ _ hedge
          obtain ⟨support, hsupport, hheights, hcolumns⟩ :=
            ih (depth F (getParent F v hroot)) (by omega) _ rfl
          have hnot : v ∉ support := by
            intro hmem
            have hle := hheights v hmem
            omega
          refine ⟨insert v support, ?_, ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact hroot
            · exact hsupport j hj
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact le_rfl
            · exact (hheights j hj).trans (Nat.le_of_lt hlt)
          · intro i
            rw [Finset.sum_insert hnot, ← hcolumns i]
            have hroots := edge_root_eq F _ _ hedge
            simp only [full, dif_neg hroot, hroots]
            ring
    exact construction (depth F v) v rfl
  let partner (F : Forest) (v : Fin n) : Fin n :=
    if hv : v ∈ U then marks (matching F ((U.orderIsoOfFin hU).symm ⟨v, hv⟩)) else v
  have partner_reachable (F : Forest) (v : Fin n) (hv : v ∈ U) :
      (graph F.val).Reachable v (partner F v) := by
    have hindex : roots ((U.orderIsoOfFin hU).symm ⟨v, hv⟩) = v := by
      simp [roots, Finset.orderEmbOfFin]
    dsimp only [partner]
    rw [dif_pos hv]
    change (graph F.val).Reachable v
      (marks (matchingIndex F ((U.orderIsoOfFin hU).symm ⟨v, hv⟩)))
    have hmatch := matchingIndex_spec F ((U.orderIsoOfFin hU).symm ⟨v, hv⟩)
    rw [hindex] at hmatch
    exact hmatch
  have partner_root (F : Forest) (v : Fin n) (hv : v ∈ U) : root F (partner F v) = v :=
    (F.property.2.2.1 (partner F v)).unique (root_spec F (partner F v))
      ⟨hv, (partner_reachable F v hv).symm⟩
  let moved (F : Forest) (selected : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => if j ∈ selected then (if i = partner F j then 1 else 0) else full F i j
  have moved_det (F : Forest) : (moved F U).det = 1 := by
    have all_selected : ∀ selected : Finset (Fin n), selected ⊆ U →
        (moved F selected).det = 1 := by
      intro selected
      induction selected using Finset.induction_on with
      | empty =>
        intro hsubset
        have heq : moved F ∅ = full F := by ext i j; simp [moved]
        rw [heq]
        exact full_det F
      | @insert vertex selected hnot ih =>
        intro hsubset
        have hv : vertex ∈ U := hsubset (Finset.mem_insert_self _ _)
        have hsubset' : selected ⊆ U := fun j hj => hsubset (Finset.mem_insert_of_mem hj)
        obtain ⟨support, hsupport, hdepths, hcolumns⟩ := path_columns F (partner F vertex)
        have hvnot : vertex ∉ support := fun h => hsupport vertex h hv
        have support_disjoint (j : Fin n) (hj : j ∈ support) : j ∉ selected :=
          fun h => hsupport j hj (hsubset' h)
        let coeff := fun j : Fin n =>
          (if j = vertex then (1 : ℤ) else 0) + (if j ∈ support then 1 else 0)
        have hsum (i : Fin n) : (∑ j, coeff j • moved F selected i j) =
              if i = partner F vertex then 1 else 0 := by
          simp only [coeff, smul_eq_mul, add_mul, Finset.sum_add_distrib,
            ite_mul, one_mul, zero_mul]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
            Finset.sum_ite_mem, Finset.univ_inter]
          have hsupport_sum : (∑ j ∈ support, moved F selected i j) =
              ∑ j ∈ support, full F i j := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [moved, support_disjoint j hj]
          rw [hsupport_sum, ← hcolumns i, partner_root F vertex hv]
          simp only [moved, Matrix.of_apply, if_neg hnot, full, dif_pos hv]
          ring
        have hupdate : moved F (insert vertex selected) =
            (moved F selected).updateCol vertex
              (fun i => ∑ j, coeff j • moved F selected i j) := by
          ext i j
          rw [Matrix.updateCol_apply]
          by_cases hj : j = vertex
          · subst j
            rw [if_pos rfl, hsum]
            simp [moved]
          · rw [if_neg hj]
            simp [moved, hj]
        rw [hupdate, Matrix.det_updateCol_sum]
        simp [coeff, hvnot, ih hsubset']
    exact all_selected U (Finset.Subset.refl _)
  let incidence (p : Parent) : Matrix (Fin (n - k)) (Fin (n - k)) ℤ :=
    fun i j => (if row i = (p j).val then 1 else 0) -
      (if row i = col j then 1 else 0)
  have column_expansion (j : Fin (n - k)) : (fun i : Fin (n - k) => M (row i) (col j)) =
      ∑ a : {a : Fin n // a ≠ col j},
        M a.val (col j) •
          (fun i => (if row i = a.val then 1 else 0) -
            (if row i = col j then 1 else 0)) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    have hdiag : (∑ a : {a : Fin n // a ≠ col j}, M a.val (col j)) =
        -M (col j) (col j) := by
      have hc := hcol (col j)
      rw [← Finset.sum_compl_add_sum ({col j} : Finset (Fin n))
        (fun a => M a (col j))] at hc
      simp only [Finset.sum_singleton] at hc
      have heq : (∑ a : {a : Fin n // a ≠ col j}, M a.val (col j)) =
          ∑ a ∈ ({col j} : Finset (Fin n))ᶜ, M a (col j) := by
        exact (Finset.sum_subtype (p := fun a : Fin n => a ≠ col j)
          ({col j}ᶜ : Finset (Fin n)) (by intro a; simp)
          (fun a => M a (col j))).symm
      rw [heq]
      exact eq_neg_of_add_eq_zero_left hc
    by_cases hij : row i = col j
    · have hzero : (∑ a : {a : Fin n // a ≠ col j},
          M a.val (col j) * if col j = a.val then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        simp [Ne.symm a.property]
      simp only [hij, if_true, mul_one]
      rw [hzero, hdiag]
      simp
    · have hsingle : (∑ a : {a : Fin n // a ≠ col j},
          M a.val (col j) * if row i = a.val then 1 else 0) =
          M (row i) (col j) := by
        rw [Finset.sum_eq_single ⟨row i, hij⟩]
        · simp
        · intro a ha hne
          have hval : row i ≠ a.val := by
            intro heq
            apply hne
            exact Subtype.ext heq.symm
          simp [hval]
        · simp
      simp only [if_neg hij, mul_zero, Finset.sum_const_zero, sub_zero]
      exact hsingle.symm
  have expansion : (M.submatrix row col).det =
        ∑ p : Parent, (∏ j, M (p j).val (col j)) *
          ((incidence p).det : ℤ) := by
    rw [← Matrix.det_transpose]
    change Matrix.detRowAlternating
      (fun j i => M (row i) (col j)) = _
    have heq : (fun j i => M (row i) (col j)) =
        (fun j => ∑ a : {a : Fin n // a ≠ col j},
          M a.val (col j) •
            (fun i => (if row i = a.val then 1 else 0) -
              (if row i = col j then 1 else 0))) := funext column_expansion
    rw [heq]
    change Matrix.detRowAlternating.toMultilinearMap
      (fun j => ∑ a : {a : Fin n // a ≠ col j},
        M a.val (col j) •
          (fun i => (if row i = a.val then 1 else 0) -
            (if row i = col j then 1 else 0))) = _
    rw [Matrix.detRowAlternating.toMultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Matrix.detRowAlternating.toMultilinearMap.map_smul_univ, smul_eq_mul]
    congr 1
    change Matrix.det (Matrix.of fun i j =>
      (if row j = (p i).val then (1 : R) else 0) -
        (if row j = col i then 1 else 0)) = _
    trans ((incidence p).map (fun value => (value : R)))ᵀ.det
    · congr 1
      ext i j
      change (if row j = (p i).val then (1 : R) else 0) -
        (if row j = col i then 1 else 0) =
          (((if row j = (p i).val then (1 : ℤ) else 0) -
            (if row j = col i then 1 else 0) : ℤ) : R)
      simp only [Int.cast_sub, Int.cast_ite, Int.cast_zero, Int.cast_one]
    · rw [Matrix.det_transpose]
      exact (Int.cast_det (incidence p)).symm
  have missing_mark_coefficient (p : Parent) (vertex : Fin n)
      (hmissing : ∀ w ∈ W, ¬(graph (parentEdges p)).Reachable vertex w) :
      (incidence p).det = 0 := by
    let coeff := fun i : Fin (n - k) =>
      if (graph (parentEdges p)).Reachable vertex (row i) then (1 : ℤ) else 0
    have hv : vertex ∉ W := fun h => hmissing vertex h (SimpleGraph.Reachable.refl _)
    let index : Fin (n - k) := (Wᶜ.orderIsoOfFin
      (by simp [Finset.card_compl, hW])).symm ⟨vertex, Finset.mem_compl.mpr hv⟩
    have hindex : row index = vertex := by simp [row, index, Finset.orderEmbOfFin]
    have sum_delta (v : Fin n) : (∑ i, coeff i * if row i = v then 1 else 0) =
          if (graph (parentEdges p)).Reachable vertex v then 1 else 0 := by
      by_cases hw : v ∈ W
      · have hother (i : Fin (n - k)) : row i ≠ v := by
          intro heq
          have hi : row i ∉ W :=
            Finset.mem_compl.mp (Wᶜ.orderEmbOfFin_mem (by simp [Finset.card_compl, hW]) i)
          exact hi (heq ▸ hw)
        simp [hother, hmissing v hw]
      · let otherIndex : Fin (n - k) := (Wᶜ.orderIsoOfFin
          (by simp [Finset.card_compl, hW])).symm ⟨v, Finset.mem_compl.mpr hw⟩
        have hi : row otherIndex = v := by simp [row, otherIndex, Finset.orderEmbOfFin]
        rw [Finset.sum_eq_single otherIndex]
        · simp [coeff, hi]
        · intro i himem hne
          have hrow : row i ≠ v := by
            intro heq
            exact hne (row.injective (heq.trans hi.symm))
          simp [hrow]
        · simp
    have relation : (∑ i, coeff i • incidence p i) = 0 := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, incidence,
        mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
      rw [sum_delta, sum_delta]
      have hedge : ((p j).val, col j) ∈ parentEdges p :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hadj : (graph (parentEdges p)).Adj (p j).val (col j) :=
        ⟨(p j).property, Or.inl hedge⟩
      have heq : (graph (parentEdges p)).Reachable vertex (p j).val ↔
          (graph (parentEdges p)).Reachable vertex (col j) :=
        ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
      simp only [heq, sub_self]
    apply Matrix.det_eq_zero_of_not_linearIndependent_rows
    rw [Fintype.not_linearIndependent_iff]
    refine ⟨coeff, relation, index, ?_⟩
    simp [coeff, hindex]
  have forest_coefficient (F : Forest) : (incidence (forestParent F)).det =
        (-1 : ℤ) ^ (n + k + (∑ u ∈ U, u.val) + (∑ w ∈ W, w.val)) *
          (Equiv.Perm.sign (matching F) : ℤ) := by
    have hmoved := moved_det F
    let groupU : Fin k ⊕ Fin (n - k) ≃ Fin n :=
      (Equiv.sumCongr (U.orderIsoOfFin hU).toEquiv
        ((Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).toEquiv.trans
          (Equiv.subtypeEquivRight (by intro v; exact Finset.mem_compl)))).trans
        (Equiv.sumCompl (fun v => v ∈ U))
    let groupW : Fin k ⊕ Fin (n - k) ≃ Fin n :=
      (Equiv.sumCongr (W.orderIsoOfFin hW).toEquiv
        ((Wᶜ.orderIsoOfFin (by simp [Finset.card_compl, hW])).toEquiv.trans
          (Equiv.subtypeEquivRight (by intro v; exact Finset.mem_compl)))).trans
        (Equiv.sumCompl (fun v => v ∈ W))
    have groupU_root (a : Fin k) : groupU (Sum.inl a) = roots a := rfl
    have groupU_nonroot (j : Fin (n - k)) : groupU (Sum.inr j) = col j := rfl
    have groupW_mark (a : Fin k) : groupW (Sum.inl a) = marks a := rfl
    have groupW_nonmark (j : Fin (n - k)) : groupW (Sum.inr j) = row j := rfl
    let shuffle : Equiv.Perm (Fin n) := groupU.symm.trans groupW
    let extendedMatching : Equiv.Perm (Fin n) :=
      groupU.permCongr (Equiv.sumCongr (matching F) (Equiv.refl (Fin (n - k))))
    let sigma : Equiv.Perm (Fin n) := shuffle * extendedMatching
    have sigma_root (a : Fin k) : sigma (roots a) = marks (matching F a) := by
      rw [← groupU_root]
      simp [sigma, shuffle, extendedMatching, Equiv.permCongr_apply, groupW_mark]
    have sigma_nonroot (j : Fin (n - k)) : sigma (col j) = row j := by
      rw [← groupU_nonroot]
      simp [sigma, shuffle, extendedMatching, Equiv.permCongr_apply, groupW_nonmark]
    have sigma_partner (v : Fin n) (hv : v ∈ U) : sigma v = partner F v := by
      let index := (U.orderIsoOfFin hU).symm ⟨v, hv⟩
      have hindex : roots index = v := by simp [roots, index, Finset.orderEmbOfFin]
      have hsigma := sigma_root index
      rw [hindex] at hsigma
      simpa only [partner, dif_pos hv, index] using hsigma
    let reordered : Matrix (Fin n) (Fin n) ℤ := (moved F U).submatrix sigma id
    have reordered_lowerleft (i : Fin n) (hi : i ∉ U) (j : Fin n) (hj : j ∈ U) :
        reordered i j = 0 := by
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      change moved F U (sigma i) j = 0
      simp only [moved, Matrix.of_apply, if_pos hj, ← sigma_partner j hj,
        if_neg (sigma.injective.ne hij)]
    have getParent_col (j : Fin (n - k)) :
        getParent F (col j) (column_nonroot j) = (forestParent F j).val := by
      let index : Fin (n - k) := (Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
        ⟨col j, Finset.mem_compl.mpr (column_nonroot j)⟩
      have hindex : index = j := by
        change (Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
          ((Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])) j) = j
        exact OrderIso.symm_apply_apply _ _
      change (forestParent F index).val = (forestParent F j).val
      rw [hindex]
    have reordered_minor : reordered.submatrix col col = -(incidence (forestParent F)) := by
      ext i j
      change moved F U (sigma (col i)) (col j) = _
      rw [sigma_nonroot]
      simp only [moved, Matrix.of_apply, if_neg (column_nonroot j), full,
        dif_neg (column_nonroot j), getParent_col, Matrix.neg_apply]
      change (if row i = col j then (1 : ℤ) else 0) -
        (if row i = (forestParent F j).val then 1 else 0) =
          -((if row i = (forestParent F j).val then 1 else 0) -
            (if row i = col j then 1 else 0))
      ring
    have reordered_det : reordered.det = (-(incidence (forestParent F))).det := by
      let upperRight : Matrix (Fin k) (Fin (n - k)) ℤ := reordered.submatrix roots col
      have hblocks : reordered.submatrix groupU groupU =
          Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℤ) upperRight
            (0 : Matrix (Fin (n - k)) (Fin k) ℤ) (-(incidence (forestParent F))) := by
        ext first second
        cases first with
        | inl first =>
          cases second with
          | inl second =>
            change moved F U (sigma (roots first)) (roots second) = _
            have hmember : roots second ∈ U := U.orderEmbOfFin_mem hU second
            simp only [moved, Matrix.of_apply, if_pos hmember,
              ← sigma_partner (roots second) (U.orderEmbOfFin_mem hU second)]
            simp only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply,
              sigma.injective.eq_iff, roots.injective.eq_iff]
          | inr second => rfl
        | inr first =>
          cases second with
          | inl second =>
            exact reordered_lowerleft (col first) (column_nonroot first) (roots second)
              (U.orderEmbOfFin_mem hU second)
          | inr second => exact congrFun (congrFun reordered_minor first) second
      rw [← Matrix.det_submatrix_equiv_self groupU, hblocks,
        Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    have sign_relation : (-1 : ℤ) ^ (n - k) * (incidence (forestParent F)).det =
        (Equiv.Perm.sign sigma : ℤ) := by
      have hneg := Matrix.det_neg (incidence (forestParent F))
      rw [Fintype.card_fin] at hneg
      rw [← hneg, ← reordered_det]
      change ((moved F U).submatrix sigma id).det = _
      rw [Matrix.det_permute, hmoved, mul_one]
      simp
    have shuffle_sign : (Equiv.Perm.sign shuffle : ℤ) =
        (-1 : ℤ) ^ ((∑ u ∈ U, u.val) + (∑ w ∈ W, w.val)) := by
      let twist (S : Finset (Fin n)) (i j : Fin n) : ℤ := if i = j then 0 else
          if i ∈ S then
            if j ∈ S then (if i < j then 1 else -1) else 1
          else if j ∈ S then -1 else (if i < j then 1 else -1)
      let cross (S : Finset (Fin n)) : ℤ := ∏ j, ∏ i ∈ Finset.Iio j, twist S i j
      let triangle : ℤ := ∏ a : Fin k, (-1 : ℤ) ^ a.val
      have antisymmetric (S : Finset (Fin n)) (i j : Fin n) :
          twist S i j = -twist S j i := by
        by_cases hij : i = j
        · simp [twist, hij]
        · rcases lt_or_gt_of_ne hij with hlt | hlt <;>
            by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
            simp [twist, hij, Ne.symm hij, hi, hj, hlt, hlt.not_gt]
      have cross_inner (S : Finset (Fin n)) (j : Fin n) :
          (∏ i ∈ Finset.Iio j, twist S i j) =
            if j ∈ S then (-1 : ℤ) ^ (Finset.Iio j \ S).card else 1 := by
        have hentry (i : Fin n) (hi : i ∈ Finset.Iio j) :
            twist S i j = if j ∈ S then (if i ∈ S then 1 else -1) else 1 := by
          have hij : i < j := Finset.mem_Iio.mp hi
          by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S <;>
            simp [twist, hij.ne, hij, hiS, hjS]
        rw [Finset.prod_congr rfl hentry]
        by_cases hj : j ∈ S
        · simp only [if_pos hj]
          rw [Finset.prod_ite]
          simp [Finset.filter_notMem_eq_sdiff]
        · simp [hj]
      have cross_square (S : Finset (Fin n)) : cross S * cross S = 1 := by
        simp only [cross, cross_inner]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro j hj
        split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]
      have cross_formula (S : Finset (Fin n)) (hS : S.card = k) :
          cross S * triangle = (-1 : ℤ) ^ (∑ v ∈ S, v.val) := by
        let ascending := S.orderEmbOfFin hS
        have rank (a : Fin k) : (Finset.Iio (ascending a) ∩ S).card = a.val := by
          have himage : (Finset.Iio a).image ascending = Finset.Iio (ascending a) ∩ S := by
            ext v
            simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_inter]
            constructor
            · rintro ⟨b, hb, rfl⟩
              exact ⟨ascending.strictMono hb, S.orderEmbOfFin_mem hS b⟩
            · rintro ⟨hv, hmember⟩
              let b := (S.orderIsoOfFin hS).symm ⟨v, hmember⟩
              have hb : ascending b = v := by simp [ascending, b, Finset.orderEmbOfFin]
              exact ⟨b, ascending.lt_iff_lt.mp (hb.symm ▸ hv), hb⟩
          rw [← himage, Finset.card_image_of_injective _ ascending.injective, Fin.card_Iio]
        have counts (a : Fin k) :
            (Finset.Iio (ascending a) \ S).card + a.val = (ascending a).val := by
          simpa [rank, Fin.card_Iio] using
            Finset.card_sdiff_add_card_inter (Finset.Iio (ascending a)) S
        have hcross : cross S = ∏ a : Fin k,
            (-1 : ℤ) ^ (Finset.Iio (ascending a) \ S).card := by
          simp only [cross, cross_inner]
          rw [Finset.prod_ite_mem_eq]
          rw [← S.image_orderEmbOfFin_univ hS, Finset.prod_image]
          exact fun first _ second _ heq => ascending.injective heq
        have hsum : (∑ a : Fin k, (ascending a).val) = ∑ v ∈ S, v.val := by
          rw [← S.image_orderEmbOfFin_univ hS, Finset.sum_image]
          exact fun first _ second _ heq => ascending.injective heq
        rw [hcross]
        change (∏ a : Fin k, (-1 : ℤ) ^ (Finset.Iio (ascending a) \ S).card) *
          (∏ a : Fin k, (-1 : ℤ) ^ a.val) = _
        rw [← Finset.prod_mul_distrib]
        simp only [← pow_add, counts]
        rw [Finset.prod_pow_eq_pow_sum, hsum]
      have triangle_square : triangle * triangle = 1 := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro a ha
        simp [← pow_add, ← two_mul, pow_mul]
      have shuffle_root (a : Fin k) : shuffle (roots a) = marks a := by
        rw [← groupU_root]
        simp [shuffle, groupW_mark]
      have shuffle_nonroot (a : Fin (n - k)) : shuffle (col a) = row a := by
        rw [← groupU_nonroot]
        simp [shuffle, groupW_nonmark]
      have membership (v : Fin n) : shuffle v ∈ W ↔ v ∈ U := by
        cases heq : groupU.symm v with
        | inl a =>
          have hv : v = roots a := by
            calc
              v = groupU (groupU.symm v) := (groupU.apply_symm_apply v).symm
              _ = roots a := by rw [heq]; rfl
          rw [hv, shuffle_root]
          exact iff_of_true (W.orderEmbOfFin_mem hW a) (U.orderEmbOfFin_mem hU a)
        | inr a =>
          have hv : v = col a := by
            calc
              v = groupU (groupU.symm v) := (groupU.apply_symm_apply v).symm
              _ = col a := by rw [heq]; rfl
          have hrow : row a ∉ W := Finset.mem_compl.mp
            (Wᶜ.orderEmbOfFin_mem (by simp [Finset.card_compl, hW]) a)
          simp [hv, shuffle_nonroot, column_nonroot, hrow]
      have monotone_parts (i j : Fin n) (hij : i < j) (hpart : i ∈ U ↔ j ∈ U) :
          shuffle i < shuffle j := by
        by_cases hi : i ∈ U
        · have hj := hpart.mp hi
          let first := (U.orderIsoOfFin hU).symm ⟨i, hi⟩
          let second := (U.orderIsoOfFin hU).symm ⟨j, hj⟩
          have hfirst : roots first = i := by simp [roots, first, Finset.orderEmbOfFin]
          have hsecond : roots second = j := by simp [roots, second, Finset.orderEmbOfFin]
          rw [← hfirst, ← hsecond, shuffle_root, shuffle_root]
          exact marks.strictMono (roots.lt_iff_lt.mp (by simpa only [hfirst, hsecond] using hij))
        · have hj : j ∉ U := fun hj => hi (hpart.mpr hj)
          let first : Fin (n - k) := (Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
            ⟨i, Finset.mem_compl.mpr hi⟩
          let second : Fin (n - k) := (Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
            ⟨j, Finset.mem_compl.mpr hj⟩
          have hfirst : col first = i := by simp [col, first, Finset.orderEmbOfFin]
          have hsecond : col second = j := by simp [col, second, Finset.orderEmbOfFin]
          rw [← hfirst, ← hsecond, shuffle_nonroot, shuffle_nonroot]
          exact row.strictMono (col.lt_iff_lt.mp (by simpa only [hfirst, hsecond] using hij))
      have transported : (∏ j, ∏ i ∈ Finset.Iio j, twist W (shuffle i) (shuffle j)) =
          cross U := by
        apply Finset.prod_congr rfl
        intro j hj
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_Iio.mp hi
        have hne := shuffle.injective.ne hij.ne
        by_cases hiU : i ∈ U <;> by_cases hjU : j ∈ U
        · have hlt := monotone_parts i j hij (by simp [hiU, hjU])
          simp [twist, hne, hij.ne, hij, hlt, membership, hiU, hjU]
        · simp [twist, hne, hij.ne, membership, hiU, hjU]
        · simp [twist, hne, hij.ne, membership, hiU, hjU]
        · have hlt := monotone_parts i j hij (by simp [hiU, hjU])
          simp [twist, hne, hij.ne, hij, hlt, membership, hiU, hjU]
      have hsign : cross U = (Equiv.Perm.sign shuffle : ℤ) * cross W := by
        rw [← transported]
        exact shuffle.prod_Iio_comp_eq_sign_mul_prod (antisymmetric W)
      calc
        (Equiv.Perm.sign shuffle : ℤ) =
            (Equiv.Perm.sign shuffle : ℤ) * (cross W * cross W) := by rw [cross_square]; simp
        _ = cross U * cross W := by rw [← mul_assoc, ← hsign]
        _ = (cross U * triangle) * (cross W * triangle) := by
          rw [mul_mul_mul_comm, triangle_square, mul_one]
        _ = _ := by rw [cross_formula U hU, cross_formula W hW, pow_add]
    have hsigma : (Equiv.Perm.sign sigma : ℤ) =
        (-1 : ℤ) ^ ((∑ u ∈ U, u.val) + (∑ w ∈ W, w.val)) *
          (Equiv.Perm.sign (matching F) : ℤ) := by
      simp only [sigma, Equiv.Perm.sign_mul, Units.val_mul, shuffle_sign]
      simp only [extendedMatching, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
        Equiv.Perm.sign_refl, mul_one]
    have hkn : k ≤ n := by
      have hbound := Finset.card_le_univ U
      simpa [hU] using hbound
    have hparity : (-1 : ℤ) ^ (n - k) = (-1) ^ (n + k) := by
      have hexp : n + k = (n - k) + 2 * k := by omega
      rw [hexp, pow_add, pow_mul]
      norm_num
    have hsquare : (-1 : ℤ) ^ (n - k) * (-1) ^ (n - k) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hresult := congrArg (fun value : ℤ => (-1) ^ (n - k) * value) sign_relation
    rw [← mul_assoc, hsquare, one_mul, hsigma, hparity] at hresult
    simpa only [pow_add, mul_assoc] using hresult
  have rejected_coefficient (p : Parent) (hp : ¬isForest (parentEdges p)) :
      (incidence p).det = 0 := by
    by_cases hmissing : ∃ v, ∀ w ∈ W, ¬(graph (parentEdges p)).Reachable v w
    · obtain ⟨v, hv⟩ := hmissing
      exact missing_mark_coefficient p v hv
    · push Not at hmissing
      by_contra hnonzero
      have independent := Matrix.linearIndependent_cols_of_det_ne_zero hnonzero
      let selectedGraph (S : Finset (Fin (n - k))) :=
        graph (S.image (fun j => ((p j).val, col j)))
      let delta (v : Fin n) : Fin (n - k) → ℤ := fun i => if row i = v then 1 else 0
      have column_delta (j : Fin (n - k)) :
          (incidence p).col j = delta (p j).val - delta (col j) := rfl
      have path_span (S : Finset (Fin (n - k))) {a b : Fin n}
          (path : (selectedGraph S).Walk a b) :
          delta a - delta b ∈ Submodule.span ℤ ((incidence p).col '' (S : Set _)) := by
        induction path with
        | nil => simp
        | @cons first middle last hadj path ih =>
          have hstep : delta first - delta middle ∈
              Submodule.span ℤ ((incidence p).col '' (S : Set _)) := by
            change first ≠ middle ∧
              ((first, middle) ∈ S.image (fun j => ((p j).val, col j)) ∨
               (middle, first) ∈ S.image (fun j => ((p j).val, col j))) at hadj
            rcases hadj.2 with hedge | hedge
            · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hedge
              have hparent : (p j).val = first := congrArg Prod.fst heq
              have hhead : col j = middle := congrArg Prod.snd heq
              rw [← hparent, ← hhead, ← column_delta]
              exact Submodule.subset_span (Set.mem_image_of_mem _ hj)
            · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hedge
              have hparent : (p j).val = middle := congrArg Prod.fst heq
              have hhead : col j = first := congrArg Prod.snd heq
              have hgen : (incidence p).col j ∈
                  Submodule.span ℤ ((incidence p).col '' (S : Set _)) :=
                Submodule.subset_span (Set.mem_image_of_mem _ hj)
              rw [column_delta, hparent, hhead] at hgen
              simpa only [neg_sub] using Submodule.neg_mem _ hgen
          convert Submodule.add_mem _ hstep ih using 1
          abel
      have unjoined (S : Finset (Fin (n - k))) (j : Fin (n - k)) (hj : j ∉ S) :
          ¬(selectedGraph S).Reachable (p j).val (col j) := by
        rintro ⟨path⟩
        have hspan := path_span S path
        rw [← column_delta] at hspan
        apply independent.notMem_span j
        apply Submodule.span_mono (Set.image_mono ?_) hspan
        intro other hother heq
        exact hj (heq ▸ hother)
      have acyclic_partial (S : Finset (Fin (n - k))) : (selectedGraph S).IsAcyclic := by
        induction S using Finset.induction_on with
        | empty =>
          have hempty : selectedGraph ∅ = ⊥ := by
            ext a b
            simp [selectedGraph, graph, SimpleGraph.fromRel_adj]
          rw [hempty]
          exact SimpleGraph.isAcyclic_bot
        | @insert j S hj ih =>
          have hinsert : selectedGraph (insert j S) =
              selectedGraph S ⊔ SimpleGraph.edge (p j).val (col j) := by
            ext a b
            simp only [selectedGraph, graph, SimpleGraph.fromRel_adj, SimpleGraph.sup_adj,
              SimpleGraph.edge_adj, Finset.image_insert, Finset.mem_insert,
              Prod.mk.injEq]
            tauto
          rw [hinsert]
          exact ih.sup_edge_of_not_reachable (unjoined S j hj)
      have acyclic : (graph (parentEdges p)).IsAcyclic := acyclic_partial Finset.univ
      have edge_injective : Function.Injective (fun j : Fin (n - k) => s((p j).val, col j)) := by
        intro first second heq
        rcases Sym2.eq_iff.mp heq with hsame | hreverse
        · exact col.injective hsame.2
        · by_contra hne
          have hedge : (col first, (p first).val) ∈
              (Finset.univ.erase first).image (fun j => ((p j).val, col j)) := by
            exact Finset.mem_image.mpr ⟨second, by simp [Ne.symm hne],
              Prod.ext hreverse.2.symm hreverse.1.symm⟩
          have hadj : (selectedGraph (Finset.univ.erase first)).Adj (p first).val (col first) :=
            ⟨(p first).property, Or.inr hedge⟩
          exact unjoined (Finset.univ.erase first) first (by simp) hadj.reachable
      let G := graph (parentEdges p)
      have component_root (C : G.ConnectedComponent) : ∃! u, u ∈ U ∧ u ∈ C.supp := by
        let Heads := {j : Fin (n - k) // col j ∈ C.supp}
        let componentParent (j : Heads) : C :=
          ⟨(p j.val).val, C.mem_supp_of_adj_mem_supp j.property
            (show G.Adj (col j.val) (p j.val).val from
              ⟨(p j.val).property.symm, Or.inr
                (Finset.mem_image.mpr ⟨j.val, Finset.mem_univ _, rfl⟩)⟩)⟩
        let edgeMap (j : Heads) : C.toSimpleGraph.edgeSet :=
          ⟨s(componentParent j, (⟨col j.val, j.property⟩ : C)),
            show G.Adj (p j.val).val (col j.val) from
              ⟨(p j.val).property, Or.inl
                (Finset.mem_image.mpr ⟨j.val, Finset.mem_univ _, rfl⟩)⟩⟩
        have edgeMap_injective : Function.Injective edgeMap := by
          intro first second heq
          have hmap := congrArg (fun e : C.toSimpleGraph.edgeSet =>
            Sym2.map (fun v : C => v.val) e.val) heq
          change s((p first.val).val, col first.val) = s((p second.val).val, col second.val) at hmap
          exact Subtype.ext (edge_injective hmap)
        have edgeMap_surjective : Function.Surjective edgeMap := by
          rintro ⟨edge, hedge⟩
          obtain ⟨⟨first, second⟩, rfl⟩ := Sym2.mk_surjective edge
          change G.Adj first.val second.val at hedge
          rcases hedge.2 with hforward | hbackward
          · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hforward
            have hparent : (p j).val = first.val := congrArg Prod.fst heq
            have hhead : col j = second.val := congrArg Prod.snd heq
            have hheadC : col j ∈ C.supp := hhead.symm ▸ second.property
            refine ⟨⟨j, hheadC⟩, Subtype.ext ?_⟩
            exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hparent, Subtype.ext hhead⟩)
          · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hbackward
            have hparent : (p j).val = second.val := congrArg Prod.fst heq
            have hhead : col j = first.val := congrArg Prod.snd heq
            have hheadC : col j ∈ C.supp := hhead.symm ▸ first.property
            refine ⟨⟨j, hheadC⟩, Subtype.ext ?_⟩
            exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hparent, Subtype.ext hhead⟩)
        let headMap (j : Heads) : {v : C // v.val ∉ U} :=
          ⟨⟨col j.val, j.property⟩, column_nonroot j.val⟩
        have headMap_injective : Function.Injective headMap := by
          intro first second heq
          exact Subtype.ext (col.injective
            (congrArg (fun v : {v : C // v.val ∉ U} => v.val.val) heq))
        have headMap_surjective : Function.Surjective headMap := by
          intro v
          let j : Fin (n - k) := (Uᶜ.orderIsoOfFin (by simp [Finset.card_compl, hU])).symm
            ⟨v.val.val, Finset.mem_compl.mpr v.property⟩
          have hhead : col j = v.val.val := by simp [col, j, Finset.orderEmbOfFin]
          refine ⟨⟨j, hhead.symm ▸ v.val.property⟩, Subtype.ext (Subtype.ext hhead)⟩
        have hheads : Fintype.card Heads = Fintype.card {v : C // v.val ∉ U} :=
          Fintype.card_congr (Equiv.ofBijective headMap ⟨headMap_injective, headMap_surjective⟩)
        have hedges : Fintype.card Heads = Fintype.card C.toSimpleGraph.edgeSet :=
          Fintype.card_congr (Equiv.ofBijective edgeMap ⟨edgeMap_injective, edgeMap_surjective⟩)
        have htree := (acyclic.isTree_connectedComponent C).card_edgeFinset
        rw [SimpleGraph.edgeFinset_card] at htree
        have hpartition : Fintype.card {v : C // v.val ∈ U} +
            Fintype.card {v : C // v.val ∉ U} = Fintype.card C := by
          rw [← Fintype.card_sum]
          exact Fintype.card_congr (Equiv.sumCompl (fun v : C => v.val ∈ U))
        have hone : Fintype.card {v : C // v.val ∈ U} = 1 := by omega
        obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hone
        refine ⟨u.val.val, ⟨u.property, u.val.property⟩, ?_⟩
        intro other hother
        exact congrArg (fun v : {v : C // v.val ∈ U} => v.val.val)
          (hu ⟨⟨other, hother.2⟩, hother.1⟩)
      have uniqueRoots (v : Fin n) : ∃! u, u ∈ U ∧ G.Reachable v u := by
        obtain ⟨u, hu, huniq⟩ := component_root (G.connectedComponentMk v)
        refine ⟨u, ⟨hu.1, SimpleGraph.ConnectedComponent.exact hu.2.symm⟩, ?_⟩
        intro other hother
        exact huniq other ⟨hother.1, SimpleGraph.ConnectedComponent.sound hother.2.symm⟩
      let rootChoice (v : Fin n) : U :=
        ⟨Classical.choose (uniqueRoots v), (Classical.choose_spec (uniqueRoots v)).1.1⟩
      have rootChoice_spec (v : Fin n) : G.Reachable v (rootChoice v).val :=
        (Classical.choose_spec (uniqueRoots v)).1.2
      let markRoot (w : W) : U := rootChoice w.val
      have markRoot_surjective : Function.Surjective markRoot := by
        intro u
        obtain ⟨w, hw, hreach⟩ := hmissing u.val
        refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
        exact (uniqueRoots w).unique ⟨(rootChoice w).property, rootChoice_spec w⟩
          ⟨u.property, hreach.symm⟩
      have markRoot_injective : Function.Injective markRoot :=
        ((Fintype.bijective_iff_surjective_and_card markRoot).mpr
          ⟨markRoot_surjective, by simp [hU, hW]⟩).1
      have uniqueMarks (v : Fin n) : ∃! w, w ∈ W ∧ G.Reachable v w := by
        obtain ⟨w, hw, hreach⟩ := hmissing v
        refine ⟨w, ⟨hw, hreach⟩, ?_⟩
        intro other hother
        apply congrArg Subtype.val (markRoot_injective (a₁ := ⟨other, hother.1⟩) (a₂ := ⟨w, hw⟩) ?_)
        apply Subtype.ext
        exact (uniqueRoots v).unique
          ⟨(rootChoice other).property, hother.2.trans (rootChoice_spec other)⟩
          ⟨(rootChoice w).property, hreach.trans (rootChoice_spec w)⟩
      have incoming_unique (first second head : Fin n)
          (hfirst : (first, head) ∈ parentEdges p)
          (hsecond : (second, head) ∈ parentEdges p) : first = second := by
        obtain ⟨a, ha, heqa⟩ := Finset.mem_image.mp hfirst
        obtain ⟨b, hb, heqb⟩ := Finset.mem_image.mp hsecond
        have hheads : col a = col b := (congrArg Prod.snd heqa).trans (congrArg Prod.snd heqb).symm
        have hab := col.injective hheads
        subst b
        exact (congrArg Prod.fst heqa).symm.trans (congrArg Prod.fst heqb)
      have root_no_incoming (u : Fin n) (hu : u ∈ U) : ∀ i, (i, u) ∉ parentEdges p := by
        intro i hedge
        obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hedge
        have hhead : col j = u := congrArg Prod.snd heq
        exact column_nonroot j (hhead.symm ▸ hu)
      have directed_path {a b : Fin n} (path : G.Walk a b) : path.IsPath →
          (∀ i, (i, a) ∈ parentEdges p → i ∉ path.support) →
          ∀ dart ∈ path.darts, (dart.fst, dart.snd) ∈ parentEdges p := by
        induction path with
        | nil => simp
        | @cons first second last hadj path ih =>
          intro hpath hstart
          have hforward : (first, second) ∈ parentEdges p := by
            rcases hadj.2 with hedge | hedge
            · exact hedge
            · exact False.elim (hstart second hedge (by
                simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr path.start_mem_support))
          have hstart' : ∀ i, (i, second) ∈ parentEdges p → i ∉ path.support := by
            intro i hi
            have heq := incoming_unique i first second hi hforward
            rw [heq]
            exact (SimpleGraph.Walk.cons_isPath_iff hadj path).mp hpath |>.2
          intro dart hdart
          rw [SimpleGraph.Walk.darts_cons] at hdart
          rcases List.mem_cons.mp hdart with hdart | hdart
          · subst dart
            exact hforward
          · exact ih hpath.of_cons hstart' dart hdart
      apply hp
      refine ⟨?_, acyclic, uniqueRoots, uniqueMarks, ?_⟩
      · intro edge hedge
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hedge
        exact (p j).property
      · intro i j hedge u hu hreach
        have hj : j ∉ U := fun hj => root_no_incoming j hj i hedge
        have huj : u ≠ j := fun heq => hj (heq ▸ hu)
        have hne : i ≠ j := by
          obtain ⟨index, hindex, heq⟩ := Finset.mem_image.mp hedge
          have hparent : (p index).val = i := congrArg Prod.fst heq
          have hhead : col index = j := congrArg Prod.snd heq
          simpa [hparent, hhead] using (p index).property
        have hadj : G.Adj i j := ⟨hne, Or.inl hedge⟩
        obtain ⟨path, hpath, hlength⟩ := (hreach.trans hadj.reachable).exists_path_of_dist
        have hnil : ¬path.Nil := SimpleGraph.Walk.not_nil_of_ne huj
        have hlast := path.adj_penultimate hnil
        let dart : G.Dart := ⟨(path.penultimate, j), hlast⟩
        have hdart : dart ∈ path.darts := by
          rw [← SimpleGraph.Walk.concat_dropLast hlast, SimpleGraph.Walk.darts_concat]
          simp [dart]
        have hforward := directed_path path hpath
          (fun other hother => False.elim (root_no_incoming u hu other hother)) dart hdart
        have hi : i = path.penultimate := incoming_unique i path.penultimate j hedge hforward
        have hle := SimpleGraph.dist_le path.dropLast
        have hlen := path.length_dropLast_add_one hnil
        change G.dist u path.penultimate ≤ path.dropLast.length at hle
        change path.length = G.dist u j at hlength
        change G.dist u i < G.dist u j
        rw [hi]
        omega
  rw [expansion]
  have sum_good : (∑ p : Parent, (∏ j, M (p j).val (col j)) * ((incidence p).det : ℤ)) =
        ∑ p : GoodParent, (∏ j, M (p.val j).val (col j)) * ((incidence p.val).det : ℤ) := by
    calc
      _ = ∑ p : Parent, if isForest (parentEdges p) then
          (∏ j, M (p j).val (col j)) * ((incidence p).det : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hgood : isForest (parentEdges p)
        · rw [if_pos hgood]
        · rw [if_neg hgood, rejected_coefficient p hgood, Int.cast_zero, mul_zero]
      _ = _ := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by intro p; simp) _
  rw [sum_good]
  apply Fintype.sum_equiv forestEquiv
  intro p
  have hparent : forestParent (forestEquiv p) = p.val :=
    congrArg Subtype.val (forestEquiv.left_inv p)
  have hcoefficient := forest_coefficient (forestEquiv p)
  rw [hparent] at hcoefficient
  rw [hcoefficient]
  change _ = _ * ∏ edge ∈ parentEdges p.val, M edge.1 edge.2
  rw [edgeWeight, mul_comm]
end D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
