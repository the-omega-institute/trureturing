/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Weighted Huang defects on actual components of induced candidates. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
import Mathlib.LinearAlgebra.Matrix.Block

/-! The exterior Huang Gram defect forces singularity on actual components. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip_adj)
open Q9BoundaryGram (Interior Exterior selected_parity_card_eq_exterior_add_two)
open Q9IsotropicHuang (parity weightedLinear)
open Q9WeightedSaturation (Rows)
open Q9WeightedBoundaryGram (signed switched gram_split signed_mulVec signed_transpose)
open Q9SignedContactCells (unit_weight weighted_cross weighted_square)
open Q9WeightedSaturation (defect)
open TwoBalancedComponents (componentFinset mem_componentFinset zero_iff_of_reachable)

private abbrev Comp (U : Finset (Q 9)) :=
  ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent

private def label {U : Finset (Q 9)} {b : Bool} (x : Rows U b) : Comp U :=
  ((hypercube 9).induce (U : Set (Q 9))).connectedComponentMk x.1

private def rowEmbedding (U : Finset (Q 9)) (b : Bool) : Rows U b ↪ Q 9 :=
  ⟨fun x => x.1.1, fun _ _ h => Subtype.ext (Subtype.ext h)⟩

private theorem row_parity {U : Finset (Q 9)} {b : Bool} (x : Rows U b) :
    parity (x.1.1) = b := (Finset.mem_filter.mp x.property).2

private def signedInterior {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool) {ι : Type*} (r : ι → Q 9) :
    Matrix ι (Interior U b) R :=
  (signed w).submatrix r (fun y => y.1.1)

private def signedDefect {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool) {ι : Type*} [DecidableEq ι] (r : ι → Q 9) :
    Matrix ι ι R := defect w (signedInterior w U b r)

private theorem signed_gram {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool) {ι : Type*} [DecidableEq ι] (r : ι ↪ Q 9)
    (hr : ∀ i, parity (r i) = b) :
    let K := (signed w).submatrix r (fun y : Exterior U b => y.1.1)
    K * Kᵀ = signedDefect w U b r := by
  have h := gram_split w (fun _ => 1) (by simp) U b r hr
  dsimp only at h ⊢
  have he : switched w (fun _ => 1) = signed w := by
    ext i j
    simp [switched]
  rw [he] at h
  exact h

private theorem signed_defect_det_eq_zero_of_width {R : Type*} [CommRing R] [IsDomain R]
    (w : Fin 9 → R) (U : Finset (Q 9)) (b : Bool)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι ↪ Q 9)
    (hr : ∀ i, parity (r i) = b) (hn : Fintype.card (Exterior U b) < Fintype.card ι) :
    (signedDefect w U b r).det = 0 := by
  let K := (signed w).submatrix r (fun y : Exterior U b => y.1.1)
  rw [← signed_gram w U b r hr]
  by_contra h
  have hfull := Matrix.rank_of_det_ne_zero h
  have hle := (Matrix.rank_mul_le_left K Kᵀ).trans (Matrix.rank_le_card_width K)
  exact (not_le_of_gt hn) (hfull ▸ hle)

private theorem signed_eval_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Fin 9 → ℝ) (U : Finset (Q 9)) (b : Bool) (r : ι → Q 9) :
    MvPolynomial.eval v (signedDefect MvPolynomial.X U b r).det =
      (signedDefect v U b r).det := by
  let e := MvPolynomial.eval v
  have hM : (signedInterior MvPolynomial.X U b r).map e = signedInterior v U b r := by
    ext i j
    change e (signed MvPolynomial.X (r i) j.1.1) = signed v (r i) j.1.1
    simp only [signed, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [e]
  have hq : e (∑ a : Fin 9, (MvPolynomial.X a) ^ 2) = ∑ a, v a ^ 2 := by
    simp only [map_sum, map_pow, e, MvPolynomial.eval_X]
  change e _ = _
  rw [RingHom.map_det]
  congr 1
  change (signedDefect MvPolynomial.X U b r).map e = signedDefect v U b r
  unfold signedDefect defect
  rw [Matrix.map_sub e (map_sub e), Matrix.map_smul' e _ _ (map_mul e),
    Matrix.map_one e (map_zero e) (map_one e), hq, Matrix.map_mul, Matrix.transpose_map, hM]

private theorem signed_zero {R : Type*} [CommRing R] (w : Fin 9 → R) {x y : Q 9}
    (h : ¬ (hypercube 9).Adj x y) : signed w x y = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  refine ite_eq_right ?_
  rintro rfl
  exact h (flip_adj x a)

private theorem defect_off_component {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool) (i j : Rows U b) (h : label i ≠ label j) :
    signedDefect w U b (rowEmbedding U b) i j = 0 := by
  classical
  have hij : i ≠ j := fun e => h (congrArg label e)
  simp only [signedDefect, defect, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_eq_right hij, smul_zero, zero_sub, neg_eq_zero, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_eq_zero
  intro k _
  change signed w i.1.1 k.1.1 * signed w j.1.1 k.1.1 = 0
  by_cases hi : (hypercube 9).Adj i.1.1 k.1.1
  · have hj : ¬ (hypercube 9).Adj j.1.1 k.1.1 := by
      intro hj
      let G := (hypercube 9).induce (U : Set (Q 9))
      let ky : (U : Set (Q 9)) := ⟨k.1.1, k.property⟩
      exact h ((SimpleGraph.ConnectedComponent.sound (show G.Reachable i.1 ky from
        (show G.Adj i.1 ky from hi).reachable)).trans
        (SimpleGraph.ConnectedComponent.sound (show G.Reachable j.1 ky from
          (show G.Adj j.1 ky from hj).reachable)).symm)
    rw [signed_zero w hj, mul_zero]
  · rw [signed_zero w hi, zero_mul]

private theorem signed_defect_restrict {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool) {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (r : ι → Q 9) (e : κ ↪ ι) :
    (signedDefect w U b r).submatrix e e = signedDefect w U b (r ∘ e) := by
  ext i j
  simp only [signedDefect, defect, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    e.injective.eq_iff]
  rfl

/-- The signed Huang defect restricted to one actual component and one parity. -/
def componentDefect {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    Matrix {i : Rows U b // label i = C} {i : Rows U b // label i = C} R :=
  (signedDefect w U b (rowEmbedding U b)).toSquareBlock label C

open Classical in
/-- The vertices of an actual component on a specified cube parity. -/
def componentParityFinset (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) : Finset (Q 9) :=
  (componentFinset U C).filter fun x => parity x = b

private def componentRowEquiv (U : Finset (Q 9)) (b : Bool) (C : Comp U) :
    {i : Rows U b // label i = C} ≃ ↥(componentParityFinset U b C) := by
  classical
  let f (i : {i : Rows U b // label i = C}) : ↥(componentParityFinset U b C) :=
    ⟨i.1.1.1, Finset.mem_filter.mpr
      ⟨(mem_componentFinset U C _).mpr ⟨i.1.1.property, i.property⟩, row_parity i.1⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    have hv : i.1.1.1 = j.1.1.1 := congrArg (fun x : ↥(componentParityFinset U b C) => x.1) h
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  · intro x
    obtain ⟨hx, hp⟩ := Finset.mem_filter.mp x.property
    obtain ⟨hxU, hxC⟩ := (mem_componentFinset U C _).mp hx
    exact ⟨⟨⟨⟨x.1, hxU⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩, hxC⟩,
      Subtype.ext rfl⟩

open Classical in
/-- The determinant of an actual component defect uses only its signed block
between the two cube parities. -/
theorem componentDefect_det_eq {R : Type*} [CommRing R] (w : Fin 9 → R)
    (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    (componentDefect w U b C).det =
      (defect w ((signed w).submatrix
        (fun x : ↥(componentParityFinset U b C) => x.1)
        (fun y : ↥(componentParityFinset U (!b) C) => y.1))).det := by
  classical
  let e := componentRowEquiv U b C
  rw [← Matrix.det_reindex_self e]
  congr 1
  let T := componentParityFinset U (!b) C
  let column (y : ↥T) : Interior U b :=
    ⟨⟨y.1, by
        have hp := (Finset.mem_filter.mp y.property).2
        exact (Bool.not_eq_iff.mp hp.symm).symm⟩,
      ((mem_componentFinset U C _).mp (Finset.mem_filter.mp y.property).1).choose⟩
  have hrow (x : ↥(componentParityFinset U b C)) :
      rowEmbedding U b (e.symm x).1 = x.1 :=
    congrArg Subtype.val (e.apply_symm_apply x)
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, componentDefect,
    Matrix.toSquareBlock_def, signedDefect, defect, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Subtype.coe_inj, e.symm.injective.eq_iff, Matrix.mul_apply,
    Matrix.transpose_apply, signedInterior, hrow]
  congr 1
  symm
  refine Fintype.sum_of_injective column (fun _ _ h => Subtype.ext
    (congrArg (fun k : Interior U b => k.1.1) h)) _ _ ?_ (fun _ => rfl)
  intro k hk
  have hki : ¬ (hypercube 9).Adj i.1 k.1.1 := by
    intro hadj
    obtain ⟨hiU, hiC⟩ := (mem_componentFinset U C _).mp (Finset.mem_filter.mp i.property).1
    have hkC : (⟨k.1.1, k.property⟩ : (U : Set (Q 9))) ∈ C.supp :=
      (C.mem_supp_congr_adj (show ((hypercube 9).induce (U : Set (Q 9))).Adj
        ⟨i.1, hiU⟩ ⟨k.1.1, k.property⟩ from hadj)).mp hiC
    have hp : parity k.1.1 = !b := Bool.eq_not_of_ne k.1.property
    have hT : k.1.1 ∈ T := Finset.mem_filter.mpr
      ⟨(mem_componentFinset U C _).mpr ⟨k.property, hkC⟩, hp⟩
    exact hk ⟨⟨k.1.1, hT⟩, Subtype.ext (Subtype.ext rfl)⟩
  rw [signed_zero w hki, zero_mul]

private theorem unit_kernel_extension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Finset (Q 9)) (b : Bool) (r : ι ↪ Q 9)
    (hr : ∀ i, parity (r i) = b) (hU : ∀ i, r i ∈ U)
    (u : ι → ℝ) (hu : signedDefect (fun _ => (1 : ℝ)) U b r *ᵥ u = 0) :
    ∃ z : Q 9 → ℝ, (∀ x ∉ U, z x = 0) ∧
      weightedLinear (fun _ => (1 : ℝ)) z = (3 : ℝ) • z ∧
      ∀ x, parity x = b → z x = Function.extend r u 0 x := by
  let w : Fin 9 → ℝ := fun _ => 1
  let K := (signed w).submatrix r (fun y : Exterior U b => y.1.1)
  have hker : u ∈ LinearMap.ker ((Kᵀ)ᵀ * Kᵀ).mulVecLin := by
    rw [Matrix.transpose_transpose, signed_gram w U b r hr,
      LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hu
  rw [Matrix.ker_mulVecLin_transpose_mul_self Kᵀ] at hker
  have hKu : Kᵀ *ᵥ u = 0 := hker
  let f := Function.extend r u 0
  have hfzero (x : Q 9) (hx : ¬ ∃ i, r i = x) : f x = 0 :=
    Function.extend_apply' _ _ _ hx
  have hfb (x : Q 9) (hx : parity x ≠ b) : f x = 0 :=
    hfzero x (by rintro ⟨i, rfl⟩; exact hx (hr i))
  have hcross (x : Q 9) (hx : x ∉ U) : weightedLinear w f x = 0 := by
    by_cases hxb : parity x = b
    · exact weighted_cross w hfb x (by rw [hxb]; cases b <;> decide)
    · let y : Exterior U b := ⟨⟨x, hxb⟩, hx⟩
      rw [← signed_mulVec]
      change (∑ a, signed w x a * f a) = 0
      calc
        _ = ∑ i, signed w x (r i) * f (r i) := by
          symm
          exact Fintype.sum_of_injective r r.injective _ _
            (fun a ha => by rw [hfzero a ha, mul_zero]) (fun _ => rfl)
        _ = (Kᵀ *ᵥ u) y := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show f (r i) = u i from r.injective.extend_apply _ _ i]
          exact congrArg (fun t => t * u i)
            (congrFun (congrFun (signed_transpose w) (r i)) x)
        _ = 0 := congrFun hKu y
  let z := f + (1 / 3 : ℝ) • weightedLinear w f
  have hsq : weightedLinear w (weightedLinear w f) = (9 : ℝ) • f := by
    simpa [w] using weighted_square w f
  refine ⟨z, ?_, ?_, ?_⟩
  · intro x hx
    change f x + (1 / 3 : ℝ) * weightedLinear w f x = 0
    rw [hcross x hx, hfzero x (by rintro ⟨i, rfl⟩; exact hx (hU i)), mul_zero, add_zero]
  · change weightedLinear w z = (3 : ℝ) • z
    dsimp only [z]
    rw [map_add, map_smul, hsq, smul_add, smul_smul, smul_smul]
    norm_num [add_comm]
  · intro x hx
    change f x + (1 / 3 : ℝ) * weightedLinear w f x = f x
    rw [weighted_cross w hfb x (by rw [hx]; cases b <;> decide), mul_zero, add_zero]

private def rootedRowInclusion {U : Finset (Q 9)} {b : Bool} (root : Rows U b) (C : Comp U) :
    {i : {i : Rows U b // i ≠ root} // label i.1 = C} ↪ Rows U b :=
  ⟨fun i => i.1.1, fun _ _ h => Subtype.ext (Subtype.ext h)⟩

open Classical in
private theorem rooted_component_det_ne_zero
    (U : Finset (Q 9)) (b : Bool)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (root : Rows U b) (C : Comp U) (hroot : label root = C) :
    (signedDefect (fun _ => (1 : ℝ)) U b
      ((rowEmbedding U b) ∘ (rootedRowInclusion root C))).det ≠ 0 := by
  classical
  let r := (rootedRowInclusion root C).trans (rowEmbedding U b)
  intro hdet
  obtain ⟨u, hne, hu⟩ := (Matrix.exists_mulVec_eq_zero_iff
    (M := signedDefect (fun _ => (1 : ℝ)) U b r)).mpr hdet
  obtain ⟨z, hz, he, hval⟩ :=
    unit_kernel_extension U b r (fun i => row_parity i.1.1) (fun i => i.1.1.1.property) u hu
  have hzr : z root.1.1 = 0 := by
    rw [hval _ (row_parity root)]
    apply Function.extend_apply'
    rintro ⟨i, hi⟩
    exact i.1.property (Subtype.ext (Subtype.ext hi))
  apply hne
  funext i
  have hreach : ((hypercube 9).induce (U : Set (Q 9))).Reachable root.1 i.1.1.1 :=
    SimpleGraph.ConnectedComponent.exact (hroot.trans i.property.symm)
  have hzi := (zero_iff_of_reachable U z hdeg hz ((unit_weight z).symm.trans he) hreach).mp hzr
  rw [hval _ (row_parity i.1.1)] at hzi
  change Function.extend r u 0 (r i) = 0 at hzi
  rwa [r.injective.extend_apply] at hzi

open Classical in
private theorem two_singular_blocks {R ι α : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] [DecidableEq ι] [decEq : DecidableEq α] (order : Nonempty (LinearOrder α))
    (A : Matrix ι ι R) (c : ι → α)
    (hoff : ∀ i j, c i ≠ c j → A i j = 0) (hdet : A.det = 0)
    (hdel : ∀ r : ι, (A.toSquareBlockProp (fun i => i ≠ r)).det = 0)
    (hminor : ∀ a, (A.toSquareBlock c a).det = 0 →
      ∃ r, c r = a ∧
        (((A.toSquareBlockProp (fun i => i ≠ r)).toSquareBlock (fun i => c i.1) a).det ≠ 0)) :
    ∃ a b, a ≠ b ∧ (A.toSquareBlock c a).det = 0 ∧ (A.toSquareBlock c b).det = 0 := by
  classical
  let : LinearOrder α := Classical.choice order
  let : DecidableEq α := decEq
  have htri : A.BlockTriangular c := fun i j hij => hoff i j (ne_of_gt hij)
  rw [htri.det] at hdet
  obtain ⟨a, _, ha⟩ := Finset.prod_eq_zero_iff.mp hdet
  obtain ⟨r, hr, hm⟩ := hminor a ha
  let B := A.toSquareBlockProp (fun i => i ≠ r)
  let d : {i : ι // i ≠ r} → α := fun i => c i.1
  have htri' : B.BlockTriangular d := fun i j hij => hoff i.1 j.1 (ne_of_gt hij)
  have hd := hdel r
  change B.det = 0 at hd
  rw [htri'.det] at hd
  obtain ⟨b, _, hb⟩ := Finset.prod_eq_zero_iff.mp hd
  have hba : b ≠ a := by rintro rfl; exact hm hb
  let e : {i : {i : ι // i ≠ r} // d i = b} ≃ {i : ι // c i = b} :=
    Equiv.subtypeSubtypeEquivSubtype (p := fun i => i ≠ r) (q := fun i => c i = b)
      (fun {i} hi h => hba (hi.symm.trans ((congrArg c h).trans hr)))
  have he : (B.toSquareBlock d b) = (A.toSquareBlock c b).submatrix e e := rfl
  rw [he, Matrix.det_submatrix_equiv_self] at hb
  exact ⟨a, b, hba.symm, ha, hb⟩

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 500000 in
-- Elaborating the principal submatrices reduces several nested subtype indices.
open Classical in
/-- In every induced subcubic 258-vertex candidate, two distinct actual components
have singular signed Huang defects at every real coordinate weight. For each
retained parity the components are chosen before the weights are specialized. -/
theorem exists_two_weighted_singular_components (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (b : Bool) :
    ∃ C D : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      C ≠ D ∧ ∀ v : Fin 9 → ℝ,
        (componentDefect v U b C).det = 0 ∧ (componentDefect v U b D).det = 0 := by
  classical
  let w : Fin 9 → MvPolynomial (Fin 9) ℝ := MvPolynomial.X
  let r := rowEmbedding U b
  let A := signedDefect w U b r
  have hn : Fintype.card (Rows U b) = Fintype.card (Exterior U b) + 2 :=
    (Fintype.card_coe _).trans (selected_parity_card_eq_exterior_add_two U hU b)
  have hdet : A.det = 0 :=
    signed_defect_det_eq_zero_of_width w U b r row_parity (by omega)
  have hdel (i : Rows U b) : (A.toSquareBlockProp (fun j => j ≠ i)).det = 0 := by
    let e : {j : Rows U b // j ≠ i} ↪ Rows U b := ⟨Subtype.val, Subtype.val_injective⟩
    change (A.submatrix e e).det = 0
    rw [signed_defect_restrict]
    apply signed_defect_det_eq_zero_of_width w U b (e.trans r) (fun j => row_parity j.1)
    rw [Fintype.card_subtype_compl (fun j : Rows U b => j = i), Fintype.card_subtype_eq]
    omega
  have hminor (C : Comp U) (hC : (A.toSquareBlock label C).det = 0) :
      ∃ i, label i = C ∧
        ((A.toSquareBlockProp (fun j => j ≠ i)).toSquareBlock
          (fun j => label j.1) C).det ≠ 0 := by
    have : Nonempty {i : Rows U b // label i = C} := by
      by_cases h : Nonempty {i : Rows U b // label i = C}
      · exact h
      · have : IsEmpty {i : Rows U b // label i = C} := ⟨fun i => h ⟨i⟩⟩
        rw [Matrix.det_isEmpty] at hC
        exact (one_ne_zero hC).elim
    let i : {i : Rows U b // label i = C} := Classical.choice inferInstance
    refine ⟨i.1, i.2, ?_⟩
    change (A.submatrix (rootedRowInclusion i.1 C) (rootedRowInclusion i.1 C)).det ≠ 0
    rw [signed_defect_restrict]
    intro hz
    have hv := signed_eval_det (fun _ => 1) U b (r ∘ rootedRowInclusion i.1 C)
    rw [← show w = MvPolynomial.X from rfl, hz, map_zero] at hv
    exact rooted_component_det_ne_zero U b hdeg i.1 C i.2 hv.symm
  have hblocks : ∃ C D : Comp U, C ≠ D ∧
      (A.toSquareBlock label C).det = 0 ∧ (A.toSquareBlock label D).det = 0 := by
    let : Fintype (Comp U) := Fintype.ofFinite _
    let e := Fintype.equivFin (Comp U)
    refine @two_singular_blocks (MvPolynomial (Fin 9) ℝ) (Rows U b) (Comp U)
      _ _ _ _ (Classical.decEq _) ⟨LinearOrder.lift' e e.injective⟩
      A (@label U b) ?_ hdet hdel ?_
    · exact defect_off_component w U b
    · exact hminor
  obtain ⟨C, D, hCD, hC, hD⟩ := hblocks
  have hspecial (K : Comp U) (hK : (componentDefect w U b K).det = 0)
      (v : Fin 9 → ℝ) : (componentDefect v U b K).det = 0 := by
    let e : {i : Rows U b // label i = K} ↪ Rows U b := ⟨Subtype.val, Subtype.val_injective⟩
    change ((signedDefect w U b r).submatrix e e).det = 0 at hK
    change ((signedDefect v U b r).submatrix e e).det = 0
    rw [signed_defect_restrict] at hK ⊢
    have he := signed_eval_det v U b (r ∘ e)
    rw [← show w = MvPolynomial.X from rfl, hK, map_zero] at he
    exact he.symm
  exact ⟨C, D, hCD, fun v => ⟨hspecial C hC v, hspecial D hD v⟩⟩

#print axioms exists_two_weighted_singular_components

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
