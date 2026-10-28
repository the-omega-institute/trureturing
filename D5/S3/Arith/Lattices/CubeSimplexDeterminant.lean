/- GID: D5/S3/Arith/Lattices/CubeSimplexDeterminant
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/CubeSimplexDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cube simplex determinants attain their maxima at sign matrices. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none; mathematical owners are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17570.
abs_affine_le_endpoints: proof_shape: bind-only; escape_witness: none; consumers: separately_affine_cube_vertex.
separately_affine_cube_vertex: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CubeSimplexDeterminant.0.D5.S3.Arith.Lattices.CubeSimplexDeterminant.separately_affine_cube_vertex; consumers: augmented_det_cube_vertex.
signMatrix: proof_shape: bind-only; escape_witness: none; consumers: augmented_det_cube_vertex, _proof_1_4, exists_maximizing_sign_simplex, delta, _proof_1_2, augmented_det_unit_bound.
delta: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, _proof_1_4, exists_maximizing_sign_simplex, result, _proof_1_1, augmented_det_integer_box_bound, D_lower_eventually, D_upper_eventually, delta_pos, D_upper_bound, augmented_det_box_bound, _proof_1_2, augmented_det_unit_bound, girard_plagne_box_limit.
det_update_entry_affine: proof_shape: bind-only; escape_witness: none; consumers: augmented_det_cube_vertex.
augment_update_flat: proof_shape: bind-only; escape_witness: none; consumers: augmented_det_cube_vertex.
augmented_det_cube_vertex: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CubeSimplexDeterminant.0.D5.S3.Arith.Lattices.CubeSimplexDeterminant.separately_affine_cube_vertex; consumers: augmented_det_unit_bound.
augment_map: proof_shape: bind-only; escape_witness: none; consumers: augmented_det_integer_box_bound, normalized_pencil_det_limit, augmented_det_unit_bound.
augmented_det_unit_bound: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CubeSimplexDeterminant.0.D5.S3.Arith.Lattices.CubeSimplexDeterminant.separately_affine_cube_vertex; consumers: augmented_det_box_bound.
augmented_det_smul: proof_shape: bind-only; escape_witness: none; consumers: normalized_pencil_det_limit, augmented_det_box_bound.
augmented_det_box_bound: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CubeSimplexDeterminant.0.D5.S3.Arith.Lattices.CubeSimplexDeterminant.separately_affine_cube_vertex; consumers: augmented_det_integer_box_bound.
augmented_det_integer_box_bound: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CubeSimplexDeterminant.0.D5.S3.Arith.Lattices.CubeSimplexDeterminant.separately_affine_cube_vertex; consumers: lengths_upper_bound, exists_maximizing_sign_simplex, delta_pos.
affineAugment: proof_shape: bind-only; escape_witness: none; consumers: affineAugment_det, augmented_det_affine, augment_affine_eq.
affineAugment_det: proof_shape: bind-only; escape_witness: none; consumers: augmented_det_affine.
augment_affine_eq: proof_shape: bind-only; escape_witness: none; consumers: augmented_det_affine.
augmented_det_affine: proof_shape: bind-only; escape_witness: none; consumers: interiorSimplex_det.
flipColumn: proof_shape: bind-only; escape_witness: none; consumers: exists_maximizing_sign_simplex, det_flipColumn.
det_replace_column_e0: proof_shape: bind-only; escape_witness: none; consumers: det_flipColumn.
det_flipColumn: proof_shape: bind-only; escape_witness: none; consumers: exists_maximizing_sign_simplex.
standardSimplex: proof_shape: bind-only; escape_witness: none; consumers: standardSimplex_det, delta_pos.
standardSimplex_det: proof_shape: bind-only; escape_witness: none; consumers: delta_pos.
delta_pos: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CubeSimplexDeterminant.0.D5.S3.Arith.Lattices.CubeSimplexDeterminant.separately_affine_cube_vertex; consumers: exists_maximizing_sign_simplex.
exists_maximizing_sign_simplex: proof_shape: content; escape_witness: D5.S3.Arith.Lattices.CubeSimplexDeterminant.exists_maximizing_sign_simplex; consumers: D_lower_eventually.
columns_injective_of_augmented_det: proof_shape: bind-only; escape_witness: none; consumers: primitive_cofactor_admissible.
fromWeights_support_card: proof_shape: bind-only; escape_witness: none; consumers: primitive_cofactor_admissible.
primitive_cofactor_admissible: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: exists_asymptotic_lower_family.
-/

import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic

noncomputable section
namespace D5.S3.Arith.Lattices.CubeSimplexDeterminant
open D5.S3.Arith.Lattices.CofactorKernel

open scoped BigOperators
open Matrix

private theorem abs_affine_le_endpoints (a b t : ℝ) (ht : |t| ≤ 1) :
    |a*t+b| ≤ max |a*(-1)+b| |a*1+b| := by
  rcases abs_le.mp ht with ⟨hlo, hhi⟩
  by_cases ha : 0 ≤ a
  · apply abs_le_max_abs_abs <;> nlinarith
  · rw [max_comm]
    apply abs_le_max_abs_abs <;> nlinarith

private theorem separately_affine_cube_vertex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ)
    (hF : ∀ x i, ∃ a b : ℝ, ∀ t,
      F (Function.update x i t) = a*t+b)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∃ y : ι → ℝ, (∀ i, y i = -1 ∨ y i = 1) ∧ |F x| ≤ |F y| := by
  classical
  have aux (s : Finset ι) : ∀ x : ι → ℝ, (∀ i, |x i| ≤ 1) →
      ∃ y : ι → ℝ, (∀ i ∈ s, y i = -1 ∨ y i = 1) ∧
        (∀ i ∉ s, y i = x i) ∧ |F x| ≤ |F y| := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      exact ⟨x, by simp, by simp, le_rfl⟩
    | @insert i s his ih =>
      intro x hx
      obtain ⟨a,b,hab⟩ := hF x i
      have hle : |F x| ≤ max |F (Function.update x i (-1))|
          |F (Function.update x i 1)| := by
        rw [hab (-1), hab 1, ← Function.update_eq_self i x]
        rw [hab (x i)]
        exact abs_affine_le_endpoints a b (x i) (hx i)
      obtain ⟨e, he, heF⟩ : ∃ e : ℝ, (e = -1 ∨ e = 1) ∧
          |F x| ≤ |F (Function.update x i e)| := by
        rcases le_max_iff.mp hle with h | h
        · exact ⟨-1, Or.inl rfl, h⟩
        · exact ⟨1, Or.inr rfl, h⟩
      have hx' : ∀ j, |Function.update x i e j| ≤ 1 := by
        intro j
        by_cases hij : j = i
        · subst j
          rcases he with rfl | rfl <;> norm_num
        · simpa [hij] using hx j
      obtain ⟨y, hys, hyo, hFy⟩ := ih (Function.update x i e) hx'
      refine ⟨y, ?_, ?_, heF.trans hFy⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          rw [hyo i his]
          simpa using he
        · exact hys j hj
      · intro j hj
        rw [hyo j (fun h => hj (Finset.mem_insert_of_mem h))]
        have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
        simp [hji]
  obtain ⟨y, hys, hyo, hFy⟩ := aux Finset.univ x hx
  exact ⟨y, fun i => hys i (Finset.mem_univ i), hFy⟩

def signMatrix (d : ℕ) (V : Matrix (Fin d) (Fin (d+1)) Bool) :
    Matrix (Fin d) (Fin (d+1)) ℤ := fun i j => if V i j then 1 else -1

def delta (d : ℕ) : ℕ :=
  Finset.univ.sup (fun V : Matrix (Fin d) (Fin (d+1)) Bool =>
    (augment (signMatrix d V)).det.natAbs)

private theorem det_update_entry_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (i j : ι) : ∃ a b : ℝ, ∀ t : ℝ,
    (N.updateRow i (Function.update (N i) j t)).det = a*t+b := by
  refine ⟨(N.updateRow i (Pi.single j 1)).det,
    (N.updateRow i (Function.update (N i) j 0)).det, fun t => ?_⟩
  have hr : Function.update (N i) j t =
      t • Pi.single j 1 + Function.update (N i) j 0 := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]
  rw [hr, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  ring

private theorem augment_update_flat {d : ℕ}
    (x : (Fin d × Fin (d+1)) → ℝ) (p : Fin d × Fin (d+1)) (t : ℝ) :
    augment (Matrix.of (Function.curry (Function.update x p t))) =
      (augment (Matrix.of (Function.curry x))).updateRow p.1.succ
        (Function.update (Function.curry x p.1) p.2 t) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [augment_zero, Matrix.updateRow_ne (Ne.symm (Fin.succ_ne_zero _)), augment_zero]
  · by_cases hi : i = p.1
    · subst i
      by_cases hj : j = p.2
      · subst j
        rw [augment_succ, Matrix.updateRow_self]
        simp [Function.curry, Function.update_apply]
      · rw [augment_succ, Matrix.updateRow_self]
        simp [Function.curry, Function.update_apply, Prod.ext_iff, hj]
    · rw [augment_succ, Matrix.updateRow_ne (Fin.succ_inj.ne.mpr hi), augment_succ]
      simp [Function.curry, Function.update_apply, Prod.ext_iff, hi]

private theorem augmented_det_cube_vertex {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℝ) (hM : ∀ i j, |M i j| ≤ 1) :
    ∃ V : Matrix (Fin d) (Fin (d+1)) Bool,
      |(augment M).det| ≤ |(augment ((signMatrix d V).map (Int.castRingHom ℝ))).det| := by
  classical
  let F : ((Fin d × Fin (d+1)) → ℝ) → ℝ := fun x => (augment (Matrix.of (Function.curry x))).det
  have hF : ∀ x i, ∃ a b : ℝ, ∀ t,
      F (Function.update x i t) = a*t+b := by
    intro x p
    obtain ⟨a,b,hab⟩ := det_update_entry_affine (augment (Matrix.of (Function.curry x))) p.1.succ p.2
    refine ⟨a,b, fun t => ?_⟩
    change (augment (Matrix.of (Function.curry (Function.update x p t)))).det = _
    rw [augment_update_flat]
    exact hab t
  obtain ⟨y, hy, hFy⟩ := separately_affine_cube_vertex F hF (Function.uncurry M)
    (fun p => hM p.1 p.2)
  let V : Matrix (Fin d) (Fin (d+1)) Bool := fun i j => decide (y (i,j) = 1)
  refine ⟨V, ?_⟩
  have he : (signMatrix d V).map (Int.castRingHom ℝ) = Matrix.of (Function.curry y) := by
    ext i j
    rcases hy (i,j) with h | h <;> norm_num [Matrix.map, signMatrix, V, h, Function.curry]
  rw [he]
  change |(augment M).det| ≤ |(augment (Matrix.of (Function.curry y))).det| at hFy
  exact hFy


theorem augment_map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (f : R →+* S) (M : Matrix (Fin d) (Fin (d+1)) R) :
    augment (M.map f) = (augment M).map f := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [augment_zero, Matrix.map_apply, map_one]
  · simp only [augment_succ, Matrix.map_apply]

private theorem augmented_det_unit_bound {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℝ) (hM : ∀ i j, |M i j| ≤ 1) :
    |(augment M).det| ≤ (delta d : ℝ) := by
  obtain ⟨V, hV⟩ := augmented_det_cube_vertex M hM
  have hs : (augment (signMatrix d V)).det.natAbs ≤ delta d := by
    unfold delta
    exact Finset.le_sup (f := fun V : Matrix (Fin d) (Fin (d+1)) Bool =>
      (augment (signMatrix d V)).det.natAbs) (Finset.mem_univ V)
  have hr : |((augment (signMatrix d V)).det : ℝ)| ≤ (delta d : ℝ) := by
    have h : (((augment (signMatrix d V)).det.natAbs : ℕ) : ℝ) ≤ (delta d : ℝ) := by
      exact_mod_cast hs
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  rw [augment_map] at hV
  change |(augment M).det| ≤ |((augment (signMatrix d V)).map (fun z : ℤ => (z : ℝ))).det| at hV
  rw [← Int.cast_det] at hV
  exact hV.trans hr

theorem augmented_det_smul {R : Type*} [CommRing R] {d : ℕ}
    (c : R) (M : Matrix (Fin d) (Fin (d+1)) R) :
    (augment (c • M)).det = c^d * (augment M).det := by
  let v : Fin (d+1) → R := Fin.cases 1 (fun _ => c)
  have he : augment (c • M) = Matrix.of (fun i j => v i * augment M i j) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [v, augment_zero]
    · simp [v, augment_succ, Matrix.smul_apply]
  rw [he, Matrix.det_mul_column]
  simp [v, Fin.prod_univ_succ, Fin.prod_const]


private theorem augmented_det_box_bound {d : ℕ} (m : ℝ) (hm : 0 < m)
    (M : Matrix (Fin d) (Fin (d+1)) ℝ) (hM : ∀ i j, |M i j| ≤ m) :
    |(augment M).det| ≤ (delta d : ℝ) * m^d := by
  let N : Matrix (Fin d) (Fin (d+1)) ℝ := m⁻¹ • M
  have hN : ∀ i j, |N i j| ≤ 1 := by
    intro i j
    change |m⁻¹ * M i j| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hm)]
    calc
      m⁻¹ * |M i j| ≤ m⁻¹ * m :=
        mul_le_mul_of_nonneg_left (hM i j) (inv_nonneg.mpr hm.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hm)
  have h := augmented_det_unit_bound N hN
  have he : M = m • N := by simp [N, smul_smul, ne_of_gt hm]
  rw [he, augmented_det_smul, abs_mul, abs_of_nonneg (pow_nonneg hm.le d)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left h (pow_nonneg hm.le d)

theorem augmented_det_integer_box_bound {d m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin d) (Fin (d+1)) ℤ) (hM : ∀ i j, |M i j| ≤ m) :
    |(augment M).det| ≤ (delta d : ℤ) * (m : ℤ)^d := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hMr : ∀ i j, |(M.map (Int.castRingHom ℝ)) i j| ≤ (m : ℝ) := by
    intro i j
    change |(M i j : ℝ)| ≤ (m : ℝ)
    exact_mod_cast hM i j
  have hr := augmented_det_box_bound (m : ℝ) hm' (M.map (Int.castRingHom ℝ)) hMr
  rw [augment_map] at hr
  change |((augment M).map (fun z : ℤ => (z : ℝ))).det| ≤ (delta d : ℝ) * (m : ℝ)^d at hr
  rw [← Int.cast_det] at hr
  exact_mod_cast hr

open scoped BigOperators
open Matrix

private def affineAugment {R : Type*} [CommRing R] {d : ℕ} (c : R) (a : Fin d → R) :
    Matrix (Fin (d+1)) (Fin (d+1)) R :=
  Matrix.of (Fin.cases (Pi.single 0 1) (fun i => Fin.cases (a i) (fun j => if i=j then c else 0)))

private theorem affineAugment_det {R : Type*} [CommRing R] {d : ℕ} (c : R) (a : Fin d → R) :
    (affineAugment c a).det = c^d := by
  have ht : (affineAugment c a).IsLowerTriangular := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hij
      have hj : j ≠ 0 := by intro h; subst j; exact (lt_irrefl _) hij
      simp [affineAugment, hj]
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact False.elim (not_lt_of_ge (Fin.zero_le _) hij)
      · intro hij
        have hne : i ≠ j := by intro h; subst j; exact (lt_irrefl _) hij
        simp [affineAugment, hne]
  rw [Matrix.det_of_isLowerTriangular _ ht, Fin.prod_univ_succ]
  simp [affineAugment]

private theorem augment_affine_eq {R : Type*} [CommRing R] {d : ℕ}
    (c : R) (a : Fin d → R) (M : Matrix (Fin d) (Fin (d+1)) R) :
    augment (Matrix.of (fun i j => c*M i j+a i)) = affineAugment c a * augment M := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [affineAugment, Matrix.mul_apply, Pi.single_apply, augment_zero]
  · simp [affineAugment, Matrix.mul_apply, Fin.sum_univ_succ,
      augment_zero, augment_succ, eq_comm]
    ring

theorem augmented_det_affine {R : Type*} [CommRing R] {d : ℕ}
    (c : R) (a : Fin d → R) (M : Matrix (Fin d) (Fin (d+1)) R) :
    (augment (Matrix.of (fun i j => c*M i j+a i))).det = c^d*(augment M).det := by
  rw [augment_affine_eq, Matrix.det_mul, affineAugment_det]

open scoped BigOperators
open Matrix

private def flipColumn {R : Type*} [Neg R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    Matrix (Fin d) (Fin (d+1)) R := Matrix.of (fun i k => if k=j then -M i k else M i k)

private theorem det_replace_column_e0 {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    ((augment M).updateCol j (Pi.single 0 1)).det = cofactor M j := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec_single, Matrix.col, cofactor_eq_adjugate]

private theorem det_flipColumn {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    (augment (flipColumn M j)).det = 2*cofactor M j-(augment M).det := by
  have he : augment (flipColumn M j) = (augment M).updateCol j
      ((-1 : R) • (augment M).col j + (2 : R) • Pi.single 0 1) := by
    ext i k
    refine Fin.cases ?_ (fun i => ?_) i
    · by_cases hk : k=j
      · subst k
        simp [Matrix.updateCol_self, Matrix.col, augment_zero]
        ring
      · rw [Matrix.updateCol_ne hk, augment_zero, augment_zero]
    · by_cases hk : k=j
      · subst k
        simp [Matrix.updateCol_self, Matrix.col, augment_succ, flipColumn]
      · rw [Matrix.updateCol_ne hk, augment_succ, augment_succ]
        simp [flipColumn, hk]
  have hc : (augment M).updateCol j ((augment M).col j) = augment M := by
    change (augment M).updateCol j (fun i => augment M i j) = augment M
    exact Matrix.updateCol_eq_self (augment M) j
  rw [he, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
    Matrix.det_updateCol_smul, hc, det_replace_column_e0]
  ring


open scoped BigOperators
open Matrix

private def standardSimplex (d : ℕ) : Matrix (Fin d) (Fin (d+1)) ℤ :=
  Matrix.of (fun i => Fin.cases 0 (fun j => if i=j then 1 else 0))

private theorem standardSimplex_det (d : ℕ) : (augment (standardSimplex d)).det=1 := by
  have ht : (augment (standardSimplex d)).IsUpperTriangular := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hij
      exact False.elim (not_lt_of_ge (Fin.zero_le _) hij)
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        rfl
      · intro hij
        have hn : i ≠ j := by intro h; subst j; exact (lt_irrefl _) hij
        simp [augment_succ, standardSimplex, hn]
  rw [Matrix.det_of_isUpperTriangular ht, Fin.prod_univ_succ]
  simp [augment_zero, augment_succ, standardSimplex]

private theorem delta_pos (d : ℕ) : 0 < delta d := by
  have hb : ∀ i j, |standardSimplex d i j| ≤ (1 : ℕ) := by
    intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [standardSimplex]
    · simp only [standardSimplex, Matrix.of_apply, Fin.cases_succ]
      split_ifs <;> norm_num
  have h := augmented_det_integer_box_bound (by omega : 1 ≤ (1 : ℕ)) (standardSimplex d) hb
  rw [standardSimplex_det] at h
  have hd : (1 : ℤ) ≤ delta d := by simpa using h
  exact_mod_cast hd

theorem exists_maximizing_sign_simplex (d : ℕ) :
    ∃ V : Matrix (Fin d) (Fin (d+1)) ℤ,
      (∀ i j, |V i j| ≤ 1) ∧
      |(augment V).det| = delta d ∧
      (augment V).det ≠ 0 ∧
      (∀ j, 0 ≤ (augment V).det * cofactor V j) := by
  classical
  obtain ⟨b,hb,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun b : Matrix (Fin d) (Fin (d+1)) Bool => (augment (signMatrix d b)).det.natAbs)
  let V := signMatrix d b
  have hbound : ∀ i j, |V i j| ≤ 1 := by
    intro i j
    simp only [V, signMatrix]
    split_ifs <;> norm_num
  have heq : |(augment V).det| = delta d := by
    change |(augment (signMatrix d b)).det| = delta d
    rw [← Int.natCast_natAbs, ← he]
    rfl
  have hne : (augment V).det ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at heq
    have hp := delta_pos d
    omega
  refine ⟨V,hbound,heq,hne,fun j => ?_⟩
  have hf : ∀ i k, |flipColumn V j i k| ≤ (1 : ℕ) := by
    intro i k
    simp only [flipColumn, Matrix.of_apply]
    split_ifs <;> simpa only [abs_neg, Nat.cast_one] using hbound i k
  have h := augmented_det_integer_box_bound (by omega : 1 ≤ (1 : ℕ)) (flipColumn V j) hf
  simp only [Nat.cast_one, one_pow, mul_one] at h
  rw [← heq, det_flipColumn] at h
  rcases le_total 0 (augment V).det with hpos | hneg
  · rw [abs_of_nonneg hpos] at h
    have hl := (abs_le.mp h).1
    exact mul_nonneg hpos (by linarith)
  · rw [abs_of_nonpos hneg] at h
    have hl := (abs_le.mp h).2
    exact mul_nonneg_of_nonpos_of_nonpos hneg (by linarith)

open scoped BigOperators
open Matrix

private theorem columns_injective_of_augmented_det {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ) (hdet : (augment M).det ≠ 0) :
    Function.Injective (fun j => fun i => M i j) := by
  intro a b hab
  by_contra hn
  apply hdet
  apply Matrix.det_zero_of_column_eq hn
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · exact congrFun hab i

private theorem fromWeights_support_card {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) (hp : ∀ i,0<x i) : (fromWeights v x).support.card=k := by
  classical
  have he : (fromWeights v x).support=Finset.univ.map v := by
    ext w
    constructor
    · intro hw
      obtain ⟨j,rfl⟩ := fromWeights_support_subset v x hw
      exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
    · intro hw
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hw
      rw [Finsupp.mem_support_iff,fromWeights_apply]
      exact ne_of_gt (hp j)
  rw [he,Finset.card_map,Finset.card_univ,Fintype.card_fin]

theorem primitive_cofactor_admissible {d m : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ) (hbound : ∀ i j,|M i j|≤m)
    (hdet : (augment M).det ≠ 0)
    (s : ℤ) (hs : s=1 ∨ s= -1)
    (hp : ∀ j,0<s*cofactor M j)
    (hgcd : Finset.univ.gcd (cofactor M)=1) :
    (augment M).det.natAbs ∈ lengths d m (d+1) := by
  classical
  let v : Fin (d+1) ↪ (Fin d → ℤ) := ⟨fun j i => M i j,columns_injective_of_augmented_det M hdet⟩
  have hcv : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose=M := rfl
  let x : Fin (d+1) → ℤ := fun j => s*cofactor M j
  have hxk : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ x=0 := by
    rw [hcv]
    change M *ᵥ (s • cofactor M)=0
    rw [Matrix.mulVec_smul,cofactor_mulVec_eq_zero,smul_zero]
  have hxg : Finset.univ.gcd x=1 := by
    change (Finset.univ.gcd fun j => s*cofactor M j)=1
    rw [Finset.gcd_mul_left,hgcd,mul_one]
    rcases hs with rfl | rfl <;> rw [← Int.abs_eq_normalize] <;> norm_num
  let f := fromWeights v (fun j => (x j).toNat)
  have hmin : IsMinimalZeroSum f := fromWeights_minimal_of_primitive v
    (hcv.symm ▸ hdet) x hxk hp hxg
  have hxp : ∀ j,0<(x j).toNat := by
    intro j
    have he : ((x j).toNat : ℤ)=x j := Int.toNat_of_nonneg (hp j).le
    have hpj : 0<x j := hp j
    exact_mod_cast (show (0 : ℤ)<(x j).toNat by rw [he]; exact hpj)
  have hbox : (↑f.support : Set (Fin d → ℤ)) ⊆ (fun d m => {v : Fin d → ℤ | ∀ i, |v i| ≤ (m : ℕ)}) d m := by
    intro w hw
    obtain ⟨j,rfl⟩ := fromWeights_support_subset v _ hw
    exact fun i => hbound i j
  have hlen := (sequence_cofactor_multiplicities v (fun j => (x j).toNat) hxp hmin (hcv.symm ▸ hdet)).2
  rw [hcv,hgcd,Int.ediv_one] at hlen
  have hlen' : (Finsupp.degree (R := ℕ)) f=(augment M).det.natAbs := by
    apply Int.ofNat_inj.mp
    simpa only [Int.natCast_natAbs] using hlen
  exact ⟨f,hmin,hbox,fromWeights_support_card v _ hxp,hlen'⟩

end D5.S3.Arith.Lattices.CubeSimplexDeterminant
