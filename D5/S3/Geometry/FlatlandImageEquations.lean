/- GID: D5/S3/Geometry/FlatlandImageEquations
   generality: G
   mirror-B: D5/B/S3/Geometry/FlatlandImageEquations
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Set-theoretic equations for the closed image of two variable cameras. -/

/-
admission_basis: open-problem-resolution (#25719; Proved)
escape_witness: none; settling result
Direct frozen dependencies: C = D5/S3/Arith/Lattices/CofactorKernel.cofactor @
  sha256:3166337f4d6d020e4b4c7683bf2c13d3987b090b3e99f722181e1790e47736fd.
The signed-minor expression in cofactorMatrix is literal; proofs use the cofactor owner.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30117
Declaration classifications (same-delivery helpers expanded; C denotes the declaration above):
singular_kernel_implies_equations | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: actual_image_equations.
reshapeEquiv | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: equations_imply_singular_kernel, actual_image_equations, equations_imply_imageClosure.
equations_imply_singular_kernel | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: equations_imply_imageClosure.
segre_kernel_bilinear | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: actual_image_equations, equations_imply_imageClosure.
segrePolynomial | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minorPolynomial, cofactorPolynomial, segrePolynomial_homogeneous, minorPolynomial_multihomogeneous, cofactorPolynomial_homogeneous, minorPolynomial_eval.
minorPolynomial | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minorPolynomial_multihomogeneous, minorPolynomial_eval, imageClosure_equations_of_actual.
cofactorPolynomial | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: eightPointPolynomial, cofactorPolynomial_homogeneous, eightPointPolynomial_multihomogeneous, eightPointPolynomial_eval.
eightPointPolynomial | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: eightPointPolynomial_multihomogeneous, eightPointPolynomial_eval, imageClosure_equations_of_actual.
segrePolynomial_homogeneous | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minorPolynomial_multihomogeneous, cofactorPolynomial_homogeneous.
minorPolynomial_multihomogeneous | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_equations_of_actual.
cofactorPolynomial_homogeneous | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: eightPointPolynomial_multihomogeneous.
eightPointPolynomial_multihomogeneous | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: imageClosure_equations_of_actual.
minorPolynomial_eval | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_equations_of_actual.
eightPointPolynomial_eval | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: imageClosure_equations_of_actual.
imageClosure_equations_of_actual | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: imageClosure_implies_equations.
transpose_injective_of_surjective | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: surjective_cameras_constraint.
singular_outer_difference | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: surjective_cameras_constraint.
surjective_cameras_constraint | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: all_cameras_constraint.
deficient_camera_constraint | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: all_cameras_constraint.
all_cameras_constraint | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: actual_image_equations.
actual_image_equations | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: imageClosure_implies_equations.
imageClosure_implies_equations | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: result.
claim | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: result.
equations_imply_imageClosure | proof_shape: content; escape_witness: D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure; Direct frozen dependencies: C; consumers: result.
result | proof_shape: content; escape_witness: D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure; Direct frozen dependencies: C; consumers: none (settling result).
-/

import D5.S3.Geometry.FlatlandImageAlgebra
import D5.S3.Geometry.FlatlandImageClosure
import D5.S3.Arith.Lattices.CofactorKernel

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Geometry.FlatlandImageEquations
open D5.S3.Geometry.FlatlandImageAlgebra
open D5.S3.Geometry.FlatlandImageClosure

section
open Matrix
open scoped Classical

/-- A nonzero singular vector in the Segre kernel forces every stated equation. -/
private theorem singular_kernel_implies_equations {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (v : Fin 9 → ℂ) (hv : v ≠ 0) (hk : segreMatrix p *ᵥ v = 0)
    (hs : Matrix.det (fun (b a : Fin 3) => v (finProdFinEquiv (a,b))) = 0) : equations p := by
  constructor
  · intro J
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v,hv,?_⟩
    funext i
    exact congrFun hk (J i)
  · intro I
    let A : Matrix (Fin 8) (Fin 9) ℂ := (segreMatrix p).submatrix I id
    have hvA : A *ᵥ v = 0 := by
      funext i
      exact congrFun hk (I i)
    have hcof : D5.S3.Arith.Lattices.CofactorKernel.cofactor A = (D5.S3.Arith.Lattices.CofactorKernel.cofactor ((segreMatrix p).submatrix I id)) := by
      rfl
    by_cases hc : D5.S3.Arith.Lattices.CofactorKernel.cofactor A = 0
    · have hzero : cofactorMatrix p I = 0 := by
        funext b a
        exact congrFun (hcof.symm.trans hc) (finProdFinEquiv (a,b))
      rw [hzero, Matrix.det_zero]
    · obtain ⟨a,ha⟩ := kernel_eq_smul_cofactor A hc v hvA
      have ha0 : a ≠ 0 := by
        intro he
        rw [he,zero_smul] at ha
        exact hv ha
      have hr : (fun (b a : Fin 3) => v (finProdFinEquiv (a,b))) = a • cofactorMatrix p I := by
        funext b c
        simpa [cofactorMatrix, D5.S3.Arith.Lattices.CofactorKernel.cofactor, A] using congrFun ha (finProdFinEquiv (c,b))
      rw [hr, Matrix.det_smul, Fintype.card_fin] at hs
      exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero 3 ha0)
end

section
open Matrix Module
open scoped Classical

private def reshapeEquiv : (Fin 9 → ℂ) ≃ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ :=
  (LinearEquiv.funCongrLeft ℂ ℂ
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)).trans
    ((LinearEquiv.curry ℂ ℂ (Fin 3) (Fin 3)).trans
      (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ))

/-- The stated equations force a nonzero singular element of the entire Segre kernel. -/
private theorem equations_imply_singular_kernel {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (hp : equations p) :
    ∃ v : Fin 9 → ℂ, v ≠ 0 ∧ segreMatrix p *ᵥ v = 0 ∧ Matrix.det (fun (b a : Fin 3) => v (finProdFinEquiv (a,b))) = 0 := by
  classical
  let M := segreMatrix p
  obtain ⟨v,hv,hkv⟩ := kernel_nonzero_of_maximal_minors M hp.1
  let W := LinearMap.ker M.mulVecLin
  have hW : W ≠ ⊥ := by
    intro he
    have hh : v ∈ W := hkv
    rw [he, Submodule.mem_bot] at hh
    exact hv hh
  have hnull : 1 ≤ Module.finrank ℂ W := Submodule.one_le_finrank_iff.mpr hW
  have hdim := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + Module.finrank ℂ W = Module.finrank ℂ (Fin 9 → ℂ) at hdim
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  have hle : M.rank ≤ 8 := by omega
  by_cases hr : M.rank = 8
  · obtain ⟨I,hspan,hlin⟩ : ∃ I : Fin 8 ↪ Fin n,
        Submodule.span ℂ (Set.range (M.submatrix I id).row) =
          Submodule.span ℂ (Set.range M.row) ∧
        LinearIndependent ℂ (M.submatrix I id).row := by
      have hb := finite_row_basis M
      have hMr : M.rank = 8 := hr
      rw [hMr] at hb
      exact hb
    refine ⟨D5.S3.Arith.Lattices.CofactorKernel.cofactor (M.submatrix I id),
      cofactor_nonzero_of_independent_rows _ hlin,
      cofactor_in_full_kernel M hp.1 I, ?_⟩
    exact hp.2 I
  · have hnull2 : 2 ≤ Module.finrank ℂ W := by omega
    let Wm : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) := W.map reshapeEquiv.toLinearMap
    have hdimWm : 2 ≤ Module.finrank ℂ Wm := by
      have he := (Submodule.equivMapOfInjective reshapeEquiv.toLinearMap reshapeEquiv.injective W).finrank_eq
      rw [← he]
      exact hnull2
    obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank hdimWm
    have hf2 := linearIndependent_fin2.mp hf
    have hu : (f 1 : Matrix (Fin 3) (Fin 3) ℂ) ≠ 0 := by
      intro he
      exact hf2.1 (Subtype.ext he)
    have hvu : ∀ a : ℂ, (f 0 : Matrix (Fin 3) (Fin 3) ℂ) ≠ a • (f 1) := by
      intro a he
      exact hf2.2 a (Subtype.ext he.symm)
    obtain ⟨F,hF,hF0,hFs⟩ := singular_in_matrix_subspace Wm (f 1) (f 0)
      (f 1).property (f 0).property hu hvu
    obtain ⟨w,hw,he⟩ := hF
    refine ⟨w,?_,hw,?_⟩
    · intro hw0
      apply hF0
      rw [← he, hw0, map_zero]
    · have he' : (fun (b a : Fin 3) => w (finProdFinEquiv (a,b))) = F := he
      rw [he']
      exact hFs

end

section
open Matrix
open scoped BigOperators Classical

/-- Column vectorization agrees with the bilinear epipolar pairing. -/
private theorem segre_kernel_bilinear {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (v : Fin 9 → ℂ) (j : Fin n) :
    (segreMatrix p *ᵥ v) j = (p j 1).rep ⬝ᵥ (((fun (b a : Fin 3) => v (finProdFinEquiv (a,b)))) *ᵥ (p j 0).rep) := by
  change (∑ k, segreMatrix p j k * v k) = _
  rw [← (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp]
  simp only [segreMatrix, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring
end

section
open Matrix
open scoped BigOperators Classical

private def segrePolynomial {n : ℕ} (j : Fin n) (k : Fin 9) : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) :=
  MvPolynomial.X ((j,0), ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).1) *
    MvPolynomial.X ((j,1), ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).2)

private def minorPolynomial {n : ℕ} (J : Fin 9 ↪ Fin n) : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) :=
  Matrix.det (Matrix.of (fun i k => segrePolynomial (J i) k))

private def cofactorPolynomial {n : ℕ} (I : Fin 8 ↪ Fin n) (k : Fin 9) : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) :=
  D5.S3.Arith.Lattices.CofactorKernel.cofactor (Matrix.of (fun i a => segrePolynomial (I i) a)) k

private def eightPointPolynomial {n : ℕ} (I : Fin 8 ↪ Fin n) : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) :=
  Matrix.det (Matrix.of (fun b a : Fin 3 => cofactorPolynomial I (finProdFinEquiv (a,b))))

private theorem segrePolynomial_homogeneous {n : ℕ} (j : Fin n) (k : Fin 9)
    (b : Fin n × Fin 2) :
    (segrePolynomial j k).IsWeightedHomogeneous
      (fun c => if c.1 = b then (1 : ℕ) else 0) (if j = b.1 then (1 : ℕ) else 0) := by
  have h := (MvPolynomial.isWeightedHomogeneous_X ℂ
    (fun c : ((Fin n × Fin 2) × Fin 3) => if c.1 = b then (1 : ℕ) else 0)
    ((j,0), ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).1)).mul
    (MvPolynomial.isWeightedHomogeneous_X ℂ
    (fun c : ((Fin n × Fin 2) × Fin 3) => if c.1 = b then (1 : ℕ) else 0)
    ((j,1), ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).2))
  rcases b with ⟨b,i⟩
  fin_cases i <;> by_cases hj : j = b <;> simpa [segrePolynomial,hj] using h

private theorem minorPolynomial_multihomogeneous {n : ℕ} (J : Fin 9 ↪ Fin n) :
    Multihomogeneous (minorPolynomial J) := by
  refine ⟨fun b => ∑ i, if J i = b.1 then 1 else 0, fun b => ?_⟩
  exact homogeneous_determinant _ _ _ (fun i k => segrePolynomial_homogeneous (J i) k b)

private theorem cofactorPolynomial_homogeneous {n : ℕ} (I : Fin 8 ↪ Fin n)
    (k : Fin 9) (b : Fin n × Fin 2) :
    (cofactorPolynomial I k).IsWeightedHomogeneous
      (fun c => if c.1 = b then (1 : ℕ) else 0)
      (∑ i, if I i = b.1 then (1 : ℕ) else 0) := by
  unfold cofactorPolynomial D5.S3.Arith.Lattices.CofactorKernel.cofactor
  rw [show (-1 : MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) ^ k.val =
    MvPolynomial.C ((-1 : ℂ) ^ k.val) by simp]
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  exact homogeneous_determinant
    (fun c : ((Fin n × Fin 2) × Fin 3) => if c.1 = b then (1 : ℕ) else 0)
    (Matrix.of (fun i a => segrePolynomial (I i) (k.succAbove a)))
    (fun i => if I i = b.1 then (1 : ℕ) else 0)
    (fun i a => segrePolynomial_homogeneous (I i) (k.succAbove a) b)

private theorem eightPointPolynomial_multihomogeneous {n : ℕ} (I : Fin 8 ↪ Fin n) :
    Multihomogeneous (eightPointPolynomial I) := by
  refine ⟨fun b => ∑ _ : Fin 3, ∑ i, if I i = b.1 then 1 else 0, fun b => ?_⟩
  exact homogeneous_determinant _ _ _
    (fun a c => cofactorPolynomial_homogeneous I (finProdFinEquiv (c,a)) b)

private theorem minorPolynomial_eval {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (J : Fin 9 ↪ Fin n) :
    MvPolynomial.eval (coordinates p) (minorPolynomial J) =
      ((segreMatrix p).submatrix J id).det := by
  rw [minorPolynomial, RingHom.map_det]
  congr 1
  ext i k
  simp [segrePolynomial, coordinates, segreMatrix, Matrix.map_apply, Matrix.submatrix]

private theorem eightPointPolynomial_eval {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (I : Fin 8 ↪ Fin n) :
    MvPolynomial.eval (coordinates p) (eightPointPolynomial I) = (cofactorMatrix p I).det := by
  rw [eightPointPolynomial, RingHom.map_det]
  congr 1
  ext b a
  simp [cofactorPolynomial, RingHom.map_det, cofactorMatrix, D5.S3.Arith.Lattices.CofactorKernel.cofactor,
    Matrix.map_apply, segrePolynomial, segreMatrix, coordinates, Matrix.submatrix]
  all_goals
    apply congrArg Matrix.det
    ext i k
    simp [Matrix.map_apply, Matrix.of_apply, coordinates]

private theorem imageClosure_equations_of_actual {n : ℕ}
    (h : ∀ s : ImagingDomain n, equations (theta s)) (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : p ∈ imageClosure n) : equations p := by
  constructor
  · intro J
    rw [← minorPolynomial_eval]
    apply hp _ (minorPolynomial_multihomogeneous J)
    intro s
    rw [minorPolynomial_eval]
    exact (h s).1 J
  · intro I
    rw [← eightPointPolynomial_eval]
    apply hp _ (eightPointPolynomial_multihomogeneous I)
    intro s
    rw [eightPointPolynomial_eval]
    exact (h s).2 I
end

section
open Matrix Module
open scoped BigOperators Classical

private theorem transpose_injective_of_surjective {K m n : Type*} [Field K]
    [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n K) (hA : Function.Surjective A.mulVec) :
    Function.Injective A.transpose.mulVec := by
  obtain ⟨R,hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hh : R.transpose * A.transpose = 1 := by rw [← Matrix.transpose_mul,hR,Matrix.transpose_one]
  intro u v huv
  have := congrArg (fun w => R.transpose *ᵥ w) huv
  simpa [Matrix.mulVec_mulVec, hh] using this

private theorem singular_outer_difference {K : Type*} [CommRing K]
    (a b c d : Fin 3 → K) :
    (Matrix.vecMulVec a b - Matrix.vecMulVec c d).det = 0 := by
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.vecMulVec_apply]
  ring

/-- Any two surjective cameras admit a nonzero singular bilinear constraint on all world vectors. -/
private theorem surjective_cameras_constraint {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 4) K)
    (hA : Function.Surjective A.mulVec) (hB : Function.Surjective B.mulVec) :
    ∃ F : Matrix (Fin 3) (Fin 3) K, F ≠ 0 ∧ F.det = 0 ∧
      ∀ q : Fin 4 → K, (B *ᵥ q) ⬝ᵥ (F *ᵥ (A *ᵥ q)) = 0 := by
  let T : ((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] (Fin 4 → K) :=
    A.transpose.mulVecLin.coprod (-B.transpose.mulVecLin)
  let W := LinearMap.ker T
  have hd := LinearMap.finrank_range_add_finrank_ker T
  have hr := Submodule.finrank_le (LinearMap.range T)
  have hW : 2 ≤ Module.finrank K W := by
    simpa only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      (show 2 ≤ Module.finrank K (LinearMap.ker T) by
        simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd hr
        omega)
  obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank hW
  let a : Fin 2 → Fin 3 → K := fun i => (f i).val.1
  let b : Fin 2 → Fin 3 → K := fun i => (f i).val.2
  have hab (i : Fin 2) : A.transpose *ᵥ a i = B.transpose *ᵥ b i := by
    have hh := (f i).property
    change A.transpose *ᵥ a i + -(B.transpose *ᵥ b i) = 0 at hh
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hh)
  have hAi := transpose_injective_of_surjective A hA
  have hBi := transpose_injective_of_surjective B hB
  have ha0 : a 0 ≠ 0 := by
    intro ha
    have hb : b 0 = 0 := hBi (by simpa [ha] using (hab 0).symm)
    have hh : f 0 = 0 := Subtype.ext (Prod.ext ha hb)
    exact hf.ne_zero 0 hh
  let F := Matrix.vecMulVec (b 0) (a 1) - Matrix.vecMulVec (b 1) (a 0)
  have hF : F ≠ 0 := by
    intro he
    obtain ⟨k,hk⟩ := Function.ne_iff.mp ha0
    let t := a 1 k / a 0 k
    have hb : b 1 = t • b 0 := by
      funext i
      have hh := congrFun (congrFun he i) k
      change b 0 i * a 1 k - b 1 i * a 0 k = 0 at hh
      change b 1 i = t * b 0 i
      calc
        b 1 i = (b 0 i * a 1 k) / a 0 k :=
          (eq_div_iff hk).mpr (sub_eq_zero.mp hh).symm
        _ = t * b 0 i := by dsimp [t]; ring
    have ha : a 1 = t • a 0 := by
      apply hAi
      rw [hab 1, hb, Matrix.mulVec_smul, Matrix.mulVec_smul, hab 0]
    have hh : f 1 = t • f 0 := Subtype.ext (Prod.ext ha hb)
    have ht : t ≠ 0 := by
      intro ht
      exact hf.ne_zero 1 (by simpa [ht] using hh)
    apply (linearIndependent_fin2.mp hf).2 t⁻¹
    rw [hh, smul_smul, inv_mul_cancel₀ ht, one_smul]
  refine ⟨F,hF,singular_outer_difference _ _ _ _,?_⟩
  intro q
  have hq (i : Fin 2) : b i ⬝ᵥ (B *ᵥ q) = a i ⬝ᵥ (A *ᵥ q) := by
    rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose]
    change (B.transpose *ᵥ b i) ⬝ᵥ q = (A.transpose *ᵥ a i) ⬝ᵥ q
    rw [hab]
  change (B *ᵥ q) ⬝ᵥ ((Matrix.vecMulVec (b 0) (a 1) -
    Matrix.vecMulVec (b 1) (a 0)) *ᵥ (A *ᵥ q)) = 0
  rw [Matrix.sub_mulVec, dotProduct_sub]
  have houter (u v : Fin 3 → K) :
      (B *ᵥ q) ⬝ᵥ (Matrix.vecMulVec u v *ᵥ (A *ᵥ q)) =
        ((B *ᵥ q) ⬝ᵥ u) * (v ⬝ᵥ (A *ᵥ q)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct]
    rfl
  rw [houter,houter]
  rw [dotProduct_comm (B *ᵥ q) (b 0), dotProduct_comm (B *ᵥ q) (b 1), hq 0,hq 1]
  ring
end

section
open Matrix Module
open scoped BigOperators Classical

private theorem deficient_camera_constraint {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 4) K) (hA : ¬ Function.Surjective A.mulVec) :
    ∃ F : Matrix (Fin 3) (Fin 3) K, F ≠ 0 ∧ F.det = 0 ∧
      ∀ q : Fin 4 → K, (B *ᵥ q) ⬝ᵥ (F *ᵥ (A *ᵥ q)) = 0 := by
  have hni : ¬ Function.Injective A.transpose.mulVec := by
    intro hi
    apply hA
    have hv : Function.Injective A.vecMul := by
      intro x y hxy
      apply hi
      change A.transpose *ᵥ x = A.transpose *ᵥ y
      rw [Matrix.mulVec_transpose,Matrix.mulVec_transpose]
      exact hxy
    exact (Matrix.vecMul_injective_iff.mp hv).mulVec_surjective
  obtain ⟨u,v,he,hne⟩ := Function.not_injective_iff.mp hni
  let a := u-v
  have ha : a ≠ 0 := sub_ne_zero.mpr hne
  have hka : A.transpose *ᵥ a = 0 := by rw [Matrix.mulVec_sub,he,sub_self]
  let b : Fin 3 → K := Pi.single 0 1
  have hb : b ≠ 0 := by intro hh; have := congrFun hh 0; simpa [b] using this
  refine ⟨Matrix.vecMulVec b a,Matrix.vecMulVec_ne_zero hb ha,Matrix.det_vecMulVec _ _,?_⟩
  intro q
  have hh : a ⬝ᵥ (A *ᵥ q) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    change (A.transpose *ᵥ a) ⬝ᵥ q = 0
    rw [hka,zero_dotProduct]
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_vecMulVec,smul_dotProduct,hh,smul_zero]

/-- All camera pairs, including deficient and coincident ones, have a singular compatible form. -/
private theorem all_cameras_constraint {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 4) K) :
    ∃ F : Matrix (Fin 3) (Fin 3) K, F ≠ 0 ∧ F.det = 0 ∧
      ∀ q : Fin 4 → K, (B *ᵥ q) ⬝ᵥ (F *ᵥ (A *ᵥ q)) = 0 := by
  by_cases hA : Function.Surjective A.mulVec
  · by_cases hB : Function.Surjective B.mulVec
    · exact surjective_cameras_constraint A B hA hB
    · obtain ⟨F,hF,hFs,hFq⟩ := deficient_camera_constraint B A hB
      refine ⟨F.transpose,?_,by simpa using hFs,?_⟩
      · intro he
        apply hF
        have hh := congrArg Matrix.transpose he
        simpa only [Matrix.transpose_transpose,Matrix.transpose_zero] using hh
      · intro q
        rw [Matrix.dotProduct_transpose_mulVec]
        exact hFq q
  · exact deficient_camera_constraint A B hA

private theorem actual_image_equations {n : ℕ} (s : ImagingDomain n) : equations (theta s) := by
  obtain ⟨F,hF,hFs,hFq⟩ := all_cameras_constraint (s.val.2 0).rep (s.val.2 1).rep
  let v := reshapeEquiv.symm F
  apply singular_kernel_implies_equations (theta s) v
  · intro he
    apply hF
    have := congrArg reshapeEquiv he
    simpa [v] using this
  · funext j
    rw [segre_kernel_bilinear]
    change (Projectivization.mk ℂ _ (s.property j 1)).rep ⬝ᵥ
      ((fun (b a : Fin 3) => v (finProdFinEquiv (a,b))) *ᵥ (Projectivization.mk ℂ _ (s.property j 0)).rep) = 0
    have hv : (fun (b a : Fin 3) => v (finProdFinEquiv (a,b))) = F := reshapeEquiv.apply_symm_apply F
    rw [hv]
    exact (bilinear_projective_mk_zero_iff F _ _ (s.property j 0) (s.property j 1)).2
      (hFq (s.val.1 j).rep)
  · simpa only [show (fun (b a : Fin 3) => v (finProdFinEquiv (a,b))) = F from reshapeEquiv.apply_symm_apply F] using hFs

private theorem imageClosure_implies_equations {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : p ∈ imageClosure n) : equations p :=
  imageClosure_equations_of_actual actual_image_equations p hp
end

def claim : Prop :=
  ∀ n : ℕ, 9 ≤ n → ∀ p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)), p ∈ imageClosure n ↔ equations p

private theorem equations_imply_imageClosure {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (hp : equations p) :
    p ∈ imageClosure n := by
  obtain ⟨v,hv,hk,hs⟩ := equations_imply_singular_kernel p hp
  apply singular_compatible_closure ((fun (b a : Fin 3) => v (finProdFinEquiv (a,b))))
  · intro he
    apply hv
    have hh : reshapeEquiv v = 0 := he
    exact reshapeEquiv.injective (hh.trans (map_zero reshapeEquiv).symm)
  · exact hs
  · intro j
    rw [← segre_kernel_bilinear]
    exact congrFun hk j

theorem result : claim := by
  intro n hn p
  exact ⟨imageClosure_implies_equations p,equations_imply_imageClosure p⟩


end D5.S3.Geometry.FlatlandImageEquations
