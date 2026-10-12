/- GID: D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/RealL2FirstReturnMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint moments agree until the first boundary return. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped InnerProductSpace lp
open Matrix ContinuousLinearMap

namespace D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments



/-- Natural coordinate `j` represents the source coordinate `j+1`. -/
def endpoint : ℓ²(Nat, Real) := lp.single 2 0 1

/-- The unilateral shift on the complete real square-summable carrier. -/
def shift : ℓ²(Nat, Real) →L[Real] ℓ²(Nat, Real) := (show ℓ²(Nat, Real) →ₗᵢ[Real] ℓ²(Nat, Real) from by
  let f : ℓ²(Nat, Real) → Nat → Real := fun x j => Nat.casesOn j 0 (fun i => x i)
  have hf (x : ℓ²(Nat, Real)) : HasSum (fun j => ‖f x j‖ ^ 2) (‖x‖ ^ 2) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa [f] using lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) x
  let v : ℓ²(Nat, Real) → ℓ²(Nat, Real) := fun x => ⟨f x, memℓp_gen (by simpa using (hf x).summable)⟩
  refine { toFun := v, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }
  · intro x y
    apply lp.ext
    funext j
    change f (x + y) j = f x j + f y j
    cases j <;> simp [f]
  · intro c x
    apply lp.ext
    funext j
    cases j <;> simp [v, f]
  · intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hv := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (v x)
    have hv2 : HasSum (fun j => ‖f x j‖ ^ 2) (‖v x‖ ^ 2) := by simpa [v] using hv
    exact hv2.unique (hf x)).toContinuousLinearMap

def infiniteOperator : ℓ²(Nat, Real) →L[Real] ℓ²(Nat, Real) := (3 : Real) • (1 : ℓ²(Nat, Real) →L[Real] ℓ²(Nat, Real)) - shift - shift.adjoint

def pathAdjacency (n : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

def finiteMatrix (n : Nat) : Matrix (Fin n) (Fin n) Real :=
  (3 : Real) • (1 : Matrix (Fin n) (Fin n) Real) - pathAdjacency n

def finiteOperator (n : Nat) : EuclideanSpace Real (Fin n) →L[Real] EuclideanSpace Real (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := Real) (finiteMatrix n)

def finiteEndpoint (n : Nat) (hn : 1 ≤ n) : EuclideanSpace Real (Fin n) :=
  EuclideanSpace.single ⟨0, by omega⟩ 1

def extension (n : Nat) (x : EuclideanSpace Real (Fin n)) : ℓ²(Nat, Real) :=
  ∑ i : Fin n, lp.single 2 i.val (x i)


/-- The endpoint moments on the finite path and complete real half-line coincide
before the first boundary return, whose exact contribution is one. -/
theorem endpoint_moments (n : Nat) (hn : 1 ≤ n) :
    (∀ k : Nat, k < 2 * n →
      inner Real (finiteEndpoint n hn) ((finiteOperator n ^ k) (finiteEndpoint n hn)) =
      inner Real endpoint ((infiniteOperator ^ k) endpoint)) ∧
    inner Real endpoint ((infiniteOperator ^ (2 * n)) endpoint) -
      inner Real (finiteEndpoint n hn)
        ((finiteOperator n ^ (2 * n)) (finiteEndpoint n hn)) = 1 := by
  classical
  have hs0 (x : ℓ²(Nat, Real)) : shift x 0 = 0 := rfl
  have hss (x : ℓ²(Nat, Real)) (j : Nat) : shift x (j + 1) = x j := rfl
  have hsa (x : ℓ²(Nat, Real)) (j : Nat) : shift.adjoint x j = x (j + 1) := by
    have hsingle : shift (lp.single 2 j (1 : Real)) = lp.single 2 (j + 1) 1 := by
      apply lp.ext
      funext i
      cases i with
      | zero => simp [shift, lp.single_apply]
      | succ i => simp [shift, lp.single_apply, Pi.single_apply]
    have h := ContinuousLinearMap.adjoint_inner_left shift (lp.single 2 j (1 : Real)) x
    rw [hsingle, lp.inner_single_right, lp.inner_single_right] at h
    simpa using h
  have hzero (x : ℓ²(Nat, Real)) : infiniteOperator x 0 = 3 * x 0 - x 1 := by
    change 3 * x 0 - shift x 0 - shift.adjoint x 0 = _
    rw [hs0, hsa]
    ring
  have his (x : ℓ²(Nat, Real)) (j : Nat) :
      infiniteOperator x (j + 1) = 3 * x (j + 1) - x j - x (j + 2) := by
    change 3 * x (j + 1) - shift x (j + 1) - shift.adjoint x (j + 1) = _
    rw [hss, hsa]
  have hext (x : EuclideanSpace Real (Fin n)) (i : Fin n) : extension n x i.val = x i := by
    simp only [extension, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (by intro h; exact hji (Fin.ext h.symm))]
    · simp
  have hext0 (x : EuclideanSpace Real (Fin n)) (j : Nat) (hj : n ≤ j) :
      extension n x j = 0 := by
    simp only [extension, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  have hfinite (x : EuclideanSpace Real (Fin n)) (i : Fin n) :
      finiteOperator n x i = 3 * x i -
        ((if h : i.val = 0 then 0 else x ⟨i.val - 1, by omega⟩) +
         (if h : i.val + 1 < n then x ⟨i.val + 1, h⟩ else 0)) := by
    change ((finiteMatrix n) *ᵥ x) i = _
    rw [finiteMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    congr 1
    have hsplit (j : Fin n) : pathAdjacency n i j * x j =
        (if i.val + 1 = j.val then x j else 0) +
        (if j.val + 1 = i.val then x j else 0) := by
      by_cases h1 : i.val + 1 = j.val <;>
        by_cases h2 : j.val + 1 = i.val <;> simp_all [pathAdjacency] <;> omega
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hu : (∑ j : Fin n, if i.val + 1 = j.val then x j else 0) =
        if h : i.val + 1 < n then x ⟨i.val + 1, h⟩ else 0 := by
      split_ifs with h
      · let t : Fin n := ⟨i.val + 1, h⟩
        rw [Finset.sum_eq_single t]
        · simp [t]
        · intro j _ hj
          rw [if_neg (by intro e; exact hj (Fin.ext e.symm))]
        · simp
      · apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (by omega)]
    have hd : (∑ j : Fin n, if j.val + 1 = i.val then x j else 0) =
        if h : i.val = 0 then 0 else x ⟨i.val - 1, by omega⟩ := by
      split_ifs with h
      · apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (by omega)]
      · let t : Fin n := ⟨i.val - 1, by omega⟩
        rw [Finset.sum_eq_single t]
        · simp [t, show i.val - 1 + 1 = i.val by omega]
        · intro j _ hj
          rw [if_neg (by intro e; apply hj; apply Fin.ext; dsimp [t]; omega)]
        · simp
    rw [hu, hd, add_comm]
  let v : Nat → ℓ²(Nat, Real) := fun k => (infiniteOperator ^ k) endpoint
  let w : Nat → EuclideanSpace Real (Fin n) :=
    fun k => (finiteOperator n ^ k) (finiteEndpoint n hn)
  have hvstep (k : Nat) : v (k + 1) = infiniteOperator (v k) := by
    dsimp only [v]
    rw [pow_succ', mul_apply_eq_comp]
  have hwstep (k : Nat) : w (k + 1) = finiteOperator n (w k) := by
    dsimp only [w]
    rw [pow_succ', mul_apply_eq_comp]
  have hsupport : ∀ k j : Nat, k < j → v k j = 0 := by
    intro k
    induction k with
    | zero =>
      intro j hj
      simp [v, endpoint, lp.single_apply, (show j ≠ 0 by omega)]
    | succ k ih =>
      intro j hj
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      rw [hvstep, his, ih (i + 1) (by omega), ih i (by omega), ih (i + 2) (by omega)]
      ring
  have hfrontier : ∀ k : Nat, v k k = (-1 : Real) ^ k := by
    intro k
    induction k with
    | zero => simp [v, endpoint, lp.single_apply]
    | succ k ih =>
      rw [hvstep, his, hsupport k (k + 1) (by omega),
        hsupport k (k + 2) (by omega), ih, pow_succ]
      ring
  have hcompare : ∀ k : Nat, k ≤ n → ∀ i : Fin n, v k i.val = w k i := by
    intro k
    induction k with
    | zero =>
      intro _ i
      simp [v, w, endpoint, finiteEndpoint, lp.single_apply, Pi.single_apply,
        PiLp.single_apply, Fin.ext_iff]
    | succ k ih =>
      rintro hk ⟨i, hi⟩
      cases i with
      | zero =>
        rw [hvstep, hzero, hwstep, hfinite]
        simp only [Fin.val_mk, dite_true, zero_add]
        rw [ih (by omega) ⟨0, hi⟩]
        split_ifs with ht
        · rw [ih (by omega) ⟨1, ht⟩]
        · rw [hsupport k 1 (by omega)]
      | succ j =>
        rw [hvstep, his, hwstep, hfinite]
        simp only [Fin.val_mk, Nat.succ_ne_zero, dite_false, Nat.succ_sub_one]
        rw [ih (by omega) ⟨j + 1, hi⟩, ih (by omega) ⟨j, by omega⟩]
        split_ifs with ht
        · rw [ih (by omega) ⟨j + 2, ht⟩]
          all_goals ring
        · rw [hsupport k (j + 2) (by omega)]
          all_goals ring
  have actual_iterate_comparison :
      (∀ k, k < n → v k = extension n (w k)) ∧
      v n = extension n (w n) + (-1 : Real) ^ n • lp.single 2 n 1 := by
    constructor
    · intro k hk
      apply lp.ext
      funext j
      by_cases hj : j < n
      · exact (hcompare k (by omega) ⟨j, hj⟩).trans (hext (w k) ⟨j, hj⟩).symm
      · rw [hext0 (w k) j (by omega), hsupport k j (by omega)]
    · apply lp.ext
      funext j
      change v n j = extension n (w n) j +
        (-1 : Real) ^ n * (lp.single (E := fun _ : Nat => Real) 2 n 1) j
      by_cases hj : j < n
      · simp only [lp.single_apply, Pi.single_apply,
          if_neg (by omega : j ≠ n), mul_zero, add_zero]
        exact (hcompare n le_rfl ⟨j, hj⟩).trans (hext (w n) ⟨j, hj⟩).symm
      · by_cases hje : j = n
        · subst j
          rw [hfrontier, hext0 (w n) n le_rfl]
          simp
        · rw [hsupport n j (by omega)]
          simp [hext0 (w n) j (by omega), lp.single_apply, hje]
  have hinner_extension (x y : EuclideanSpace Real (Fin n)) :
      inner Real (extension n x) (extension n y) = inner Real x y := by
    change inner Real (∑ i : Fin n, lp.single 2 i.val (x i)) (extension n y) = _
    rw [sum_inner]
    simp only [lp.inner_single_left]
    simp_rw [hext]
    simp [PiLp.inner_apply]
  have hinfinite_self : IsSelfAdjoint infiniteOperator := by
    simp [infiniteOperator, isSelfAdjoint_iff, star_sub, star_smul, star_eq_adjoint]
    abel
  have hfinite_self : IsSelfAdjoint (finiteOperator n) := by
    apply IsSelfAdjoint.map
    change (finiteMatrix n).conjTranspose = finiteMatrix n
    ext i j
    simp [finiteMatrix, pathAdjacency, Matrix.conjTranspose_apply,
      Matrix.one_apply, Matrix.smul_apply, eq_comm, or_comm]
  have hsplit_infinite (a b : Nat) :
      inner Real endpoint ((infiniteOperator ^ (a + b)) endpoint) =
      inner Real (v a) (v b) := by
    rw [pow_add]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    simp [v, (hinfinite_self.pow a).adjoint_eq]
  have hsplit_finite (a b : Nat) :
      inner Real (finiteEndpoint n hn)
        ((finiteOperator n ^ (a + b)) (finiteEndpoint n hn)) =
      inner Real (w a) (w b) := by
    rw [pow_add]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    simp [w, (hfinite_self.pow a).adjoint_eq]
  have horth (x : EuclideanSpace Real (Fin n)) :
      inner Real (extension n x) (lp.single 2 n 1) = 0 := by
    rw [lp.inner_single_right, hext0 x n le_rfl]
    simp
  constructor
  · intro k hk
    let a := k / 2
    let b := k - a
    have hab : a + b = k := by dsimp [a, b]; omega
    have ha : a < n := by dsimp [a]; omega
    have hb : b ≤ n := by dsimp [b, a]; omega
    rw [← hab, hsplit_finite, hsplit_infinite, actual_iterate_comparison.1 a ha]
    by_cases hbn : b < n
    · rw [actual_iterate_comparison.1 b hbn, hinner_extension]
    · have hbe : b = n := by omega
      rw [hbe, actual_iterate_comparison.2, inner_add_right, inner_smul_right,
        horth, mul_zero, add_zero, hinner_extension]
  · rw [show 2 * n = n + n by omega, hsplit_infinite, hsplit_finite,
      actual_iterate_comparison.2]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_comm (lp.single 2 n 1), hinner_extension]
    simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq,
      conj_trivial, Nat.ofNat_pos, lp.norm_single, norm_one, one_pow, mul_one]
    have hsign : (-1 : Real) ^ n * (-1 : Real) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    have hz := horth (w n)
    rw [real_inner_comm] at hz
    rw [hz]
    linear_combination hsign

#print axioms endpoint_moments


end D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
