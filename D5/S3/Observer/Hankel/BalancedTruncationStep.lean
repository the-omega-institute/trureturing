/- GID: D5/S3/Observer/Hankel/BalancedTruncationStep
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/BalancedTruncationStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Actual principal-state truncation inherits both Stein inequalities and has a two-sigma energy bound. -/

import D5.S3.Observer.Hankel.BalancedSteinEnergy

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.BalancedTruncationStep

open D5.S3.Observer.Hankel.BalancedSteinEnergy
open D5.S3.Observer.Hankel.ProjectedRealizationError
open scoped BigOperators

variable {n m p : ℕ}

/-- Delete the final coordinate. -/
def keep (x : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => x i.castSucc

/-- Lift retained coordinates with a zero final coordinate. -/
def lift (z : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc z 0

/-- Actual principal-state truncation of the transition matrix. -/
def truncateA (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A.submatrix Fin.castSucc Fin.castSucc

/-- Actual retained input rows. -/
def truncateB (B : Matrix (Fin (n + 1)) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ := B.submatrix Fin.castSucc id

/-- Actual retained output columns. -/
def truncateC (C : Matrix (Fin p) (Fin (n + 1)) ℝ) :
    Matrix (Fin p) (Fin n) ℝ := C.submatrix id Fin.castSucc

@[simp] theorem lift_last (z : Fin n → ℝ) : lift z (Fin.last n) = 0 := by
  simp [lift]

@[simp] theorem keep_lift (z : Fin n → ℝ) : keep (lift z) = z := by
  ext i
  simp [keep, lift]

@[simp] theorem keep_add (x y : Fin (n + 1) → ℝ) : keep (x + y) = keep x + keep y := rfl
@[simp] theorem keep_sub (x y : Fin (n + 1) → ℝ) : keep (x - y) = keep x - keep y := rfl
@[simp] theorem keep_smul (a : ℝ) (x : Fin (n + 1) → ℝ) : keep (a • x) = a • keep x := rfl

/-- The projection as a standard continuous linear map. -/
def keepMap : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := keep, map_add' := keep_add, map_smul' := fun _ _ => rfl }

/-- The zero-padding lift as a standard continuous linear map. -/
def liftMap : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := lift
      map_add' := by
        intro x y
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [lift]
        · simp [lift]
      map_smul' := by
        intro a x
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [lift]
        · simp [lift] }

@[simp] theorem keep_mul_lift (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℝ) : keep (A.mulVec (lift z)) = (truncateA A).mulVec z := by
  ext i
  simp [keep, lift, truncateA, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

@[simp] theorem keep_mul_input (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (u : Fin m → ℝ) : keep (B.mulVec u) = (truncateB B).mulVec u := rfl

@[simp] theorem output_mul_lift (C : Matrix (Fin p) (Fin (n + 1)) ℝ)
    (z : Fin n → ℝ) : C.mulVec (lift z) = (truncateC C).mulVec z := by
  ext i
  simp [lift, truncateC, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- These matrix blocks are exactly the constructed P A J, P B and C J model
from ProjectedRealizationError, on the actual retained coordinate space. -/
theorem truncated_model_is_projected
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin (n + 1)) ℝ) :
    matrixMap (truncateA A) = reducedDynamics (matrixMap A) keepMap liftMap ∧
    matrixMap (truncateB B) = reducedInput (matrixMap B) keepMap ∧
    matrixMap (truncateC C) = reducedOutput (matrixMap C) liftMap := by
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro z
    change (truncateA A).mulVec z = keep (A.mulVec (lift z))
    exact (keep_mul_lift A z).symm
  · apply ContinuousLinearMap.ext
    intro u
    rfl
  · apply ContinuousLinearMap.ext
    intro z
    change (truncateC C).mulVec z = C.mulVec (lift z)
    exact (output_mul_lift C z).symm

/-- The diagonal energy decomposes into retained and final coordinates. -/
theorem energy_split (w x : Fin (n + 1) → ℝ) :
    energy w x = energy (keep w) (keep x) + w (Fin.last n) * (x (Fin.last n)) ^ 2 := by
  exact Fin.sum_univ_castSucc (fun i => w i * (x i) ^ 2)

@[simp] theorem energy_lift (w : Fin (n + 1) → ℝ) (z : Fin n → ℝ) :
    energy w (lift z) = energy (keep w) z := by
  rw [energy_split]
  simp

private theorem energy_keep_le (w x : Fin (n + 1) → ℝ) (hw : 0 ≤ w (Fin.last n)) :
    energy (keep w) (keep x) ≤ energy w x := by
  rw [energy_split]
  exact le_add_of_nonneg_right (mul_nonneg hw (sq_nonneg _))

/-- Principal truncation preserves both diagonal Stein inequalities.
Equality is not asserted: the omitted coordinates contribute positive terms. -/
theorem truncate_preserves_stein (w : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin (n + 1)) ℝ) (h : BalancedStein w A B C) :
    BalancedStein (keep w) (truncateA A) (truncateB B) (truncateC C) := by
  rcases h with ⟨hw, hO, hR⟩
  refine ⟨fun i => hw i.castSucc, ?_, ?_⟩
  · intro z
    have ho := hO (lift z)
    have hd := energy_keep_le w (A.mulVec (lift z)) (le_of_lt (hw (Fin.last n)))
    rw [keep_mul_lift] at hd
    rw [energy_lift, output_mul_lift] at ho
    exact (add_le_add_right hd _).trans ho
  · intro z
    have hr := hR (lift z)
    have hd := energy_keep_le w (A.transpose.mulVec (lift z)) (le_of_lt (hw (Fin.last n)))
    rw [keep_mul_lift] at hd
    rw [energy_lift, output_mul_lift] at hr
    change energy (keep w) ((truncateA A).transpose.mulVec z) ≤
      energy w (A.transpose.mulVec (lift z)) at hd
    change energy w (A.transpose.mulVec (lift z)) +
      squareSum ((truncateB B).transpose.mulVec z) ≤ energy (keep w) z at hr
    exact (add_le_add_right hd _).trans hr

/-- The balanced error storage combines difference and sum states. -/
def truncationStorage (w : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ)
    (z : Fin n → ℝ) : ℝ :=
  energy w (x - lift z) + (w (Fin.last n)) ^ 2 *
    energy (fun i => (w i)⁻¹) (x + lift z)

theorem truncationStorage_nonneg (w : Fin (n + 1) → ℝ)
    (hw : ∀ i, 0 < w i) (x : Fin (n + 1) → ℝ) (z : Fin n → ℝ) :
    0 ≤ truncationStorage w x z := by
  exact add_nonneg (energy_nonneg _ _ (fun i => le_of_lt (hw i)))
    (mul_nonneg (sq_nonneg _) (energy_nonneg _ _ (fun i => inv_nonneg.mpr (le_of_lt (hw i)))))

/-- The omitted-coordinate forcing is computed from the actual reduced state. -/
def discardedForcing (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  (A.mulVec (lift z) + B.mulVec u) (Fin.last n)

/-- Single-step balanced truncation dissipativity, including the nonnegative
omitted-forcing term. All next states are the actual full and truncated updates. -/
theorem single_step_dissipation (w : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin (n + 1)) ℝ) (h : BalancedStein w A B C)
    (x : Fin (n + 1) → ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) :
    truncationStorage w (A.mulVec x + B.mulVec u)
        ((truncateA A).mulVec z + (truncateB B).mulVec u) +
      squareSum (C.mulVec x - (truncateC C).mulVec z) +
      2 * w (Fin.last n) * (discardedForcing A B z u) ^ 2 ≤
    truncationStorage w x z + 4 * (w (Fin.last n)) ^ 2 * squareSum u := by
  rcases h with ⟨hw, hO, hR⟩
  let X := A.mulVec x + B.mulVec u
  let Z := (truncateA A).mulVec z + (truncateB B).mulVec u
  let e := X - lift Z
  let f := X + lift Z
  let a := A.mulVec (x - lift z)
  let b := A.mulVec (x + lift z) + B.mulVec ((2 : ℝ) • u)
  let v := discardedForcing A B z u
  have hae : keep a = keep e := by
    change keep (A.mulVec (x - lift z)) = keep (X - lift Z)
    rw [Matrix.mulVec_sub, keep_sub, keep_mul_lift A z, keep_sub, keep_lift]
    dsimp only [X, Z]
    rw [keep_add, keep_mul_input B u]
    abel
  have hbf : keep b = keep f := by
    have hbkeep : keep b = keep (A.mulVec x) + (truncateA A).mulVec z +
        (2 : ℝ) • (truncateB B).mulVec u := by
      change keep (A.mulVec (x + lift z) + B.mulVec ((2 : ℝ) • u)) = _
      rw [keep_add, Matrix.mulVec_add, keep_add, keep_mul_lift A z,
        Matrix.mulVec_smul, keep_smul, keep_mul_input B u]
    rw [hbkeep]
    change _ = keep (X + lift Z)
    rw [keep_add, keep_lift]
    dsimp only [X, Z]
    rw [keep_add, keep_mul_input B u]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ha : a (Fin.last n) = X (Fin.last n) - v := by
    simp only [a, X, v, discardedForcing, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]
    ring
  have hb : b (Fin.last n) = X (Fin.last n) + v := by
    simp only [b, X, v, discardedForcing, Matrix.mulVec_add, Matrix.mulVec_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he : e (Fin.last n) = X (Fin.last n) := by simp [e]
  have hf : f (Fin.last n) = X (Fin.last n) := by simp [f]
  have cancel : energy w a + (w (Fin.last n)) ^ 2 * energy (fun i => (w i)⁻¹) b =
      truncationStorage w X Z + 2 * w (Fin.last n) * v ^ 2 := by
    change energy w a + (w (Fin.last n)) ^ 2 * energy (fun i => (w i)⁻¹) b =
      energy w e + (w (Fin.last n)) ^ 2 * energy (fun i => (w i)⁻¹) f +
        2 * w (Fin.last n) * v ^ 2
    rw [energy_split w a, energy_split (fun i => (w i)⁻¹) b,
      energy_split w e, energy_split (fun i => (w i)⁻¹) f, hae, hbf, ha, hb, he, hf]
    field_simp [ne_of_gt (hw (Fin.last n))]
    <;> ring
  have ho := hO (x - lift z)
  have hr := inverse_energy_step w A B hw hR (x + lift z) ((2 : ℝ) • u)
  rw [squareSum_smul] at hr
  have hrs := mul_le_mul_of_nonneg_left hr (sq_nonneg (w (Fin.last n)))
  have hout : C.mulVec (x - lift z) = C.mulVec x - (truncateC C).mulVec z := by
    rw [Matrix.mulVec_sub, output_mul_lift]
  rw [hout] at ho
  change energy w a + squareSum (C.mulVec x - (truncateC C).mulVec z) ≤
    energy w (x - lift z) at ho
  change (w (Fin.last n)) ^ 2 * energy (fun i => (w i)⁻¹) b ≤ _ at hrs
  change truncationStorage w X Z + squareSum (C.mulVec x - (truncateC C).mulVec z) +
    2 * w (Fin.last n) * v ^ 2 ≤ _
  unfold truncationStorage
  change energy w a + (w (Fin.last n)) ^ 2 * energy (fun i => (w i)⁻¹) b =
    energy w (X - lift Z) + (w (Fin.last n)) ^ 2 * energy (fun i => (w i)⁻¹) (X + lift Z) +
      2 * w (Fin.last n) * v ^ 2 at cancel
  nlinarith

/-- Finite-horizon energy accounting. The terminal storage and omitted-forcing
energy are retained, so no limit, stability or contraction premise is needed. -/
theorem finite_horizon_dissipation (w : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin (n + 1)) ℝ) (h : BalancedStein w A B C)
    (u : ℕ → Fin m → ℝ) (N : ℕ) :
    truncationStorage w (matrixState A B u N)
        (matrixState (truncateA A) (truncateB B) u N) +
      (∑ k ∈ Finset.range N, squareSum
        (matrixResponse A B C u k -
          matrixResponse (truncateA A) (truncateB B) (truncateC C) u k)) +
      2 * w (Fin.last n) * (∑ k ∈ Finset.range N,
        (discardedForcing A B (matrixState (truncateA A) (truncateB B) u k) (u k)) ^ 2) ≤
    4 * (w (Fin.last n)) ^ 2 * ∑ k ∈ Finset.range N, squareSum (u k) := by
  induction N with
  | zero => simp [truncationStorage, lift]
  | succ N ih =>
      have step := single_step_dissipation w A B C h (matrixState A B u N)
        (matrixState (truncateA A) (truncateB B) u N) (u N)
      rw [← matrixState_succ, ← matrixState_succ] at step
      change truncationStorage w (matrixState A B u (N + 1))
          (matrixState (truncateA A) (truncateB B) u (N + 1)) +
        squareSum (matrixResponse A B C u N -
          matrixResponse (truncateA A) (truncateB B) (truncateC C) u N) +
        2 * w (Fin.last n) *
          (discardedForcing A B (matrixState (truncateA A) (truncateB B) u N) (u N)) ^ 2 ≤
        truncationStorage w (matrixState A B u N)
          (matrixState (truncateA A) (truncateB B) u N) +
          4 * (w (Fin.last n)) ^ 2 * squareSum (u N) at step
      simp only [Finset.sum_range_succ]
      nlinarith

/-- The usual squared two-sigma bound for the output of actual principal truncation. -/
theorem finite_horizon_output_bound (w : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin (n + 1)) ℝ) (h : BalancedStein w A B C)
    (u : ℕ → Fin m → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, squareSum
      (matrixResponse A B C u k -
        matrixResponse (truncateA A) (truncateB B) (truncateC C) u k)) ≤
      4 * (w (Fin.last n)) ^ 2 * ∑ k ∈ Finset.range N, squareSum (u k) := by
  have ht := finite_horizon_dissipation w A B C h u N
  have hs := truncationStorage_nonneg w h.1 (matrixState A B u N)
    (matrixState (truncateA A) (truncateB B) u N)
  have hv : 0 ≤ 2 * w (Fin.last n) * (∑ k ∈ Finset.range N,
      (discardedForcing A B (matrixState (truncateA A) (truncateB B) u k) (u k)) ^ 2) :=
    mul_nonneg (by have := h.1 (Fin.last n); positivity)
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  linarith

#print axioms truncate_preserves_stein
#print axioms single_step_dissipation
#print axioms finite_horizon_output_bound

end D5.S3.Observer.Hankel.BalancedTruncationStep
