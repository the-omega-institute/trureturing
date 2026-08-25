/- GID: D5/S3/Observer/Approximation/IntertwiningDefectPropagation
   generality: G
   mirror-B: D5/B/S3/Observer/Approximation/IntertwiningDefectPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Operator defects telescope and obey both norm bounds, including time zero. -/
/- Library-search audit trail (2026-08-25):
   * Repository searches for `opNorm`, composition norms, telescoping, and intertwining found
     no operator-defect telescope. `IteratedDefectAccumulation` is a statewise Lipschitz bound,
     and `GNSZeroPropagation` concerns zero norms rather than intertwining defects.
   * Pinned Mathlib provides `ContinuousLinearMap.opNorm_comp_le`, `norm_pow_le'`,
     `ContinuousLinearMap.norm_id_le`, `norm_sum_le`, and `Finset.sum_range_succ_comm`.
   * `geom_sum` and `geom_sum₂_self` were inspected; neither represents the inserted map `C`.
     Three `smart_search.sh` phrase searches exited 1 with no exact declaration-name hit. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Approximation.IntertwiningDefectPropagation

open scoped BigOperators

/-- The one-step approximate intertwining defect `C T - A C`. -/
def intertwiningDefect
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] Y) (C : X →L[𝕜] Y) (T : X →L[𝕜] X) : X →L[𝕜] Y :=
  C.comp T - A.comp C

/-- The iterated intertwining defect is the exact telescope of transported one-step defects. -/
theorem intertwining_defect_telescope
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] Y) (C : X →L[𝕜] Y) (T : X →L[𝕜] X) (n : Nat) :
    C.comp (T ^ n) - (A ^ n).comp C =
      ∑ j ∈ Finset.range n,
        (A ^ (n - 1 - j)).comp ((intertwiningDefect A C T).comp (T ^ j)) := by
  induction n with
  | zero =>
      ext
      simp [ContinuousLinearMap.comp_apply]
  | succ n ih =>
      rw [Finset.sum_range_succ_comm]
      simp only [Nat.succ_sub_one]
      have hshift :
          (∑ j ∈ Finset.range n,
              (A ^ (n - j)).comp ((intertwiningDefect A C T).comp (T ^ j))) =
            A.comp (∑ j ∈ Finset.range n,
              (A ^ (n - 1 - j)).comp ((intertwiningDefect A C T).comp (T ^ j))) := by
        rw [ContinuousLinearMap.comp_finsetSum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hexponent : n - j = (n - 1 - j) + 1 := by
          have hjlt : j < n := Finset.mem_range.mp hj
          omega
        rw [hexponent, pow_succ']
        rfl
      rw [hshift, ← ih]
      ext x
      simp [pow_succ', intertwiningDefect, ContinuousLinearMap.comp_apply]
#print axioms intertwining_defect_telescope

/-- Taking operator norms in the exact telescope gives the weighted finite-sum bound. -/
theorem norm_intertwining_defect_le
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] Y) (C : X →L[𝕜] Y) (T : X →L[𝕜] X) (n : Nat) :
    ‖C.comp (T ^ n) - (A ^ n).comp C‖ ≤
      ∑ j ∈ Finset.range n,
        ‖A‖ ^ (n - 1 - j) * ‖intertwiningDefect A C T‖ * ‖T‖ ^ j := by
  rw [intertwining_defect_telescope]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have hApow : ‖A ^ (n - 1 - j)‖ ≤ ‖A‖ ^ (n - 1 - j) := by
    cases n - 1 - j with
    | zero =>
        simpa only [pow_zero, ContinuousLinearMap.one_def] using
          ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := Y)
    | succ k => exact norm_pow_le' A k.succ_pos
  have hTpow : ‖T ^ j‖ ≤ ‖T‖ ^ j := by
    cases j with
    | zero =>
        simpa only [pow_zero, ContinuousLinearMap.one_def] using
          ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := X)
    | succ k => exact norm_pow_le' T k.succ_pos
  calc
    ‖(A ^ (n - 1 - j)).comp ((intertwiningDefect A C T).comp (T ^ j))‖ ≤
        ‖A ^ (n - 1 - j)‖ * ‖(intertwiningDefect A C T).comp (T ^ j)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A ^ (n - 1 - j)‖ * (‖intertwiningDefect A C T‖ * ‖T ^ j‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ ^ (n - 1 - j) * (‖intertwiningDefect A C T‖ * ‖T‖ ^ j) := by
      gcongr
    _ = (‖A‖ ^ (n - 1 - j) * ‖intertwiningDefect A C T‖) * ‖T‖ ^ j := by
      ring
#print axioms norm_intertwining_defect_le

/-- Uniform operator-norm bounds give the linear-in-time estimate, without needing `L < 1`. -/
theorem uniform_norm_intertwining_defect_le
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] Y) (C : X →L[𝕜] Y) (T : X →L[𝕜] X)
    (L : ℝ) (n : Nat)
    (hA : ‖A‖ ≤ L) (hT : ‖T‖ ≤ L) :
    ‖C.comp (T ^ n) - (A ^ n).comp C‖ ≤
      (n : ℝ) * L ^ (n - 1) * ‖intertwiningDefect A C T‖ := by
  cases n with
  | zero =>
      simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.id_comp, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n =>
      have hL : 0 ≤ L := (norm_nonneg A).trans hA
      have hbound :
          ‖C.comp (T ^ (n + 1)) - (A ^ (n + 1)).comp C‖ ≤
            (n + 1 : ℝ) * L ^ n * ‖intertwiningDefect A C T‖ := by
        calc
          ‖C.comp (T ^ (n + 1)) - (A ^ (n + 1)).comp C‖ ≤
              ∑ j ∈ Finset.range (n + 1),
                ‖A‖ ^ (n + 1 - 1 - j) *
                  ‖intertwiningDefect A C T‖ * ‖T‖ ^ j :=
            norm_intertwining_defect_le A C T (n + 1)
          _ ≤ ∑ _j ∈ Finset.range (n + 1),
                L ^ n * ‖intertwiningDefect A C T‖ := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            have hApow : ‖A‖ ^ (n - j) ≤ L ^ (n - j) := by
              exact pow_le_pow_left₀ (norm_nonneg A) hA _
            have hTpow : ‖T‖ ^ j ≤ L ^ j := by
              exact pow_le_pow_left₀ (norm_nonneg T) hT _
            have hpow : L ^ (n - j) * L ^ j = L ^ n := by
              rw [← pow_add]
              congr 1
              omega
            simp only [Nat.succ_sub_succ_eq_sub]
            calc
              ‖A‖ ^ (n - j) * ‖intertwiningDefect A C T‖ * ‖T‖ ^ j ≤
                  L ^ (n - j) * ‖intertwiningDefect A C T‖ * L ^ j := by
                gcongr
              _ = (L ^ (n - j) * L ^ j) * ‖intertwiningDefect A C T‖ := by ring
              _ = L ^ n * ‖intertwiningDefect A C T‖ := by rw [hpow]
          _ = (n + 1 : ℝ) * L ^ n * ‖intertwiningDefect A C T‖ := by
            simp
            ring
      simpa only [Nat.succ_sub_one, Nat.cast_succ] using hbound
#print axioms uniform_norm_intertwining_defect_le

private noncomputable def scalarEnd (r : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.lsmul ℝ ℝ r

@[simp] private lemma scalarEnd_mul (r s : ℝ) :
    scalarEnd r * scalarEnd s = scalarEnd (r * s) := by
  ext
  simp [scalarEnd]

@[simp] private lemma scalarEnd_comp (r s : ℝ) :
    (scalarEnd r).comp (scalarEnd s) = scalarEnd (r * s) := by
  ext
  simp [scalarEnd]

@[simp] private lemma scalarEnd_sub (r s : ℝ) :
    scalarEnd r - scalarEnd s = scalarEnd (r - s) := by
  ext
  simp [scalarEnd]

@[simp] private lemma scalarEnd_pow (r : ℝ) (n : Nat) :
    scalarEnd r ^ n = scalarEnd (r ^ n) := by
  induction n with
  | zero =>
      ext
      simp [scalarEnd]
  | succ n ih => simp [pow_succ, ih]

@[simp] private lemma scalarEnd_norm (r : ℝ) : ‖scalarEnd r‖ = |r| := by
  simp [scalarEnd, Real.norm_eq_abs]

/-- Without the bound on `A`, the uniform estimate fails even for real scalar operators. -/
theorem left_norm_bound_is_necessary :
    ∃ (A C T : ℝ →L[ℝ] ℝ) (L : ℝ) (n : Nat),
      ‖T‖ ≤ L ∧
        ¬‖C.comp (T ^ n) - (A ^ n).comp C‖ ≤
          (n : ℝ) * L ^ (n - 1) * ‖intertwiningDefect A C T‖ := by
  refine ⟨scalarEnd 2, scalarEnd 1, scalarEnd 0, 1, 3, ?_, ?_⟩
  · norm_num
  · norm_num [intertwiningDefect]
#print axioms left_norm_bound_is_necessary

/-- Without the bound on `T`, the uniform estimate fails even for real scalar operators. -/
theorem right_norm_bound_is_necessary :
    ∃ (A C T : ℝ →L[ℝ] ℝ) (L : ℝ) (n : Nat),
      ‖A‖ ≤ L ∧
        ¬‖C.comp (T ^ n) - (A ^ n).comp C‖ ≤
          (n : ℝ) * L ^ (n - 1) * ‖intertwiningDefect A C T‖ := by
  refine ⟨scalarEnd 0, scalarEnd 1, scalarEnd 2, 1, 3, ?_, ?_⟩
  · norm_num
  · norm_num [intertwiningDefect]
#print axioms right_norm_bound_is_necessary

/- An additive carrier cannot be empty because its zero element inhabits it. -/
example {E : Type*} [SeminormedAddCommGroup E] : Nonempty E := ⟨0⟩

/- The zero-dimensional space is a one-element carrier, and the first bound remains valid. -/
example (n : Nat) :
    ‖(0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)).comp
          ((0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) ^ n) -
        ((0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) ^ n).comp
          (0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))‖ ≤
      ∑ j ∈ Finset.range n,
        ‖(0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))‖ ^ (n - 1 - j) *
          ‖intertwiningDefect (0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))
            (0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))
            (0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))‖ *
            ‖(0 : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))‖ ^ j := by
  exact norm_intertwining_defect_le 0 0 0 n

/- At time zero, truncated natural subtraction makes the exponent zero and both sides vanish. -/
example
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] Y) (C : X →L[𝕜] Y) (T : X →L[𝕜] X) (L : ℝ) :
    ‖C.comp (T ^ 0) - (A ^ 0).comp C‖ ≤
      (0 : ℝ) * L ^ (0 - 1) * ‖intertwiningDefect A C T‖ := by
  simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.id_comp, sub_self, norm_zero, zero_mul, le_refl]

/- Zero defects, zero maps, and identity maps all satisfy the expected degenerate equations. -/
example
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (n : Nat) :
    intertwiningDefect (1 : E →L[𝕜] E) (1 : E →L[𝕜] E) (1 : E →L[𝕜] E) = 0 ∧
      intertwiningDefect (0 : E →L[𝕜] E) (0 : E →L[𝕜] E) (0 : E →L[𝕜] E) = 0 ∧
      ‖(0 : E →L[𝕜] E).comp ((0 : E →L[𝕜] E) ^ n) -
        ((0 : E →L[𝕜] E) ^ n).comp (0 : E →L[𝕜] E)‖ = 0 := by
  simp [intertwiningDefect]

end D5.S3.Observer.Approximation.IntertwiningDefectPropagation
