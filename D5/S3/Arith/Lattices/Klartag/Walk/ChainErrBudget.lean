/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainErrBudget

open MeasureTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain

variable {n : ℕ}

section Inv

/-- `Q_{A⁻¹}` is non-negative: with `x = A⁻¹y`, `⟪y, A⁻¹y⟫ = ⟪x, Ax⟫ ≥ m‖x‖² ≥ 0`. -/
theorem inv_quad_nonneg {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) (y : EuclideanSpace ℝ (Fin n)) :
    (0 : ℝ) ≤ ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y⟫ := by
  set x := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y with hx
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.2 (ne_of_gt hSB.posDef.det_pos)
  have hAx : Matrix.toEuclideanCLM (𝕜 := ℝ) A x = y := by
    have hmul : (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y)
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (A * A⁻¹)) y := by
      rw [map_mul]; rfl
    rw [hx, hmul, Matrix.mul_nonsing_inv A hunit, map_one]
    rfl
  have h1 := hSB.lower x
  rw [hAx] at h1
  have h2 : (0 : ℝ) ≤ m * ‖x‖ ^ 2 := by
    have := hSB.mpos
    positivity
  have h3 : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  rw [h3]
  linarith

/-- `Q_{A⁻¹}(y) ≤ ‖y‖²/m`, from `DriftStopped2.norm_inv_apply_le` and Cauchy–Schwarz. -/
theorem inv_quad_le {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y⟫ ≤ ‖y‖ ^ 2 / m := by
  have hm := hSB.mpos
  have h1 := DriftStopped2.norm_inv_apply_le hSB y
  have h2 : ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y⟫
      ≤ ‖y‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y‖ := real_inner_le_norm _ _
  have h3 : ‖y‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y‖ ≤ ‖y‖ * (‖y‖ / m) :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have h4 : ‖y‖ * (‖y‖ / m) = ‖y‖ ^ 2 / m := by ring
  linarith

end Inv

section Quad

/-- `Q_M(x) = ⟪x, Mx⟫` in the `EuclideanSpace` currency the state bounds are stated in. -/
theorem quadForm_eq_innerLp (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ChainWiring.quadForm M x
      = ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)),
          Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 x)⟫ := by
  rw [Matrix.inner_toEuclideanCLM, ChainWiring.quadForm, dotProduct_comm]

theorem normLp_sq (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = x ⬝ᵥ x :=
  ChainEllipsoid.norm_sq_eq_dotProduct (WithLp.toLp 2 x)

/-- `0 ≤ Q_{A⁻¹}`. -/
theorem quadForm_inv_nonneg {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) (x : Fin n → ℝ) :
    (0 : ℝ) ≤ ChainWiring.quadForm A⁻¹ x := by
  rw [quadForm_eq_innerLp]
  exact inv_quad_nonneg hSB _

/-- `Q_{A⁻¹}(x) ≤ (x ⬝ᵥ x)/m`. -/
theorem quadForm_inv_le {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) (x : Fin n → ℝ) :
    ChainWiring.quadForm A⁻¹ x ≤ (x ⬝ᵥ x) / m := by
  rw [quadForm_eq_innerLp, ← normLp_sq x]
  exact inv_quad_le hSB _

/-- `−Q_B(x) ≤ ‖B‖_op · (x ⬝ᵥ x)`: the increment's overshoot along one constraint direction. -/
theorem neg_quadForm_le_opNorm (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    -ChainWiring.quadForm B x
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * (x ⬝ᵥ x) := by
  have hx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = x ⬝ᵥ x := normLp_sq x
  have habs : |⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)),
        Matrix.toEuclideanCLM (𝕜 := ℝ) B (WithLp.toLp 2 x)⟫|
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖
        * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (WithLp.toLp 2 x)‖ :=
    abs_real_inner_le_norm _ _
  have hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (WithLp.toLp 2 x)‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖
        * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hmul : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖
        * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (WithLp.toLp 2 x)‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * (x ⬝ᵥ x) := by
    have h := mul_le_mul_of_nonneg_left hop
      (norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)))
    calc ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖
          * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (WithLp.toLp 2 x)‖
        ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖
            * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖
              * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖) := h
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖
            * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by ring
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * (x ⬝ᵥ x) := by rw [hx]
  rw [quadForm_eq_innerLp]
  have := (abs_le.1 habs).1
  linarith

/-- `‖q x‖ = x ⬝ᵥ x`: the constraint vector's norm is the squared length of the lattice point. -/
theorem norm_qUT (x : Fin n → ℝ) : ‖ChainWiring.qUT x‖ = x ⬝ᵥ x := by
  have h : ‖ChainWiring.qUT x‖ ^ 2 = (x ⬝ᵥ x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ChainWiring.inner_qUT]
  have h0 : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  nlinarith [norm_nonneg (ChainWiring.qUT x), h, h0]

theorem dotProduct_self_pos {x : Fin n → ℝ} (hx : ChainWiring.qUT x ≠ 0) : 0 < x ⬝ᵥ x := by
  have h0 : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases eq_or_lt_of_le h0 with h | h
  · exact absurd (norm_eq_zero.1 (by rw [norm_qUT, ← h])) hx
  · exact h

end Quad

section LiftTrace

variable {ι : Type*} [DecidableEq ι]

/-- **`ChainWiring.inner_lift_sub` with the test matrix in matrix currency.** -/
theorem inner_matToUT_lift_sub {xs : ι → (Fin n → ℝ)} {W : Finset ι}
    {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.IsSymm) (A' : EuclideanSpace ℝ (UT n)) :
    ⟪Discharge.matToUT C,
        Chain.lift (fun i => ChainWiring.qUT (xs i)) W A' - A'⟫
      = ∑ i ∈ Chain.violated (fun i => ChainWiring.qUT (xs i)) W A',
          ((1 - ⟪A', ChainWiring.qUT (xs i)⟫) / ‖ChainWiring.qUT (xs i)‖ ^ 2)
            * ChainWiring.quadForm C (xs i) := by
  have hsym : symMat (Discharge.matToUT C) = C := by
    ext i j
    exact Discharge.symMat_matToUT hC i j
  have h := ChainWiring.inner_lift_sub (xs := xs) (W := W) (Discharge.matToUT C) A'
  rw [hsym] at h
  exact h

/-- The coefficients of the one-sided lift are non-negative. -/
theorem lift_coeff_nonneg {xs : ι → (Fin n → ℝ)} {W : Finset ι} {A' : EuclideanSpace ℝ (UT n)}
    {i : ι} (hi : i ∈ Chain.violated (fun i => ChainWiring.qUT (xs i)) W A') :
    (0 : ℝ) ≤ (1 - ⟪A', ChainWiring.qUT (xs i)⟫) / ‖ChainWiring.qUT (xs i)‖ ^ 2 :=
  div_nonneg (by linarith [(Chain.mem_violated.1 hi).2]) (sq_nonneg _)

/-- **The lift's trace cost is non-negative against any positive semi-definite test matrix.** -/
theorem inner_matToUT_lift_sub_nonneg {xs : ι → (Fin n → ℝ)} {W : Finset ι}
    {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.IsSymm)
    (hCnn : ∀ x : Fin n → ℝ, (0 : ℝ) ≤ ChainWiring.quadForm C x)
    (A' : EuclideanSpace ℝ (UT n)) :
    (0 : ℝ) ≤ ⟪Discharge.matToUT C,
      Chain.lift (fun i => ChainWiring.qUT (xs i)) W A' - A'⟫ := by
  rw [inner_matToUT_lift_sub hC]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (lift_coeff_nonneg hi) (hCnn _)

/-- **The lift's trace cost, with no Frobenius norm.**  `ChainWiring.coeff_le` replaces the
coefficient by the step's own increment against the same constraint, `‖q i‖ = x_i ⬝ᵥ x_i` cancels
the squared length, and each broken constraint costs at most `t/m` — the increment's operator
scale over the state's lower bound.  A Frobenius Cauchy–Schwarz would cost a further `√n`. -/
theorem inner_matToUT_lift_sub_le {xs : ι → (Fin n → ℝ)} {W : Finset ι}
    {A B : EuclideanSpace ℝ (UT n)} {C : Matrix (Fin n) (Fin n) ℝ} {m t : ℝ}
    (hC : C.IsSymm)
    (hA : A ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hCle : ∀ x : Fin n → ℝ, ChainWiring.quadForm C x ≤ (x ⬝ᵥ x) / m) (hm : 0 < m)
    (ht : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat B)‖ ≤ t) :
    ⟪Discharge.matToUT C,
        Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B)⟫
      ≤ ((Chain.violated (fun i => ChainWiring.qUT (xs i)) W (A + B)).card : ℝ) * (t / m) := by
  classical
  have ht0 : (0 : ℝ) ≤ t := le_trans (norm_nonneg _) ht
  rw [inner_matToUT_lift_sub hC]
  have hterm : ∀ i ∈ Chain.violated (fun i => ChainWiring.qUT (xs i)) W (A + B),
      ((1 - ⟪A + B, ChainWiring.qUT (xs i)⟫) / ‖ChainWiring.qUT (xs i)‖ ^ 2)
        * ChainWiring.quadForm C (xs i) ≤ t / m := by
    intro i hi
    obtain ⟨hiW, hilt⟩ := Chain.mem_violated.1 hi
    have hqne : ChainWiring.qUT (xs i) ≠ 0 := Chain.q_ne_zero_of_nonempty hA hiW
    have hs : 0 < xs i ⬝ᵥ xs i := dotProduct_self_pos hqne
    have hnorm : ‖ChainWiring.qUT (xs i)‖ = xs i ⬝ᵥ xs i := norm_qUT (xs i)
    set s : ℝ := xs i ⬝ᵥ xs i with hsdef
    set lam : ℝ := (1 - ⟪A + B, ChainWiring.qUT (xs i)⟫) / ‖ChainWiring.qUT (xs i)‖ ^ 2 with hlam
    have hlam0 : (0 : ℝ) ≤ lam := lift_coeff_nonneg hi
    have hcoeff : lam ≤ (-⟪B, ChainWiring.qUT (xs i)⟫) / ‖ChainWiring.qUT (xs i)‖ ^ 2 :=
      ChainWiring.coeff_le hA hi
    have hQb : ⟪B, ChainWiring.qUT (xs i)⟫ = ChainWiring.quadForm (symMat B) (xs i) :=
      ChainWiring.quadForm_eq_inner B (xs i)
    have hQble : -ChainWiring.quadForm (symMat B) (xs i) ≤ t * s := by
      refine le_trans (neg_quadForm_le_opNorm (symMat B) (xs i)) ?_
      exact mul_le_mul_of_nonneg_right ht (le_of_lt hs)
    have hcoeff' : lam ≤ (t * s) / s ^ 2 := by
      refine le_trans hcoeff ?_
      rw [hnorm]
      gcongr
      rw [hQb]; exact hQble
    have h1 : lam * ChainWiring.quadForm C (xs i) ≤ lam * (s / m) :=
      mul_le_mul_of_nonneg_left (hCle (xs i)) hlam0
    have h2 : lam * (s / m) ≤ ((t * s) / s ^ 2) * (s / m) :=
      mul_le_mul_of_nonneg_right hcoeff' (by positivity)
    have h3 : ((t * s) / s ^ 2) * (s / m) = t / m := by
      field_simp
    linarith
  calc ∑ i ∈ Chain.violated (fun i => ChainWiring.qUT (xs i)) W (A + B),
        ((1 - ⟪A + B, ChainWiring.qUT (xs i)⟫) / ‖ChainWiring.qUT (xs i)‖ ^ 2)
          * ChainWiring.quadForm C (xs i)
      ≤ (Chain.violated (fun i => ChainWiring.qUT (xs i)) W (A + B)).card • (t / m) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Chain.violated (fun i => ChainWiring.qUT (xs i)) W (A + B)).card : ℝ) * (t / m) := by
        rw [nsmul_eq_mul]

end LiftTrace

section Cost

variable {ι : Type*} [DecidableEq ι]

/-- **The freeze cost, above.**  `StepInputs2.log_det_step_unconj` at the pre-lift state bounds
`log det` by its linearisation; §3 prices the linearisation at `|violated| · t / m`. -/
theorem liftCost_le {xs : ι → (Fin n → ℝ)} {W : Finset ι} {A B : EuclideanSpace ℝ (UT n)}
    {m M t tΔ δ : ℝ}
    (hA : A ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hSB : Discharge.StateBounds (symMat (A + B)) m M)
    (hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat B)‖ ≤ t)
    (hΔ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat
        (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B)))‖ ≤ tΔ)
    (hδ : tΔ / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ChainWiring.liftCost (fun i => ChainWiring.qUT (xs i)) W (A + B)
      ≤ ((Chain.violated (fun i => ChainWiring.qUT (xs i)) W (A + B)).card : ℝ) * (t / m) := by
  classical
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  have hHherm : Matrix.IsHermitian
      (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B))) :=
    Matrix.isHermitian_iff_isSymm.2 (symMat_isSymm _)
  have hstep := StepInputs2.log_det_step_unconj hSB.posDef hSherm hSA hHherm hSB.mpos
    hSB.lower hΔ hδ hδ0 hδ1 hSB.upper hSB.Mpos
  have hsum : symMat (A + B)
      + symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B))
      = symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B)) := by
    rw [← symMat_add]
    congr 1
    abel
  have hineq := hstep.2
  rw [hsum] at hineq
  have htr : ((symMat (A + B))⁻¹
        * symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B))).trace
      = ⟪Discharge.matToUT (symMat (A + B))⁻¹,
          Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B)⟫ :=
    Discharge.trace_mul_symMat_eq_inner (symMat_isSymm (A + B)).inv _
  have hbound := inner_matToUT_lift_sub_le (xs := xs) (W := W) (A := A) (B := B)
    (C := (symMat (A + B))⁻¹) (m := m) (t := t)
    (symMat_isSymm (A + B)).inv hA (quadForm_inv_le hSB) hSB.mpos hop
  have hMpos := hSB.Mpos
  have hnn : (0 : ℝ) ≤ (∑ i, ∑ j,
      ((symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B) - (A + B))) i j) ^ 2)
      / (2 * M ^ 2 * (1 + δ) ^ 2) := by positivity
  rw [htr] at hineq
  show Real.log (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W (A + B))).det
      - Real.log (symMat (A + B)).det ≤ _
  linarith

/-- **The freeze cost is non-negative.**  `log_det_step_unconj` run *backwards* — at the lifted
state, with `H = −Δ` — bounds `log det A'` by `log det (lift A')` minus the trace term, and that
term is `∑_i λ_i ⟪(lift A')⁻¹ x_i, x_i⟫ ≥ 0`: the coefficients of a one-sided lift are
non-negative and the inverse of a positive definite matrix is positive semi-definite.  So the
two-sided freeze budget is the one-sided one. -/
theorem liftCost_nonneg {xs : ι → (Fin n → ℝ)} {W : Finset ι} {A' : EuclideanSpace ℝ (UT n)}
    {m M tΔ δ : ℝ}
    (hSB : Discharge.StateBounds
      (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')) m M)
    (hΔ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat
        (A' - Chain.lift (fun i => ChainWiring.qUT (xs i)) W A'))‖ ≤ tΔ)
    (hδ : tΔ / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (0 : ℝ) ≤ ChainWiring.liftCost (fun i => ChainWiring.qUT (xs i)) W A' := by
  classical
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  have hHherm : (symMat (A' - Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.2 (symMat_isSymm _)
  have hstep := StepInputs2.log_det_step_unconj hSB.posDef hSherm hSA hHherm hSB.mpos
    hSB.lower hΔ hδ hδ0 hδ1 hSB.upper hSB.Mpos
  have hsum : symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')
      + symMat (A' - Chain.lift (fun i => ChainWiring.qUT (xs i)) W A') = symMat A' := by
    rw [← symMat_add]
    congr 1
    abel
  have hineq := hstep.2
  rw [hsum] at hineq
  have hflip : A' - Chain.lift (fun i => ChainWiring.qUT (xs i)) W A'
      = -(Chain.lift (fun i => ChainWiring.qUT (xs i)) W A' - A') := by abel
  have htr : ((symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A'))⁻¹
        * symMat (A' - Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')).trace
      = -⟪Discharge.matToUT (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A'))⁻¹,
          Chain.lift (fun i => ChainWiring.qUT (xs i)) W A' - A'⟫ := by
    rw [Discharge.trace_mul_symMat_eq_inner
      (symMat_isSymm (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')).inv, hflip,
      inner_neg_right]
  have hnneg := inner_matToUT_lift_sub_nonneg (xs := xs) (W := W)
    (C := (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A'))⁻¹)
    (symMat_isSymm (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')).inv
    (quadForm_inv_nonneg hSB) A'
  have hMpos := hSB.Mpos
  have hnn : (0 : ℝ) ≤ (∑ i, ∑ j,
      ((symMat (A' - Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')) i j) ^ 2)
      / (2 * M ^ 2 * (1 + δ) ^ 2) := by positivity
  rw [htr] at hineq
  show (0 : ℝ) ≤ Real.log (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W A')).det
      - Real.log (symMat A').det
  linarith

end Cost

section ChainBudget

variable {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {xs : ι → (Fin n → ℝ)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `A'_k = A₀ + Σ_{j<k+1} π_jξ_j + Σ_{j<k} Δ_j`: the pre-lift state carries the accumulated
Gaussian part at **`k+1`** and the accumulated lift at `k`. -/
theorem preState_eq_sum {q : ι → EuclideanSpace ℝ (UT n)} (k : ℕ) (ω : Ω) :
    ChainWiring.preState q W A₀ ξ k ω
      = A₀ + gaussSum q W A₀ ξ (k + 1) ω + liftSum q W A₀ ξ k ω := by
  rw [StateInvariant.preState_eq, StateInvariant.chain_fst_eq]
  simp only [StateInvariant.gaussSum, Finset.sum_range_succ]
  abel

/-- **`StateBounds` at the pre-lift state**, at the same `m` and `M` as the chain's own states:
`stateGood (k+1)` bounds the accumulated Gaussian part at `k+1` and `stateGood k` the lift at `k`. -/
theorem stateBounds_preState {q : ι → EuclideanSpace ℝ (UT n)} {a₀ r₀ L : ℝ} {k : ℕ} {ω : Ω}
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hr₀ : 0 ≤ r₀) (hL : 0 ≤ L)
    (hacc : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ (k + 1) ω))‖ ≤ r₀)
    (hlift : ‖liftSum q W A₀ ξ k ω‖ ≤ L)
    (hlt : r₀ + L < a₀) :
    Discharge.StateBounds (symMat (ChainWiring.preState q W A₀ ξ k ω))
      (a₀ - (r₀ + L)) (a₀ + (r₀ + L)) := by
  refine StateInvariant.stateBounds_of_opNorm_le (symMat_isSymm _) (by positivity) hlt ?_
  have hdec : symMat (ChainWiring.preState q W A₀ ξ k ω) - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)
      = symMat (gaussSum q W A₀ ξ (k + 1) ω) + symMat (liftSum q W A₀ ξ k ω) := by
    rw [preState_eq_sum, symMat_add, symMat_add, hA₀m]
    abel
  rw [hdec, map_add]
  exact (norm_add_le _ _).trans
    (add_le_add hacc ((StepInputs2.opNorm_symMat_le_norm _).trans hlift))

theorem chainErr_bounds_of_lt_tau {η a₀ r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (hδ1 : c₃ * η < a₀ - (r₀ + c₃ * η))
    (hk : k + 1 < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω) :
    (0 : ℝ) ≤ ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω ∧
      ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω
        ≤ ((Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card : ℝ)
          * (η / (a₀ - (r₀ + c₃ * η))) := by
  classical
  have hq : ∀ i ∈ W, ∀ j ∈ W,
      (0 : ℝ) ≤ ⟪ChainWiring.qUT (xs i), ChainWiring.qUT (xs j)⟫ :=
    fun i _ j _ => ChainWiring.inner_qUT_nonneg _ _
  have hne : ∀ i ∈ W, ChainWiring.qUT (xs i) ≠ 0 :=
    fun i hi => Chain.q_ne_zero_of_nonempty hA₀ hi
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hcη : (0 : ℝ) ≤ c₃ * η := mul_nonneg hc₃ hη
  have hk0 : k < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω := by omega
  obtain ⟨hstep1, hacc1, hcnt1⟩ := stateGood_of_lt_tau (N := N) (q := fun i => ChainWiring.qUT (xs i))
    (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃) hk
  obtain ⟨hstep0, hacc0, hcnt0⟩ := stateGood_of_lt_tau (N := N) (q := fun i => ChainWiring.qUT (xs i))
    (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃) hk0
  have hgs : ∀ j, j < k + 1 →
      ‖gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω‖ ≤ η := fun j hj =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hstep1 j hj)
  have hlift0 : ‖liftSum (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη k ω
      (fun j hj => hgs j (by omega))) ?_
    exact mul_le_mul_of_nonneg_right hcnt0 hη
  have hlift1 : ‖liftSum (fun i => ChainWiring.qUT (xs i)) W A₀ ξ (k + 1) ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη (k + 1) ω hgs) ?_
    exact mul_le_mul_of_nonneg_right hcnt1 hη

  have hVcard : ((Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card : ℝ) ≤ c₃ := by
    have hsplit := Chain.card_chain_snd_succ (ξ := ξ) hA₀ hq hne k ω
    have hle : (Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card
        ≤ (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ (k + 1) ω).2.card := by omega
    exact le_trans (by exact_mod_cast hle) hcnt1
  have hliftStep : ‖liftStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω‖ ≤ c₃ * η := by
    refine le_trans (StateInvariant2.norm_liftStep_le hA₀ hq hne k ω) ?_
    exact mul_le_mul hVcard (hgs k (by omega)) (norm_nonneg _) hc₃

  have hSBpre : Discharge.StateBounds
      (symMat ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).1
        + gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω))
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) :=
    stateBounds_preState hA₀m hr₀ hcη hacc1 hlift0 hlt
  have hSBlift : Discharge.StateBounds
      (symMat (Chain.lift (fun i => ChainWiring.qUT (xs i)) W
        ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).1
          + gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω)))
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) :=
    LiftBound.stateBounds_of_chain_count (k := k + 1) hA₀ hq hne hA₀m hr₀ hcη hacc1 hlift1 hlt

  have hopB : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (symMat (gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω))‖ ≤ η :=
    le_trans (StepInputs2.opNorm_symMat_le_norm _) (hgs k (by omega))
  have hopΔ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat
      (Chain.lift (fun i => ChainWiring.qUT (xs i)) W
          ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).1
            + gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω)
        - ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).1
            + gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω)))‖ ≤ c₃ * η :=
    le_trans (StepInputs2.opNorm_symMat_le_norm _) hliftStep
  have hopΔneg : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat
      (((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).1
            + gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω)
        - Chain.lift (fun i => ChainWiring.qUT (xs i)) W
          ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).1
            + gaussStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω)))‖ ≤ c₃ * η := by
    refine le_trans (StepInputs2.opNorm_symMat_le_norm _) ?_
    rw [norm_sub_rev]
    exact hliftStep
  have hδlt : c₃ * η / (a₀ - (r₀ + c₃ * η)) < 1 := (div_lt_one hm).2 hδ1
  have hδ0 : (0 : ℝ) ≤ c₃ * η / (a₀ - (r₀ + c₃ * η)) := by positivity
  constructor
  · exact liftCost_nonneg (xs := xs) (W := W) hSBlift hopΔneg le_rfl hδ0 hδlt
  · exact liftCost_le (xs := xs) (W := W) (t := η) (tΔ := c₃ * η)
      (Chain.chain_fst_mem_kSet hA₀ hq hne k ω) hSBpre hopB hopΔ le_rfl hδ0 hδlt

/-- The count of constraints broken at one step, bounded by the accumulated contact count. -/
theorem card_newActive_le {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hk : k + 1 < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω) :
    ((Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card : ℝ) ≤ c₃ := by
  have hq : ∀ i ∈ W, ∀ j ∈ W,
      (0 : ℝ) ≤ ⟪ChainWiring.qUT (xs i), ChainWiring.qUT (xs j)⟫ :=
    fun i _ j _ => ChainWiring.inner_qUT_nonneg _ _
  have hne : ∀ i ∈ W, ChainWiring.qUT (xs i) ≠ 0 :=
    fun i hi => Chain.q_ne_zero_of_nonempty hA₀ hi
  obtain ⟨-, -, hcnt1⟩ := stateGood_of_lt_tau (N := N)
    (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) hk
  have hsplit := Chain.card_chain_snd_succ (ξ := ξ) hA₀ hq hne k ω
  have hle : (Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card
      ≤ (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ (k + 1) ω).2.card := by omega
  exact le_trans (by exact_mod_cast hle) hcnt1

/-- **The two-sided form, as `hbdabs` reads it**, at `ε = c₃ · η / m`. -/
theorem chainErr_abs_le_of_lt_tau {η a₀ r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (hδ1 : c₃ * η < a₀ - (r₀ + c₃ * η))
    (hk : k + 1 < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω) :
    |ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω|
      ≤ c₃ * (η / (a₀ - (r₀ + c₃ * η))) := by
  obtain ⟨h0, h1⟩ := chainErr_bounds_of_lt_tau hA₀ hA₀m hη hr₀ hc₃ hlt hδ1 hk
  rw [abs_of_nonneg h0]
  refine le_trans h1 ?_
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  exact mul_le_mul_of_nonneg_right (card_newActive_le hA₀ hk) (by positivity)

theorem sum_chainErr_le_of_lt_tau {η a₀ r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (hδ1 : c₃ * η < a₀ - (r₀ + c₃ * η))
    (hK : K < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω) :
    ∑ k ∈ Finset.range K, ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω
      ≤ ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ K ω).2.card : ℝ)
        * (η / (a₀ - (r₀ + c₃ * η))) := by
  classical
  have hq : ∀ i ∈ W, ∀ j ∈ W,
      (0 : ℝ) ≤ ⟪ChainWiring.qUT (xs i), ChainWiring.qUT (xs j)⟫ :=
    fun i _ j _ => ChainWiring.inner_qUT_nonneg _ _
  have hne : ∀ i ∈ W, ChainWiring.qUT (xs i) ≠ 0 :=
    fun i hi => Chain.q_ne_zero_of_nonempty hA₀ hi
  have hterm : ∀ k ∈ Finset.range K,
      ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω
        ≤ ((Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card : ℝ)
          * (η / (a₀ - (r₀ + c₃ * η))) := by
    intro k hk
    have hk' : k + 1 < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω := by
      have := Finset.mem_range.1 hk
      omega
    exact (chainErr_bounds_of_lt_tau hA₀ hA₀m hη hr₀ hc₃ hlt hδ1 hk').2
  calc ∑ k ∈ Finset.range K,
        ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω
      ≤ ∑ k ∈ Finset.range K,
          ((Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card : ℝ)
            * (η / (a₀ - (r₀ + c₃ * η))) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range K,
          ((Chain.newActive (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω).card : ℝ))
        * (η / (a₀ - (r₀ + c₃ * η))) := by rw [Finset.sum_mul]
    _ = ((Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ K ω).2.card : ℝ)
        * (η / (a₀ - (r₀ + c₃ * η))) := by
        rw [← Nat.cast_sum, Chain.sum_card_newActive hA₀ hq hne K ω]

end ChainBudget

section HandOff

variable {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `k + 1 ≤ τ − 1` is `k + 1 < τ`, since the chain never stops at `0`. -/
theorem lt_tau_of_le_pred {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω} (hN : 1 ≤ N)
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (h : k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1) :
    k + 1 < tau q W A₀ ξ η r₀ c₃ N ω := by
  have h1 := one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃)
    (N := N) hN hr₀ hc₃ ω
  omega

/-- **The reformulation of `GoodPathBounds.goodPathAt_of_S`'s `hbdabs`.**  That binder reads
`∀ ω, ∀ k, |chainErr … k ω| ≤ ε`, on *every* path; this is the same bound restricted to the one
branch of `DriftStopped.stoppedErr` (`:70`) that evaluates `chainErr`, namely `k + 1 ≤ τ ω − 1`.
Off the stopping event the chain's state has no lower bound and `chainErr` is not bounded at all,
so the unrestricted binder is not provable; this one is (§7). -/
def StoppedErrBudget (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (η r₀ c₃ : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ ω : Ω, ∀ k : ℕ, k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1 →
    |ChainWiring.chainErr q W A₀ ξ k ω| ≤ ε

end HandOff

section Deliver

variable {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {xs : ι → (Fin n → ℝ)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The deliverable.**  `ε = c₃ · η / (a₀ − (r₀ + c₃η))` — the accumulated contact bound times
the per-step increment's operator scale, over the state's lower bound. -/
theorem stoppedErrBudget_of_params {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (hδ1 : c₃ * η < a₀ - (r₀ + c₃ * η)) :
    StoppedErrBudget (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N
      (c₃ * (η / (a₀ - (r₀ + c₃ * η)))) := by
  intro ω k hk
  exact chainErr_abs_le_of_lt_tau hA₀ hA₀m hη hr₀ hc₃ hlt hδ1
    (lt_tau_of_le_pred hN hr₀ hc₃ hk)

end Deliver

section Adopted

/-- **`ε` at the adopted parameters**, at a free contact threshold: the accumulated contact bound
`c₃` times the per-step increment scale `η`, over the state's lower bound `mAt n c₃`. -/
noncomputable def epsAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  c₃ * (DriftStopped6.etaAdopted n / GoodPathBounds.mAt n c₃)

end Adopted

section Integrability

open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped

variable {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`GoodPathBounds.integrable_stoppedErr` under the restricted budget.**  The frozen proof reads
`hbd ω k` only inside `if_pos h1`, where `h1 : k + 1 ≤ τ ω − 1`; this is the same theorem with the
hypothesis weakened to that branch.  Together with `sum_good_le_of_stopped` (§6) these are the two
places the tree consumes a bound on `chainErr`, so `StoppedErrBudget` is enough for both. -/
theorem integrable_stoppedErr_of_stopped {a₀ η r₀ c₃ cq ε : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hcq : 0 ≤ cq) (hε : 0 ≤ ε) {cstep : ℝ}
    (hτ : Measurable (tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N))
    (hbd : ∀ ω k, k + 1 ≤ tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N ω - 1 →
      |ChainWiring.chainErr q W A₀ (ChainSetup.step cstep) k ω| ≤ ε)
    (k : ℕ) :
    Integrable (stoppedErr q W A₀ (ChainSetup.step cstep) η r₀ c₃ cq N k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  classical
  set Cv : ℝ := Real.sqrt n / (a₀ - (r₀ + c₃ * η)) with hCv
  have hCv0 : 0 ≤ Cv := by
    have : 0 < a₀ - (r₀ + c₃ * η) := by linarith
    rw [hCv]; positivity
  have hdom : Integrable (fun ω : ℕ → EuclideanSpace ℝ (UT n) =>
      ε + cq * ‖ChainSetup.step cstep k ω‖ ^ 2 + Cv * ‖ChainSetup.step cstep k ω‖)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
    ((integrable_const ε).add ((ChainSetup.integrable_norm_sq_step cstep k).const_mul cq)).add
      ((GoodPathBounds.integrable_norm_step cstep k).const_mul Cv)
  refine Integrable.mono' hdom
    (GoodPathBounds.measurable_stoppedErr
      (fun j => ChainSetup.measurable_step cstep j) hτ k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hnn : (0 : ℝ) ≤ ‖ChainSetup.step cstep k ω‖ := norm_nonneg _
  have hsq : (0 : ℝ) ≤ cq * ‖ChainSetup.step cstep k ω‖ ^ 2 := by positivity
  have hlin : (0 : ℝ) ≤ Cv * ‖ChainSetup.step cstep k ω‖ := mul_nonneg hCv0 hnn
  rw [stoppedErr]
  by_cases h1 : k + 1 ≤ tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N ω - 1
  · rw [if_pos h1]
    have := hbd ω k h1
    rw [abs_le] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · rw [if_neg h1]
    by_cases h2 : k < tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N ω
    · rw [if_pos h2]
      have hproj : ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ≤ ‖ChainSetup.step cstep k ω‖ :=
        Submodule.norm_starProjection_apply_le _ _
      have hp0 : (0 : ℝ) ≤ ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ := norm_nonneg _
      have hq2 : ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2 ≤ ‖ChainSetup.step cstep k ω‖ ^ 2 := by nlinarith
      have hA : cq * ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2 ≤ cq * ‖ChainSetup.step cstep k ω‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hq2 hcq
      have hB : (0 : ℝ) ≤ cq * ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2 := by positivity
      have hV := DriftStopped2.norm_stoppedV_le (ξ := ChainSetup.step cstep) (N := N)
        hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
      have hinner : |⟪stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω,
          ChainSetup.step cstep k ω⟫| ≤ Cv * ‖ChainSetup.step cstep k ω‖ :=
        le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right hV hnn)
      rw [abs_le] at hinner ⊢
      constructor <;> linarith [hinner.1, hinner.2]
    · rw [if_neg h2]
      rw [abs_zero]
      linarith

end Integrability

end D5.S3.Arith.Lattices.Klartag.Walk.ChainErrBudget
