/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Quadratic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Taylor
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Moments
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Commutator

/-! The constant, linear, and quadratic Taylor coefficients of the four-copy defect. -/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

noncomputable section

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarQuadratic

open D5.S3.Quantum.Analysis.RefinedBMVNearScalarTaylor
  (orderedProd gapWeight traceCoeff traceCoeff_sub_sorted)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarMoments (sum_coordinate_mul_coordinate)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator (four_copy_hessian_ge)
open D5.S3.TotalVariation.ParityKernelMasses (antidiagonal_tuple_card)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Uniform mean over the four-part weak compositions of `p`. -/
def compositionMean (p : ℕ) (f : (Fin 4 → ℕ) → ℝ) : ℝ :=
  (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, f r) /
    ((Finset.Nat.antidiagonalTuple 4 p).card : ℝ)

/-- The mean Taylor coefficient minus the coefficient for four equal gaps. -/
def defectCoeff (p : ℕ) (H B : Matrix n n ℂ) (m : ℕ) : ℝ :=
  compositionMean p (fun r => traceCoeff (fun i => (r i : ℝ)) H B m) -
    traceCoeff (fun _ => (p : ℝ) / 4) H B m

private theorem card_four (p : ℕ) :
    (Finset.Nat.antidiagonalTuple 4 p).card = (p + 3).choose 3 := by
  simpa only [show p + 4 - 1 = p + 3 by omega] using
    (antidiagonal_tuple_card (d := 4) (by decide) p)

private theorem compositionMean_const (p : ℕ) (c : ℝ) :
    compositionMean p (fun _ => c) = c := by
  rw [compositionMean, Finset.sum_const, nsmul_eq_mul, card_four]
  exact mul_div_cancel_left₀ c
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega))))

private theorem compositionMean_congr (p : ℕ) {f g : (Fin 4 → ℕ) → ℝ}
    (h : ∀ r ∈ Finset.Nat.antidiagonalTuple 4 p, f r = g r) :
    compositionMean p f = compositionMean p g := by
  unfold compositionMean
  rw [Finset.sum_congr rfl h]

private theorem compositionMean_add (p : ℕ) (f g : (Fin 4 → ℕ) → ℝ) :
    compositionMean p (fun r => f r + g r) = compositionMean p f + compositionMean p g := by
  simp only [compositionMean, Finset.sum_add_distrib, add_div]

private theorem compositionMean_mul_right (p : ℕ) (f : (Fin 4 → ℕ) → ℝ) (c : ℝ) :
    compositionMean p (fun r => f r * c) = compositionMean p f * c := by
  unfold compositionMean
  rw [div_mul_eq_mul_div, Finset.sum_mul]

private theorem defectCoeff_eq_centered (p : ℕ) (H B : Matrix n n ℂ) (m : ℕ) (c : ℝ) :
    defectCoeff p H B m =
      compositionMean p (fun r => traceCoeff (fun i => (r i : ℝ)) H B m - c) -
        (traceCoeff (fun _ => (p : ℝ) / 4) H B m - c) := by
  have hc := compositionMean_const p c
  unfold compositionMean at hc
  simp only [defectCoeff, compositionMean, Finset.sum_sub_distrib, sub_div, hc]
  ring

private theorem sum_cast_coordinates (p : ℕ) (r : Fin 4 → ℕ)
    (hr : r ∈ Finset.Nat.antidiagonalTuple 4 p) :
    (∑ i, (r i : ℝ)) = (p : ℝ) := by
  exact_mod_cast (Finset.Nat.mem_antidiagonalTuple.mp hr)

private theorem sum_balanced (p : ℕ) :
    (∑ _ : Fin 4, (p : ℝ) / 4) = (p : ℝ) := by
  rw [Fin.sum_univ_four]
  ring

private theorem choose_five_div_choose_three (p : ℕ) :
    ((p + 3).choose 5 : ℝ) / ((p + 3).choose 3 : ℝ) =
      (p : ℝ) * ((p : ℝ) - 1) / 20 := by
  cases p with
  | zero => norm_num [Nat.choose_eq_zero_of_lt (show 3 < 5 by decide)]
  | succ q =>
    have h₄ := Nat.choose_succ_right_eq (q + 1 + 3) 3
    have h₅ := Nat.choose_succ_right_eq (q + 1 + 3) 4
    rw [show q + 1 + 3 - 3 = q + 1 by omega] at h₄
    rw [show q + 1 + 3 - 4 = q by omega] at h₅
    have h₄' : ((q + 1 + 3).choose 4 : ℝ) * 4 =
        ((q + 1 + 3).choose 3 : ℝ) * ((q : ℝ) + 1) := by
      exact_mod_cast h₄
    have h₅' : ((q + 1 + 3).choose 5 : ℝ) * 5 =
        ((q + 1 + 3).choose 4 : ℝ) * (q : ℝ) := by
      exact_mod_cast h₅
    have hcard : ((q + 1 + 3).choose 3 : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
    rw [Nat.cast_succ]
    apply (div_eq_iff hcard).2
    calc
      _ = ((q + 1 + 3).choose 4 : ℝ) * (q : ℝ) / 5 := by linarith only [h₅']
      _ = _ := by
        rw [show ((q + 1 + 3).choose 4 : ℝ) =
          ((q + 1 + 3).choose 3 : ℝ) * ((q : ℝ) + 1) / 4 by linarith only [h₄']]
        ring

private theorem compositionMean_pair (p : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    compositionMean p (fun r => (r i : ℝ) * (r j : ℝ)) =
      (p : ℝ) * ((p : ℝ) - 1) / 20 := by
  have hsum : (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, (r i : ℝ) * (r j : ℝ)) =
      ((p + 3).choose 5 : ℝ) := by
    exact_mod_cast (sum_coordinate_mul_coordinate p i j hij)
  rw [compositionMean, hsum, card_four, choose_five_div_choose_three]

-- The list underlying the antidiagonal gives the same sum without membership side goals.
private theorem sum_antidiagonal (m : ℕ) (f : (Fin 4 → ℕ) → ℝ) :
    (∑ k ∈ Finset.Nat.antidiagonalTuple 4 m, f k) =
      ((List.Nat.antidiagonalTuple 4 m).map f).sum := by
  rw [Finset.sum_eq_multiset_sum]
  change (Multiset.map f (↑(List.Nat.antidiagonalTuple 4 m) : Multiset _)).sum = _
  rw [Multiset.map_coe, Multiset.sum_coe]

private theorem antidiagonal_zero : List.Nat.antidiagonalTuple 4 0 = [![0, 0, 0, 0]] := by
  rfl

private theorem antidiagonal_one :
    List.Nat.antidiagonalTuple 4 1 = [![0, 0, 0, 1], ![0, 0, 1, 0],
      ![0, 1, 0, 0], ![1, 0, 0, 0]] := by
  rfl

private theorem antidiagonal_two :
    List.Nat.antidiagonalTuple 4 2 = [![0, 0, 0, 2], ![0, 0, 1, 1], ![0, 0, 2, 0],
      ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 2, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0],
      ![1, 1, 0, 0], ![2, 0, 0, 0]] := by
  rfl

private theorem orderedProd_four {M : Type*} [Monoid M] (x : Fin 4 → M) :
    orderedProd x = x 0 * x 1 * x 2 * x 3 := by
  simp only [orderedProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] <;> rfl

private theorem trace_four_rotate (A B C D : Matrix n n ℂ) :
    (A * B * C * D).trace = (B * C * D * A).trace := by
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_comm A (B * C * D))

private theorem trace_four_single (P B : Matrix n n ℂ) :
    (P * B * B * B * B).trace = (P * B ^ 4).trace ∧
    (B * (P * B) * B * B).trace = (P * B ^ 4).trace ∧
    (B * B * (P * B) * B).trace = (P * B ^ 4).trace ∧
    (B * B * B * (P * B)).trace = (P * B ^ 4).trace := by
  have h₀ : (P * B * B * B * B).trace = (P * B ^ 4).trace := by
    congr 1
    noncomm_ring
  have h₁ := (trace_four_rotate B (P * B) B B).trans h₀
  have h₂ := (trace_four_rotate B B (P * B) B).trans h₁
  exact ⟨h₀, h₁, h₂, (trace_four_rotate B B B (P * B)).trans h₂⟩

private theorem trace_four_adjacent (H B : Matrix n n ℂ) :
    ((H * B) * (H * B) * B * B).trace = (H * B * H * B ^ 3).trace ∧
    ((H * B) * B * B * (H * B)).trace = (H * B * H * B ^ 3).trace ∧
    (B * (H * B) * (H * B) * B).trace = (H * B * H * B ^ 3).trace ∧
    (B * B * (H * B) * (H * B)).trace = (H * B * H * B ^ 3).trace := by
  let X := H * B
  have h₀ : (X * X * B * B).trace = (H * B * H * B ^ 3).trace := by
    dsimp only [X]
    congr 1
    noncomm_ring
  have h₁ := (trace_four_rotate B X X B).trans h₀
  have h₂ := (trace_four_rotate B B X X).trans h₁
  exact ⟨h₀, (trace_four_rotate X B B X).trans h₂, h₁, h₂⟩

private theorem trace_four_opposite (H B : Matrix n n ℂ) :
    ((H * B) * B * (H * B) * B).trace = (H * B ^ 2 * H * B ^ 2).trace ∧
    (B * (H * B) * B * (H * B)).trace = (H * B ^ 2 * H * B ^ 2).trace := by
  have h : ((H * B) * B * (H * B) * B).trace = (H * B ^ 2 * H * B ^ 2).trace := by
    congr 1
    noncomm_ring
  exact ⟨h, (trace_four_rotate B (H * B) B (H * B)).trans h⟩

private theorem traceCoeff_zero (g : Fin 4 → ℝ) (H B : Matrix n n ℂ) :
    traceCoeff g H B 0 = (B ^ 4).trace.re := by
  have h : B * B * B * B = B ^ 4 := by noncomm_ring
  rw [traceCoeff, sum_antidiagonal, antidiagonal_zero]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    gapWeight, Fin.prod_univ_four, orderedProd_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
    Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul, add_zero, h]

private theorem traceCoeff_one (g : Fin 4 → ℝ) (H B : Matrix n n ℂ) :
    traceCoeff g H B 1 = (∑ i, g i) * (H * B ^ 4).trace.re := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := trace_four_single H B
  rw [traceCoeff, sum_antidiagonal, antidiagonal_one, Fin.sum_univ_four]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    gapWeight, Fin.prod_univ_four, orderedProd_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, pow_zero, pow_one, div_one,
    one_mul, mul_one, add_zero, h₀, h₁, h₂, h₃]
  ring

private theorem traceCoeff_two_sub_sorted (g : Fin 4 → ℝ) (H B : Matrix n n ℂ) :
    traceCoeff g H B 2 - ((∑ i, g i) ^ 2 / (Nat.factorial 2 : ℝ)) * (H ^ 2 * B ^ 4).trace.re =
      (g 0 * g 1 + g 0 * g 3 + g 1 * g 2 + g 2 * g 3) *
        ((H * B * H * B ^ 3).trace.re - (H ^ 2 * B ^ 4).trace.re) +
      (g 0 * g 2 + g 1 * g 3) *
        ((H * B ^ 2 * H * B ^ 2).trace.re - (H ^ 2 * B ^ 4).trace.re) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := trace_four_single (H ^ 2) B
  obtain ⟨ha₀₁, ha₀₃, ha₁₂, ha₂₃⟩ := trace_four_adjacent H B
  obtain ⟨ho₀₂, ho₁₃⟩ := trace_four_opposite H B
  rw [traceCoeff_sub_sorted, sum_antidiagonal, antidiagonal_two]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    gapWeight, Fin.prod_univ_four, orderedProd_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, pow_zero, pow_one, div_one,
    one_mul, mul_one, h₀, h₁, h₂, h₃, ha₀₁, ha₀₃, ha₁₂, ha₂₃, ho₀₂, ho₁₃,
    sub_self, mul_zero, zero_add, add_zero]
  ring

theorem defectCoeff_zero (p : ℕ) (H B : Matrix n n ℂ) : defectCoeff p H B 0 = 0 := by
  simp only [defectCoeff, traceCoeff_zero, compositionMean_const, sub_self]

theorem defectCoeff_one (p : ℕ) (H B : Matrix n n ℂ) : defectCoeff p H B 1 = 0 := by
  simp only [defectCoeff, traceCoeff_one, sum_balanced]
  rw [compositionMean_congr p (g := fun _ => (p : ℝ) * (H * B ^ 4).trace.re),
    compositionMean_const, sub_self]
  intro r hr
  rw [sum_cast_coordinates p r hr]

/-- The exact quadratic coefficient, with the Hessian used by `four_copy_hessian_ge`. -/
theorem defectCoeff_two (p : ℕ) (H B : Matrix n n ℂ) :
    defectCoeff p H B 2 =
      ((p : ℝ) * ((p : ℝ) + 4) / 40) *
        (((3 : ℂ) • (H ^ 2 * B ^ 4) - (2 : ℂ) • (H * B * H * B ^ 3) -
          H * B ^ 2 * H * B ^ 2).trace).re := by
  let U := (H ^ 2 * B ^ 4).trace.re
  let V := (H * B * H * B ^ 3).trace.re
  let W := (H * B ^ 2 * H * B ^ 2).trace.re
  let c := ((p : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) * U
  let b : ℝ := (p : ℝ) / 4
  rw [defectCoeff_eq_centered p H B 2 c]
  have hmean :
      compositionMean p (fun r => traceCoeff (fun i => (r i : ℝ)) H B 2 - c) =
        compositionMean p (fun r =>
          ((r 0 : ℝ) * (r 1 : ℝ) + (r 0 : ℝ) * (r 3 : ℝ) + (r 1 : ℝ) * (r 2 : ℝ) +
             (r 2 : ℝ) * (r 3 : ℝ)) * (V - U) +
          ((r 0 : ℝ) * (r 2 : ℝ) + (r 1 : ℝ) * (r 3 : ℝ)) * (W - U)) := by
    apply compositionMean_congr
    intro r hr
    have h := traceCoeff_two_sub_sorted (fun i => (r i : ℝ)) H B
    rw [sum_cast_coordinates p r hr] at h
    exact h
  have hbalanced :
      traceCoeff (fun _ => (p : ℝ) / 4) H B 2 - c =
        (b * b + b * b + b * b + b * b) * (V - U) + (b * b + b * b) * (W - U) := by
    have h := traceCoeff_two_sub_sorted (fun _ => (p : ℝ) / 4) H B
    rw [sum_balanced p] at h
    exact h
  rw [hmean, hbalanced]
  simp only [compositionMean_add, compositionMean_mul_right,
    compositionMean_pair p 0 1 (by decide), compositionMean_pair p 0 3 (by decide),
    compositionMean_pair p 1 2 (by decide), compositionMean_pair p 2 3 (by decide),
    compositionMean_pair p 0 2 (by decide), compositionMean_pair p 1 3 (by decide),
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  dsimp only [b, U, V, W]
  ring

theorem defectCoeff_two_ge (p : ℕ) (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.PosSemidef) :
    ((p : ℝ) * ((p : ℝ) + 4) / 40) * (3 * ‖B * (H * B - B * H)‖ ^ 2) ≤
      defectCoeff p H B 2 := by
  rw [defectCoeff_two]
  exact mul_le_mul_of_nonneg_left (four_copy_hessian_ge H B hH hB) (by positivity)

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarQuadratic
