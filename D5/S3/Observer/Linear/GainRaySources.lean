/- GID: D5/S3/Observer/Linear/GainRaySources
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRaySources
   mirror-E: none(waiver:normalized-and-identical-row-source-worlds)
   anchors: []
   utility: none
   digest: Positive unnormalized and identical-row sources retain the literal whole-world readings. -/

import D5.S3.Observer.Linear.GainRayHistory

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

/-- Chart coordinates impose only positivity and a nonzero whole coefficient vector. -/
def chartWorld (d : ℕ) (x r : ℝ) (hx : 0 < x) (hr : 0 < r)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) : World d :=
  ⟨sourceChart x r, source_chart_legal x r hx hr, β, hβ, δ⟩

/-- The full chart's pure-J factors at the original consecutive clocks. -/
theorem source_chart_pureJ (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (n : ℕ) :
    Matrix.trace (acquisition (List.replicate n true) * sourceChart x r) =
      if n % 2 = 0 then 1 else (x + r) / (1 + x * r) := by
  have hj : action true ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [acquisition_pure, pow_eq_pow_mod n hj]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp only [h, pow_zero, one_mul, ite_true]
    exact (source_chart_legal x r hx hr).2.2
  · have hn : ¬n % 2 = 0 := by omega
    simp only [h, pow_one, if_neg (by omega : ¬(1 : ℕ) = 0)]
    simp [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      sourceChart, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
    <;> ring

structure UnnormalizedWorld (d : ℕ) where
  source : Mat
  positive : ∀ i j, 0 < source i j
  rank_one : source.rank = 1
  coeff : Coeff d
  nonzero : coeff ≠ 0
  drift : ℝ

private theorem source_trace_positive {d : ℕ} (W : UnnormalizedWorld d) :
    0 < Matrix.trace W.source := by
  simp only [Matrix.trace, Fin.sum_univ_two]
  exact add_pos (W.positive 0 0) (W.positive 1 1)

private theorem normalized_source_legal {d : ℕ} (W : UnnormalizedWorld d) :
    LegalSource ((Matrix.trace W.source)⁻¹ • W.source) := by
  have ht := source_trace_positive W
  refine ⟨fun i j => mul_pos (inv_pos.mpr ht) (W.positive i j), ?_, ?_⟩
  · rw [Matrix.rank_smul_of_mem_nonZeroDivisors W.source
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (ne_of_gt ht))), W.rank_one]
  · rw [Matrix.trace_smul]
    simp [ne_of_gt ht]

def normalizeWorld {d : ℕ} (W : UnnormalizedWorld d) : World d :=
  ⟨(Matrix.trace W.source)⁻¹ • W.source, normalized_source_legal W,
    Matrix.trace W.source • W.coeff,
    smul_ne_zero (ne_of_gt (source_trace_positive W)) W.nonzero, W.drift⟩

/-- Every literal clock agrees with the unnormalized positive rank-one representation. -/
theorem normalized_readAt {d : ℕ} (W : UnnormalizedWorld d) (w : List Bool) (i : ℕ) :
    readAt (normalizeWorld W) w i =
      (gain d W.coeff).eval (i : ℝ) *
        Matrix.trace (acquisition (w.take i) * W.source) + W.drift := by
  have hg : gain d (Matrix.trace W.source • W.coeff) =
      Matrix.trace W.source • gain d W.coeff := (Polynomial.ofFn (d + 1)).map_smul _ _
  unfold readAt normalizeWorld
  dsimp only
  rw [hg, Polynomial.eval_smul]
  exact normalization_read W.source _ _ _ (ne_of_gt (source_trace_positive W))

def identicalRow (θ : ℝ) : Mat := !![1 - θ, θ; 1 - θ, θ]

private theorem identical_row_chart (θ : ℝ) (hθ' : θ < 1) :
    identicalRow θ = sourceChart 1 (θ / (1 - θ)) := by
  have ht : 1 - θ ≠ 0 := by linarith
  have hi : (1 + 1 * (θ / (1 - θ)))⁻¹ = 1 - θ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [identicalRow, sourceChart, hi] <;> field_simp <;> ring

/-- Every parameter in the open unit interval gives a legal original source. -/
theorem identical_row_legal (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) :
    LegalSource (identicalRow θ) := by
  rw [identical_row_chart θ hθ']
  exact source_chart_legal 1 _ zero_lt_one (div_pos hθ (by linarith))

def rowWorld (d : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) : World d :=
  ⟨identicalRow θ, identical_row_legal θ hθ hθ', β, hβ, δ⟩

private theorem identical_row_J (θ : ℝ) : action true * identicalRow θ = identicalRow θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [action, identicalRow,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem identical_row_pureJ (θ : ℝ) (n : ℕ) :
    acquisition (List.replicate n true) * identicalRow θ = identicalRow θ := by
  induction n with
  | zero => simp [acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
  | succ n ih =>
      rw [List.replicate_succ', acquisition_append, mul_assoc, ih, identical_row_J]

/-- Every pure-J prefix, including no actions, has its original clock polynomial reads. -/
theorem identical_row_readings (d : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) (n : ℕ) :
    readings (rowWorld d θ hθ hθ' β hβ δ) (List.replicate n true) =
      fun i : Fin ((List.replicate n true).length + 1) =>
        (gain d β).eval (i.val : ℝ) + δ := by
  ext i
  change (gain d β).eval (i.val : ℝ) *
    Matrix.trace (acquisition ((List.replicate n true).take i.val) * identicalRow θ) + δ = _
  rw [List.take_replicate, identical_row_pureJ]
  simp [identicalRow, Matrix.trace, Fin.sum_univ_two]

#print axioms normalized_readAt
#print axioms identical_row_readings
end D5.S3.Observer.Linear.GainRay
