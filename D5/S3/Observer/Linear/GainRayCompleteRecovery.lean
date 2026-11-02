/- GID: D5/S3/Observer/Linear/GainRayCompleteRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayCompleteRecovery
   mirror-E: none(waiver:full-native-complete-recovery)
   anchors: []
   utility: none
   digest: One literal fixed trajectory identifies every original world and returns exact gain coefficients within the complete recovery bound. -/

import D5.S3.Observer.Linear.GainRayCompleteCritical

set_option autoImplicit false
noncomputable section
open scoped Matrix
open Classical
namespace D5.S3.Observer.Linear.GainRay

/-- A fixed chronological word, with a read after every individual atom. -/
def recoveryWord (d : ℕ) : List Bool :=
  List.replicate (2*(d+1)) false ++ [true] ++ List.replicate (2*d+1) false

private theorem recovery_length (d : ℕ) : (recoveryWord d).length = 4*d+4 := by
  simp [recoveryWord]
  omega

/-- A nonzero degree-bounded gain cannot vanish once in every disjoint adjacent pair. -/
private theorem consecutive_nonroots (d s : ℕ) (β : Coeff d) (hβ : β ≠ 0) :
    ∃ j : Fin (d+1),
      (gain d β).eval ((s+2*j.val : ℕ) : ℝ) ≠ 0 ∧
      (gain d β).eval ((s+2*j.val+1 : ℕ) : ℝ) ≠ 0 := by
  by_contra h
  have hz : ∀ j : Fin (d+1), ∃ r : ℕ, (r = 0 ∨ r = 1) ∧
      (gain d β).eval ((s+2*j.val+r : ℕ) : ℝ) = 0 := by
    intro j
    by_cases hj : (gain d β).eval ((s+2*j.val : ℕ) : ℝ) = 0
    · exact ⟨0, Or.inl rfl, by simpa using hj⟩
    · exact ⟨1, Or.inr rfl, by simpa using not_and.mp (not_exists.mp h j) hj⟩
  choose r hr hz using hz
  let t : Fin (d+1) → ℝ := fun j => ((s+2*j.val+r j : ℕ) : ℝ)
  have ht : Function.Injective t := by
    intro i j he
    have hn : s+2*i.val+r i = s+2*j.val+r j := by exact_mod_cast he
    have hi := hr i
    have hj := hr j
    apply Fin.ext
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
  apply hβ
  apply evaluation_injective d (d+1) t ht le_rfl
  ext j
  rw [evaluation_polynomial, hz]
  simp [evaluate]

private theorem recovery_prefix (d : ℕ) (i : ℕ) (hi : i ≤ 2*(d+1)) :
    (recoveryWord d).take i = List.replicate i false := by
  simp [recoveryWord, List.take_append_of_le_length (by simpa using hi),
    min_eq_left hi]

private theorem recovery_tail (d r : ℕ) (hr : r ≤ 2*d+1) :
    acquisition ((recoveryWord d).take (2*(d+1)+1+r)) =
      action false ^ r * action true * action false ^ (2*(d+1)) := by
  have ht : (recoveryWord d).take (2*(d+1)+1+r) =
      List.replicate (2*(d+1)) false ++ [true] ++ List.replicate r false := by
    simp [recoveryWord, List.take_append, List.take_replicate, min_eq_left hr]
  rw [ht]
  induction r with
  | zero => simp [acquisition_append, acquisition_pure]
  | succ r ih =>
      rw [List.replicate_succ', ← List.append_assoc, acquisition_append]
      rw [ih (by omega), pow_succ']
      simp only [Matrix.mul_assoc]

private theorem powers_trace (S T : Mat)
    (h0 : Matrix.trace S = Matrix.trace T)
    (h1 : Matrix.trace (action false * S) = Matrix.trace (action false * T))
    (k : ℕ) : Matrix.trace (action false ^ k * S) =
      Matrix.trace (action false ^ k * T) := by
  cases k with
  | zero => simpa using h0
  | succ k =>
      obtain ⟨a,b,_,_,he⟩ := m_power_coordinates k
      simp [he, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
        Matrix.trace_smul, h0, h1]

private theorem backwards_trace (S T : Mat) (k : ℕ)
    (h0 : Matrix.trace (action false ^ k * S) = Matrix.trace (action false ^ k * T))
    (h1 : Matrix.trace (action false ^ (k+1) * S) =
      Matrix.trace (action false ^ (k+1) * T)) :
    Matrix.trace S = Matrix.trace T ∧
      Matrix.trace (action false * S) = Matrix.trace (action false * T) := by
  have hm : action false ^ 2 = action false + (1 : Mat) := by
    rw [action_m_shape]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  induction k with
  | zero => simpa using And.intro h0 h1
  | succ k ih =>
      apply ih ?_ h0
      have he (U : Mat) :
          Matrix.trace (action false ^ (k+1+1) * U) =
          Matrix.trace (action false ^ (k+1) * U) + Matrix.trace (action false ^ k * U) := by
        rw [show k+1+1 = k+2 by omega, pow_add, hm, Matrix.mul_add,
          Matrix.mul_one, Matrix.add_mul, Matrix.trace_add]
        rw [← pow_succ]
      rw [he S, he T] at h1
      linarith

private theorem four_traces (S T : Mat)
    (h0 : Matrix.trace S = Matrix.trace T)
    (hM : Matrix.trace (action false * S) = Matrix.trace (action false * T))
    (hJ : Matrix.trace (action true * S) = Matrix.trace (action true * T))
    (hMJ : Matrix.trace (action false * (action true * S)) =
      Matrix.trace (action false * (action true * T))) : S = T := by
  simp [action_m_shape, action_j_shape, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two] at h0 hM hJ hMJ
  ext i j
  fin_cases i <;> fin_cases j <;> linarith

end D5.S3.Observer.Linear.GainRay
