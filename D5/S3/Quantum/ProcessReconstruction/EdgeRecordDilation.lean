/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordDilation
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite edge-record isometry traces to the channel on every input matrix. -/

import D5.S3.Quantum.ProcessReconstruction.EdgeRecordQuantum

/-! The finite edge-record isometry traces to the channel on every input matrix. -/

namespace D5.S3.Quantum.EnvironmentRecords.EdgePath

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

variable {n : ℕ}

/-- The retained classical records specify the computational input and all sampled bits. -/
abbrev Environment (n : ℕ) := Word (n + 1) × Records n

def amplitude (n : ℕ) : ℂ := (Real.sqrt ((Fintype.card (Records n) : ℝ)⁻¹) : ℂ)

private theorem amplitude_star (n : ℕ) : star (amplitude n) = amplitude n :=
  Complex.conj_ofReal _

private theorem amplitude_sq (n : ℕ) :
    amplitude n * amplitude n = (Fintype.card (Records n) : ℂ)⁻¹ := by
  rw [← pow_two]
  unfold amplitude
  have h := Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card (Records n) : ℝ)⁻¹)
  rw [← Complex.ofReal_pow, h, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The coherent map writes the local output into the system and keeps the label (x,e,r)
in the environment. The copied and garbage bits are determined by this label. -/
def dilation (b : Bit) :
    Matrix (Word (n + 1) × Environment n) (Word (n + 1)) ℂ :=
  fun p x => if p.2.1 = x then
    if localOutput b p.2.1 p.2.2 = p.1 then amplitude n else 0
    else 0

theorem dilation_isometry (b : Bit) :
    (dilation (n := n) b)ᴴ * dilation (n := n) b = 1 := by
  ext x z
  rw [Matrix.mul_apply, Fintype.sum_prod_type_right]
  by_cases h : x = z
  · subst z
    have hh (p : Environment n) (y : Word (n + 1)) :
        ((dilation (n := n) b)ᴴ) x (y,p) * dilation (n := n) b (y,p) x =
          if localOutput b p.1 p.2 = y then
            (if p.1 = x then (Fintype.card (Records n) : ℂ)⁻¹ else 0)
          else 0 := by
      change star (dilation (n := n) b (y,p) x) * dilation (n := n) b (y,p) x = _
      by_cases hp : p.1 = x
      · unfold dilation
        rw [ite_eq_left hp]
        by_cases hy : localOutput b p.1 p.2 = y
        · rw [ite_eq_left hy, ite_eq_left hp, amplitude_star, amplitude_sq, ite_eq_left hy]
        · rw [ite_eq_right hy, star_zero, zero_mul, ite_eq_right hy]
      · unfold dilation
        rw [ite_eq_right hp]
        simp [hp]
    simp_rw [hh, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    rw [Fintype.sum_prod_type, Matrix.one_apply_eq]
    have hrec : ∑ r : Records n, (Fintype.card (Records n) : ℂ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Records n) ≠ 0))
    calc
      _ = ∑ j : Word (n + 1), if j = x then (∑ _ : Records n,
          (Fintype.card (Records n) : ℂ)⁻¹) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = x <;> simp only [hj, ite_true, ite_false, Finset.sum_const_zero]
      _ = 1 := by simp only [hrec, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · have hk (p : Environment n) (y : Word (n + 1)) :
        ((dilation (n := n) b)ᴴ) x (y,p) * dilation (n := n) b (y,p) z = 0 := by
      by_cases hp : p.1 = x
      · subst x
        simp [Matrix.conjTranspose_apply, dilation, h]
      · simp [Matrix.conjTranspose_apply, dilation, hp]
    simp only [hk, Finset.sum_const_zero, Matrix.one_apply_ne h]

private theorem joint_entry (b : Bit) (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ)
    (y z : Word (n + 1)) (p : Environment n) :
    (dilation (n := n) b * X * (dilation (n := n) b)ᴴ) (y,p) (z,p) =
      if localOutput b p.1 p.2 = y ∧ localOutput b p.1 p.2 = z then
        X p.1 p.1 * (Fintype.card (Records n) : ℂ)⁻¹ else 0 := by
  have hm (j : Word (n + 1)) : (dilation (n := n) b * X) (y,p) j =
      if localOutput b p.1 p.2 = y then amplitude n * X p.1 j else 0 := by
    by_cases hy : localOutput b p.1 p.2 = y
    · simp [Matrix.mul_apply, dilation, hy, ite_mul]
    · simp [Matrix.mul_apply, dilation, hy]
  have ht (j : Word (n + 1)) :
      (dilation (n := n) b * X) (y,p) j * (dilation (n := n) b)ᴴ j (z,p) =
      if p.1 = j then
        (if localOutput b p.1 p.2 = y ∧ localOutput b p.1 p.2 = z then
          X p.1 p.1 * (Fintype.card (Records n) : ℂ)⁻¹ else 0)
      else 0 := by
    rw [hm]
    change (if localOutput b p.1 p.2 = y then amplitude n * X p.1 j else 0) *
      star (dilation (n := n) b (z,p) j) = _
    by_cases hj : p.1 = j
    · subst j
      by_cases hy : localOutput b p.1 p.2 = y
      · by_cases hz : localOutput b p.1 p.2 = z
        · have hd : dilation (n := n) b (z,p) p.1 = amplitude n := by
            unfold dilation
            rw [ite_eq_left rfl, ite_eq_left hz]
          rw [hd, ite_eq_left hy, ite_eq_left rfl, ite_eq_left ⟨hy,hz⟩, amplitude_star]
          rw [mul_comm (amplitude n) (X p.1 p.1), mul_assoc, amplitude_sq]
        · have hd : dilation (n := n) b (z,p) p.1 = 0 := by
            unfold dilation
            rw [ite_eq_left rfl, ite_eq_right hz]
          rw [hd, ite_eq_left rfl, star_zero, mul_zero]
          exact (ite_eq_right (show ¬ (_ ∧ _) from fun h => hz h.2)).symm
      · rw [ite_eq_right hy, zero_mul, ite_eq_left rfl, ite_eq_right (fun h => hy h.1)]
    · simp [dilation, hj]
  rw [Matrix.mul_apply]
  simp only [ht, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The physical partial trace of the finite record isometry equals the CPTP
measure-and-prepare action on every matrix, including off-diagonal inputs. -/
theorem trace_environment_eq_channel (b : Bit)
    (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ) :
    partialTraceRight (dilation (n := n) b * X * (dilation (n := n) b)ᴴ) =
      Action (channel b) X := by
  rw [channel_action]
  ext y z
  change (∑ p : Environment n, (dilation (n := n) b * X * (dilation (n := n) b)ᴴ) (y,p) (z,p)) = _
  simp_rw [joint_entry]
  by_cases hyz : y = z
  · subst z
    simp only [and_self, Matrix.diagonal_apply_eq]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    unfold kernel push
    push_cast
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split <;> simp_all
  · have h (p : Environment n) :
        ¬ (localOutput b p.1 p.2 = y ∧ localOutput b p.1 p.2 = z) :=
      fun h => hyz (h.1.symm.trans h.2)
    simp [h, hyz]

end

end D5.S3.Quantum.EnvironmentRecords.EdgePath
