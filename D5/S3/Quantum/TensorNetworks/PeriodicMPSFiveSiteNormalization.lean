/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteNormalization
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteNormalization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialFiber]
   utility: none
   digest: The normalized five-site marginal is invariant under complex projective scaling. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialFiber
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAlignedFiber

/-! Passing between raw and trace-one observations identifies the special
normalized fiber with the same two projective rays. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteNormalization

open Matrix hiding gram
open PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteSpecialFiber
  PeriodicMPSFiveSiteAlignedFiber
open private sparse from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialFiber
open private a b from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAlignedFiber

noncomputable section

/-- The squared mass of the necklaces with cyclic multiplicities. -/
def mass (p : Fin 8 → ℂ) : ℝ := (gram p).trace.re

theorem mass_eq_sum (p : Fin 8 → ℂ) :
    mass p = ∑ i : Fin 4, ∑ j : Fin 8, Complex.normSq (flatten p i j) := by
  have h : (gram p).trace =
      (↑(∑ i : Fin 4, ∑ j : Fin 8, Complex.normSq (flatten p i j)) : ℂ) := by
    simp only [gram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Complex.mul_conj _
  exact (congrArg Complex.re h).trans (Complex.ofReal_re _)

private theorem flatten_injective : Function.Injective (flatten (R := ℂ)) := by
  intro p q h
  funext i
  fin_cases i
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 0) 5
  · exact congrFun (congrFun h 0) 7
  · exact congrFun (congrFun h 1) 3
  · exact congrFun (congrFun h 1) 7
  · exact congrFun (congrFun h 3) 7

theorem mass_positive (p : Fin 8 → ℂ) (hp : p ≠ 0) : 0 < mass p := by
  rw [mass_eq_sum]
  have h₀ (i : Fin 4) : 0 ≤ ∑ j : Fin 8, Complex.normSq (flatten p i j) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  apply lt_of_le_of_ne (Finset.sum_nonneg fun i _ => h₀ i)
  intro h
  apply hp
  apply flatten_injective
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h₀ i)).mp h.symm i
    (Finset.mem_univ _)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg (flatten p i k))).mp hi j (Finset.mem_univ _)
  have hzero : flatten (R := ℂ) 0 = 0 := by
    ext r c
    fin_cases r <;> fin_cases c <;> rfl
  rw [hzero, Matrix.zero_apply]
  exact Complex.normSq_eq_zero.mp hj

theorem gram_scale (p : Fin 8 → ℂ) (z : ℂ) :
    gram (z • p) = (Complex.normSq z : ℝ) • gram p := by
  have hf : flatten (z • p) = z • flatten p := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [gram, hf, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show z * star z = ↑(Complex.normSq z) from Complex.mul_conj z]
  rfl

theorem mass_scale (p : Fin 8 → ℂ) (z : ℂ) :
    mass (z • p) = Complex.normSq z * mass p := by
  rw [mass, gram_scale, Matrix.trace_smul]
  exact Complex.smul_re _ _

/-- The trace-one adjacent two-site Gram matrix. -/
def normalizedGram (p : Fin 8 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (mass p)⁻¹ • gram p

/-- Trace-one observations are well defined on projective amplitude rays. -/
theorem normalizedGram_scale (p : Fin 8 → ℂ) {z : ℂ} (hz : z ≠ 0) :
    normalizedGram (z • p) = normalizedGram p := by
  rw [normalizedGram, normalizedGram, mass_scale, gram_scale, smul_smul, mul_inv]
  congr 1
  have hn : Complex.normSq z ≠ 0 := fun h => hz (Complex.normSq_eq_zero.mp h)
  rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul]

/-- Positive mass and the trace-one special observation determine one of the two
projective necklace rays. -/
theorem normalized_special_fiber (p : Fin 8 → ℂ) (hp : p ≠ 0)
    (h : normalizedGram p = (target.trace.re)⁻¹ • target) :
    ∃ z : ℂ, z ≠ 0 ∧ (z • p = ray 1 ∨ z • p = ray (-1)) := by
  have ht : 0 < target.trace.re := by
    norm_num [target, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  have hm := mass_positive p hp
  let g := Real.sqrt (target.trace.re / mass p)
  have hgp : 0 < g := Real.sqrt_pos_of_pos (div_pos ht hm)
  have hgain : Complex.normSq (g : ℂ) = target.trace.re / mass p := by
    rw [Complex.normSq_ofReal]
    simpa only [pow_two] using Real.sq_sqrt (div_nonneg ht.le hm.le)
  have hg : gram ((g : ℂ) • p) = target := by
    rw [gram_scale, hgain, div_eq_mul_inv, ← smul_smul, ← normalizedGram,
      h, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  obtain ⟨z, hz, hs⟩ := special_fiber_classification _ hg
  have hzn : z ≠ 0 := by
    intro he
    simp [he] at hz
  refine ⟨z * g, mul_ne_zero hzn (Complex.ofReal_ne_zero.mpr hgp.ne'), ?_⟩
  rw [← smul_smul]
  rcases hs with hs | hs
  · left
    rw [hs]
    simp [ray, sparse, a, b]
  · right
    rw [hs]
    simp [ray, sparse, a, b]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteNormalization
