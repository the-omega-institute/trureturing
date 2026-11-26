import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

/-! Integral norm congruence for order-three twisted conformal weights. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdNormWeightCongruence

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open ThirdTwistedChargeAction (N N_apply norm_fixed norm_pairing)
open ThirdTwistedChargeCocycle (pairing_shift_two)
open LatticeHalfFockChargedMonodromy (norm_even)

variable (D : LatticeData) (g : Charge D ≃+ Charge D)
variable (h3 : ∀ a, g (g (g a)) = a)
variable (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)

include h3 hg in
theorem six_dvd_norm_quadratic (p : (N D g).range) :
    (6 : ℤ) ∣ bilinear D p.1 p.1 := by
  obtain ⟨a, ha⟩ := p.2
  have hFixed := norm_fixed D g h3 a
  have hNorm : bilinear D (N D g a) (N D g a) =
      3 * bilinear D a (N D g a) := by
    calc
      bilinear D (N D g a) (N D g a) =
          bilinear D (N D g a) (a + g a + g (g a)) :=
        congrArg (bilinear D (N D g a)) (N_apply D g a)
      _ = 3 * bilinear D (N D g a) a := by
        have h₁ := hg (N D g a) a
        have h₂ := hg (N D g a) (g a)
        rw [hFixed] at h₁ h₂
        rw [bilinear_add_right, bilinear_add_right, h₂, h₁]
        ring
      _ = _ := by rw [norm_pairing D g h3 hg]
  have hPair : bilinear D a (g (g a)) = bilinear D a (g a) := by
    rw [pairing_shift_two D g hg h3, bilinear_symmetric]
  obtain ⟨k, hk⟩ := norm_even D a
  change bilinear D a a = k + k at hk
  refine ⟨k + bilinear D a (g a), ?_⟩
  rw [← ha, hNorm, N_apply, bilinear_add_right, bilinear_add_right, hPair, hk]
  ring

include h3 hg in
theorem weight_congruent_sixteen_ninths (p : (N D g).range) (oscillator : ℕ) :
    ∃ k : ℤ, (16 / 9 : ℚ) + oscillator / 3 + (bilinear D p.1 p.1 : ℚ) / 18 =
      16 / 9 + (k : ℚ) / 3 := by
  obtain ⟨q, hq⟩ := six_dvd_norm_quadratic D g h3 hg p
  refine ⟨(oscillator : ℤ) + q, ?_⟩
  rw [hq]
  push_cast
  ring

include h3 hg in
theorem weight_ne_integer (p : (N D g).range) (oscillator : ℕ) (m : ℤ) :
    (16 / 9 : ℚ) + oscillator / 3 + (bilinear D p.1 p.1 : ℚ) / 18 ≠ (m : ℚ) := by
  obtain ⟨k, hk⟩ := weight_congruent_sixteen_ninths D g h3 hg p oscillator
  rw [hk]
  intro heq
  have heq' : (16 : ℚ) + 3 * (k : ℚ) = 9 * (m : ℚ) := by linarith
  exact (by omega : (16 : ℤ) + 3 * k ≠ 9 * m) (by exact_mod_cast heq')

#print axioms weight_ne_integer

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdNormWeightCongruence
