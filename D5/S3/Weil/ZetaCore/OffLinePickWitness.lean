/- GID: D5/S3/Weil/ZetaCore/OffLinePickWitness
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaCore/OffLinePickWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluate the shifted finite-difference observer at an off-line zero. -/

import D5.S3.Zeros.CompletedZeta

namespace D5.S3.Weil.ZetaCore.OffLinePickWitness

open D5.S3.Weil.Convention
open D5.S3.Zeros.CompletedZeta

/-! The finite-difference observer used in the source definition of `m_omega`. -/
noncomputable def shiftedWeyl (omega : ℝ) (z : ℂ) : ℂ :=
  (Complex.I / (omega : ℂ)) *
    (xiReading ((1 / 2 : ℂ) + (omega : ℂ) - Complex.I * z) -
      xiReading ((1 / 2 : ℂ) - (omega : ℂ) - Complex.I * z)) /
    (xiReading ((1 / 2 : ℂ) + (omega : ℂ) - Complex.I * z) +
      xiReading ((1 / 2 : ℂ) - (omega : ℂ) - Complex.I * z))

/-! The one-point diagonal of the Nevanlinna quotient. -/
noncomputable def diagonalValue (omega : ℝ) (z : ℂ) : ℝ :=
  (shiftedWeyl omega z).im / z.im

theorem off_line_one_point_pick_witness
    (rho : ℂ) (delta gamma omega : ℝ)
    (h_repr : rho = (1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (gamma : ℂ))
    (h_delta : 0 < delta) (h_omega : 0 < omega) (h_lt : omega < delta)
    (h_zero : xiReading rho = 0)
    (h_shift : xiReading (rho - (2 * omega : ℂ)) ≠ 0) :
    let zrho : ℂ := -(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)
    diagonalValue omega zrho = -1 / (omega * (delta - omega)) ∧
      diagonalValue omega zrho < 0 ∧
      diagonalValue omega zrho ≤ -4 / delta ^ 2 := by
  dsimp
  have hz_im :
      (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)).im = delta - omega := by
    simp
  have hplus_arg :
      (1 / 2 : ℂ) + (omega : ℂ) - Complex.I *
          (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)) = rho := by
    rw [h_repr]
    apply Complex.ext <;> norm_num <;> ring
  have hminus_arg :
      (1 / 2 : ℂ) - (omega : ℂ) - Complex.I *
          (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)) =
        rho - (2 * omega : ℂ) := by
    rw [h_repr]
    apply Complex.ext <;> norm_num <;> ring
  have hplus :
      xiReading ((1 / 2 : ℂ) + (omega : ℂ) - Complex.I *
          (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ))) = 0 := by
    rw [hplus_arg]
    exact h_zero
  have hminus :
      xiReading ((1 / 2 : ℂ) - (omega : ℂ) - Complex.I *
          (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ))) ≠ 0 := by
    rw [hminus_arg]
    exact h_shift
  have homega_ne : (omega : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt h_omega)
  have hdiag :
      diagonalValue omega
          (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)) =
        -1 / (omega * (delta - omega)) := by
    unfold diagonalValue shiftedWeyl
    rw [hplus]
    have hminus_real : delta - omega ≠ (0 : ℝ) := ne_of_gt (sub_pos.mpr h_lt)
    have hminus_complex :
        xiReading (rho - (2 * omega : ℂ)) ≠ 0 := h_shift
    let B : ℂ := xiReading ((1 / 2 : ℂ) - (omega : ℂ) - Complex.I *
      (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)))
    have hB : B ≠ 0 := by
      dsimp [B]
      exact hminus
    change (((Complex.I / (omega : ℂ)) * (0 - B) / (0 + B)).im /
      (-(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)).im) =
      -1 / (omega * (delta - omega))
    have hcancel :
        (Complex.I / (omega : ℂ)) * (0 - B) / (0 + B) =
          -Complex.I / (omega : ℂ) := by
      rw [zero_sub, zero_add]
      field_simp [homega_ne, hB]
    rw [hcancel, hz_im]
    norm_num
    field_simp [hminus_real, ne_of_gt h_omega]
  refine ⟨hdiag, ?_, ?_⟩
  · rw [hdiag]
    have hprod : 0 < omega * (delta - omega) :=
      mul_pos h_omega (sub_pos.mpr h_lt)
    exact div_neg_of_neg_of_pos (by norm_num) hprod
  · rw [hdiag]
    have hprod_le : omega * (delta - omega) ≤ delta ^ 2 / 4 := by
      nlinarith [sq_nonneg (delta - 2 * omega)]
    have hprod_pos : 0 < omega * (delta - omega) :=
      mul_pos h_omega (sub_pos.mpr h_lt)
    have hbound : 4 / delta ^ 2 ≤ 1 / (omega * (delta - omega)) := by
      have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos h_delta
      apply (div_le_div_iff₀ hdelta_sq hprod_pos).2
      nlinarith
    simpa only [neg_div] using (neg_le_neg hbound)

end D5.S3.Weil.ZetaCore.OffLinePickWitness
