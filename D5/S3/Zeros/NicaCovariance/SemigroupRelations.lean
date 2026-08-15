/- GID: D5/S3/Zeros/NicaCovariance/SemigroupRelations
   generality: I
   mirror-B: D5/B/S3/Zeros/NicaCovariance/SemigroupRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Establish the shift semigroup laws and coprime Nica covariance of range projections. -/

import D5.S3.Zeros.ShiftOperators.ShiftRangeProjection

namespace D5.S3.Zeros.NicaCovariance.SemigroupRelations

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.SpectralShift
open D5.S3.Zeros.ShiftOperators.BackwardShiftOperator
open D5.S3.Zeros.ShiftOperators.ShiftRangeProjection

noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

private theorem normalizedTableAdd_assoc (a u v : PrimeAxisTable) :
    normalizedTableAdd (normalizedTableAdd a u) v =
      normalizedTableAdd a (normalizedTableAdd u v) := by
  apply primeAxisEncoding.injective
  simp [normalizedTableAdd, mul_assoc]

private theorem normalizedTableAdd_right_comm (a u v : PrimeAxisTable) :
    normalizedTableAdd (normalizedTableAdd a v) u =
      normalizedTableAdd a (normalizedTableAdd u v) := by
  apply primeAxisEncoding.injective
  simp [normalizedTableAdd, mul_comm, mul_left_comm]

private theorem normalizedTableAdd_dvd (a u : PrimeAxisTable) :
    primeAxisEncoding u ∣ primeAxisEncoding (normalizedTableAdd a u) :=
  ⟨primeAxisEncoding a, by simp [normalizedTableAdd, mul_comm]⟩

/-- Backward shifts represent normalized address addition as a semigroup. -/
theorem backward_shift_comp (u v : PrimeAxisTable) :
    (backwardShiftCLM u).comp (backwardShiftCLM v) =
      backwardShiftCLM (normalizedTableAdd u v) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext a
  change x (normalizedTableAdd (normalizedTableAdd a u) v) =
    x (normalizedTableAdd a (normalizedTableAdd u v))
  rw [normalizedTableAdd_assoc]

/-- Zero-extended forward translations represent normalized address addition as a semigroup. -/
theorem forward_translation_comp (u v : PrimeAxisTable) :
    (forwardTranslationCLM u).comp (forwardTranslationCLM v) =
      forwardTranslationCLM (normalizedTableAdd u v) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext b
  change forwardTranslationCLM u (forwardTranslationCLM v x) b =
    forwardTranslationCLM (normalizedTableAdd u v) x b
  by_cases h : primeAxisEncoding (normalizedTableAdd u v) ∣ primeAxisEncoding b
  · let a := normalizedTableSub b (normalizedTableAdd u v)
    have hb : normalizedTableAdd a (normalizedTableAdd u v) = b :=
      normalizedTableSub_add_cancel h
    calc
      forwardTranslationCLM u (forwardTranslationCLM v x) b =
          forwardTranslationCLM u (forwardTranslationCLM v x)
            (normalizedTableAdd (normalizedTableAdd a v) u) := by
        rw [normalizedTableAdd_right_comm, hb]
      _ = forwardTranslationCLM v x (normalizedTableAdd a v) :=
        forward_translation_apply_translate u (normalizedTableAdd a v)
          (forwardTranslationCLM v x)
      _ = x a := forward_translation_apply_translate v a x
      _ = forwardTranslationCLM (normalizedTableAdd u v) x
          (normalizedTableAdd a (normalizedTableAdd u v)) :=
        (forward_translation_apply_translate (normalizedTableAdd u v) a x).symm
      _ = forwardTranslationCLM (normalizedTableAdd u v) x b := by rw [hb]
  · rw [forward_translation_apply_of_not_dvd (normalizedTableAdd u v) b x h]
    by_cases hu : primeAxisEncoding u ∣ primeAxisEncoding b
    · rw [forward_translation_apply_of_dvd u b _ hu]
      by_cases hv : primeAxisEncoding v ∣
          primeAxisEncoding (normalizedTableSub b u)
      · let a := normalizedTableSub (normalizedTableSub b u) v
        have hv' : normalizedTableAdd a v = normalizedTableSub b u :=
          normalizedTableSub_add_cancel hv
        have hu' : normalizedTableAdd (normalizedTableSub b u) u = b :=
          normalizedTableSub_add_cancel hu
        have hb : normalizedTableAdd a (normalizedTableAdd u v) = b := by
          calc
            normalizedTableAdd a (normalizedTableAdd u v) =
                normalizedTableAdd (normalizedTableAdd a v) u :=
              (normalizedTableAdd_right_comm a u v).symm
            _ = normalizedTableAdd (normalizedTableSub b u) u := by rw [hv']
            _ = b := hu'
        exfalso
        apply h
        rw [← hb]
        exact normalizedTableAdd_dvd a (normalizedTableAdd u v)
      · exact forward_translation_apply_of_not_dvd v (normalizedTableSub b u) x hv
    · exact forward_translation_apply_of_not_dvd u b (forwardTranslationCLM v x) hu

/-- Coprime shift-range projections satisfy the Nica covariance relation. -/
theorem shift_range_projection_comp_of_coprime (u v : PrimeAxisTable)
    (hcop : Nat.Coprime (primeAxisEncoding u) (primeAxisEncoding v)) :
    (shiftRangeProjection u).comp (shiftRangeProjection v) =
      shiftRangeProjection (normalizedTableAdd u v) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext b
  change shiftRangeProjection u (shiftRangeProjection v x) b =
    shiftRangeProjection (normalizedTableAdd u v) x b
  rw [shiftRangeProjection_apply, shiftRangeProjection_apply,
    shiftRangeProjection_apply]
  have hdvd :
      primeAxisEncoding (normalizedTableAdd u v) ∣ primeAxisEncoding b ↔
        primeAxisEncoding u ∣ primeAxisEncoding b ∧
          primeAxisEncoding v ∣ primeAxisEncoding b := by
    simp only [PNat.dvd_iff]
    rw [show ((primeAxisEncoding (normalizedTableAdd u v) : ℕ+) : ℕ) =
        (primeAxisEncoding u : ℕ) * (primeAxisEncoding v : ℕ) by
      simp [normalizedTableAdd]]
    constructor
    · intro huv
      exact ⟨(dvd_mul_right _ _).trans huv, (dvd_mul_left _ _).trans huv⟩
    · rintro ⟨hu, hv⟩
      exact hcop.mul_dvd_of_dvd_of_dvd hu hv
  by_cases hu : primeAxisEncoding u ∣ primeAxisEncoding b <;>
    by_cases hv : primeAxisEncoding v ∣ primeAxisEncoding b <;>
      simp [hu, hv, hdvd]

#print axioms backward_shift_comp
#print axioms forward_translation_comp
#print axioms shift_range_projection_comp_of_coprime

end D5.S3.Zeros.NicaCovariance.SemigroupRelations
