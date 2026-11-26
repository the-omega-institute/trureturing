/- GID: D5/S3/TotalVariation/ParrySectionMarginals
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParrySectionMarginals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The zero-section Parry law has different first two zero-bit marginals. -/

import D5.S3.TotalVariation.ParryFirstReturn

namespace D5.S3.TotalVariation.ParrySectionMarginals

open MeasureTheory ProbabilityTheory Set
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryFirstReturn
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.TwistedResetPaths
open scoped ENNReal

/-- The zero-section probability has different zero-bit marginals at the first two
coordinates, so the original shift does not preserve it. -/
theorem section_zero_marginals {k : ℕ} (hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ : ProbabilityMeasure (RelationPath k))
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (hμ : (μ : Measure (RelationPath k)).map relationShift = μ)
    (hcylinder : ∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
        ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))) :
    sectionMeasure (μ : Measure (RelationPath k)) {r | r.val 0 = false} =
        ENNReal.ofReal (parryParameter k) ∧
      sectionMeasure (μ : Measure (RelationPath k)) {r | r.val 1 = false} =
        ENNReal.ofReal (2 * parryParameter k ^ 2) ∧
      (sectionMeasure (μ : Measure (RelationPath k))).map relationShift ≠
        sectionMeasure (μ : Measure (RelationPath k)) := by
  let p := parryParameter k
  let a := sectionMeasure (μ : Measure (RelationPath k))
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  let w0 : Fin 2 → Fin k := ![z, z]
  let w00 : Fin 3 → Fin k := ![z, z, z]
  let w10 : Fin 3 → Fin k := ![z, o, z]
  let C0 : Set (RelationPath k) := {r | r.val 0 = false}
  let C00 : Set (RelationPath k) := {r | r.val 0 = false ∧ r.val 1 = false}
  let C10 : Set (RelationPath k) := {r | r.val 0 = true ∧ r.val 1 = false}
  let C1 : Set (RelationPath k) := {r | r.val 1 = false}
  have hp : 1 / 2 < p := (parry_stationary_law k hk).1.1
  have weight : suffixWeight k p z = 1 := by
    simpa [p, z, suffixWeight, rootSum] using (parry_stationary_law k hk).1.2.2
  have law0 := zero_section_raw_window hk e μ hsuffix hμ hcylinder w0 rfl
    (fun i => Or.inl (by fin_cases i; rfl))
  have law00 := zero_section_raw_window hk e μ hsuffix hμ hcylinder w00 rfl
    (fun i => Or.inl (by fin_cases i <;> rfl))
  have law10 := zero_section_raw_window hk e μ hsuffix hμ hcylinder w10 rfl (by
    intro i
    fin_cases i
    · exact Or.inr rfl
    · exact Or.inl rfl)
  have event0 : {r | matchesRawWindow r w0 = true} = C0 := by
    ext r
    simp [matchesRawWindow, C0, w0, z]
  have event00 : {r | matchesRawWindow r w00 = true} = C00 := by
    ext r
    simp [matchesRawWindow, Fin.forall_fin_succ, C00, w00, z]
  have event10 : {r | matchesRawWindow r w10 = true} = C10 := by
    ext r
    simp [matchesRawWindow, Fin.forall_fin_succ, C10, w10, z, o]
  have result0 : a C0 = ENNReal.ofReal p := by
    rw [event0] at law0
    change a C0 = ENNReal.ofReal (p ^ 1 * suffixWeight k p z) at law0
    simpa only [weight, mul_one, pow_one] using law0
  have result00 : a C00 = ENNReal.ofReal (p ^ 2) := by
    rw [event00] at law00
    change a C00 = ENNReal.ofReal (p ^ 2 * suffixWeight k p z) at law00
    simpa only [weight, mul_one] using law00
  have result10 : a C10 = ENNReal.ofReal (p ^ 2) := by
    rw [event10] at law10
    change a C10 = ENNReal.ofReal (p ^ 2 * suffixWeight k p z) at law10
    simpa only [weight, mul_one] using law10
  have readout (t : ℤ) : Measurable (fun r : RelationPath k => r.val t) :=
    (measurable_pi_apply t).comp measurable_subtype_coe
  have m0 : MeasurableSet C0 := readout 0 (measurableSet_singleton false)
  have m1 : MeasurableSet C1 := readout 1 (measurableSet_singleton false)
  have m10 : MeasurableSet C10 :=
    (readout 0 (measurableSet_singleton true)).inter m1
  have split : C1 = C00 ∪ C10 := by
    ext r
    cases h : r.val 0 <;> simp [C1, C00, C10, h]
  have disjoint : Disjoint C00 C10 := by
    rw [Set.disjoint_left]
    intro r h00 h10
    exact Bool.false_ne_true (h00.1.symm.trans h10.1)
  have result1 : a C1 = ENNReal.ofReal (2 * p ^ 2) := by
    rw [split, measure_union disjoint m10, result00, result10, ← ENNReal.ofReal_add (sq_nonneg p)
      (sq_nonneg p), two_mul]
  refine ⟨result0, result1, ?_⟩
  intro heq
  have shift : Measurable (@relationShift k) := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval fun t => readout (t + 1)
  have pullback : relationShift ⁻¹' C0 = C1 := rfl
  have hm := congrArg (fun v : Measure (RelationPath k) => v C0) heq
  change a.map relationShift C0 = a C0 at hm
  rw [Measure.map_apply shift m0, pullback, result1, result0] at hm
  have positive : 0 < p := by linarith
  have strict : p < 2 * p ^ 2 := by nlinarith [mul_pos positive (sub_pos.mpr hp)]
  exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 strict).ne' hm

#print axioms section_zero_marginals

end D5.S3.TotalVariation.ParrySectionMarginals
