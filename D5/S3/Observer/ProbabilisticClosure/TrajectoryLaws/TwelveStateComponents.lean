/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native stationary hidden components preserve the actual ergodic output law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateErgodicity

set_option maxHeartbeats 2400000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Set Filter
open scoped BigOperators ENNReal Classical symmDiff
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming PositiveRectangleLaw
open TwelveStateErgodicity

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateComponents

private theorem subtype_sum_le {A : Type*} [Fintype A] (C : Finset A) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) : (∑ a : {a // a ∈ C}, f a.val) ≤ ∑ a, f a := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hf a)

private theorem cylinder_ac (μ ν : Measure (ℤ → Bool)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hc : 0 < c)
    (h : ∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
      c*μ.real (visibleCylinder t n w) ≤ ν.real (visibleCylinder t n w)) : μ ≪ ν := by
  classical
  have hC (C : Set (ℤ → Bool)) (hC : C ∈ measurableCylinders (fun _ : ℤ => Bool)) :
      c*μ.real C ≤ ν.real C := by
    obtain ⟨I,S,hS,he⟩ := (mem_measurableCylinders C).mp hC
    let n : ℕ := I.sup Int.natAbs
    let window : (ℤ → Bool) → (Fin (2*n+1) → Bool) := fun z k => z (-(n:ℤ)+k.val)
    let select : (Fin (2*n+1) → Bool) → ((i : I) → Bool) := fun w i =>
      w ⟨(i.val+(n:ℤ)).toNat,by
        have hi := Finset.le_sup (f := Int.natAbs) i.property
        have hab := Int.natAbs_eq i.val
        omega⟩
    let U : Finset (Fin (2*n+1) → Bool) := Finset.univ.filter (fun w => select w ∈ S)
    have hread : I.restrict = select ∘ window := by
      funext z i
      have hi := Finset.le_sup (f := Int.natAbs) i.property
      have hab := Int.natAbs_eq i.val
      change z i.val = z (-(n:ℤ)+((i.val+(n:ℤ)).toNat:ℤ))
      congr 1
      omega
    have hset : C = window ⁻¹' (U : Set (Fin (2*n+1) → Bool)) := by
      rw [he]
      change (I.restrict : (ℤ → Bool) → (I → Bool)) ⁻¹' S = _
      rw [hread]
      ext z
      simp [U,Function.comp_def]
    have hmass (ρ : Measure (ℤ → Bool)) [IsProbabilityMeasure ρ] :
        ρ.real C = ∑ w ∈ U, ρ.real (visibleCylinder (-(n:ℤ)) (2*n+1) w) := by
      have hh := sum_measureReal_preimage_singleton (μ := ρ) U
        (f := window) (fun w _ => (measurableSet_singleton w).preimage (by unfold window; fun_prop))
      have hw (w : Fin (2*n+1) → Bool) : window ⁻¹' {w} = visibleCylinder (-(n:ℤ)) (2*n+1) w := by
        ext z
        simp [window,visibleCylinder,funext_iff]
      simpa only [hset,hw] using hh.symm
    rw [hmass μ,hmass ν,Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => h _ _ _
  intro E hnull
  obtain ⟨F,hEF,hF,hFm⟩ := exists_measurable_superset_of_null hnull
  suffices μ F = 0 from measure_mono_null hEF this
  by_contra hm
  let m := μ.real F
  have hmpos : 0 < m := ENNReal.toReal_pos hm (measure_ne_top _ _)
  let δ : ℝ := c*m/(2*(c+1))
  have hδ : 0 < δ := div_pos (mul_pos hc hmpos) (by linarith)
  have hcover : ∃ D : Set (Set (ℤ → Bool)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℤ => Bool) ∧ (μ+ν) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ},Set.countable_singleton _,?_,by simp⟩
    intro C hC
    rcases Set.mem_singleton_iff.mp hC with rfl
    exact univ_mem_measurableCylinders _
  obtain ⟨C,hCm,ha⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ+ν) isSetRing_measurableCylinders hcover
    generateFrom_measurableCylinders.symm hF (ENNReal.ofReal_pos.mpr hδ)
  have hCa := MeasurableSet.of_mem_measurableCylinders hCm
  have hμdiff : μ.real (C ∆ F) < δ := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr
      ((show μ (C ∆ F) ≤ (μ+ν) (C ∆ F) by simp only [Measure.add_apply]; exact le_add_of_nonneg_right bot_le).trans_lt ha) |>.trans_eq
        (ENNReal.toReal_ofReal hδ.le)
  have hνdiff : ν.real (C ∆ F) < δ := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr
      ((show ν (C ∆ F) ≤ (μ+ν) (C ∆ F) by simp only [Measure.add_apply]; exact le_add_of_nonneg_left bot_le).trans_lt ha) |>.trans_eq
        (ENNReal.toReal_ofReal hδ.le)
  have hgμ := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) hCa.nullMeasurableSet hF.nullMeasurableSet
  have hgν := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν) hCa.nullMeasurableSet hF.nullMeasurableSet
  have heν : ν.real F = 0 := by simp [Measure.real,hFm]
  have hlo : m-δ < μ.real C := by have hh := (abs_le.mp hgμ).1; dsimp [m]; linarith
  have hhi : ν.real C < δ := by have hh := (abs_le.mp hgν).2; linarith
  have hbound := hC C hCm
  have hsmall : δ*(c+1) = c*m/2 := by dsimp [δ]; field_simp
  nlinarith [mul_lt_mul_of_pos_left hlo hc]

private theorem component_domination {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (θ : Presentation H) (C : Finset H)
    (κ : Presentation {i // i ∈ C}) (c : ℝ) (hc : 0 < c)
    (hinit : ∀ i, c*κ.initial i = θ.initial i.val)
    (hmat : ∀ x i j, κ.matrix x i j = θ.matrix x i.val j.val) :
    (visibleLaw κ : Measure (ℤ → Bool)) ≪ (visibleLaw θ : Measure (ℤ → Bool)) := by
  have hn (n : ℕ) (w : Fin n → Bool) (i j : H) : 0 ≤ wordMatrix θ.matrix n w i j := by
    induction n generalizing i j with
    | zero => simp [wordMatrix,Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      rw [wordMatrix,Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (θ.matrix_nonneg _ _ _) (ih _ k _)
  have hw : ∀ n (w : Fin n → Bool) (i j : {i // i ∈ C}),
      wordMatrix κ.matrix n w i j ≤ wordMatrix θ.matrix n w i.val j.val := by
    intro n
    induction n with
    | zero => intro w i j; simp only [wordMatrix,Matrix.one_apply,Subtype.val_inj]; split_ifs <;> norm_num
    | succ n ih =>
      intro w i j
      rw [wordMatrix,wordMatrix,Matrix.mul_apply,Matrix.mul_apply]
      calc
        _ ≤ ∑ k : {i // i ∈ C}, θ.matrix (w 0) i.val k.val *
            wordMatrix θ.matrix n (Fin.tail w) k.val j.val := by
          apply Finset.sum_le_sum
          intro k _
          rw [hmat]
          exact mul_le_mul_of_nonneg_left (ih _ _ _) (θ.matrix_nonneg _ _ _)
        _ ≤ _ := subtype_sum_le C (fun k => θ.matrix (w 0) i.val k * wordMatrix θ.matrix n (Fin.tail w) k j.val) (fun k => mul_nonneg (θ.matrix_nonneg _ _ _) (hn _ _ _ _))
  apply cylinder_ac _ _ c hc
  intro t n w
  rw [(same_law_trimming κ).2.2.2.2.2.2.2.1 t n w,
    (same_law_trimming θ).2.2.2.2.2.2.2.1 t n w,Finset.mul_sum]
  calc
    _ = ∑ i : {i // i ∈ C}, θ.initial i.val*futureMass κ.matrix i n w := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc,hinit]
    _ ≤ ∑ i : {i // i ∈ C}, θ.initial i.val*futureMass θ.matrix i.val n w := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (θ.initial_nonneg _)
      exact (Finset.sum_le_sum fun j _ => hw n w i j).trans
        (subtype_sum_le C _ (hn n w i.val))
    _ ≤ _ := subtype_sum_le C (fun i => θ.initial i * futureMass θ.matrix i n w) fun i => mul_nonneg (θ.initial_nonneg _)
      (Finset.sum_nonneg fun j _ => hn n w i j)

/-- A positive native stationary component has the same whole output law whenever
that original stationary output law is ergodic. Component entries and stationary
masses are linked to the original presentation, rather than independently posited. -/
theorem ergodic_native_component_law {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (θ : Presentation H)
    (herg : Ergodic (fun z : ℤ → Bool => fun t => z (1+t))
      (visibleLaw θ : Measure (ℤ → Bool))) (C : Finset H)
    (κ : Presentation {i // i ∈ C}) (c : ℝ) (hc : 0 < c)
    (hinit : ∀ i, c*κ.initial i = θ.initial i.val)
    (hmat : ∀ x i j, κ.matrix x i j = θ.matrix x i.val j.val) :
    visibleLaw κ = visibleLaw θ := by
  have hAC := component_domination θ C κ c hc hinit hmat
  have hs : MeasurePreserving (fun z : ℤ → Bool => fun t => z (1+t))
      (visibleLaw κ : Measure _) (visibleLaw κ : Measure _) :=
    ⟨by fun_prop,(same_law_trimming κ).2.2.2.2.2.2.1 1⟩
  exact ProbabilityMeasure.toMeasure_injective (herg.eq_of_absolutelyContinuous hs hAC)

#print axioms ergodic_native_component_law

/-- Every native positive-weight stationary hidden component of every finite
presentation of the actual law has that same whole output law. Its irreducible
restriction excludes every positive rectangular-support word product. -/
theorem actual_native_component {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (θ : Presentation H)
    (hsame : visibleLaw θ = TwelveStatePresentation.visible) (C : Finset H)
    (κ : Presentation {i // i ∈ C}) (c : ℝ) (hc : 0 < c)
    (hinit : ∀ i, c*κ.initial i = θ.initial i.val)
    (hmat : ∀ x i j, κ.matrix x i j = θ.matrix x i.val j.val)
    (hirr : ∀ i j, ∃ n : ℕ, 0 < ((κ.matrix false+κ.matrix true)^n) i j) :
    visibleLaw κ = TwelveStatePresentation.visible ∧
    ∀ (n : ℕ) (w : Fin n → Bool),
      ¬ Nonempty (PositiveRectangleMessages.Rectangle (wordMatrix κ.matrix n w)) := by
  have herg : Ergodic (fun z : ℤ → Bool => fun t => z (1+t))
      (visibleLaw θ : Measure (ℤ → Bool)) := by
    rw [hsame]
    exact actual_output_ergodic
  have he := (ergodic_native_component_law θ herg C κ c hc hinit hmat).trans hsame
  refine ⟨he,fun n w => actual_irreducible_obstruction κ he ?_ n w⟩
  intro i j
  convert hirr i j using 1 <;> congr!

#print axioms actual_native_component
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateComponents
