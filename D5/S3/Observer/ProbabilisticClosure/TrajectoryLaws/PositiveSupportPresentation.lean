/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive stationary support is closed and preserves every original marked cylinder. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Function
open scoped BigOperators Matrix
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation

universe u
variable {H : Type u} [Fintype H]

/-- Retained states are selected by the original stationary mass. -/
abbrev Positive (θ : Presentation H) := {i : H // 0 < θ.initial i}

private theorem sum_positive (θ : Presentation H) (f : H → ℝ)
    (hz : ∀ i, ¬ 0 < θ.initial i → f i = 0) :
    ∑ i : Positive θ, f i.val = ∑ i, f i := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < θ.initial i) f
  have hh : ∑ i : {i : H // ¬ 0 < θ.initial i}, f i.val = 0 :=
    Finset.sum_eq_zero (fun i _ => hz i.val i.property)
  simpa only [hh, add_zero] using he

private theorem next_positive (θ : Presentation H) {i j : H} {x : Bool}
    (hi : 0 < θ.initial i) (hm : 0 < θ.matrix x i j) : 0 < θ.initial j := by
  have hx : θ.matrix x i j ≤ θ.matrix false i j + θ.matrix true i j := by
    cases x <;> linarith [θ.matrix_nonneg false i j, θ.matrix_nonneg true i j]
  have hp : 0 < θ.initial i * (θ.matrix false i j + θ.matrix true i j) :=
    mul_pos hi (hm.trans_le hx)
  have hle : θ.initial i * (θ.matrix false i j + θ.matrix true i j) ≤
      ∑ k, θ.initial k * (θ.matrix false k j + θ.matrix true k j) :=
    Finset.single_le_sum (fun k _ => mul_nonneg (θ.initial_nonneg k)
      (add_nonneg (θ.matrix_nonneg false k j) (θ.matrix_nonneg true k j))) (Finset.mem_univ i)
  rw [θ.stationary j] at hle
  exact hp.trans_le hle

private theorem closed (θ : Presentation H) (i : Positive θ) (j : H)
    (hj : ¬ 0 < θ.initial j) (x : Bool) : θ.matrix x i.val j = 0 :=
  le_antisymm (le_of_not_gt (fun hm => hj (next_positive θ i.property hm)))
    (θ.matrix_nonneg _ _ _)

private theorem weighted_no11 (θ : Presentation H) (i : Positive θ) (j : H) :
    (θ.matrix true * θ.matrix true) i.val j = 0 := by
  have hn (i j : H) : 0 ≤ (θ.matrix true * θ.matrix true) i j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (θ.matrix_nonneg true i k)
      (θ.matrix_nonneg true k j))
  have hterm : θ.initial i.val * (θ.matrix true * θ.matrix true) i.val j ≤ 0 := by
    calc
      _ ≤ ∑ k, θ.initial i.val * (θ.matrix true * θ.matrix true) i.val k :=
        Finset.single_le_sum (fun k _ => mul_nonneg (θ.initial_nonneg i.val) (hn i.val k))
          (Finset.mem_univ j)
      _ ≤ ∑ l, ∑ k, θ.initial l * (θ.matrix true * θ.matrix true) l k :=
        Finset.single_le_sum (fun l _ => Finset.sum_nonneg
          (fun k _ => mul_nonneg (θ.initial_nonneg l) (hn l k))) (Finset.mem_univ i.val)
      _ = 0 := θ.no11
  have hi := i.property
  have hh := hn i.val j
  nlinarith

/-- The restricted matrices, still with their exact original real entries. -/
def trim (θ : Presentation H) : Presentation (Positive θ) where
  initial i := θ.initial i.val
  matrix x i j := θ.matrix x i.val j.val
  initial_nonneg i := θ.initial_nonneg i.val
  initial_sum := by
    rw [sum_positive θ θ.initial (fun i hi => le_antisymm (le_of_not_gt hi) (θ.initial_nonneg i))]
    exact θ.initial_sum
  matrix_nonneg x i j := θ.matrix_nonneg x i.val j.val
  stochastic i := by
    rw [sum_positive θ (fun j => θ.matrix false i.val j + θ.matrix true i.val j)
      (fun j hj => by rw [closed θ i j hj false, closed θ i j hj true]; simp)]
    exact θ.stochastic i.val
  stationary j := by
    rw [sum_positive θ (fun i => θ.initial i *
      (θ.matrix false i j.val + θ.matrix true i j.val)) (fun i hi => by
        rw [le_antisymm (le_of_not_gt hi) (θ.initial_nonneg i), zero_mul])]
    exact θ.stationary j.val
  no11 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have he : (∑ k : Positive θ, θ.matrix true i.val k.val * θ.matrix true k.val j.val) =
        (θ.matrix true * θ.matrix true) i.val j.val := by
      rw [sum_positive θ (fun k => θ.matrix true i.val k * θ.matrix true k j.val)
        (fun k hk => by rw [closed θ i k hk true, zero_mul])]
      rfl
    change θ.initial i.val * (∑ k : Positive θ, _) = 0
    rw [he, weighted_no11 θ i j.val, mul_zero]

/-- The retained no11 constraint is entrywise, even if the original ghost block is not. -/
theorem trim_no11 (θ : Presentation H) : (trim θ).matrix true * (trim θ).matrix true = 0 := by
  classical
  ext i j
  change (∑ k : Positive θ, θ.matrix true i.val k.val * θ.matrix true k.val j.val) = 0
  rw [sum_positive θ (fun k => θ.matrix true i.val k * θ.matrix true k j.val)
        (fun k hk => by rw [closed θ i k hk true, zero_mul])]
  exact weighted_no11 θ i j.val

/-- The measurable inclusion leaves every original integer output coordinate intact. -/
def includePath (θ : Presentation H) (z : PathSpace (Positive θ)) : PathSpace H :=
  (fun t => (z.1 t).val, z.2)

private theorem support_of_mass (θ : Presentation H) (n : ℕ)
    (h : Fin (n + 1) → H) (w : Fin n → Bool)
    (hp : θ.initial (h 0) * pathMass θ.matrix n h w ≠ 0) :
    ∀ k, 0 < θ.initial (h k) := by
  classical
  have hi : 0 < θ.initial (h 0) :=
    lt_of_le_of_ne (θ.initial_nonneg _) (Ne.symm (mul_ne_zero_iff.mp hp).1)
  have hm (k : Fin n) : 0 < θ.matrix (w k) (h k.castSucc) (h k.succ) := by
    apply lt_of_le_of_ne (θ.matrix_nonneg _ _ _)
    apply Ne.symm
    exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).2) k (Finset.mem_univ k)
  intro k
  exact Fin.induction hi (fun i ih => next_positive θ ih (hm i)) k

/-- Pushforward of any original cylinder law on the retained states has all the
original cylinders, including those that mention a zero-mass state. -/
theorem include_cylinders (θ : Presentation H)
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (J : Measure (PathSpace (Positive θ))) [IsProbabilityMeasure J]
    (hc : HasOriginalCylinders J (trim θ)) :
    HasOriginalCylinders (J.map (includePath θ)) θ := by
  classical
  have hm : Measurable (includePath θ) := by
    exact (Measurable.of_eval fun t => measurable_subtype_coe.comp
      ((measurable_pi_apply t).comp measurable_fst)).prodMk measurable_snd
  intro t n h w
  have hmeas : MeasurableSet (MarkedPredictiveQuotient.cylinder t n h w) := by
    simp only [MarkedPredictiveQuotient.cylinder, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.iInter fun k => (measurableSet_singleton (h k)).preimage
      ((measurable_pi_apply _).comp measurable_fst)).inter
      (MeasurableSet.iInter fun k => (measurableSet_singleton (w k)).preimage
        ((measurable_pi_apply _).comp measurable_snd))
  rw [measureReal_def, Measure.map_apply hm hmeas]
  by_cases hh : ∀ k, 0 < θ.initial (h k)
  · let h' : Fin (n + 1) → Positive θ := fun k => ⟨h k,hh k⟩
    have he : includePath θ ⁻¹' MarkedPredictiveQuotient.cylinder t n h w =
        MarkedPredictiveQuotient.cylinder t n h' w := by
      ext z
      simp only [Set.mem_preimage, MarkedPredictiveQuotient.cylinder, Set.mem_setOf_eq,
        includePath, h']
      constructor
      · rintro ⟨hz,hw⟩
        exact ⟨fun k => Subtype.ext (hz k),hw⟩
      · rintro ⟨hz,hw⟩
        exact ⟨fun k => congrArg Subtype.val (hz k),hw⟩
    rw [he]
    exact hc t n h' w
  · have he : includePath θ ⁻¹' MarkedPredictiveQuotient.cylinder t n h w = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      apply hh
      intro k
      have hk := hz.1 k
      exact hk ▸ (z.1 (t + k.val)).property
    have hz : θ.initial (h 0) * pathMass θ.matrix n h w = 0 :=
      by_contra fun hp => hh (support_of_mass θ n h w hp)
    rw [he, measure_empty, ENNReal.toReal_zero, hz]

#print axioms trim_no11
#print axioms include_cylinders
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation
