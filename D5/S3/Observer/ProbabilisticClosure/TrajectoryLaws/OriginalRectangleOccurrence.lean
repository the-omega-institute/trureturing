/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected original labelled paths pay the visible rectangular-word event against the complete marked past. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
universe u
variable {H : Type u} [Fintype H]
variable [MeasurableSpace H] [MeasurableSingletonClass H]

/-- A selected positive path in the original labelled matrices; its clock is its edge count. -/
structure LabelledRoute (θ : Presentation H) (h r : H) where
  length : ℕ
  states : Fin (length+1) → H
  labels : Fin length → Bool
  first : states 0 = h
  last : states (Fin.last length) = r
  positive : ∀ i, 0 < θ.matrix (labels i) (states i.castSucc) (states i.succ)

/-- The same visible success event counted by `originalSuccessCount` in one block. -/
def success (w : List Bool) (b : ℕ) : Set (ℕ → Bool) :=
  {x | w <:+: List.ofFn (readPrefix b x)}

/-- The minimum of the selected labelled-path probabilities followed by the original word. -/
def selectedEpsilon (θ : Presentation H) (w : List Bool) (r : H)
    (a : ∀ h, LabelledRoute θ h r) : ℝ :=
  Finset.univ.inf' ⟨r, Finset.mem_univ r⟩ (fun h =>
    pathMass θ.matrix (a h).length (a h).states (a h).labels *
      ∑ j, product θ w r j)

private theorem path_entry (θ : Presentation H) (n : ℕ)
    (h : Fin (n+1) → H) (v : Fin n → Bool) :
    pathMass θ.matrix n h v ≤ wordMatrix θ.matrix n v (h 0) (h (Fin.last n)) := by
  induction n with
  | zero => simp [pathMass, wordMatrix, Matrix.one_apply]
  | succ n ih =>
    rw [path_step, wordMatrix, Matrix.mul_apply]
    calc
      _ ≤ θ.matrix (v 0) (h 0) (h 1) *
          wordMatrix θ.matrix n (Fin.tail v) (h 1) (h (Fin.last (n+1))) := by
        apply mul_le_mul_of_nonneg_left _ (θ.matrix_nonneg _ _ _)
        simpa only [Fin.tail, Fin.succ_zero_eq_one, Fin.succ_last] using
          ih (Fin.tail h) (Fin.tail v)
      _ ≤ _ := Finset.single_le_sum
        (fun j _ => mul_nonneg (θ.matrix_nonneg _ _ _)
          (by
            have hh := product_nonneg θ (List.ofFn (Fin.tail v)) j (h (Fin.last (n+1)))
            simpa only [product_word, List.length_ofFn, List.get_ofFn] using hh))
        (Finset.mem_univ (h 1))

private theorem route_word_mass (θ : Presentation H) (w : List Bool) (r h : H)
    (a : LabelledRoute θ h r) :
    pathMass θ.matrix a.length a.states a.labels * (∑ j, product θ w r j) ≤
      ∑ j, product θ (List.ofFn a.labels ++ w) h j := by
  have he : product θ (List.ofFn a.labels) h r =
      wordMatrix θ.matrix a.length a.labels h r := by
    rw [product_word]
    simp only [List.length_ofFn, List.get_ofFn]
  have hp : pathMass θ.matrix a.length a.states a.labels ≤
      product θ (List.ofFn a.labels) h r := by
    rw [he]
    simpa only [a.first, a.last] using path_entry θ a.length a.states a.labels
  have hn : 0 ≤ ∑ j, product θ w r j :=
    Finset.sum_nonneg fun j _ => product_nonneg θ w r j
  calc
    _ ≤ product θ (List.ofFn a.labels) h r * (∑ j, product θ w r j) :=
      mul_le_mul_of_nonneg_right hp hn
    _ ≤ ∑ k, product θ (List.ofFn a.labels) h k * (∑ j, product θ w k j) :=
      Finset.single_le_sum (fun k _ => mul_nonneg
        (product_nonneg θ _ h k) (Finset.sum_nonneg fun j _ => product_nonneg θ w k j))
        (Finset.mem_univ r)
    _ = _ := by
      simp only [product, List.map_append, List.prod_append, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_comm

private theorem success_measurable (w : List Bool) (b : ℕ) : MeasurableSet (success w b) := by
  change MeasurableSet (readPrefix b ⁻¹' {v : Fin b → Bool | w <:+: List.ofFn v})
  exact (Set.toFinite _).measurableSet.preimage (by unfold readPrefix; fun_prop)

private theorem prefix_success (w p : List Bool) (b : ℕ) (hb : (p++w).length ≤ b) :
    readPrefix (p++w).length ⁻¹' {(p++w).get} ⊆ success w b := by
  intro x hx
  have hh : readPrefix (p++w).length x = (p++w).get := hx
  have ht : (List.ofFn (readPrefix b x)).take (p++w).length = p++w := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hb]
    · intro k hk hk'
      simp only [List.getElem_take, List.getElem_ofFn, readPrefix]
      exact congrFun hh ⟨k,hk'⟩
  change w <:+: List.ofFn (readPrefix b x)
  have hp : p++w <+: List.ofFn (readPrefix b x) := by
    rw [← ht]
    exact List.take_prefix _ _
  exact (show w <:+: p++w from ⟨p,[],by simp⟩).trans hp.isInfix

section Law

/-- Source-selected paths imply a lower bound for the actual visible event against
every measurable event of the complete marked past, including null hidden fibers. -/
theorem original_rectangle_occurrence (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows)
    (a : ∀ h, LabelledRoute θ h r) (ha : ∀ h, (a h).length ≤ Fintype.card H) :
    let ε := selectedEpsilon θ w r a
    let b := w.length + Fintype.card H
    0 < ε ∧ ε ≤ 1 ∧
    (∀ (t : ℤ) (h : H), 0 < θ.initial h →
      ENNReal.ofReal ε ≤ futureLaw J t h (success w b)) ∧
    (∀ (t : ℤ) (h : H) (A : Set (ℕ → H × Bool)), MeasurableSet A →
      ENNReal.ofReal ε * J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A)) ≤
        J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' success w b))) := by
  dsimp only
  let ε := selectedEpsilon θ w r a
  let b := w.length + Fintype.card H
  have hrow : 0 < ∑ j, product θ w r j := by
    obtain ⟨j,hj⟩ := R.cols_nonempty
    exact (R.positive r hr j hj).trans_le
      (Finset.single_le_sum (fun k _ => product_nonneg θ w r k) (Finset.mem_univ j))
  have hε : 0 < ε := by
    apply (Finset.lt_inf'_iff _).mpr
    intro h _
    exact mul_pos (Finset.prod_pos fun i _ => (a h).positive i) hrow
  have lower (t : ℤ) (h : H) (hi : 0 < θ.initial h) :
      ENNReal.ofReal ε ≤ futureLaw J t h (success w b) := by
    let p := List.ofFn (a h).labels
    have hb : (p++w).length ≤ b := by
      dsimp [p,b]
      simpa only [List.length_append, List.length_ofFn, Nat.add_comm] using
        Nat.add_le_add_right (ha h) w.length
    have hm := futureLaw_readPrefix θ J hc t h hi (p++w).length (p++w).get
    rw [Measure.map_apply (by unfold readPrefix; fun_prop) (measurableSet_singleton _)] at hm
    calc
      ENNReal.ofReal ε ≤ ENNReal.ofReal
          (pathMass θ.matrix (a h).length (a h).states (a h).labels * ∑ j, product θ w r j) :=
        ENNReal.ofReal_le_ofReal (Finset.inf'_le _ (Finset.mem_univ h))
      _ ≤ ENNReal.ofReal (∑ j, product θ (p++w) h j) :=
        ENNReal.ofReal_le_ofReal (route_word_mass θ w r h (a h))
      _ = futureLaw J t h (readPrefix (p++w).length ⁻¹' {(p++w).get}) := by
        rw [hm]
        congr 1
        simp only [futureMass, ← product_word]
      _ ≤ _ := measure_mono (prefix_success w p b hb)
  have hsum : 0 < ∑ h, θ.initial h := by rw [θ.initial_sum]; norm_num
  obtain ⟨h,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg fun h _ => θ.initial_nonneg h).mp hsum
  have hε1 : ε ≤ 1 := by
    have hh := (lower 0 h hi).trans prob_le_one
    exact (ENNReal.ofReal_le_one).mp hh
  refine ⟨hε,hε1,lower,?_⟩
  intro t h A hA
  by_cases hi : 0 < θ.initial h
  · rw [full_past_future_factor θ J hc t h hi A (success w b) hA (success_measurable w b),
      mul_comm (J _)]
    exact mul_le_mul_left (lower t h hi) _
  · have hz : θ.initial h = 0 := le_antisymm (le_of_not_gt hi) (θ.initial_nonneg h)
    have hn : J (state t ⁻¹' {h}) = 0 := by
      apply (ENNReal.toReal_eq_zero_iff _).mp ?_ |>.resolve_right (measure_ne_top _ _)
      change J.real (state t ⁻¹' {h}) = 0
      rw [state_mass θ J hc, hz]
    have hn' : J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A)) = 0 :=
      measure_mono_null Set.inter_subset_left hn
    rw [hn',mul_zero]
    exact zero_le

end Law
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
