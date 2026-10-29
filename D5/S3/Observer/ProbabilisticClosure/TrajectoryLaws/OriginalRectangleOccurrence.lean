/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected paths pay actual word occurrence against the complete marked past. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-! Selected original labelled paths bound one actual visible block event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Classical symmDiff
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
      _ ≤ ∑ j : H, θ.matrix (v 0) (h 0) j *
          wordMatrix θ.matrix n (Fin.tail v) j (h (Fin.last (n+1))) := by
        have hnword (j : H) :
            0 ≤ wordMatrix θ.matrix n (Fin.tail v) j (h (Fin.last (n+1))) := by
          rw [← product_ofFn θ n (Fin.tail v)]
          exact product_nonneg θ (List.ofFn (Fin.tail v)) j (h (Fin.last (n+1)))
        exact Finset.single_le_sum
          (fun (j : H) _ => mul_nonneg (θ.matrix_nonneg (v 0) (h 0) j)
            (hnword j))
          (Finset.mem_univ (h 1))

private theorem route_word_mass (θ : Presentation H) (w : List Bool) (r h : H)
    (a : LabelledRoute θ h r) :
    pathMass θ.matrix a.length a.states a.labels * (∑ j, product θ w r j) ≤
      ∑ j, product θ (List.ofFn a.labels ++ w) h j := by
  have he : product θ (List.ofFn a.labels) h r =
      wordMatrix θ.matrix a.length a.labels h r := by
    rw [product_ofFn]
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


private theorem closed_stationary (θ : Presentation H) (C : Finset H)
    (hclosed : ∀ (i : C) j, j ∉ C → ∀ x, θ.matrix x i.val j = 0) :
    ∀ j : C, ∑ i : C, θ.initial i.val *
      (θ.matrix false i.val j.val + θ.matrix true i.val j.val) = θ.initial j.val := by
  have hs (i : C) : ∑ j : C, (θ.matrix false i.val j.val + θ.matrix true i.val j.val) = 1 := by
    rw [Finset.sum_coe_sort]
    calc
      _ = ∑ j, (θ.matrix false i.val j + θ.matrix true i.val j) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        rw [hclosed i j hj false,hclosed i j hj true,add_zero]
      _ = 1 := θ.stochastic i.val
  have hl (j : C) : (∑ i : C, θ.initial i.val *
      (θ.matrix false i.val j.val + θ.matrix true i.val j.val)) ≤ θ.initial j.val := by
    rw [←θ.stationary j.val,Finset.sum_coe_sort]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      mul_nonneg (θ.initial_nonneg _) (add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _))
  have ht : (∑ j : C, ∑ i : C, θ.initial i.val *
      (θ.matrix false i.val j.val + θ.matrix true i.val j.val)) = ∑ j : C, θ.initial j.val := by
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,hs,mul_one]
  intro j
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hl j)).mp ht j (Finset.mem_univ j)

/-- The actual restriction to a positive-weight closed class, with normalized
original stationary masses and unchanged original real matrix entries. -/
def nativeComponent (θ : Presentation H)
    (C : FiniteClosedClasses.ClosedClass (θ.matrix false+θ.matrix true))
    (hc : 0 < ∑ i : C.val, θ.initial i.val) : Presentation C.val := by
  let T := θ.matrix false+θ.matrix true
  have hT : T ∈ rowStochastic ℝ H := Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨fun i j => add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _),θ.stochastic⟩
  have hclosed (i : C.val) (j : H) (hj : j ∉ C.val) (x : Bool) : θ.matrix x i.val j = 0 := by
    have hz := (FiniteClosedClasses.actual_structure T hT).class_no_exit C 1 i j hj
    change (T^1) i.val j = 0 at hz
    simp only [pow_one] at hz
    change θ.matrix false i.val j + θ.matrix true i.val j = 0 at hz
    cases x <;> linarith [θ.matrix_nonneg false i.val j,θ.matrix_nonneg true i.val j]
  let c : ℝ := ∑ i : C.val, θ.initial i.val
  refine { initial := fun i => θ.initial i.val/c
           matrix := fun x i j => θ.matrix x i.val j.val
           initial_nonneg := fun i => div_nonneg (θ.initial_nonneg _) hc.le
           initial_sum := ?_
           matrix_nonneg := fun x i j => θ.matrix_nonneg _ _ _
           stochastic := ?_
           stationary := ?_
           no11 := ?_ }
  · rw [←Finset.sum_div]
    exact div_self (ne_of_gt hc)
  · intro i
    rw [Finset.sum_coe_sort]
    calc
      _ = ∑ j, (θ.matrix false i.val j + θ.matrix true i.val j) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        rw [hclosed i j hj false,hclosed i j hj true,add_zero]
      _ = 1 := θ.stochastic i.val
  · intro j
    simp_rw [div_mul_eq_mul_div]
    rw [←Finset.sum_div,closed_stationary θ C.val hclosed j]
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hp : (∑ k : C.val, θ.matrix true i.val k.val * θ.matrix true k.val j.val) =
        (θ.matrix true*θ.matrix true) i.val j.val := by
      rw [Matrix.mul_apply,Finset.sum_coe_sort]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      rw [hclosed i k hk true,zero_mul]
    have hn (a b : H) : 0 ≤ (θ.matrix true*θ.matrix true) a b :=
      Finset.sum_nonneg fun k _ => mul_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _)
    have hz : θ.initial i.val * (θ.matrix true*θ.matrix true) i.val j.val = 0 := by
      apply le_antisymm _ (mul_nonneg (θ.initial_nonneg _) (hn _ _))
      calc
        _ ≤ ∑ b, θ.initial i.val * (θ.matrix true*θ.matrix true) i.val b :=
          Finset.single_le_sum (fun b _ => mul_nonneg (θ.initial_nonneg _) (hn _ _)) (Finset.mem_univ j.val)
        _ ≤ ∑ a, ∑ b, θ.initial a * (θ.matrix true*θ.matrix true) a b :=
          Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
            mul_nonneg (θ.initial_nonneg _) (hn _ _)) (Finset.mem_univ i.val)
        _ = 0 := θ.no11
    change θ.initial i.val / c * (∑ k : C.val, θ.matrix true i.val k.val * θ.matrix true k.val j.val) = 0
    rw [hp,div_mul_eq_mul_div,hz,zero_div]

/-- Inclusion of an actual hidden component preserves the original output clock. -/
def componentInclusion (C : Finset H) (z : PathSpace C) : PathSpace H :=
  (fun t => (z.1 t).val, z.2)

private theorem componentInclusion_measurable (C : Finset H) :
    Measurable (componentInclusion (H := H) C) := by
  exact (Measurable.of_eval fun t => measurable_subtype_coe.comp
    ((measurable_pi_apply t).comp measurable_fst)).prodMk measurable_snd

private theorem window_domination {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ ν : Measure (ℤ → S))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (t : ℤ) (n : ℕ) (w : Fin (n+1) → S),
      μ.real ((fun x (i : Fin (n+1)) => x (t+i.val)) ⁻¹' {w}) ≤
      ν.real ((fun x (i : Fin (n+1)) => x (t+i.val)) ⁻¹' {w})) : μ ≤ ν := by
  classical
  have hC (C : Set (ℤ → S)) (hC : C ∈ measurableCylinders (fun _ : ℤ => S)) :
      μ.real C ≤ ν.real C := by
    obtain ⟨I,T,hT,he⟩ := (mem_measurableCylinders C).mp hC
    let n : ℕ := I.sup Int.natAbs
    let window : (ℤ → S) → (Fin (2*n+1) → S) := fun z k => z (-(n:ℤ)+k.val)
    let select : (Fin (2*n+1) → S) → ((i : I) → S) := fun w i =>
      w ⟨(i.val+(n:ℤ)).toNat,by
        have hi := Finset.le_sup (f := Int.natAbs) i.property
        have hab := Int.natAbs_eq i.val
        omega⟩
    let U : Finset (Fin (2*n+1) → S) := Finset.univ.filter (fun w => select w ∈ T)
    have hread : I.restrict = select ∘ window := by
      funext z i
      have hi := Finset.le_sup (f := Int.natAbs) i.property
      have hab := Int.natAbs_eq i.val
      change z i.val = z (-(n:ℤ)+((i.val+(n:ℤ)).toNat:ℤ))
      congr 1
      omega
    have hset : C = window ⁻¹' (U : Set (Fin (2*n+1) → S)) := by
      rw [he]
      change (I.restrict : (ℤ → S) → (I → S)) ⁻¹' T = _
      rw [hread]
      ext z
      simp [U,Function.comp_def]
    have hmass (ρ : Measure (ℤ → S)) [IsFiniteMeasure ρ] :
        ρ.real C = ∑ w ∈ U, ρ.real (window ⁻¹' {w}) := by
      have hh := sum_measureReal_preimage_singleton (μ := ρ) U
        (f := window) (fun w _ => (measurableSet_singleton w).preimage (by unfold window; fun_prop))
      simpa only [hset] using hh.symm
    rw [hmass μ,hmass ν]
    exact Finset.sum_le_sum fun w _ => h _ _ _
  apply Measure.le_iff.mpr
  intro F hF
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  by_contra! hm
  let δ : ℝ := (μ.real F-ν.real F)/3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hcover : ∃ D : Set (Set (ℤ → S)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℤ => S) ∧ (μ+ν) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ},Set.countable_singleton _,?_,by simp⟩
    intro C hC
    rcases Set.mem_singleton_iff.mp hC with rfl
    exact univ_mem_measurableCylinders _
  obtain ⟨C,hCm,ha⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ+ν) isSetRing_measurableCylinders hcover
    generateFrom_measurableCylinders.symm hF (ENNReal.ofReal_pos.mpr hδ)
  have hCa := MeasurableSet.of_mem_measurableCylinders hCm
  have hdiff (ρ : Measure (ℤ → S)) [IsFiniteMeasure ρ] (hρ : ρ ≤ μ+ν) :
      ρ.real (C ∆ F) < δ := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr
      ((hρ _).trans_lt ha) |>.trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hμdiff := hdiff μ (le_add_of_nonneg_right bot_le)
  have hνdiff := hdiff ν (le_add_of_nonneg_left bot_le)
  have hgμ := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) hCa.nullMeasurableSet hF.nullMeasurableSet
  have hgν := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν) hCa.nullMeasurableSet hF.nullMeasurableSet
  have hlo := (abs_le.mp hgμ).1
  have hhi := (abs_le.mp hgν).2
  have hbound := hC C hCm
  dsimp [δ] at *
  linarith

private theorem marked_domination (μ ν : Measure (PathSpace H))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t n hs w, μ.real (MarkedPredictiveQuotient.cylinder t n hs w) ≤
      ν.real (MarkedPredictiveQuotient.cylinder t n hs w)) : μ ≤ ν := by
  let e := (MeasurableEquiv.arrowProdEquivProdArrow H Bool ℤ).symm
  have hm : μ.map e ≤ ν.map e := by
    apply window_domination
    intro t n w
    have hmass (ρ : Measure (PathSpace H)) [IsFiniteMeasure ρ] :
        (ρ.map e).real ((fun x (i : Fin (n+1)) => x (t+i.val)) ⁻¹' {w}) =
        ∑ j : H, ρ.real (MarkedPredictiveQuotient.cylinder t (n+1)
          (Fin.snoc (fun i => (w i).1) j) (fun i => (w i).2)) := by
      rw [measureReal_def,Measure.map_apply e.measurable
        ((measurableSet_singleton w).preimage (by fun_prop))]
      have he : e ⁻¹' ((fun x (i : Fin (n+1)) => x (t+i.val)) ⁻¹' {w}) =
          ⋃ j : H, MarkedPredictiveQuotient.cylinder t (n+1)
            (Fin.snoc (fun i => (w i).1) j) (fun i => (w i).2) := by
        ext z
        change (fun i : Fin (n+1) => (z.1 (t+i.val),z.2 (t+i.val))) = w ↔ _
        simp only [Set.mem_iUnion,MarkedPredictiveQuotient.cylinder,Set.mem_setOf_eq]
        constructor
        · intro hz
          refine ⟨z.1 (t+(n+1)),?_,fun i => congrArg Prod.snd (congrFun hz i)⟩
          intro i
          refine Fin.lastCases ?_ (fun k => ?_) i
          · simp
          · simpa using congrArg Prod.fst (congrFun hz k)
        · rintro ⟨j,hj,hw⟩
          funext i
          exact Prod.ext (by simpa using hj i.castSucc) (hw i)
      rw [he]
      exact measureReal_iUnion_fintype (fun i j hij => Set.disjoint_left.mpr (by
        intro z hi hj
        have h1 := hi.1 (Fin.last (n+1))
        have h2 := hj.1 (Fin.last (n+1))
        simp only [Fin.val_last,Fin.snoc_last] at h1 h2
        exact hij (h1.symm.trans h2))) (fun j => cylinder_measurable _ _ _ _)
    rw [hmass μ,hmass ν]
    exact Finset.sum_le_sum fun j _ => h _ _ _ _
  have hh := Measure.map_mono hm e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self,Measure.map_id] using hh

/-- A native positive stationary component is exactly the original marked law
restricted to that component, with its actual stationary weight. -/
theorem component_restriction (θ : Presentation H) (C : Finset H)
    (κ : Presentation C) (c : ℝ) (hc : 0 < c)
    (hinit : ∀ i : C, c*κ.initial i = θ.initial i.val)
    (hmat : ∀ x (i j : C), κ.matrix x i j = θ.matrix x i.val j.val)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hJ : HasOriginalCylinders J θ)
    (K : Measure (PathSpace C)) [IsProbabilityMeasure K] (hK : HasOriginalCylinders K κ)
    (t : ℤ) :
    ENNReal.ofReal c • K.map (componentInclusion C) =
      J.restrict (state t ⁻¹' (C : Set H)) := by
  let f := componentInclusion (H := H) C
  have hf : Measurable f := componentInclusion_measurable C
  let μ := ENNReal.ofReal c • K.map f
  haveI : IsFiniteMeasure μ := Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hdom : μ ≤ J := by
    apply marked_domination
    intro d n hs w
    rw [measureReal_def,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc.le,Measure.map_apply hf (cylinder_measurable _ _ _ _)]
    by_cases hh : ∀ i, hs i ∈ C
    · let hs' : Fin (n+1) → C := fun i => ⟨hs i,hh i⟩
      have he : f ⁻¹' MarkedPredictiveQuotient.cylinder d n hs w =
          MarkedPredictiveQuotient.cylinder d n hs' w := by
        ext z
        simp only [f,componentInclusion,MarkedPredictiveQuotient.cylinder,
          Set.mem_preimage,Set.mem_setOf_eq,hs',Subtype.ext_iff]
      rw [he]
      change c*K.real _ ≤ J.real _
      rw [hK,hJ,←mul_assoc,hinit]
      have hp : pathMass κ.matrix n hs' w = pathMass θ.matrix n hs w := by
        unfold pathMass
        apply Finset.prod_congr rfl
        intro i _
        exact hmat _ _ _
      rw [hp]
    · have he : f ⁻¹' MarkedPredictiveQuotient.cylinder d n hs w = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        apply hh
        intro i
        have hi := hz.1 i
        exact hi ▸ (z.1 (d+i.val)).property
      rw [he,measure_empty,ENNReal.toReal_zero,mul_zero]
      exact measureReal_nonneg
  have hE : MeasurableSet (state t ⁻¹' (C : Set H)) :=
    (Set.toFinite _).measurableSet.preimage (by unfold state; fun_prop)
  have hμ : μ.restrict (state t ⁻¹' (C : Set H)) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply (ae_iff).mpr
    change μ (state t ⁻¹' (C : Set H))ᶜ = 0
    change ENNReal.ofReal c * (K.map f) (state t ⁻¹' (C : Set H))ᶜ = 0
    rw [Measure.map_apply hf hE.compl]
    have he : f ⁻¹' (state t ⁻¹' (C : Set H))ᶜ = ∅ := by
      ext z
      simp [f,componentInclusion,state]
    rw [he,measure_empty,mul_zero]
  have hmass : J (state t ⁻¹' (C : Set H)) = ENNReal.ofReal c := by
    have hh := sum_measureReal_preimage_singleton (μ := J) C
      (f := state t) (fun i _ => (measurableSet_singleton i).preimage (by unfold state; fun_prop))
    have he : J.real (state t ⁻¹' (C : Set H)) = c := by
      rw [←hh]
      simp_rw [state_mass θ J hJ]
      rw [←Finset.sum_coe_sort]
      simp_rw [←hinit]
      rw [←Finset.mul_sum,κ.initial_sum,mul_one]
    rw [← ENNReal.ofReal_toReal (measure_ne_top J _),he]
  apply Measure.eq_of_le_of_measure_univ_eq
  · rw [←hμ]
    exact Measure.restrict_mono le_rfl hdom
  · rw [Measure.restrict_apply_univ,hmass]
    simp [μ,Measure.map_apply hf MeasurableSet.univ]

end Law
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
