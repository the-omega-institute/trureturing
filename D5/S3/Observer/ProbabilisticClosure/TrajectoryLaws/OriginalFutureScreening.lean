/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual conditional future measures screen the complete marked past on one original law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
import Mathlib.Probability.Independence.Conditional

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming

open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent (measure_eq_of_prefix)

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- A regular conditional probability of the complete actual future, defined on
every hidden state, including impossible fibers. -/
def futureLaw (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (t : ℤ) :
    Kernel H (ℕ → Bool) := condDistrib (future t) (state t) J

private instance futureLaw_markov (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (t : ℤ) :
    IsMarkovKernel (futureLaw J t) := by unfold futureLaw; infer_instance

instance classMeasurable (M : Bool → Matrix H H ℝ) : MeasurableSpace (FutureClass M) := ⊤

def readPrefix {S : Type*} (n : ℕ) (x : ℕ → S) : Fin n → S := fun i => x i.val

theorem state_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (i : H) :
    J.real (state t ⁻¹' {i}) = θ.initial i := by
  have he : MarkedPredictiveQuotient.cylinder t 0 (fun _ => i) (fun k => nomatch k) =
      state t ⁻¹' {i} := by
    ext z
    simp [MarkedPredictiveQuotient.cylinder, state]
  simpa only [Nat.cast_zero, he, pathMass, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    using hc t 0 (fun _ => i) (fun k => nomatch k)

theorem future_state_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (i : H)
    (n : ℕ) (w : Fin n → Bool) :
    J.real ((state t ⁻¹' {i}) ∩ (future t ⁻¹' (readPrefix n ⁻¹' {w}))) =
      θ.initial i * futureMass θ.matrix i n w := by
  have hh := past_future_mass θ J hc t 0 n (fun _ => i) (fun k => nomatch k) w
  have he : MarkedPredictiveQuotient.cylinder (t-0) 0 (fun _ => i) (fun k => nomatch k) ∩
      Prod.snd ⁻¹' visibleCylinder t n w =
      (state t ⁻¹' {i}) ∩ (future t ⁻¹' (readPrefix n ⁻¹' {w})) := by
    ext z
    simp [MarkedPredictiveQuotient.cylinder, state, visibleCylinder, future, readPrefix,
      funext_iff]
  simpa only [Nat.cast_zero, he, pathMass, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    using hh

theorem futureLaw_readPrefix (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (i : H)
    (hi : 0 < θ.initial i) (n : ℕ) (w : Fin n → Bool) :
    (futureLaw J t i).map (readPrefix n) {w} = ENNReal.ofReal (futureMass θ.matrix i n w) := by
  have hm : J.map (state t) {i} = ENNReal.ofReal (θ.initial i) := by
    rw [Measure.map_apply (by unfold state; fun_prop) (measurableSet_singleton i),
      ← state_mass θ J hc t i]
    exact (ENNReal.ofReal_toReal (measure_ne_top J _)).symm
  have hn : J.map (state t) {i} ≠ 0 := by rw [hm]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hi)
  have hr : Measurable (readPrefix (S := Bool) n) := by unfold readPrefix; fun_prop
  rw [Measure.map_apply hr (measurableSet_singleton w)]
  change condDistrib (future t) (state t) J i _ = _
  rw [condDistrib_apply_of_ne_zero (by unfold state; fun_prop) (by unfold future; fun_prop) i hn,
    Measure.map_apply (by unfold future state; fun_prop)
      ((measurableSet_singleton i).prod ((measurableSet_singleton w).preimage
        hr)), hm]
  have he : (fun z : PathSpace H => (state t z, future t z)) ⁻¹' ({i} ×ˢ (readPrefix n ⁻¹' {w})) =
      (state t ⁻¹' {i}) ∩ (future t ⁻¹' (readPrefix n ⁻¹' {w})) := rfl
  rw [he, ← ENNReal.ofReal_toReal (measure_ne_top J _)]
  change _ * ENNReal.ofReal (J.real _) = _
  rw [future_state_mass θ J hc,
    ENNReal.ofReal_mul (le_of_lt hi), ENNReal.inv_mul_cancel_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr hi)) ENNReal.ofReal_ne_top]

theorem cylinder_future_law (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (m : ℕ)
    (h : Fin (m+1) → H) (w : Fin m → Bool) (hi : 0 < θ.initial (h (Fin.last m))) :
    (J.restrict (MarkedPredictiveQuotient.cylinder (t-m) m h w)).map (future t) =
      J (MarkedPredictiveQuotient.cylinder (t-m) m h w) • futureLaw J t (h (Fin.last m)) := by
  have hf : Measurable (future (H := H) t) := by unfold future; fun_prop
  haveI : IsFiniteMeasure (J (MarkedPredictiveQuotient.cylinder (t-m) m h w) •
      futureLaw J t (h (Fin.last m))) := Measure.smul_finite _ (measure_ne_top J _)
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro v
  have hr : Measurable (readPrefix (S := Bool) (n+1)) := by unfold readPrefix; fun_prop
  change ((J.restrict _).map (future t)).map (readPrefix (n+1)) {v} =
    (J _ • futureLaw J t (h (Fin.last m))).map (readPrefix (n+1)) {v}
  rw [Measure.map_smul _ hr.aemeasurable, Measure.smul_apply, smul_eq_mul, futureLaw_readPrefix θ J hc t _ hi]
  rw [Measure.map_map hr hf, Measure.map_apply (hr.comp hf) (measurableSet_singleton v),
    Measure.restrict_apply ((measurableSet_singleton v).preimage (hr.comp hf))]
  have he : (readPrefix (n+1) ∘ future (H := H) t) ⁻¹' {v} = Prod.snd ⁻¹' visibleCylinder t (n+1) v := by
    ext z
    simp [readPrefix, future, visibleCylinder, funext_iff]
  rw [he, Set.inter_comm]
  have hmass := past_future_mass θ J hc t m (n+1) h w v
  rw [← ENNReal.ofReal_toReal (measure_ne_top J _)]
  change ENNReal.ofReal (J.real _) = _
  rw [hmass, ENNReal.ofReal_mul (mul_nonneg (θ.initial_nonneg _)
    (path_nonneg θ m h w))]
  congr 1
  rw [← hc (t-m) m h w]
  exact ENNReal.ofReal_toReal (measure_ne_top J _)

private theorem past_prefix_cylinder (t : ℤ) (m : ℕ)
    (p : Fin m → H × Bool) (i : H) :
    (past t ⁻¹' (readPrefix m ⁻¹' {p})) ∩ (state t ⁻¹' {i}) =
      MarkedPredictiveQuotient.cylinder (t-m) m
        (Fin.snoc (fun k => (p k.rev).1) i) (fun k => (p k.rev).2) := by
  have clock (k : Fin m) : t - (k.val + 1 : ℕ) = t - (m:ℤ) + k.rev.val := by
    simp only [Fin.val_rev]
    omega
  ext z
  change (readPrefix m (past t z) = p ∧ state t z = i) ↔ _
  constructor
  · rintro ⟨hp,hi⟩
    constructor
    · intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [state] using hi
      · rw [Fin.snoc_castSucc]
        have hh := congrArg Prod.fst (congrFun hp k.rev)
        change z.1 (t - (k.rev.val+1 : ℕ)) = (p k.rev).1 at hh
        rw [clock k.rev, Fin.rev_rev] at hh
        simpa only [Fin.val_castSucc] using hh
    · intro k
      have hh := congrArg Prod.snd (congrFun hp k.rev)
      change z.2 (t - (k.rev.val+1 : ℕ)) = (p k.rev).2 at hh
      rw [clock k.rev, Fin.rev_rev] at hh
      exact hh
  · rintro ⟨hh,hw⟩
    constructor
    · funext k
      have hh' := hh k.rev.castSucc
      have hw' := hw k.rev
      rw [Fin.snoc_castSucc, Fin.rev_rev] at hh'
      simp only [Fin.rev_rev] at hw'
      change (z.1 (t - (k.val+1 : ℕ)),z.2 (t - (k.val+1 : ℕ))) = p k
      rw [clock]
      exact Prod.ext hh' hw'
    · simpa [state] using hh (Fin.last m)

theorem full_past_future_factor (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (i : H)
    (hi : 0 < θ.initial i) (A : Set (ℕ → H × Bool)) (B : Set (ℕ → Bool))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    J ((state t ⁻¹' {i}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' B)) =
      J ((state t ⁻¹' {i}) ∩ (past t ⁻¹' A)) * futureLaw J t i B := by
  have hp : Measurable (past (H := H) t) := by unfold past; fun_prop
  have hf : Measurable (future (H := H) t) := by unfold future; fun_prop
  have hs : Measurable (state (H := H) t) := by unfold state; fun_prop
  let μ := (J.restrict ((state t ⁻¹' {i}) ∩ (future t ⁻¹' B))).map (past t)
  let ν := futureLaw J t i B • (J.restrict (state t ⁻¹' {i})).map (past t)
  haveI : IsFiniteMeasure ν := Measure.smul_finite _ (measure_ne_top (futureLaw J t i) B)
  have he : μ = ν := by
    apply measure_eq_of_prefix
    intro n
    apply Measure.ext_of_singleton
    intro p
    let E := MarkedPredictiveQuotient.cylinder (t-(n+1 : ℕ)) (n+1)
      (Fin.snoc (fun k => (p k.rev).1) i) (fun k => (p k.rev).2)
    have hE : MeasurableSet E := cylinder_measurable _ _ _ _
    have hm := cylinder_future_law θ J hc t (n+1)
      (Fin.snoc (fun k => (p k.rev).1) i) (fun k => (p k.rev).2)
      (by simpa using hi)
    have hm' := congrArg (fun ζ : Measure (ℕ → Bool) => ζ B) hm
    rw [Measure.map_apply hf hB, Measure.restrict_apply (hf hB),
      Measure.smul_apply, smul_eq_mul] at hm'
    have hr : Measurable (readPrefix (S := H × Bool) (n+1)) := by unfold readPrefix; fun_prop
    change μ.map (readPrefix (n+1)) {p} = ν.map (readPrefix (n+1)) {p}
    dsimp [μ,ν]
    rw [Measure.map_map hr hp, Measure.map_apply (hr.comp hp) (measurableSet_singleton p),
      Measure.restrict_apply ((measurableSet_singleton p).preimage (hr.comp hp)),
      Measure.map_smul _ hr.aemeasurable, Measure.smul_apply, smul_eq_mul,
      Measure.map_map hr hp, Measure.map_apply (hr.comp hp) (measurableSet_singleton p),
      Measure.restrict_apply ((measurableSet_singleton p).preimage (hr.comp hp))]
    change J ((past t ⁻¹' (readPrefix (n+1) ⁻¹' {p})) ∩
      ((state t ⁻¹' {i}) ∩ (future t ⁻¹' B))) =
      futureLaw J t i B * J ((past t ⁻¹' (readPrefix (n+1) ⁻¹' {p})) ∩ (state t ⁻¹' {i}))
    rw [← Set.inter_assoc, past_prefix_cylinder]
    simpa only [Set.inter_comm, mul_comm, E, Fin.snoc_last] using hm'
  have ha := congrArg (fun ζ : Measure (ℕ → H × Bool) => ζ A) he
  dsimp [μ,ν] at ha
  simp only [Measure.map_apply hp hA, Measure.restrict_apply (hp hA),
    Measure.smul_apply, smul_eq_mul] at ha
  simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, mul_comm] using ha

/-- The class on the complete finite-word future profile at an integer cut. -/
def classAt (M : Bool → Matrix H H ℝ) (t : ℤ) (z : PathSpace H) : FutureClass M :=
  classOf M (state t z)

private theorem full_future_eq (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (i j : H)
    (hi : 0 < θ.initial i) (hj : 0 < θ.initial j) :
    (futureSetoid θ.matrix).r i j ↔ futureLaw J t i = futureLaw J t j := by
  constructor
  · intro h
    apply measure_eq_of_prefix
    intro n
    apply Measure.ext_of_singleton
    intro w
    change (futureLaw J t i).map (readPrefix (n+1)) {w} =
      (futureLaw J t j).map (readPrefix (n+1)) {w}
    rw [futureLaw_readPrefix θ J hc t i hi, futureLaw_readPrefix θ J hc t j hj]
    exact congrArg ENNReal.ofReal (congrFun (congrFun h (n+1)) w)
  · intro h
    funext n w
    have hn (s : H) : 0 ≤ futureMass θ.matrix s n w := by
      rw [← sum_path_tails θ n s w]
      exact Finset.sum_nonneg fun k _ => path_nonneg θ n (Fin.cons s k) w
    have he := congrArg (fun μ : Measure (ℕ → Bool) => μ.map (readPrefix n) {w}) h
    rw [futureLaw_readPrefix θ J hc t i hi, futureLaw_readPrefix θ J hc t j hj] at he
    exact (ENNReal.ofReal_eq_ofReal_iff (hn i) (hn j)).mp he

private theorem state_partition (J : Measure (PathSpace H)) (t : ℤ)
    (E : Set (PathSpace H)) : J E = ∑ i, J (E ∩ (state t ⁻¹' {i})) := by
  have hs (i : H) : MeasurableSet (state t ⁻¹' {i}) :=
    (measurableSet_singleton i).preimage (by unfold state; fun_prop)
  have he := sum_measure_preimage_singleton (μ := J.restrict E) Finset.univ
    (f := state t) (fun i _ => hs i)
  simpa only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.restrict_apply (hs _), Set.inter_comm] using he.symm

private theorem class_future_factor (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (hpos : ∀ i, 0 < θ.initial i) (t : ℤ) (a : FutureClass θ.matrix)
    (A : Set (ℕ → H × Bool)) (B : Set (ℕ → Bool)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    J ((classAt θ.matrix t ⁻¹' {a}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' B)) =
      J ((classAt θ.matrix t ⁻¹' {a}) ∩ (past t ⁻¹' A)) * futureLaw J t a.out B := by
  rw [state_partition J t, state_partition J t, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hai : classOf θ.matrix i = a
  · have hs : classAt θ.matrix t ⁻¹' {a} ∩ state t ⁻¹' {i} = state t ⁻¹' {i} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, classAt]
      constructor
      · exact And.right
      · intro hz
        exact ⟨by rw [hz]; exact hai,hz⟩
    have hsame : futureLaw J t i = futureLaw J t a.out :=
      (full_future_eq θ J hc t i a.out (hpos i) (hpos a.out)).mp
        (Quotient.exact (hai.trans (Quotient.out_eq a).symm))
    have he1 : (classAt θ.matrix t ⁻¹' {a} ∩ past t ⁻¹' A ∩ future t ⁻¹' B) ∩
        state t ⁻¹' {i} = (state t ⁻¹' {i}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' B) := by
      rw [Set.inter_right_comm, Set.inter_right_comm (classAt θ.matrix t ⁻¹' {a}), hs]
    have he2 : (classAt θ.matrix t ⁻¹' {a} ∩ past t ⁻¹' A) ∩ state t ⁻¹' {i} =
        (state t ⁻¹' {i}) ∩ (past t ⁻¹' A) := by rw [Set.inter_right_comm, hs]
    rw [he1, he2, full_past_future_factor θ J hc t i (hpos i) A B hA hB, hsame]
  · have hs : classAt θ.matrix t ⁻¹' {a} ∩ state t ⁻¹' {i} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        classAt, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz hi
      exact hai (hi ▸ hz)
    have he1 : (classAt θ.matrix t ⁻¹' {a} ∩ past t ⁻¹' A ∩ future t ⁻¹' B) ∩
        state t ⁻¹' {i} = ∅ := by
      rw [Set.inter_right_comm, Set.inter_right_comm (classAt θ.matrix t ⁻¹' {a}), hs]
      simp
    have he2 : (classAt θ.matrix t ⁻¹' {a} ∩ past t ⁻¹' A) ∩ state t ⁻¹' {i} = ∅ := by
      rw [Set.inter_right_comm, hs]; simp
    simp only [he1, he2, measure_empty, zero_mul]

private theorem screening_from_fiber_factor
    {Ω Q Y Z : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → Q) (f : Ω → Y) (g : Ω → Z)
    (hq : Measurable q) (hf : Measurable f) (hg : Measurable g)
    (K : Kernel Q Z) [IsMarkovKernel K]
    (hn : ∀ a, μ.map q {a} ≠ 0)
    (hfactor : ∀ a A B, MeasurableSet A → MeasurableSet B →
      μ ((q ⁻¹' {a}) ∩ (f ⁻¹' A) ∩ (g ⁻¹' B)) = μ ((q ⁻¹' {a}) ∩ (f ⁻¹' A)) * K a B) :
    (∀ a, condDistrib g q μ a = K a) ∧
      CondIndepFun (MeasurableSpace.comap q inferInstance) hq.comap_le f g μ := by
  have hkernel (a : Q) : condDistrib g q μ a = K a := by
    ext B hB
    rw [condDistrib_apply_of_ne_zero hq hg a (hn a),
      Measure.map_apply (hq.prodMk hg) ((measurableSet_singleton a).prod hB)]
    change (μ.map q {a})⁻¹ * μ ((q ⁻¹' {a}) ∩ (g ⁻¹' B)) = K a B
    have he := hfactor a Set.univ B MeasurableSet.univ hB
    simp only [Set.preimage_univ, Set.inter_univ] at he
    rw [he, ← Measure.map_apply hq (measurableSet_singleton a),
      ENNReal.inv_mul_cancel_left (hn a) (measure_ne_top _ _)]
  have hpair (a : Q) (A : Set Y) (B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      condDistrib (fun ω => (f ω,g ω)) q μ a (A ×ˢ B) =
        condDistrib f q μ a A * condDistrib g q μ a B := by
    rw [condDistrib_apply_of_ne_zero hq (hf.prodMk hg) a (hn a),
      Measure.map_apply (hq.prodMk (hf.prodMk hg))
        ((measurableSet_singleton a).prod (hA.prod hB)),
      condDistrib_apply_of_ne_zero hq hf a (hn a),
      Measure.map_apply (hq.prodMk hf) ((measurableSet_singleton a).prod hA), hkernel]
    simp only [Set.mk_preimage_prod, ← Set.inter_assoc]
    rw [hfactor a A B hA hB, mul_assoc]
  refine ⟨hkernel,?_⟩
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mpr
  intro A B hA hB
  filter_upwards [condDistrib_ae_eq_condExp hq (hf.prodMk hg) (hA.prod hB),
    condDistrib_ae_eq_condExp hq hf hA, condDistrib_ae_eq_condExp hq hg hB]
      with ω hxy hx hy
  change (condDistrib (fun ω => (f ω,g ω)) q μ (q ω)).real (A ×ˢ B) =
    (μ⟦f ⁻¹' A ∩ g ⁻¹' B | MeasurableSpace.comap q inferInstance⟧) ω at hxy
  rw [← hxy, ← hx, ← hy]
  exact (congrArg ENNReal.toReal (hpair (q ω) A B hA hB)).trans
    ENNReal.toReal_mul

instance positiveNonempty (θ : Presentation H) : Nonempty (Positive θ) := by
  by_contra hn
  haveI : IsEmpty (Positive θ) := not_nonempty_iff.mp hn
  have hs := (trim θ).initial_sum
  simp at hs

/-- A total retained-state map; original null states receive one retained value. -/
def retainState (θ : Presentation H) (i : H) : Positive θ :=
  if hi : 0 < θ.initial i then ⟨i,hi⟩ else Classical.choice (positiveNonempty θ)

/-- A total measurable class map on the original, untrimmed path space. -/
def originalClass (θ : Presentation H) (t : ℤ) (z : PathSpace H) :
    FutureClass (trim θ).matrix := classOf (trim θ).matrix (retainState θ (state t z))

/-- The actual complete future conditional on a class in the selected retained law. -/
def classFutureLaw (θ : Presentation H) (t : ℤ) :
    Kernel (FutureClass (trim θ).matrix) (ℕ → Bool) :=
  (futureLaw (retainedLaw θ : Measure _) t).comap Quotient.out (measurable_of_finite _)

private instance classFutureLaw_markov (θ : Presentation H) (t : ℤ) :
    IsMarkovKernel (classFutureLaw θ t) := by unfold classFutureLaw; infer_instance

private def includePast (θ : Presentation H) (y : ℕ → Positive θ × Bool) : ℕ → H × Bool :=
  fun n => ((y n).1.val,(y n).2)

private theorem original_class_factor (θ : Presentation H) (t : ℤ)
    (a : FutureClass (trim θ).matrix) (A : Set (ℕ → H × Bool)) (B : Set (ℕ → Bool))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (jointLaw θ : Measure _) ((originalClass θ t ⁻¹' {a}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' B)) =
      (jointLaw θ : Measure _) ((originalClass θ t ⁻¹' {a}) ∩ (past t ⁻¹' A)) * classFutureLaw θ t a B := by
  have hi : Measurable (includePath θ) := inclusion_measurable θ
  have hq : Measurable (originalClass θ t) :=
    (measurable_of_finite _).comp (by unfold state; fun_prop)
  have hp : Measurable (past (H := H) t) := by unfold past; fun_prop
  have hf : Measurable (future (H := H) t) := by unfold future; fun_prop
  change ((retainedLaw θ : Measure _).map (includePath θ)) _ =
    ((retainedLaw θ : Measure _).map (includePath θ)) _ * _
  rw [Measure.map_apply hi (((measurableSet_singleton a).preimage hq).inter (hp hA) |>.inter (hf hB)),
    Measure.map_apply hi (((measurableSet_singleton a).preimage hq).inter (hp hA))]
  have he1 : includePath θ ⁻¹' ((originalClass θ t ⁻¹' {a}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' B)) =
      (classAt (trim θ).matrix t ⁻¹' {a}) ∩ (past t ⁻¹' (includePast θ ⁻¹' A)) ∩ (future t ⁻¹' B) := by
    ext z
    have hqz : originalClass θ t (includePath θ z) = classAt (trim θ).matrix t z := by
      dsimp [originalClass, retainState, classAt, state, includePath]
      rw [dif_pos (z.1 t).property]
    change ((originalClass θ t (includePath θ z) = a ∧ past t (includePath θ z) ∈ A) ∧
      future t (includePath θ z) ∈ B) ↔ _
    rw [hqz]
    rfl
  have he2 : includePath θ ⁻¹' ((originalClass θ t ⁻¹' {a}) ∩ (past t ⁻¹' A)) =
      (classAt (trim θ).matrix t ⁻¹' {a}) ∩ (past t ⁻¹' (includePast θ ⁻¹' A)) := by
    ext z
    have hqz : originalClass θ t (includePath θ z) = classAt (trim θ).matrix t z := by
      dsimp [originalClass, retainState, classAt, state, includePath]
      rw [dif_pos (z.1 t).property]
    change (originalClass θ t (includePath θ z) = a ∧ past t (includePath θ z) ∈ A) ↔ _
    rw [hqz]
    rfl
  rw [he1,he2]
  exact class_future_factor (trim θ) (retainedLaw θ : Measure _)
    (same_law_trimming θ).2.1 (fun i => i.property) t a (includePast θ ⁻¹' A) B
    (hA.preimage (by unfold includePast; fun_prop)) hB

theorem originalClass_measurable (θ : Presentation H) (t : ℤ) :
    Measurable (originalClass θ t) :=
  (measurable_of_finite (fun i : H => classOf (trim θ).matrix (retainState θ i))).comp
    (by unfold state; fun_prop)

private theorem original_class_nonzero (θ : Presentation H) (t : ℤ)
    (a : FutureClass (trim θ).matrix) :
    (jointLaw θ : Measure _).map (originalClass θ t) {a} ≠ 0 := by
  have hi : (jointLaw θ : Measure _).real (state t ⁻¹' {a.out.val}) = θ.initial a.out.val :=
    state_mass θ (jointLaw θ : Measure _) (same_law_trimming θ).1 t a.out.val
  have hn : (jointLaw θ : Measure _) (state t ⁻¹' {a.out.val}) ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hi
    exact (ne_of_gt a.out.property) hi.symm
  rw [Measure.map_apply (originalClass_measurable θ t) (measurableSet_singleton a)]
  intro hz
  apply hn
  apply le_antisymm (le_trans (measure_mono ?_) (le_of_eq hz)) zero_le
  intro z hi
  change state t z = a.out.val at hi
  change classOf (trim θ).matrix (retainState θ (state t z)) = a
  rw [hi]
  have hr : retainState θ a.out.val = a.out := by
    unfold retainState
    rw [dif_pos a.out.property]
  rw [hr]
  exact Quotient.out_eq a

private theorem state_map_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (i : H) :
    J.map (state t) {i} = ENNReal.ofReal (θ.initial i) := by
  rw [Measure.map_apply (by unfold state; fun_prop) (measurableSet_singleton i),
    ← state_mass θ J hc t i]
  exact (ENNReal.ofReal_toReal (measure_ne_top J _)).symm

private theorem original_future_transfer (θ : Presentation H) (t : ℤ) (i : Positive θ) :
    futureLaw (jointLaw θ : Measure _) t i.val = futureLaw (retainedLaw θ : Measure _) t i := by
  have hmo := state_map_mass θ (jointLaw θ : Measure _) (same_law_trimming θ).1 t i.val
  have hml := state_map_mass (trim θ) (retainedLaw θ : Measure _) (same_law_trimming θ).2.1 t i
  have hno : (jointLaw θ : Measure _).map (state t) {i.val} ≠ 0 := by
    rw [hmo]; exact ne_of_gt (ENNReal.ofReal_pos.mpr i.property)
  have hnl : (retainedLaw θ : Measure _).map (state t) {i} ≠ 0 := by
    rw [hml]; exact ne_of_gt (ENNReal.ofReal_pos.mpr i.property)
  have hfo : Measurable (future (H := H) t) := by unfold future; fun_prop
  have hfl : Measurable (future (H := Positive θ) t) := by unfold future; fun_prop
  have hso : Measurable (state (H := H) t) := by unfold state; fun_prop
  have hsl : Measurable (state (H := Positive θ) t) := by unfold state; fun_prop
  ext B hB
  change condDistrib (future t) (state t) (jointLaw θ : Measure _) i.val B =
    condDistrib (future t) (state t) (retainedLaw θ : Measure _) i B
  rw [condDistrib_apply_of_ne_zero hso hfo i.val hno, condDistrib_apply_of_ne_zero hsl hfl i hnl,
    hmo,hml]
  change (ENNReal.ofReal (θ.initial i.val))⁻¹ * _ = (ENNReal.ofReal (θ.initial i.val))⁻¹ * _
  congr 1
  change (((retainedLaw θ : Measure _).map (includePath θ)).map
    (fun z => (state t z,future t z))) ({i.val} ×ˢ B) =
    ((retainedLaw θ : Measure _).map (fun z => (state t z,future t z))) ({i} ×ˢ B)
  rw [Measure.map_map (hso.prodMk hfo) (inclusion_measurable θ),
    Measure.map_apply ((hso.prodMk hfo).comp (inclusion_measurable θ))
      ((measurableSet_singleton i.val).prod hB),
    Measure.map_apply (hsl.prodMk hfl) ((measurableSet_singleton i).prod hB)]
  congr 1
  ext z
  change ((z.1 t).val = i.val ∧ future (H := Positive θ) t z ∈ B) ↔
    (z.1 t = i ∧ future (H := Positive θ) t z ∈ B)
  simp only [Subtype.ext_iff]

/-- The existing finite-word classes are precisely equality of complete actual
future conditionals. On the same original law they screen the full marked past,
and conditioning further on that past leaves the complete future kernel unchanged. -/
theorem same_law_future_screening (θ : Presentation H) :
    (∀ (t : ℤ) (i j : Positive θ),
      (classOf (trim θ).matrix i = classOf (trim θ).matrix j ↔
        futureLaw (jointLaw θ : Measure _) t i.val = futureLaw (jointLaw θ : Measure _) t j.val) ∧
      ((futureSetoid θ.matrix).r i.val j.val ↔
        classOf (trim θ).matrix i = classOf (trim θ).matrix j)) ∧
    (∀ t : ℤ,
      (∀ a, condDistrib (future (H := H) t) (originalClass θ t) (jointLaw θ : Measure _) a =
        classFutureLaw θ t a) ∧
      CondIndepFun (MeasurableSpace.comap (originalClass θ t) inferInstance)
        (originalClass_measurable θ t).comap_le (future t) (past t) (jointLaw θ : Measure _) ∧
      condDistrib (future (H := H) t) (fun z => (originalClass θ t z,past t z))
          (jointLaw θ : Measure _) =ᵐ[(jointLaw θ : Measure _).map
            (fun z => (originalClass θ t z,past t z))]
        (classFutureLaw θ t).prodMkRight (ℕ → H × Bool)) := by
  letI : Nonempty H := ⟨(Classical.choice (positiveNonempty θ)).val⟩
  constructor
  · intro t i j
    have ho := full_future_eq θ (jointLaw θ : Measure _) (same_law_trimming θ).1
      t i.val j.val i.property j.property
    have ht : classOf (trim θ).matrix i = classOf (trim θ).matrix j ↔
        futureLaw (jointLaw θ : Measure _) t i.val = futureLaw (jointLaw θ : Measure _) t j.val := by
      rw [original_future_transfer θ t i, original_future_transfer θ t j]
      have he := full_future_eq (trim θ) (retainedLaw θ : Measure _) (same_law_trimming θ).2.1
        t i j i.property j.property
      exact ⟨fun h => he.mp (Quotient.exact h), fun h => Quotient.sound (he.mpr h)⟩
    exact ⟨ht,ho.trans ht.symm⟩
  · intro t
    have hf : Measurable (future (H := H) t) := by unfold future; fun_prop
    have hp : Measurable (past (H := H) t) := by unfold past; fun_prop
    have hq := originalClass_measurable θ t
    obtain ⟨hK,hI⟩ := screening_from_fiber_factor (jointLaw θ : Measure _)
      (originalClass θ t) (past t) (future t) hq hp hf (classFutureLaw θ t)
      (original_class_nonzero θ t) (original_class_factor θ t)
    refine ⟨hK,hI.symm,?_⟩
    have he := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hf hp hq).mp hI
    have hk : condDistrib (future t) (originalClass θ t) (jointLaw θ : Measure _) =
        classFutureLaw θ t := by ext a B hB; rw [hK a]
    rwa [hk] at he

#print axioms same_law_future_screening

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
