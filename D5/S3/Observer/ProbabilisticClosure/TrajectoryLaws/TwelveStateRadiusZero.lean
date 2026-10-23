/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complete half-line posteriors and exact forcing-event erasure risks. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFullErasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function Set Filter
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalFutureCylinders
open OriginalFutureScreening OriginalErasureComparison TwelveStatePresentation
open IndependentSeedPosterior TwelveStateFullErasure

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateRadiusZero

private theorem finite_integral {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : Process → A) (hf : Measurable f)
    (g : A → ℝ) (E : Set Process) :
    ∫ z in E, g (f z) ∂(joint : Measure Process) =
      ∑ a, (joint : Measure Process).real (E ∩ f ⁻¹' {a})*g a := by
  classical
  rw [← integral_map hf.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro a _
  rw [measureReal_def,Measure.map_apply hf (measurableSet_singleton a)]
  simp only [Measure.restrict_apply (hf (measurableSet_singleton a)),smul_eq_mul,
    Measure.real,Set.inter_comm]

private theorem finite_integrable {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : Process → A) (hf : Measurable f) (g : A → ℝ) :
    Integrable (fun z => g (f z)) (joint : Measure Process) :=
  (integrable_map_measure (measurable_of_finite g).aestronglyMeasurable hf.aemeasurable).mp
    Integrable.of_finite

private abbrev Cell := Bool × (Bool × (Hidden × (Hidden × Hidden)))
private def edgeSample (z : Process) : Cell := (z.2 0,z.2 1,z.1 0,z.1 1,z.1 2)
private def edgeHidden (p : Cell) (k : Fin 3) : Hidden :=
  if k.val = 0 then p.2.2.1 else if k.val = 1 then p.2.2.2.1 else p.2.2.2.2
private def edgeWord (p : Cell) (k : Fin 2) : Bool := if k.val = 0 then p.1 else p.2.1
private def prepend (b : Bool) (v : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | n+1 => v n

private theorem edge_measurable : Measurable edgeSample := by
  unfold edgeSample
  fun_prop

private theorem edge_event (p : Cell) : edgeSample ⁻¹' {p} =
    MarkedPredictiveQuotient.cylinder 0 2 (edgeHidden p) (edgeWord p) := by
  rcases p with ⟨x,y,i,j,k⟩
  ext z
  simp only [Set.mem_preimage,Set.mem_singleton_iff,edgeSample,Prod.mk.injEq,
    MarkedPredictiveQuotient.cylinder,Set.mem_setOf_eq,edgeHidden,edgeWord]
  constructor
  · rintro ⟨h0,h1,hi,hj,hk⟩
    constructor
    · intro a; fin_cases a
      · simpa using hi
      · simpa using hj
      · simpa using hk
    · intro a; fin_cases a
      · simpa using h0
      · simpa using h1
  · rintro ⟨hh,hx⟩
    exact ⟨by simpa using hx 0,by simpa using hx 1,
      by simpa using hh 0,by simpa using hh 1,by simpa using hh 2⟩

private theorem edge_future_mass (p : Cell) (D : Set (ℕ → Bool)) (hD : MeasurableSet D) :
    (joint : Measure Process).real ((after ∘ Prod.snd) ⁻¹' D ∩ edgeSample ⁻¹' {p}) =
      mass p.2.2.1 * marked p.1 p.2.2.1 p.2.2.2.1 *
        marked p.2.1 p.2.2.2.1 p.2.2.2.2 *
        (futureLaw (joint : Measure Process) 2 p.2.2.2.2).real (prepend p.2.1 ⁻¹' D) := by
  classical
  have hpre : Measurable (prepend p.2.1) := by
    apply measurable_pi_lambda
    intro n
    cases n <;> simp only [prepend] <;> fun_prop
  have he : ((after ∘ Prod.snd) ⁻¹' D ∩ edgeSample ⁻¹' {p}) =
      future 2 ⁻¹' (prepend p.2.1 ⁻¹' D) ∩
        MarkedPredictiveQuotient.cylinder 0 2 (edgeHidden p) (edgeWord p) := by
    rw [← edge_event]
    ext z
    have heq (hz : edgeSample z = p) : after z.2 = prepend p.2.1 (future 2 z) := by
      funext n
      cases n with
      | zero => exact congrArg (fun q : Cell => q.2.1) hz
      | succ n =>
          change z.2 (((n+1:ℕ):ℤ)+1) = z.2 (2+(n:ℤ))
          exact congrArg z.2 (by omega)
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,Function.comp_apply]
    exact ⟨fun hz => ⟨by simpa only [← heq hz.2] using hz.1,hz.2⟩,
      fun hz => ⟨by simpa only [heq hz.2] using hz.1,hz.2⟩⟩
  have hc := cylinder_future_law parameter (joint : Measure Process)
    (same_law_trimming parameter).1 (2:ℤ) 2 (edgeHidden p) (edgeWord p)
    (mass_pos ((edgeHidden p) (Fin.last 2)))
  have hh := congrArg (fun μ : Measure (ℕ → Bool) => μ (prepend p.2.1 ⁻¹' D)) hc
  simp only [show (2:ℤ)-(2:ℕ) = 0 by norm_num] at hh
  rw [Measure.map_apply (by unfold future; fun_prop) (hD.preimage hpre),
    Measure.restrict_apply ((hD.preimage hpre).preimage (by unfold future; fun_prop)),
    Measure.smul_apply,smul_eq_mul] at hh
  have hmass := (same_law_trimming parameter).1 0 2 (edgeHidden p) (edgeWord p)
  rw [he,Measure.real,hh,ENNReal.toReal_mul]
  change _ = _
  change (joint : Measure Process).real _ = mass (edgeHidden p 0)*pathMass marked 2 (edgeHidden p) (edgeWord p) at hmass
  rw [← Measure.real,hmass]
  simp [edgeHidden,edgeWord,pathMass,Fin.prod_univ_succ,mul_assoc,Measure.real]

private theorem edge_future_integral (D : Set (ℕ → Bool)) (hD : MeasurableSet D)
    (g : Cell → ℝ) :
    ∫ z in (after ∘ Prod.snd) ⁻¹' D, g (edgeSample z) ∂(joint : Measure Process) =
      ∑ x : Bool, ∑ y : Bool, ∑ i : Hidden, ∑ j : Hidden, ∑ k : Hidden,
        (mass i * marked x i j * marked y j k *
          (futureLaw (joint : Measure Process) 2 k).real (prepend y ⁻¹' D))*g (x,y,i,j,k) := by
  rw [finite_integral _ edge_measurable]
  simp_rw [edge_future_mass _ D hD]
  exact Fintype.sum_prod_type _ |>.trans (by
    simp only [Fintype.sum_prod_type])

/-- Actual future-only posterior candidate: it uses the time-one residue and the retained X1.
The full future recovers that residue, without recovering its initial F/T phase. -/
def futureGuess (z : Process) : ℝ := if z.2 1 then 0 else rate (z.1 1).2

private theorem future_integrals (D : Set (ℕ → Bool)) (hD : MeasurableSet D) :
    ∫ z in (after ∘ Prod.snd) ⁻¹' D, futureGuess z ∂(joint : Measure Process) =
    ∫ z in (after ∘ Prod.snd) ⁻¹' D, erasedBit z.2 ∂(joint : Measure Process) := by
  have h1 := edge_future_integral D hD (fun p => if p.2.1 then 0 else rate p.2.2.2.1.2)
  have h2 := edge_future_integral D hD (fun p => if p.1 then (1:ℝ) else 0)
  change (∫ z in (after ∘ Prod.snd) ⁻¹' D, futureGuess z ∂(joint : Measure Process)) = _ at h1
  change (∫ z in (after ∘ Prod.snd) ⁻¹' D, erasedBit z.2 ∂(joint : Measure Process)) = _ at h2
  rw [h1,h2]
  simp only [marked,mul_ite,ite_mul,mul_zero,zero_mul,
    Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  norm_num [prob,next,mass,rate,advance,Fintype.sum_bool,Fintype.sum_prod_type,Fin.sum_univ_succ]
  <;> norm_num [Fin.succ,Fin.instOfNat,Fin.ofNat]
  <;> ring

/-- Actual whole-past posterior candidate, at the fixed time-zero hidden state. -/
def pastGuess (z : Process) : ℝ := prob (z.1 0) true

private theorem right_integrals (D : Set (ℕ → Bool)) (hD : MeasurableSet D) :
    ∫ z in (before ∘ Prod.snd) ⁻¹' D, pastGuess z ∂(joint : Measure Process) =
    ∫ z in (before ∘ Prod.snd) ⁻¹' D, erasedBit z.2 ∂(joint : Measure Process) := by
  classical
  let E := (before ∘ (Prod.snd : Process → ℤ → Bool)) ⁻¹' D
  let C := {z : Process | z.2 0 = true}
  have hC : MeasurableSet C := (measurableSet_singleton true).preimage (by fun_prop)
  have hbit : (fun z : Process => erasedBit z.2) = C.indicator (fun _ => (1:ℝ)) := by
    funext z
    cases hx : z.2 0 <;> simp [C,erasedBit,hx]
  have hX : (∫ z in E, erasedBit z.2 ∂(joint : Measure Process)) =
      (joint : Measure Process).real (E ∩ C) := by rw [hbit,setIntegral_indicator hC]; simp
  have hpart := sum_measureReal_preimage_singleton
    (μ := (joint : Measure Process).restrict (E ∩ C)) Finset.univ
    (f := state 0) (fun i _ => (measurableSet_singleton i).preimage (by unfold state; fun_prop))
  simp only [Finset.coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hpart
  have hmass (i : Hidden) : (joint : Measure Process).real
      ((state 0 ⁻¹' {i}) ∩ (E ∩ C)) =
      (joint : Measure Process).real (E ∩ (state 0 ⁻¹' {i}))*prob i true := by
    let A : Set (ℕ → Hidden × Bool) := (fun v n => (v n).2) ⁻¹' D
    let B : Set (ℕ → Bool) := readPrefix 1 ⁻¹' {(fun _ => true)}
    have hA : MeasurableSet A := hD.preimage (by fun_prop)
    have hB : MeasurableSet B := (measurableSet_singleton _).preimage (by unfold readPrefix; fun_prop)
    have hp := full_past_future_factor parameter (joint : Measure Process)
      (same_law_trimming parameter).1 0 i (mass_pos i) A B hA hB
    have ht := futureLaw_readPrefix parameter (joint : Measure Process)
      (same_law_trimming parameter).1 0 i (mass_pos i) 1 (fun _ => true)
    rw [Measure.map_apply (by unfold readPrefix; fun_prop) (measurableSet_singleton _)] at ht
    change (futureLaw (joint : Measure Process) 0 i) B = ENNReal.ofReal (futureMass marked i 1 (fun _ => true)) at ht
    rw [future_one] at ht
    have he : past 0 ⁻¹' A = E := by
      have hf : (fun z : Process => fun n => (past 0 z n).2) = before ∘ Prod.snd := by
        funext z n
        dsimp [past,before,Function.comp_def]
        congr 1
      change (fun z : Process => fun n => (past 0 z n).2) ⁻¹' D = E
      rw [hf]
    have hc : future 0 ⁻¹' B = C := by
      ext z
      simp [B,C,readPrefix,future,funext_iff]
    rw [he,hc,ht] at hp
    have hprob : 0 ≤ prob i true := by
      rcases i with ⟨b,s⟩
      cases b <;> fin_cases s <;> norm_num [prob,rate]
    have hr := congrArg ENNReal.toReal hp
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofReal
      hprob,Set.inter_assoc,Set.inter_comm,
      Set.inter_left_comm] using hr
  change (∫ z in E, prob (state 0 z) true ∂(joint : Measure Process)) = _
  rw [finite_integral (state 0) (by unfold state; fun_prop) (fun i => prob i true) E,hX]
  rw [← hpart]
  apply Finset.sum_congr rfl
  intro i _
  rw [measureReal_restrict_apply ((measurableSet_singleton i).preimage (by unfold state; fun_prop)),hmass]

private theorem guess_aestrongly_measurable :
    AEStronglyMeasurable[MeasurableSpace.comap (after ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance]
      futureGuess (joint : Measure Process) ∧
    AEStronglyMeasurable[MeasurableSpace.comap (before ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance]
      pastGuess (joint : Measure Process) := by
  obtain ⟨gL,gR,hL,hR,hdec⟩ := actual_halfline_decoders
  let p (a : Fin 3) : ℝ := rate ⟨a.val,by omega⟩
  have hp (s : Fin 6) : p (label (false,s)).2 = rate s := by
    fin_cases s <;> norm_num [p,label,rate]
  constructor
  · let f : (ℕ → Bool) → ℝ := fun v => if v 0 then 0 else p (gR v)
    have hf : Measurable f := Measurable.ite
      ((measurableSet_singleton true).preimage (measurable_pi_apply 0))
      measurable_const ((measurable_of_finite p).comp hR)
    refine ⟨f ∘ (after ∘ Prod.snd),
      (hf.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable,?_⟩
    filter_upwards [hdec] with z hz
    dsimp [f,futureGuess,Function.comp_def,after]
    rw [hz.2]
    change (if z.2 1 then (0:ℝ) else rate (z.1 1).2) =
      (if z.2 1 then 0 else p (label (z.1 1)).2)
    rw [show p (label (z.1 1)).2 = rate (z.1 1).2 from hp (z.1 1).2]
  · let f : (ℕ → Bool) → ℝ := fun v => if (gL v).1 then 0 else p (gL v).2
    have hf : Measurable f := Measurable.ite
      ((measurableSet_singleton true).preimage (measurable_fst.comp hL))
      measurable_const ((measurable_of_finite p).comp (measurable_snd.comp hL))
    refine ⟨f ∘ (before ∘ Prod.snd),
      (hf.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable,?_⟩
    filter_upwards [hdec] with z hz
    dsimp only [f,Function.comp_def]
    rw [hz.1]
    dsimp only [target,pastGuess,prob,label]
    rw [show p ⟨(z.1 0).2.val%3,Nat.mod_lt _ (by decide)⟩ = rate (z.1 0).2 from hp _]
    simp

private theorem halfline_condExp (o : Process → (ℕ → Bool)) (ho : Measurable o)
    (g : Process → ℝ) (hg : Integrable g (joint : Measure Process))
    (hgm : AEStronglyMeasurable[MeasurableSpace.comap o inferInstance] g (joint : Measure Process))
    (h : ∀ D, MeasurableSet D → ∫ z in o ⁻¹' D, g z ∂(joint : Measure Process) =
      ∫ z in o ⁻¹' D, erasedBit z.2 ∂(joint : Measure Process)) :
    g =ᵐ[(joint : Measure Process)]
      (joint : Measure Process)[fun z => erasedBit z.2 | MeasurableSpace.comap o inferInstance] := by
  have hi := finite_integrable (fun z : Process => z.2 0) (by fun_prop)
    (fun b : Bool => if b then (1:ℝ) else 0)
  apply ae_eq_condExp_of_forall_setIntegral_eq ho.comap_le hi
    (fun _ _ _ => hg.integrableOn) _ hgm
  intro E hE _
  obtain ⟨D,hD,rfl⟩ := (MeasurableSpace.measurableSet_comap).mp hE
  exact h D hD

/-- The native actual radius-zero posteriors on the original law equal the stated
whole-future and whole-past versions. The future version uses only Z1 and retained X1. -/
theorem actual_halfline_posteriors :
    (fun z : Process => leftMean parameter 0 z.2) =ᵐ[(joint : Measure Process)] futureGuess ∧
    (fun z : Process => rightMean parameter 0 z.2) =ᵐ[(joint : Measure Process)] pastGuess := by
  have hL := halfline_condExp (after ∘ Prod.snd) (by unfold after; fun_prop)
    futureGuess (finite_integrable edgeSample edge_measurable (fun p =>
      if p.2.1 then 0 else rate p.2.2.2.1.2)) guess_aestrongly_measurable.1 future_integrals
  have hR := halfline_condExp (before ∘ Prod.snd) (by unfold before; fun_prop)
    pastGuess (finite_integrable (state 0) (by unfold state; fun_prop) (fun i => prob i true))
      guess_aestrongly_measurable.2 right_integrals
  have hLF : MeasurableSpace.comap (leftObservation 0 ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance =
      MeasurableSpace.comap (after ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance := by
    have hw : (fun z : Process => leftWord 0 z.2) = fun _ => (fun k : Fin 0 => nomatch k) :=
      funext fun _ => funext fun k => nomatch k
    change MeasurableSpace.comap (fun z : Process => (leftWord 0 z.2,after z.2)) inferInstance = _
    apply le_antisymm
    · apply Measurable.comap_le
      rw [show (fun z : Process => (leftWord 0 z.2,after z.2)) =
        (fun z : Process => ((fun k : Fin 0 => nomatch k),after z.2)) from by funext z; exact Prod.ext (Subsingleton.elim _ _) rfl]
      exact measurable_const.prodMk (Measurable.of_comap_le le_rfl)
    · change MeasurableSpace.comap (Prod.snd ∘ (fun z : Process => (leftWord 0 z.2,after z.2))) inferInstance ≤ _
      exact (measurable_snd.comp (Measurable.of_comap_le le_rfl)).comap_le
  have hRF : MeasurableSpace.comap (rightObservation 0 ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance =
      MeasurableSpace.comap (before ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance := by
    have hw : (fun z : Process => rightWord 0 z.2) = fun _ => (fun k : Fin 0 => nomatch k) :=
      funext fun _ => funext fun k => nomatch k
    change MeasurableSpace.comap (fun z : Process => (before z.2,rightWord 0 z.2)) inferInstance = _
    apply le_antisymm
    · apply Measurable.comap_le
      rw [show (fun z : Process => (before z.2,rightWord 0 z.2)) =
        (fun z : Process => (before z.2,(fun k : Fin 0 => nomatch k))) from by funext z; exact Prod.ext rfl (Subsingleton.elim _ _)]
      exact (Measurable.of_comap_le le_rfl).prodMk measurable_const
    · change MeasurableSpace.comap (Prod.fst ∘ (fun z : Process => (before z.2,rightWord 0 z.2))) inferInstance ≤ _
      exact (measurable_fst.comp (Measurable.of_comap_le le_rfl)).comap_le
  have hLp := visible_conditional_pullback parameter (leftObservation 0) (by unfold leftObservation leftWord after; fun_prop)
  have hRp := visible_conditional_pullback parameter (rightObservation 0) (by unfold rightObservation rightWord before; fun_prop)
  rw [hLF] at hLp
  rw [hRF] at hRp
  exact ⟨hLp.trans hL.symm,hRp.trans hR.symm⟩

private theorem edge_integral (g : Cell → ℝ) :
    ∫ z, g (edgeSample z) ∂(joint : Measure Process) =
      ∑ x : Bool, ∑ y : Bool, ∑ i : Hidden, ∑ j : Hidden, ∑ k : Hidden,
        (mass i * marked x i j * marked y j k)*g (x,y,i,j,k) := by
  have h := edge_future_integral Set.univ MeasurableSet.univ g
  simpa [futureLaw,Measure.real] using h

private theorem full_pullback : (fun z : Process => fullMean parameter z.2) =ᵐ[(joint : Measure Process)]
    (fun z => erasedBit z.2) :=
  ae_of_ae_map measurable_snd.aemeasurable actual_full_erasure.1

private theorem left_loss (r : ℕ) : Measurable (fun z : ℤ → Bool =>
    (fullMean parameter z-leftMean parameter r z)^2) := by
  apply Measurable.pow_const
  exact ((bitPredictor_measurable _ _ _).comp (by unfold exterior before after; fun_prop)).sub
    ((bitPredictor_measurable _ _ _).comp (by unfold leftObservation leftWord after; fun_prop))

private theorem right_loss (r : ℕ) : Measurable (fun z : ℤ → Bool =>
    (fullMean parameter z-rightMean parameter r z)^2) := by
  apply Measurable.pow_const
  exact ((bitPredictor_measurable _ _ _).comp (by unfold exterior before after; fun_prop)).sub
    ((bitPredictor_measurable _ _ _).comp (by unfold rightObservation rightWord before; fun_prop))

/-- Both native radius-zero defects are exactly 9/62 under the original visible law. -/
theorem actual_radius_zero_risks : leftRisk parameter 0 = 9/62 ∧ rightRisk parameter 0 = 9/62 := by
  have hp := actual_halfline_posteriors
  constructor
  · unfold leftRisk
    change (∫ z, (fullMean parameter z-leftMean parameter 0 z)^2
      ∂(joint : Measure Process).map Prod.snd) = _
    rw [integral_map measurable_snd.aemeasurable (left_loss 0).aestronglyMeasurable]
    calc
      _ = ∫ z : Process, (erasedBit z.2-futureGuess z)^2 ∂(joint : Measure Process) := by
        apply integral_congr_ae
        filter_upwards [full_pullback,hp.1] with z hq hm
        rw [hq,hm]
      _ = 9/62 := by
        have he := edge_integral (fun p => ((if p.1 then (1:ℝ) else 0)-
          (if p.2.1 then 0 else rate p.2.2.2.1.2))^2)
        simp only [edgeSample] at he
        dsimp only [erasedBit,futureGuess,pastGuess]
        rw [he]
        simp only [marked,mul_ite,ite_mul,mul_zero,zero_mul,
          Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
        norm_num [prob,next,mass,rate,advance,Fintype.sum_bool,Fintype.sum_prod_type,Fin.sum_univ_succ]
  · unfold rightRisk
    change (∫ z, (fullMean parameter z-rightMean parameter 0 z)^2
      ∂(joint : Measure Process).map Prod.snd) = _
    rw [integral_map measurable_snd.aemeasurable (right_loss 0).aestronglyMeasurable]
    calc
      _ = ∫ z : Process, (erasedBit z.2-pastGuess z)^2 ∂(joint : Measure Process) := by
        apply integral_congr_ae
        filter_upwards [full_pullback,hp.2] with z hq hm
        rw [hq,hm]
      _ = 9/62 := by
        have he := edge_integral (fun p => ((if p.1 then (1:ℝ) else 0)-prob p.2.2.1 true)^2)
        simp only [edgeSample] at he
        dsimp only [erasedBit,futureGuess,pastGuess]
        rw [he]
        simp only [marked,mul_ite,ite_mul,mul_zero,zero_mul,
          Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
        norm_num [prob,next,mass,rate,advance,Fintype.sum_bool,Fintype.sum_prod_type,Fin.sum_univ_succ]

private theorem previous_phase : ∀ᵐ z ∂(joint : Measure Process), (z.1 0).1 = z.2 (-1) := by
  have hm : Measurable (shift (H := Hidden) (-1)) := by
    unfold shift
    fun_prop
  have hs := (same_law_trimming parameter).2.2.2.2.2.1 (-1)
  change (joint : Measure Process).map (shift (-1)) = joint at hs
  have he : ∀ᵐ z ∂(joint : Measure Process).map (shift (-1)), z.1 1 = next (z.1 0) (z.2 0) := by
    rw [hs]
    exact actual_edge
  have hh := ae_of_ae_map hm.aemeasurable he
  filter_upwards [hh] with z hz
  have hp := congrArg Prod.fst hz
  simpa [shift,next] using hp

/-- The omitted forcing neighbors have positive native radius-zero contributions.
The smaller original hidden event retains its exact 9/3968 contribution. -/
theorem actual_forcing_contributions :
    (∫ z, (if z (-1) then (fullMean parameter z-leftMean parameter 0 z)^2 else 0)
      ∂(visible : Measure (ℤ → Bool))) = 15/496 ∧
    (∫ z, (if z 1 then (fullMean parameter z-rightMean parameter 0 z)^2 else 0)
      ∂(visible : Measure (ℤ → Bool))) = 15/496 ∧
    (∫ z : Process, (if z.1 0 = (true,0) ∧ z.2 1 = false then
      (fullMean parameter z.2-leftMean parameter 0 z.2)^2 else 0)
      ∂(joint : Measure Process)) = 9/3968 := by
  have hp := actual_halfline_posteriors
  refine ⟨?_,?_,?_⟩
  · change (∫ z, (if z (-1) then (fullMean parameter z-leftMean parameter 0 z)^2 else 0)
      ∂(joint : Measure Process).map Prod.snd) = _
    have hi : Measurable (fun z : ℤ → Bool => if z (-1) then
        (fullMean parameter z-leftMean parameter 0 z)^2 else 0) := by
      apply Measurable.ite
      · exact (measurableSet_singleton true).preimage (measurable_pi_apply (-1))
      · exact left_loss 0
      · exact measurable_const
    rw [integral_map measurable_snd.aemeasurable hi.aestronglyMeasurable]
    calc
      _ = ∫ z : Process, (if (z.1 0).1 then (erasedBit z.2-futureGuess z)^2 else 0)
          ∂(joint : Measure Process) := by
        apply integral_congr_ae
        filter_upwards [full_pullback,hp.1,previous_phase] with z hq hm he
        rw [hq,hm,← he]
      _ = 15/496 := by
        have he := edge_integral (fun p => if p.2.2.1.1 then ((if p.1 then (1:ℝ) else 0)-
          (if p.2.1 then 0 else rate p.2.2.2.1.2))^2 else 0)
        simp only [edgeSample] at he
        dsimp only [erasedBit,futureGuess,pastGuess]
        rw [he]
        simp only [marked,mul_ite,ite_mul,mul_zero,zero_mul,
          Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
        norm_num [prob,next,mass,rate,advance,Fintype.sum_bool,Fintype.sum_prod_type,Fin.sum_univ_succ]
  · change (∫ z, (if z 1 then (fullMean parameter z-rightMean parameter 0 z)^2 else 0)
      ∂(joint : Measure Process).map Prod.snd) = _
    have hi : Measurable (fun z : ℤ → Bool => if z 1 then
        (fullMean parameter z-rightMean parameter 0 z)^2 else 0) := by
      apply Measurable.ite
      · exact (measurableSet_singleton true).preimage (measurable_pi_apply 1)
      · exact right_loss 0
      · exact measurable_const
    rw [integral_map measurable_snd.aemeasurable hi.aestronglyMeasurable]
    calc
      _ = ∫ z : Process, (if z.2 1 then (erasedBit z.2-pastGuess z)^2 else 0)
          ∂(joint : Measure Process) := by
        apply integral_congr_ae
        filter_upwards [full_pullback,hp.2] with z hq hm
        rw [hq,hm]
      _ = 15/496 := by
        have he := edge_integral (fun p => if p.2.1 then ((if p.1 then (1:ℝ) else 0)-
          prob p.2.2.1 true)^2 else 0)
        simp only [edgeSample] at he
        dsimp only [erasedBit,futureGuess,pastGuess]
        rw [he]
        simp only [marked,mul_ite,ite_mul,mul_zero,zero_mul,
          Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
        norm_num [prob,next,mass,rate,advance,Fintype.sum_bool,Fintype.sum_prod_type,Fin.sum_univ_succ]
  · calc
      _ = ∫ z : Process, (if z.1 0 = (true,0) ∧ z.2 1 = false then
          (erasedBit z.2-futureGuess z)^2 else 0) ∂(joint : Measure Process) := by
        apply integral_congr_ae
        filter_upwards [full_pullback,hp.1] with z hq hm
        rw [hq,hm]
      _ = 9/3968 := by
        have he := edge_integral (fun p => if p.2.2.1 = (true,0) ∧ p.2.1 = false then
          ((if p.1 then (1:ℝ) else 0)-(if p.2.1 then 0 else rate p.2.2.2.1.2))^2 else 0)
        simp only [edgeSample] at he
        dsimp only [erasedBit,futureGuess,pastGuess]
        rw [he]
        simp only [marked,mul_ite,ite_mul,mul_zero,zero_mul,
          Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
        norm_num [prob,next,mass,rate,advance,Fintype.sum_bool,Fintype.sum_prod_type,Fin.sum_univ_succ]

#print axioms actual_forcing_contributions

#print axioms actual_radius_zero_risks

#print axioms actual_halfline_posteriors

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateRadiusZero
