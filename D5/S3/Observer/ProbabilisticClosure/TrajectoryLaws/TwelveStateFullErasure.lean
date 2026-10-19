/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original retained half-lines recover Q0 and Z1 and determine the erased bit. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFutureRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Set Filter
open scoped BigOperators Classical Topology ENNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalFutureCylinders
open OriginalErasureComparison OriginalFutureScreening TwelveStatePresentation IndependentSeedPosterior
open FixedTargetRecovery TwelveStateFutureRecovery

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFullErasure

theorem measurable_eventual_decoder {S Q : Type*} [MeasurableSpace S]
    [MeasurableSpace Q] [Fintype Q] [Nonempty Q] [MeasurableSingletonClass Q]
    (f : ℕ → S → Q) (hf : ∀ r, Measurable (f r)) :
    ∃ g : S → Q, Measurable g ∧
      ∀ s a, (∀ᶠ r : ℕ in atTop, f r s = a) → g s = a := by
  let E (s : S) (a : Q) := ∀ᶠ r : ℕ in atTop, f r s = a
  have hE (a : Q) : MeasurableSet {s | E s a} := by
    have he : {s | E s a} = ⋃ n : ℕ, ⋂ r : ℕ, ⋂ (_ : n ≤ r), {s | f r s = a} := by
      ext s
      simp only [E,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_iInter,eventually_atTop]
    rw [he]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun r =>
      MeasurableSet.iInter fun _ => (hf r) (measurableSet_singleton a)
  have huniq (s : S) (a b : Q) (ha : E s a) (hb : E s b) : a = b := by
    obtain ⟨r,hr,hs⟩ := (ha.and hb).exists
    exact hr.symm.trans hs
  let d : Q := Classical.choice inferInstance
  let g : S → Q := fun s => if h : ∃ a, E s a then Classical.choose h else d
  have hg (s : S) (a : Q) (ha : E s a) : g s = a := by
    have hex : ∃ b, E s b := ⟨a,ha⟩
    dsimp [g]
    rw [dif_pos hex]
    exact huniq s _ a (Classical.choose_spec hex) ha
  refine ⟨g,measurable_to_countable' (fun a => ?_),hg⟩
  have he : g ⁻¹' {a} = {s | E s a} ∪ ({s | ¬∃ b, E s b} ∩ {s : S | d = a}) := by
    ext s
    by_cases hs : ∃ b, E s b
    · have hc : E s (g s) := by simpa only [g,dif_pos hs] using Classical.choose_spec hs
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_union,Set.mem_ofPred_eq,
        Set.mem_inter_iff,hs,not_true_eq_false,false_and,or_false]
      exact ⟨fun h => h ▸ hc,fun ha => hg s a ha⟩
    · have ha : ¬ E s a := fun ha => hs ⟨a,ha⟩
      simp only [g,dif_neg hs,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_union,Set.mem_ofPred_eq,
        ha,false_or,Set.mem_inter_iff,not_false_eq_true,true_and]
      exact ⟨fun h => ⟨hs,h⟩,And.right⟩
  rw [he]
  have hnot : MeasurableSet {s | ¬∃ b, E s b} := by
    have he : {s | ¬∃ b, E s b} = (⋃ b : Q, {s | E s b})ᶜ := by ext s; simp
    rw [he]
    exact (MeasurableSet.iUnion hE).compl
  exact (hE a).union (hnot.inter (by by_cases h : d = a <;> simp [h]))

/-- Measurable versions of Q0 from the complete past and Z1 from the complete future.
Both identities hold jointly on the original J. No initial future phase is recovered. -/
theorem actual_halfline_decoders :
    ∃ (gL : (ℕ → Bool) → Label) (gR : (ℕ → Bool) → Fin 3),
      Measurable gL ∧ Measurable gR ∧
      ∀ᵐ z ∂(joint : Measure Process),
        gL (before z.2) = target z ∧ gR (after z.2) = residueTarget z := by
  let fL (r : ℕ) (v : ℕ → Bool) : Label := fixedMAP r (fun k => v (r-1-k.val))
  let fR (r : ℕ) (v : ℕ → Bool) : Fin 3 := residueMAP r (fun k => v k.val)
  obtain ⟨gL,hL,hLc⟩ := measurable_eventual_decoder fL (fun r =>
    (measurable_of_finite (fixedMAP r)).comp (Measurable.of_eval fun k => measurable_pi_apply _))
  obtain ⟨gR,hR,hRc⟩ := measurable_eventual_decoder fR (fun r =>
    (measurable_of_finite (residueMAP r)).comp (Measurable.of_eval fun k => measurable_pi_apply _))
  refine ⟨gL,gR,hL,hR,?_⟩
  have hp := actual_map_recovery.{0}.2.1
  have hf := actual_future_residue_recovery.2
  filter_upwards [hp,hf] with z hz hf
  constructor
  · apply hLc
    apply hz.mono
    intro r hr
    rw [hr]
    dsimp [fL,pastWord,before]
    congr 1
    funext k
    apply congrArg z.2
    have hk := k.isLt
    omega
  · apply hRc
    apply hf.mono
    intro r hr
    rw [hr]
    dsimp [fR,futureWord,readPrefix,future,after]
    congr 1
    funext k
    apply congrArg z.2
    omega

theorem actual_edge : ∀ᵐ z ∂(joint : Measure Process), z.1 1 = next (z.1 0) (z.2 0) := by
  have hc := (same_law_trimming parameter).1
  have hlocal (i j : Hidden) (x : Bool) : ∀ᵐ z ∂(joint : Measure Process),
      z.1 0 = i → z.1 1 = j → z.2 0 = x → j = next i x := by
    by_cases he : j = next i x
    · exact Eventually.of_forall fun _ _ _ _ => he
    · let C := MarkedPredictiveQuotient.cylinder 0 1 (Fin.cons i (fun _ => j)) (fun _ => x)
      have hm : (joint : Measure Process).real C = 0 := by
        have hh := hc 0 1 (Fin.cons i (fun _ => j)) (fun _ => x)
        simp only [pathMass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
          Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hh
        change (joint : Measure Process).real C = mass i*marked x i j at hh
        simpa only [marked,if_neg he,mul_zero] using hh
      have hzero : (joint : Measure Process) C = 0 := by
        have hh : (joint : Measure Process) C = 0 ∨ (joint : Measure Process) C = ⊤ := by
          simpa only [Measure.real,ENNReal.toReal_eq_zero_iff] using hm
        exact hh.resolve_right (measure_ne_top _ _)
      have hnot : ∀ᵐ z ∂(joint : Measure Process), z ∉ C := by
        rw [ae_iff]
        convert hzero using 2
        ext z
        simp
      filter_upwards [hnot] with z hz h0 h1 hx
      exact False.elim (hz (by
        constructor
        · intro k
          refine Fin.cases ?_ (fun k => ?_) k
          · simpa [h0]
          · have he : k = 0 := Subsingleton.elim _ _
            subst k
            simpa [h1]
        · intro k
          have he : k = 0 := Subsingleton.elim _ _
          subst k
          simpa [hx]))
  have hall : ∀ᵐ z ∂(joint : Measure Process), ∀ i j x,
      z.1 0 = i → z.1 1 = j → z.2 0 = x → j = next i x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr (hlocal i j)
  filter_upwards [hall] with z hz
  exact hz _ _ _ rfl rfl rfl

/-- The complete retained exterior determines the actual erased bit: q=X0 almost surely
under the same visible P. Its actual Bernoulli-variance density and full squared loss vanish. -/
theorem actual_full_erasure :
    fullMean parameter =ᵐ[(visible : Measure (ℤ → Bool))] erasedBit ∧
    (∫ z, fullMean parameter z*(1-fullMean parameter z) ∂(visible : Measure (ℤ → Bool))) = 0 ∧
    (∫ z, (erasedBit z-fullMean parameter z)^2 ∂(visible : Measure (ℤ → Bool))) = 0 := by
  obtain ⟨gL,gR,hL,hR,hdec⟩ := actual_halfline_decoders
  let d : ((ℕ → Bool) × (ℕ → Bool)) → ℝ := fun v =>
    if gR v.2 = (gL v.1).2 then 0 else 1
  have hd : Measurable d := by
    apply Measurable.ite
    · exact measurableSet_eq_fun (hR.comp measurable_snd) (measurable_snd.comp (hL.comp measurable_fst))
    · exact measurable_const
    · exact measurable_const
  have hdJ : (fun z : Process => d (exterior z.2)) =ᵐ[(joint : Measure Process)]
      (fun z => erasedBit z.2) := by
    filter_upwards [hdec,actual_edge] with z hz he
    have hres (i : Hidden) (x : Bool) : (label (next i x)).2 = (label i).2 ↔ x = false := by
      rcases i with ⟨b,s⟩
      cases b <;> fin_cases s <;> cases x <;> norm_num [label,next,advance]
    dsimp [d,exterior]
    rw [hz.1,hz.2]
    change (if (label (z.1 1)).2 = (label (z.1 0)).2 then (0:ℝ) else 1) = erasedBit z.2
    rw [he]
    simp only [hres]
    cases hx : z.2 0 <;> simp [erasedBit,hx]
  have ho : Measurable (exterior ∘ (Prod.snd : Process → ℤ → Bool)) := by
    unfold exterior before after
    fun_prop
  have hf : Integrable (fun z : Process => erasedBit z.2) (joint : Measure Process) := by
    have he : (fun z : Process => erasedBit z.2) = {z | z.2 0 = true}.indicator (fun _ => (1:ℝ)) := by
      funext z
      cases hx : z.2 0 <;> simp [erasedBit,hx]
    rw [he]
    exact (integrable_const 1).indicator ((measurableSet_singleton true).preimage
      ((measurable_pi_apply 0).comp measurable_snd))
  have hAES : AEStronglyMeasurable[MeasurableSpace.comap
      (exterior ∘ (Prod.snd : Process → ℤ → Bool)) inferInstance]
      (fun z : Process => erasedBit z.2) (joint : Measure Process) := by
    refine ⟨fun z => d (exterior z.2),?_,hdJ.symm⟩
    exact (hd.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hpost := visible_conditional_pullback parameter exterior (by
    unfold exterior before after
    fun_prop)
  have hfullJ : (fun z : Process => fullMean parameter z.2) =ᵐ[(joint : Measure Process)]
      (fun z => erasedBit z.2) :=
    hpost.trans (condExp_of_aestronglyMeasurable' ho.comap_le hAES hf)
  have hm : Measurable (fullMean parameter) := by
    change Measurable (fun z : ℤ → Bool =>
      ((ProbabilityTheory.condDistrib (fun z : ℤ → Bool => z 0) exterior
        (visibleLaw parameter : Measure _) (exterior z)) {true}).toReal)
    have hoV : Measurable exterior := by unfold exterior before after; fun_prop
    exact (ProbabilityTheory.Kernel.measurable_coe
      (ProbabilityTheory.condDistrib (fun z : ℤ → Bool => z 0) exterior
        (visibleLaw parameter : Measure _)) (measurableSet_singleton true)).ennreal_toReal.comp hoV
  have hbit : Measurable erasedBit :=
    (measurable_of_finite (fun b : Bool => if b then (1:ℝ) else 0)).comp (measurable_pi_apply 0)
  have hv : fullMean parameter =ᵐ[(visible : Measure (ℤ → Bool))] erasedBit := by
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_eq_fun hm hbit)).mpr
    exact hfullJ
  refine ⟨hv,?_,?_⟩
  · calc
      _ = ∫ z, (0:ℝ) ∂(visible : Measure (ℤ → Bool)) := integral_congr_ae (hv.mono fun z hz => by
        rw [hz]
        cases hx : z 0 <;> simp [erasedBit,hx])
      _ = 0 := integral_zero _ _
  · calc
      _ = ∫ z, (0:ℝ) ∂(visible : Measure (ℤ → Bool)) := integral_congr_ae (hv.mono fun z hz => by rw [hz]; ring)
      _ = 0 := integral_zero _ _

#print axioms actual_halfline_decoders
#print axioms actual_full_erasure
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFullErasure
