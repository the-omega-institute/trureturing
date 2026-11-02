/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Ergodicity/IrreducibleVisibleErgodicity
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Ergodicity/IrreducibleVisibleErgodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite irreducible stationary presentations have ergodic actual visible laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateErgodicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function Set Filter
open scoped BigOperators ENNReal Classical symmDiff
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalFutureCylinders
open OriginalFutureScreening OriginalErasureComparison
open IndependentSeedPosterior TwelveStateFullErasure TwelveStateErgodicity

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

private theorem translate_preserving (θ : Presentation H) (a : ℤ) :
    MeasurePreserving (TwelveStateErgodicity.translate a) (visibleLaw θ : Measure (ℤ → Bool))
      (visibleLaw θ : Measure (ℤ → Bool)) :=
  ⟨by unfold TwelveStateErgodicity.translate; fun_prop,(same_law_trimming θ).2.2.2.2.2.2.1 a⟩

private theorem invariant_decoder (θ : Presentation H) (E : Set (ℤ → Bool)) (hE : MeasurableSet E)
    (hi : TwelveStateErgodicity.translate 1 ⁻¹' E = E) (left : Bool) :
    ∃ g : (ℕ → Bool) → Bool, Measurable g ∧
      ∀ᵐ z ∂(visibleLaw θ : Measure (ℤ → Bool)),
        g (if left then before z else after z) = decide (z ∈ E) := by
  classical
  have hcover : ∃ D : Set (Set (ℤ → Bool)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℤ => Bool) ∧ (visibleLaw θ : Measure _) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ},Set.countable_singleton _,?_,by simp⟩
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    exact univ_mem_measurableCylinders _
  have happ (n : ℕ) : ∃ C ∈ measurableCylinders (fun _ : ℤ => Bool),
      (visibleLaw θ : Measure _) (C ∆ E) < (2⁻¹ : ℝ≥0∞)^n :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing isSetRing_measurableCylinders
      hcover generateFrom_measurableCylinders.symm hE (ENNReal.pow_pos (by norm_num) n)
  choose C hC hc using happ
  let I (n : ℕ) := measurableCylinders.finset (hC n)
  let S (n : ℕ) := measurableCylinders.set (hC n)
  let N (n : ℕ) : ℕ := (I n).sup Int.natAbs
  let a (n : ℕ) : ℤ := if left then -(N n : ℤ)-1 else (N n : ℤ)+1
  let pick (n : ℕ) (i : I n) : ℕ :=
    if left then ((N n : ℤ)-i.val).toNat else ((N n : ℤ)+i.val).toNat
  let f (n : ℕ) (v : ℕ → Bool) : Bool := decide ((fun i : I n => v (pick n i)) ∈ S n)
  have hf (n : ℕ) : Measurable (f n) :=
    (measurable_of_finite (fun w : (i : I n) → Bool => decide (w ∈ S n))).comp
      (Measurable.of_eval fun i => measurable_pi_apply _)
  have hread (n : ℕ) (z : ℤ → Bool) :
      f n (if left then before z else after z) = decide (TwelveStateErgodicity.translate (a n) z ∈ C n) := by
    have he := measurableCylinders.eq_cylinder (hC n)
    have hb (i : I n) : Int.natAbs i.val ≤ N n := Finset.le_sup i.property
    have hsel : (fun i : I n => (if left then before z else after z) (pick n i)) =
        (I n).restrict (TwelveStateErgodicity.translate (a n) z) := by
      funext i
      have h := hb i
      have hab := Int.natAbs_eq i.val
      cases left <;> dsimp [pick,a,before,after,TwelveStateErgodicity.translate,Finset.restrict] <;> congr 1 <;> omega
    simp only [f,hsel]
    congr 1
    conv_rhs => rw [he]
    rfl
  let bad (n : ℕ) := TwelveStateErgodicity.translate (a n) ⁻¹' (C n ∆ E)
  have hsum : (∑' n, (visibleLaw θ : Measure _) (bad n)) ≠ ⊤ := by
    apply ne_of_lt
    apply (ENNReal.tsum_le_tsum (fun n => ?_)).trans_lt
      (show (∑' n : ℕ, (2⁻¹ : ℝ≥0∞)^n) < ⊤ by simp)
    rw [(translate_preserving θ _).measure_preimage
      ((MeasurableSet.of_mem_measurableCylinders (hC n)).symmDiff hE).nullMeasurableSet]
    exact (hc n).le
  obtain ⟨g,hg,hcorrect⟩ := measurable_eventual_decoder f hf
  refine ⟨g,hg,?_⟩
  filter_upwards [ae_eventually_notMem hsum] with z hz
  apply hcorrect
  apply hz.mono
  intro n hn
  rw [hread]
  have hi' : TwelveStateErgodicity.translate (a n) z ∈ E ↔ z ∈ E := Set.ext_iff.mp (all_invariant E hi (a n)) z
  dsimp only [bad,Set.mem_preimage] at hn
  have hn' : ¬ (TwelveStateErgodicity.translate (a n) z ∈ C n ∆ E) := hn
  simp only [Set.mem_symmDiff,hi'] at hn'
  have heq : (TwelveStateErgodicity.translate (a n) z ∈ C n) ↔ z ∈ E := by tauto
  simp only [heq]

private theorem state_event (θ : Presentation H) (hinit : ∀ i, 0 < θ.initial i) (E : Set (ℤ → Bool)) (hE : MeasurableSet E)
    (hi : TwelveStateErgodicity.translate 1 ⁻¹' E = E) :
    ∃ c : H → Bool, ∀ᵐ z ∂(jointLaw θ : Measure (PathSpace H)),
      c (z.1 0) = decide (z.2 ∈ E) := by
  classical
  obtain ⟨gL,hgL,hL⟩ := invariant_decoder θ E hE hi true
  obtain ⟨gR,hgR,hR⟩ := invariant_decoder θ E hE hi false
  let A : Set (ℕ → H × Bool) := {v | gL (fun n => (v n).2) = true}
  let B : Set (ℕ → Bool) := {v | gR (fun n => v (n+1)) = true}
  let L : Set (PathSpace H) := past 0 ⁻¹' A
  let R : Set (PathSpace H) := future 0 ⁻¹' B
  let F : Set (PathSpace H) := Prod.snd ⁻¹' E
  have hA : MeasurableSet A := (measurableSet_singleton true).preimage (hgL.comp (by fun_prop))
  have hB : MeasurableSet B := (measurableSet_singleton true).preimage (hgR.comp (by fun_prop))
  have hF : MeasurableSet F := hE.preimage measurable_snd
  have hLa : L =ᵐ[(jointLaw θ : Measure (PathSpace H))] F := by
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hL] with z hz
    change (gL (fun n => (past 0 z n).2) = true) = (z.2 ∈ E)
    have he : (fun n => (past 0 z n).2) = before z.2 := by
      funext n; simp [past,before]
    simp only [he,Bool.true_eq,↓reduceIte] at hz ⊢
    rw [hz]
    simp
  have hRa : R =ᵐ[(jointLaw θ : Measure (PathSpace H))] F := by
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hR] with z hz
    change (gR (fun n => future 0 z (n+1)) = true) = (z.2 ∈ E)
    have he : (fun n => future 0 z (n+1)) = after z.2 := by
      funext n; simp [future,after]
    simp only [he,Bool.false_eq_true,↓reduceIte] at hz ⊢
    rw [hz]
    simp
  let k (i : H) : ℝ := (futureLaw (jointLaw θ : Measure (PathSpace H)) 0 i).real B
  let c (i : H) : Bool := decide (k i = 1)
  have hfiber (i : H) : ∀ᵐ z ∂(jointLaw θ : Measure (PathSpace H)), z.1 0 = i →
      c i = decide (z.2 ∈ E) := by
    let S : Set (PathSpace H) := state 0 ⁻¹' {i}
    have hS : MeasurableSet S := (measurableSet_singleton i).preimage (by unfold state; fun_prop)
    have hp := full_past_future_factor θ (jointLaw θ : Measure (PathSpace H))
      (same_law_trimming θ).1 0 i (hinit i) A B hA hB
    have hp0 := full_past_future_factor θ (jointLaw θ : Measure (PathSpace H))
      (same_law_trimming θ).1 0 i (hinit i) Set.univ B MeasurableSet.univ hB
    have he1 : (S ∩ L ∩ R : Set (PathSpace H)) =ᵐ[(jointLaw θ : Measure (PathSpace H))] (S ∩ F : Set (PathSpace H)) := by
      filter_upwards [hLa,hRa] with z hzL hzR
      change ((z ∈ S ∧ z ∈ L) ∧ z ∈ R) = (z ∈ S ∧ z ∈ F)
      change (z ∈ L) = (z ∈ F) at hzL
      change (z ∈ R) = (z ∈ F) at hzR
      rw [hzL,hzR]
      simp only [and_self_right]
    have he2 : (S ∩ L : Set (PathSpace H)) =ᵐ[(jointLaw θ : Measure (PathSpace H))] (S ∩ F : Set (PathSpace H)) := by
      filter_upwards [hLa] with z hzL
      change (z ∈ S ∧ z ∈ L) = (z ∈ S ∧ z ∈ F)
      change (z ∈ L) = (z ∈ F) at hzL
      rw [hzL]
    have he3 : (S ∩ R : Set (PathSpace H)) =ᵐ[(jointLaw θ : Measure (PathSpace H))] (S ∩ F : Set (PathSpace H)) := by
      filter_upwards [hRa] with z hzR
      change (z ∈ S ∧ z ∈ R) = (z ∈ S ∧ z ∈ F)
      change (z ∈ R) = (z ∈ F) at hzR
      rw [hzR]
    change (jointLaw θ : Measure (PathSpace H)) (S ∩ L ∩ R) = (jointLaw θ : Measure (PathSpace H)) (S ∩ L)*_ at hp
    rw [measure_congr he1,measure_congr he2] at hp
    simp only [Set.preimage_univ,Set.inter_univ] at hp0
    change (jointLaw θ : Measure (PathSpace H)) (S ∩ R) = (jointLaw θ : Measure (PathSpace H)) S*_ at hp0
    rw [measure_congr he3] at hp0
    have h1 := congrArg ENNReal.toReal hp
    simp only [ENNReal.toReal_mul] at h1
    have h2 := congrArg ENNReal.toReal hp0
    change (jointLaw θ : Measure (PathSpace H)).real (S ∩ F) =
      (jointLaw θ : Measure (PathSpace H)).real (S ∩ F)*k i at h1
    simp only [ENNReal.toReal_mul] at h2
    change (jointLaw θ : Measure (PathSpace H)).real (S ∩ F) =
      (jointLaw θ : Measure (PathSpace H)).real S*k i at h2
    have hs : (jointLaw θ : Measure (PathSpace H)).real S = θ.initial i :=
      state_mass θ (jointLaw θ : Measure (PathSpace H)) (same_law_trimming θ).1 0 i
    rw [hs] at h2
    rw [h2] at h1
    have hk : k i = 0 ∨ k i = 1 := by
      have he : k i = k i*k i :=
        (mul_left_cancel₀ (ne_of_gt (hinit i))) (by simpa [mul_assoc] using h1)
      have hz : k i*(k i-1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (by linarith)
    rcases hk with hk | hk
    · have hm : (jointLaw θ : Measure (PathSpace H)) (S ∩ F) = 0 := by
        have hh : (jointLaw θ : Measure (PathSpace H)).real (S ∩ F) = 0 := by
          rw [h2,hk,mul_zero]
        exact (ENNReal.toReal_eq_zero_iff _).mp hh |>.resolve_right (measure_ne_top _ _)
      have ha : ∀ᵐ z ∂(jointLaw θ : Measure (PathSpace H)), z ∉ S ∩ F := by
        simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hm
      filter_upwards [ha] with z hz hzi
      have hn : z.2 ∉ E := fun he => hz ⟨hzi,he⟩
      simp [c,hk,hn]
    · have hm : (jointLaw θ : Measure (PathSpace H)) (S ∩ F) = (jointLaw θ : Measure (PathSpace H)) S :=
        (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
          (by change (jointLaw θ : Measure (PathSpace H)).real (S ∩ F) = (jointLaw θ : Measure (PathSpace H)).real S; rw [h2,hs,hk,mul_one])
      have hz : (jointLaw θ : Measure (PathSpace H)) (S \ (S ∩ F)) = 0 := by
        rw [measure_sdiff Set.inter_subset_left (hS.inter hF).nullMeasurableSet
          (measure_ne_top _ _),hm,tsub_self]
      have ha : ∀ᵐ z ∂(jointLaw θ : Measure (PathSpace H)), z ∉ S \ (S ∩ F) := by
        simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
      filter_upwards [ha] with z hz hzi
      have he : z.2 ∈ E := by
        by_contra he
        exact hz ⟨hzi,by simpa [F,he]⟩
      simp [c,hk,he]
  refine ⟨c,?_⟩
  have hall := ae_all_iff.mpr hfiber
  filter_upwards [hall] with z hz
  exact hz (z.1 0) rfl

/-- Every finite irreducible stationary presentation has an ergodic one-step
visible law, including periodic hidden chains. -/
theorem actual_output_ergodic (θ : Presentation H)
    (hirr : Matrix.IsIrreducible (θ.matrix false+θ.matrix true)) :
    Ergodic (fun z : ℤ → Bool => fun t => z (1+t)) (visibleLaw θ : Measure (ℤ → Bool)) := by
  classical
  have hinit : ∀ i, 0 < θ.initial i :=
    PositiveRectangleLaw.irreducible_initial_positive θ (by
      intro i j
      obtain ⟨n,_,hn⟩ := (Matrix.isIrreducible_iff_exists_pow_pos
        (fun i j => add_nonneg (θ.matrix_nonneg false i j)
          (θ.matrix_nonneg true i j))).mp hirr i j
      exact ⟨n,hn⟩)
  have htotal : 0 < ∑ i, θ.initial i := by rw [θ.initial_sum]; norm_num
  obtain ⟨i₀,_,_⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => θ.initial_nonneg i)).mp htotal
  change Ergodic (TwelveStateErgodicity.translate 1) (visibleLaw θ : Measure (ℤ → Bool))
  refine Ergodic.of_preimage_eq (translate_preserving θ 1) ?_
  intro E hE hi
  obtain ⟨c,hc⟩ := state_event θ hinit E hE hi
  have hshift : (jointLaw θ : Measure (PathSpace H)).map (shift 1) = jointLaw θ :=
    (same_law_trimming θ).2.2.2.2.2.1 1
  have hm : Measurable (shift (H := H) 1) := by unfold shift; fun_prop
  have hnext : ∀ᵐ z ∂(jointLaw θ : Measure (PathSpace H)), c (z.1 1) = c (z.1 0) := by
    have hh : ∀ᵐ z ∂(jointLaw θ : Measure (PathSpace H)).map (shift 1),
        c (z.1 0) = decide (z.2 ∈ E) := by rw [hshift]; exact hc
    have ha := ae_of_ae_map hm.aemeasurable hh
    filter_upwards [ha,hc] with z h1 h0
    change c (z.1 1) = decide (TwelveStateErgodicity.translate 1 z.2 ∈ E) at h1
    have hi' : TwelveStateErgodicity.translate 1 z.2 ∈ E ↔ z.2 ∈ E := Set.ext_iff.mp hi z.2
    simp only [hi'] at h1
    exact h1.trans h0.symm
  have hedge (i j : H) (hij : 0 < (θ.matrix false+θ.matrix true) i j) : c i = c j := by
    have hx : ∃ x : Bool, 0 < θ.matrix x i j := by
      by_cases h : 0 < θ.matrix false i j
      · exact ⟨false,h⟩
      · refine ⟨true,?_⟩
        change 0 < θ.matrix false i j+θ.matrix true i j at hij
        linarith
    obtain ⟨x,hx⟩ := hx
    let C := MarkedPredictiveQuotient.cylinder 0 1 (Fin.cons i (fun _ => j)) (fun _ => x)
    have hC : (jointLaw θ : Measure (PathSpace H)) C ≠ 0 := by
      have hh := (same_law_trimming θ).1 0 1 (Fin.cons i (fun _ => j)) (fun _ => x)
      have hr : (jointLaw θ : Measure (PathSpace H)).real C = θ.initial i*θ.matrix x i j := by
        simpa [C,pathMass,Fin.prod_univ_succ] using hh
      intro hz
      have : (jointLaw θ : Measure (PathSpace H)).real C = 0 := by simp [Measure.real,hz]
      linarith [mul_pos (hinit i) hx]
    obtain ⟨z,hz,he⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hC
      (hnext.filter_mono (ae_mono Measure.restrict_le_self))
    have h0 : z.1 0 = i := by simpa [C,MarkedPredictiveQuotient.cylinder] using hz.1 0
    have h1 : z.1 1 = j := by simpa [C,MarkedPredictiveQuotient.cylinder] using hz.1 (Fin.last 1)
    rw [h0,h1] at he
    exact he.symm
  letI : Quiver H := Matrix.toQuiver (θ.matrix false+θ.matrix true)
  have hpath {i j : H} (p : Quiver.Path i j) : c i = c j := by
    induction p with
    | nil => rfl
    | cons p e ih => exact ih.trans (hedge _ _ e.down)
  have hconst (i j : H) : c i = c j := by
    obtain ⟨p,_⟩ := hirr.connected i j
    exact hpath p
  have hproj : MeasurePreserving (Prod.snd : PathSpace H → ℤ → Bool)
      (jointLaw θ : Measure (PathSpace H)) (visibleLaw θ : Measure (ℤ → Bool)) := ⟨measurable_snd,rfl⟩
  rw [← hproj.aeconst_preimage hE.nullMeasurableSet]
  apply Filter.eventuallyEmptyOrUniv_iff.mpr
  cases hb : c i₀ with
  | false =>
    right
    filter_upwards [hc] with z hz
    have he := (hconst (z.1 0) i₀).symm.trans hz
    simpa [hb] using he
  | true =>
    left
    filter_upwards [hc] with z hz
    have he := (hconst (z.1 0) i₀).symm.trans hz
    simpa [hb] using he


#print axioms actual_output_ergodic

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
