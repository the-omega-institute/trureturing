/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invariant events and positive stationary components of the actual output law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFullErasure
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function Set Filter
open scoped BigOperators ENNReal Classical symmDiff
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalFutureCylinders
open OriginalFutureScreening OriginalErasureComparison TwelveStatePresentation
open IndependentSeedPosterior TwelveStateFullErasure

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateErgodicity

private def translate (a : ℤ) (z : ℤ → Bool) : ℤ → Bool := fun t => z (a+t)

private theorem translate_preserving (a : ℤ) : MeasurePreserving (translate a)
    (visible : Measure (ℤ → Bool)) (visible : Measure (ℤ → Bool)) :=
  ⟨by unfold translate; fun_prop,(same_law_trimming parameter).2.2.2.2.2.2.1 a⟩

private theorem all_invariant (E : Set (ℤ → Bool)) (hE : translate 1 ⁻¹' E = E) (a : ℤ) :
    translate a ⁻¹' E = E := by
  induction a using Int.induction_on with
  | zero =>
    ext z
    change translate 0 z ∈ E ↔ z ∈ E
    have ht : translate 0 z = z := by
      funext t
      exact congrArg z (zero_add t)
    rw [ht]
  | succ a ih =>
    ext z
    have he : translate (a+1) z = translate 1 (translate a z) := by
      funext t; simp only [translate]; congr 1; omega
    change translate (a+1) z ∈ E ↔ z ∈ E
    rw [he]
    exact (Set.ext_iff.mp hE _).trans (Set.ext_iff.mp ih z)
  | pred a ih =>
    ext z
    have he : translate 1 (translate (-(a:ℤ)-1) z) = translate (-(a:ℤ)) z := by
      funext t; simp only [translate]; congr 1; omega
    change translate (-(a:ℤ)-1) z ∈ E ↔ z ∈ E
    have hm : translate 1 (translate (-(a:ℤ)-1) z) ∈ E ↔ translate (-(a:ℤ)-1) z ∈ E :=
      Set.ext_iff.mp hE _
    exact hm.symm.trans ((Iff.of_eq (congrArg (fun v => v ∈ E) he)).trans (Set.ext_iff.mp ih z))

private theorem invariant_decoder (E : Set (ℤ → Bool)) (hE : MeasurableSet E)
    (hi : translate 1 ⁻¹' E = E) (left : Bool) :
    ∃ g : (ℕ → Bool) → Bool, Measurable g ∧
      ∀ᵐ z ∂(visible : Measure (ℤ → Bool)),
        g (if left then before z else after z) = decide (z ∈ E) := by
  classical
  have hcover : ∃ D : Set (Set (ℤ → Bool)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℤ => Bool) ∧ (visible : Measure _) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ},Set.countable_singleton _,?_,by simp⟩
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    exact univ_mem_measurableCylinders _
  have happ (n : ℕ) : ∃ C ∈ measurableCylinders (fun _ : ℤ => Bool),
      (visible : Measure _) (C ∆ E) < (2⁻¹ : ℝ≥0∞)^n :=
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
      f n (if left then before z else after z) = decide (translate (a n) z ∈ C n) := by
    have he := measurableCylinders.eq_cylinder (hC n)
    have hb (i : I n) : Int.natAbs i.val ≤ N n := Finset.le_sup i.property
    have hsel : (fun i : I n => (if left then before z else after z) (pick n i)) =
        (I n).restrict (translate (a n) z) := by
      funext i
      have h := hb i
      have hab := Int.natAbs_eq i.val
      cases left <;> dsimp [pick,a,before,after,translate,Finset.restrict] <;> congr 1 <;> omega
    simp only [f,hsel]
    congr 1
    conv_rhs => rw [he]
    rfl
  let bad (n : ℕ) := translate (a n) ⁻¹' (C n ∆ E)
  have hsum : (∑' n, (visible : Measure _) (bad n)) ≠ ⊤ := by
    apply ne_of_lt
    apply (ENNReal.tsum_le_tsum (fun n => ?_)).trans_lt
      (show (∑' n : ℕ, (2⁻¹ : ℝ≥0∞)^n) < ⊤ by simp)
    rw [(translate_preserving _).measure_preimage
      ((MeasurableSet.of_mem_measurableCylinders (hC n)).symmDiff hE).nullMeasurableSet]
    exact (hc n).le
  obtain ⟨g,hg,hcorrect⟩ := measurable_eventual_decoder f hf
  refine ⟨g,hg,?_⟩
  filter_upwards [ae_eventually_notMem hsum] with z hz
  apply hcorrect
  apply hz.mono
  intro n hn
  rw [hread]
  have hi' : translate (a n) z ∈ E ↔ z ∈ E := Set.ext_iff.mp (all_invariant E hi (a n)) z
  dsimp only [bad,Set.mem_preimage] at hn
  have hn' : ¬ (translate (a n) z ∈ C n ∆ E) := hn
  simp only [Set.mem_symmDiff,hi'] at hn'
  have heq : (translate (a n) z ∈ C n) ↔ z ∈ E := by tauto
  simp only [heq]

private theorem state_event (E : Set (ℤ → Bool)) (hE : MeasurableSet E)
    (hi : translate 1 ⁻¹' E = E) :
    ∃ c : Hidden → Bool, ∀ᵐ z ∂(joint : Measure Process),
      c (z.1 0) = decide (z.2 ∈ E) := by
  classical
  obtain ⟨gL,hgL,hL⟩ := invariant_decoder E hE hi true
  obtain ⟨gR,hgR,hR⟩ := invariant_decoder E hE hi false
  let A : Set (ℕ → Hidden × Bool) := {v | gL (fun n => (v n).2) = true}
  let B : Set (ℕ → Bool) := {v | gR (fun n => v (n+1)) = true}
  let L : Set Process := past 0 ⁻¹' A
  let R : Set Process := future 0 ⁻¹' B
  let F : Set Process := Prod.snd ⁻¹' E
  have hA : MeasurableSet A := (measurableSet_singleton true).preimage (hgL.comp (by fun_prop))
  have hB : MeasurableSet B := (measurableSet_singleton true).preimage (hgR.comp (by fun_prop))
  have hF : MeasurableSet F := hE.preimage measurable_snd
  have hLa : L =ᵐ[(joint : Measure Process)] F := by
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hL] with z hz
    change (gL (fun n => (past 0 z n).2) = true) = (z.2 ∈ E)
    have he : (fun n => (past 0 z n).2) = before z.2 := by
      funext n; simp [past,before]
    simp only [he,Bool.true_eq,↓reduceIte] at hz ⊢
    rw [hz]
    simp
  have hRa : R =ᵐ[(joint : Measure Process)] F := by
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hR] with z hz
    change (gR (fun n => future 0 z (n+1)) = true) = (z.2 ∈ E)
    have he : (fun n => future 0 z (n+1)) = after z.2 := by
      funext n; simp [future,after]
    simp only [he,Bool.false_eq_true,↓reduceIte] at hz ⊢
    rw [hz]
    simp
  let k (i : Hidden) : ℝ := (futureLaw (joint : Measure Process) 0 i).real B
  let c (i : Hidden) : Bool := decide (k i = 1)
  have hfiber (i : Hidden) : ∀ᵐ z ∂(joint : Measure Process), z.1 0 = i →
      c i = decide (z.2 ∈ E) := by
    let S : Set Process := state 0 ⁻¹' {i}
    have hS : MeasurableSet S := (measurableSet_singleton i).preimage (by unfold state; fun_prop)
    have hp := full_past_future_factor parameter (joint : Measure Process)
      (same_law_trimming parameter).1 0 i (mass_pos i) A B hA hB
    have hp0 := full_past_future_factor parameter (joint : Measure Process)
      (same_law_trimming parameter).1 0 i (mass_pos i) Set.univ B MeasurableSet.univ hB
    have he1 : (S ∩ L ∩ R : Set Process) =ᵐ[(joint : Measure Process)] (S ∩ F : Set Process) := by
      filter_upwards [hLa,hRa] with z hzL hzR
      change ((z ∈ S ∧ z ∈ L) ∧ z ∈ R) = (z ∈ S ∧ z ∈ F)
      change (z ∈ L) = (z ∈ F) at hzL
      change (z ∈ R) = (z ∈ F) at hzR
      rw [hzL,hzR]
      simp only [and_self_right]
    have he2 : (S ∩ L : Set Process) =ᵐ[(joint : Measure Process)] (S ∩ F : Set Process) := by
      filter_upwards [hLa] with z hzL
      change (z ∈ S ∧ z ∈ L) = (z ∈ S ∧ z ∈ F)
      change (z ∈ L) = (z ∈ F) at hzL
      rw [hzL]
    have he3 : (S ∩ R : Set Process) =ᵐ[(joint : Measure Process)] (S ∩ F : Set Process) := by
      filter_upwards [hRa] with z hzR
      change (z ∈ S ∧ z ∈ R) = (z ∈ S ∧ z ∈ F)
      change (z ∈ R) = (z ∈ F) at hzR
      rw [hzR]
    change (joint : Measure Process) (S ∩ L ∩ R) = (joint : Measure Process) (S ∩ L)*_ at hp
    rw [measure_congr he1,measure_congr he2] at hp
    simp only [Set.preimage_univ,Set.inter_univ] at hp0
    change (joint : Measure Process) (S ∩ R) = (joint : Measure Process) S*_ at hp0
    rw [measure_congr he3] at hp0
    have h1 := congrArg ENNReal.toReal hp
    simp only [ENNReal.toReal_mul] at h1
    have h2 := congrArg ENNReal.toReal hp0
    change (joint : Measure Process).real (S ∩ F) =
      (joint : Measure Process).real (S ∩ F)*k i at h1
    simp only [ENNReal.toReal_mul] at h2
    change (joint : Measure Process).real (S ∩ F) =
      (joint : Measure Process).real S*k i at h2
    have hs : (joint : Measure Process).real S = mass i :=
      state_mass parameter (joint : Measure Process) (same_law_trimming parameter).1 0 i
    rw [hs] at h2
    rw [h2] at h1
    have hk : k i = 0 ∨ k i = 1 := by
      have he : k i = k i*k i :=
        (mul_left_cancel₀ (ne_of_gt (mass_pos i))) (by simpa [mul_assoc] using h1)
      have hz : k i*(k i-1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (by linarith)
    rcases hk with hk | hk
    · have hm : (joint : Measure Process) (S ∩ F) = 0 := by
        have hh : (joint : Measure Process).real (S ∩ F) = 0 := by
          rw [h2,hk,mul_zero]
        exact (ENNReal.toReal_eq_zero_iff _).mp hh |>.resolve_right (measure_ne_top _ _)
      have ha : ∀ᵐ z ∂(joint : Measure Process), z ∉ S ∩ F := by
        simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hm
      filter_upwards [ha] with z hz hzi
      have hn : z.2 ∉ E := fun he => hz ⟨hzi,he⟩
      simp [c,hk,hn]
    · have hm : (joint : Measure Process) (S ∩ F) = (joint : Measure Process) S :=
        (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
          (by change (joint : Measure Process).real (S ∩ F) = (joint : Measure Process).real S; rw [h2,hs,hk,mul_one])
      have hz : (joint : Measure Process) (S \ (S ∩ F)) = 0 := by
        rw [measure_sdiff Set.inter_subset_left (hS.inter hF).nullMeasurableSet
          (measure_ne_top _ _),hm,tsub_self]
      have ha : ∀ᵐ z ∂(joint : Measure Process), z ∉ S \ (S ∩ F) := by
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

/-- The actual twelve-state output law is ergodic on the original integer-bit shift.
The proof uses invariant half-line versions, the actual Markov factorization and
positive paths of the original hidden chain. -/
theorem actual_output_ergodic :
    Ergodic (fun z : ℤ → Bool => fun t => z (1+t)) (visible : Measure (ℤ → Bool)) := by
  classical
  change Ergodic (translate 1) (visible : Measure (ℤ → Bool))
  refine Ergodic.of_preimage_eq (translate_preserving 1) ?_
  intro E hE hi
  obtain ⟨c,hc⟩ := state_event E hE hi
  have hshift : (joint : Measure Process).map (shift 1) = joint :=
    (same_law_trimming parameter).2.2.2.2.2.1 1
  have hm : Measurable (shift (H := Hidden) 1) := by unfold shift; fun_prop
  have hnext : ∀ᵐ z ∂(joint : Measure Process), c (z.1 1) = c (z.1 0) := by
    have hh : ∀ᵐ z ∂(joint : Measure Process).map (shift 1),
        c (z.1 0) = decide (z.2 ∈ E) := by rw [hshift]; exact hc
    have ha := ae_of_ae_map hm.aemeasurable hh
    filter_upwards [ha,hc] with z h1 h0
    change c (z.1 1) = decide (translate 1 z.2 ∈ E) at h1
    have hi' : translate 1 z.2 ∈ E ↔ z.2 ∈ E := Set.ext_iff.mp hi z.2
    simp only [hi'] at h1
    exact h1.trans h0.symm
  have hedge (i j : Hidden) (hij : 0 < hiddenTransition i j) : c i = c j := by
    have hx : ∃ x : Bool, 0 < marked x i j := by
      by_cases h : 0 < marked false i j
      · exact ⟨false,h⟩
      · refine ⟨true,?_⟩
        change 0 < marked false i j+marked true i j at hij
        linarith
    obtain ⟨x,hx⟩ := hx
    let C := MarkedPredictiveQuotient.cylinder 0 1 (Fin.cons i (fun _ => j)) (fun _ => x)
    have hC : (joint : Measure Process) C ≠ 0 := by
      have hh := (same_law_trimming parameter).1 0 1 (Fin.cons i (fun _ => j)) (fun _ => x)
      have hr : (joint : Measure Process).real C = mass i*marked x i j := by
        simpa [C,pathMass,Fin.prod_univ_succ,parameter,joint] using hh
      intro hz
      have : (joint : Measure Process).real C = 0 := by simp [Measure.real,hz]
      linarith [mul_pos (mass_pos i) hx]
    obtain ⟨z,hz,he⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hC
      (hnext.filter_mono (ae_mono Measure.restrict_le_self))
    have h0 : z.1 0 = i := by simpa [C,MarkedPredictiveQuotient.cylinder] using hz.1 0
    have h1 : z.1 1 = j := by simpa [C,MarkedPredictiveQuotient.cylinder] using hz.1 (Fin.last 1)
    rw [h0,h1] at he
    exact he.symm
  letI : Quiver Hidden := Matrix.toQuiver hiddenTransition
  have hpath {i j : Hidden} (p : Quiver.Path i j) : c i = c j := by
    induction p with
    | nil => rfl
    | cons p e ih => exact ih.trans (hedge _ _ e.down)
  have hconst (i j : Hidden) : c i = c j := by
    obtain ⟨p,_⟩ := actual_hidden_primitivity.1.isIrreducible.connected i j
    exact hpath p
  have hproj : MeasurePreserving (Prod.snd : Process → ℤ → Bool)
      (joint : Measure Process) (visible : Measure (ℤ → Bool)) := ⟨measurable_snd,rfl⟩
  rw [← hproj.aeconst_preimage hE.nullMeasurableSet]
  apply Filter.eventuallyEmptyOrUniv_iff.mpr
  cases hb : c (false,0) with
  | false =>
    right
    filter_upwards [hc] with z hz
    have he := (hconst (z.1 0) (false,0)).symm.trans hz
    simpa [hb] using he
  | true =>
    left
    filter_upwards [hc] with z hz
    have he := (hconst (z.1 0) (false,0)).symm.trans hz
    simpa [hb] using he

#print axioms actual_output_ergodic

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateErgodicity
