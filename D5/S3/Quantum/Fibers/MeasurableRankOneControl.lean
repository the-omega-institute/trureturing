/- GID: D5/S3/Quantum/Fibers/MeasurableRankOneControl
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/MeasurableRankOneControl
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary independent measurable controls have normalized actual joint record laws. -/

import D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexOrder Matrix ENNReal ProbabilityTheory

namespace D5.S3.Quantum.Fibers.MeasurableRankOneControl

open MeasureTheory ProbabilityTheory Set
open D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

universe u v
variable {n : Type u}

/-- The whole density domain, with no faithfulness or positive-branch restriction. -/
abbrev Density (n : Type u) [Fintype n] [DecidableEq n] :=
  {X : Matrix n n ℂ // X.PosSemidef ∧ Matrix.trace X = 1}

/-- The common discrete coding of all finite outcome histories. The seed determines
all waits and branch decisions, so retaining it and this word retains the actual record. -/
def code : (P : Protocol n) → Record P → List n
  | .stop, _ => []
  | .wait _ P, h => code P h
  | .read P, h => h.1 :: code (P h.1) h.2

private theorem code_injective (P : Protocol n) : Function.Injective (code P) := by
  induction P with
  | stop => exact fun _ _ _ => Subsingleton.elim _ _
  | wait t P ih => exact ih
  | read P ih =>
    rintro ⟨s,h⟩ ⟨t,k⟩ he
    change s :: code (P s) h = t :: code (P t) k at he
    obtain ⟨hst, hh⟩ := List.cons.inj he
    subst t
    exact congrArg (Sigma.mk s) (ih s hh)

instance wordMeasurableSpace : MeasurableSpace (List n) := ⊤
instance wordDiscreteMeasurableSpace : DiscreteMeasurableSpace (List n) := ⟨fun _ => trivial⟩

variable [Fintype n] [DecidableEq n]

/-- A finite sum of actual unnormalized Lueders masses, pushed into common record codes. -/
def recordMeasure (M : Menu n) (P : Protocol n) (X : Density n) : Measure (List n) :=
  ∑ h : Record P, ENNReal.ofReal (ludersLaw M P X.val h) • Measure.dirac (code P h)

private theorem mass_nonnegative (M : Menu n) (P : Protocol n) (X : Density n)
    (h : Record P) : 0 ≤ ludersLaw M P X.val h := by
  rw [luders_law_eq M P X.val X.property.1]
  exact law_nonnegative M P X.val X.property.1 h

private theorem mass_normalized (M : Menu n) (P : Protocol n) (X : Density n) :
    ∑ h, ludersLaw M P X.val h = 1 := by
  rw [luders_law_eq M P X.val X.property.1, law_mass, X.property.2]
  simp

open Classical in
private theorem recordMeasure_apply (M : Menu n) (P : Protocol n) (X : Density n)
    (A : Set (List n)) :
    recordMeasure M P X A = ENNReal.ofReal
      (∑ h ∈ Finset.univ.filter (fun h => code P h ∈ A), ludersLaw M P X.val h) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg (fun h _ => mass_nonnegative M P X h)]
  simp only [recordMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ (MeasurableSet.of_discrete : MeasurableSet A),
    Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_filter]

instance recordProbability (M : Menu n) (P : Protocol n) (X : Density n) :
    IsProbabilityMeasure (recordMeasure M P X) where
  measure_univ := by rw [recordMeasure_apply]; simp [mass_normalized]

/-- Input-independent control on any probability space. Coordinate measurability for
all densities is exactly the requirement that the actual discrete record laws form kernels.
It imposes no bound on the number of seeds, tree sizes, or nonnegative waits. -/
structure Control (M : Menu n) where
  Seed : Type v
  space : MeasurableSpace Seed
  seedLaw : @Measure Seed space
  probability : @IsProbabilityMeasure Seed space seedLaw
  strategy : Seed → Protocol n
  measurable_mass : letI := space
    ∀ (X : Density n) (w : List n),
      Measurable (fun c => recordMeasure M (strategy c) X {w})

attribute [instance] Control.space Control.probability

/-- The kernel is constructed from the actual record laws, not postulated independently. -/
def recordKernel (M : Menu n) (R : Control.{u, v} M) (X : Density n) :
    Kernel R.Seed (List n) where
  toFun c := recordMeasure M (R.strategy c) X
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have he (c : R.Seed) :=
      Measure.tsum_indicator_apply_singleton (recordMeasure M (R.strategy c) X) A hA
    simp_rw [← he]
    apply Measurable.tsum
    intro w
    by_cases hw : w ∈ A
    · simpa [Set.indicator_of_mem hw] using R.measurable_mass X w
    · simp only [Set.indicator_of_notMem hw]
      exact measurable_const

instance recordMarkov (M : Menu n) (R : Control.{u, v} M) (X : Density n) :
    IsMarkovKernel (recordKernel M R X) where
  isProbabilityMeasure c := recordProbability M (R.strategy c) X

/-- The actual seed and complete finite adaptive record have a jointly defined law. -/
def jointLaw (M : Menu n) (R : Control.{u, v} M) (X : Density n) :
    Measure (R.Seed × List n) := R.seedLaw ⊗ₘ recordKernel M R X

instance jointProbability (M : Menu n) (R : Control.{u, v} M) (X : Density n) :
    IsProbabilityMeasure (jointLaw M R X) := inferInstanceAs
      (IsProbabilityMeasure (R.seedLaw ⊗ₘ recordKernel M R X))

private theorem directed_gap (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    max (a-b) (b-a) = ENNReal.ofReal |a.toReal-b.toReal| := by
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb,
    ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ← ENNReal.ofReal_max]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, abs_eq_max_neg, neg_sub]

private theorem record_tv (M : Menu n) (P : Protocol n) (X Y : Density n) :
    measurableTotalVariation (recordMeasure M P X) (recordMeasure M P Y) =
      ENNReal.ofReal (totalVariation (ludersLaw M P X.val) (ludersLaw M P Y.val)) := by
  classical
  have hm := (mass_normalized M P X).trans (mass_normalized M P Y).symm
  have hg := total_variation_eq_sup_event_gap (ludersLaw M P X.val)
    (ludersLaw M P Y.val) hm
  have ev (Z : Density n) (A : Set (List n)) :
      (recordMeasure M P Z A).toReal =
        ∑ h ∈ Finset.univ.filter (fun h => code P h ∈ A), ludersLaw M P Z.val h := by
    rw [recordMeasure_apply, ENNReal.toReal_ofReal]
    exact Finset.sum_nonneg (fun h _ => mass_nonnegative M P Z h)
  apply le_antisymm
  · refine iSup_le fun A => ?_
    rw [directed_gap _ _ (measure_ne_top _ _) (measure_ne_top _ _), ev, ev]
    exact ENNReal.ofReal_le_ofReal (hg.2 ⟨_, rfl⟩)
  · obtain ⟨A, hA⟩ := hg.1
    let B : Set (List n) := code P '' (A : Set (Record P))
    have hfilter : Finset.univ.filter (fun h => code P h ∈ B) = A := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, B,
        Set.mem_image, Finset.mem_coe]
      exact ⟨fun ⟨k,hk,he⟩ => (code_injective P he) ▸ hk,
        fun hh => ⟨h,hh,rfl⟩⟩
    have hb := le_iSup (fun C : {C : Set (List n) // MeasurableSet C} =>
      max (recordMeasure M P X C.val - recordMeasure M P Y C.val)
        (recordMeasure M P Y C.val - recordMeasure M P X C.val))
      ⟨B, MeasurableSet.of_discrete⟩
    rw [directed_gap _ _ (measure_ne_top _ _) (measure_ne_top _ _), ev, ev,
      hfilter] at hb
    change |(∑ h ∈ A, ludersLaw M P X.val h) -
      ∑ h ∈ A, ludersLaw M P Y.val h| = _ at hA
    rw [hA] at hb
    exact hb

open Classical in
/-- Actual finite records whose common codes lie in a seed-dependent joint event. -/
def sectionEvent (M : Menu n) (R : Control.{u, v} M)
    (A : Set (R.Seed × List n)) (c : R.Seed) : Finset (Record (R.strategy c)) :=
  Finset.univ.filter (fun h => (c, code (R.strategy c) h) ∈ A)

private theorem section_real (M : Menu n) (R : Control.{u, v} M) (X : Density n)
    (A : Set (R.Seed × List n)) (c : R.Seed) :
    (recordKernel M R X c (Prod.mk c ⁻¹' A)).toReal =
      ∑ h ∈ sectionEvent M R A c, ludersLaw M (R.strategy c) X.val h := by
  rw [show recordKernel M R X c = recordMeasure M (R.strategy c) X from rfl,
    recordMeasure_apply, ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun h _ => mass_nonnegative M (R.strategy c) X h))]
  rfl

private theorem section_integrable (M : Menu n) (R : Control.{u, v} M)
    (X : Density n) (A : Set (R.Seed × List n)) (hA : MeasurableSet A) :
    Integrable (fun c => ∑ h ∈ sectionEvent M R A c,
      ludersLaw M (R.strategy c) X.val h) R.seedLaw := by
  simp_rw [← section_real]
  apply (integrable_const (1 : ℝ)).mono'
    (Kernel.measurable_kernel_prodMk_left hA).ennreal_toReal.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro c
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hle : recordKernel M R X c (Prod.mk c ⁻¹' A) ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  exact (ENNReal.toReal_mono (by norm_num) hle).trans_eq (by simp)

private theorem joint_event_real (M : Menu n) (R : Control.{u, v} M)
    (X : Density n) (A : Set (R.Seed × List n)) (hA : MeasurableSet A) :
    (jointLaw M R X A).toReal =
      ∫ c, (∑ h ∈ sectionEvent M R A c, ludersLaw M (R.strategy c) X.val h) ∂(R.seedLaw) := by
  rw [jointLaw, Measure.compProd_apply hA,
    ← integral_toReal (Kernel.measurable_kernel_prodMk_left hA).aemeasurable
      (Filter.Eventually.of_forall (fun c => measure_lt_top _ _))]
  exact integral_congr_ae (Filter.Eventually.of_forall (section_real M R X A))

private theorem joint_bound
    (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t + u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (R : Control.{u, v} (unitaryMenu U hzero hadd hunitary)) (X Y : Density n) :
    let M := unitaryMenu U hzero hadd hunitary
    measurableTotalVariation (jointLaw M R X) (jointLaw M R Y) ≤
      ENNReal.ofReal (firstSup M X.val Y.val) := by
  dsimp only
  let M := unitaryMenu U hzero hadd hunitary
  refine iSup_le fun A => ?_
  rw [directed_gap _ _ (measure_ne_top _ _) (measure_ne_top _ _),
    joint_event_real M R X A.val A.property, joint_event_real M R Y A.val A.property]
  exact ENNReal.ofReal_le_ofReal (arbitrary_random_control_event_bound
    U hzero hadd hunitary X.val Y.val X.property.1 Y.property.1 X.property.2 Y.property.2
    R.seedLaw R.strategy (sectionEvent M R A.val)
    (section_integrable M R X A.val A.property) (section_integrable M R Y A.val A.property))

/-- Deterministic control is an admissible one-point probability control at any seed universe. -/
def fixedControl (M : Menu n) (P : Protocol n) : Control.{u, v} M where
  Seed := ULift.{v} Unit
  space := ⊤
  seedLaw := Measure.dirac ⟨()⟩
  probability := inferInstance
  strategy _ := P
  measurable_mass _ _ := measurable_const

private theorem fixed_record_le_joint (M : Menu n) (P : Protocol n) (X Y : Density n) :
    ENNReal.ofReal (totalVariation (ludersLaw M P X.val) (ludersLaw M P Y.val)) ≤
      measurableTotalVariation (jointLaw M (fixedControl.{u, v} M P) X)
        (jointLaw M (fixedControl.{u, v} M P) Y) := by
  rw [← record_tv]
  refine iSup_le fun A => ?_
  have hb := le_iSup (fun B : {B : Set ((fixedControl.{u, v} M P).Seed × List n) //
      MeasurableSet B} =>
    max (jointLaw M (fixedControl M P) X B.val - jointLaw M (fixedControl M P) Y B.val)
      (jointLaw M (fixedControl M P) Y B.val - jointLaw M (fixedControl M P) X B.val))
    ⟨Set.univ ×ˢ A.val, MeasurableSet.univ.prod A.property⟩
  have ev (Z : Density n) :
      jointLaw M (fixedControl.{u, v} M P) Z (Set.univ ×ˢ A.val) =
        recordMeasure M P Z A.val := by
    rw [jointLaw, Measure.compProd_apply_prod MeasurableSet.univ A.property]
    change (∫⁻ _ in Set.univ, recordMeasure M P Z A.val
      ∂(fixedControl.{u, v} M P).seedLaw) = _
    simp
  rw [ev, ev] at hb
  exact hb

/-- Arbitrary independent probability seeds, actual finite feedback, and complete records
have exactly the deterministic first-read supremum. All measurability hypotheses occur in
Control and concern existence of the actual probability law, never its contraction. -/
theorem arbitrary_protocol_tv_supremum
    (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t + u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1) (X Y : Density n) :
    let M := unitaryMenu U hzero hadd hunitary
    (⨆ R : Control.{u, v} M, measurableTotalVariation (jointLaw M R X) (jointLaw M R Y)) =
      ENNReal.ofReal (firstSup M X.val Y.val) := by
  dsimp only
  let M := unitaryMenu U hzero hadd hunitary
  let T := ⨆ R : Control.{u, v} M,
    measurableTotalVariation (jointLaw M R X) (jointLaw M R Y)
  have upper : T ≤ ENNReal.ofReal (firstSup M X.val Y.val) :=
    iSup_le (fun R => joint_bound U hzero hadd hunitary R X Y)
  have hfinite : T ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top upper
  have lower : firstSup M X.val Y.val ≤ T.toReal := by
    change sSup (Set.range (fun t : NNReal => totalVariation
      (fun s => ((U t * X.val * (U t)ᴴ) s s).re)
      (fun s => ((U t * Y.val * (U t)ᴴ) s s).re))) ≤ T.toReal
    rw [← actual_protocol_tv_supremum U hzero hadd hunitary X.val Y.val
      X.property.1 Y.property.1 (X.property.2.trans Y.property.2.symm)]
    apply csSup_le
    · exact ⟨_, ⟨Protocol.stop, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
      exact (fixed_record_le_joint M P X Y).trans
        (le_iSup (fun R : Control.{u, v} M =>
          measurableTotalVariation (jointLaw M R X) (jointLaw M R Y)) (fixedControl M P))
  exact le_antisymm upper ((ENNReal.ofReal_le_ofReal lower).trans_eq
    (ENNReal.ofReal_toReal hfinite))

#print axioms arbitrary_protocol_tv_supremum

end D5.S3.Quantum.Fibers.MeasurableRankOneControl
