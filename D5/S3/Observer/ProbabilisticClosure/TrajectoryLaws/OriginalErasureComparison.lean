/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalErasureComparison
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalErasureComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both complete opposite-half-line erasure risks compare with actual current-class error. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ScreenedBinaryPredictor
import D5.S3.ConceptDynamics.Prediction.ConditionalExpectationOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming
open OriginalFutureCylinders OriginalFutureScreening ScreenedBinaryPredictor

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- The complete visible past strictly before the erased site. -/
def before (z : ℤ → Bool) : ℕ → Bool := fun n => z (-(n+1 : ℕ))

/-- The complete visible future strictly after the erased site. -/
def after (z : ℤ → Bool) : ℕ → Bool := fun n => z (n+1)

/-- Original chronological finite word immediately before the cut zero. -/
def leftWord (r : ℕ) (z : ℤ → Bool) : Fin r → Bool := fun i => z (-(r : ℤ)+i)

/-- Original chronological finite word from coordinate one through r. -/
def rightWord (r : ℕ) (z : ℤ → Bool) : Fin r → Bool := fun i => z (i+1)

def exterior (z : ℤ → Bool) := (before z,after z)
def leftObservation (r : ℕ) (z : ℤ → Bool) := (leftWord r z,after z)
def rightObservation (r : ℕ) (z : ℤ → Bool) := (before z,rightWord r z)

def erasedBit (z : ℤ → Bool) : ℝ := if z 0 then 1 else 0

/-- The actual conditional probability of the center bit, total on every observed value. -/
def bitPredictor {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : Ω → Bool) (o : Ω → E) : E → ℝ :=
  fun e => (condDistrib x o μ e).real {true}

theorem bitPredictor_condExp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : Ω → Bool) (o : Ω → E)
    (hx : Measurable x) (ho : Measurable o) :
    (fun ω => bitPredictor μ x o (o ω)) =ᵐ[μ]
      μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap o inferInstance] := by
  have hp := condDistrib_ae_eq_condExp (μ := μ) ho hx (measurableSet_singleton true)
  have hi : (x ⁻¹' {true}).indicator (fun _ => (1 : ℝ)) =
      (fun ω => if x ω then (1 : ℝ) else 0) := by
    ext ω
    cases heq : x ω <;> simp [heq]
  rw [hi] at hp
  exact hp

/-- Bounded versions under the selected actual visible pushforward. -/
def fullMean (θ : Presentation H) : (ℤ → Bool) → ℝ :=
  bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) exterior ∘ exterior

def leftMean (θ : Presentation H) (r : ℕ) : (ℤ → Bool) → ℝ :=
  bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (leftObservation r) ∘ leftObservation r

def rightMean (θ : Presentation H) (r : ℕ) : (ℤ → Bool) → ℝ :=
  bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (rightObservation r) ∘ rightObservation r

def leftRisk (θ : Presentation H) (r : ℕ) : ℝ :=
  ∫ z, (fullMean θ z-leftMean θ r z)^2 ∂(visibleLaw θ : Measure _)

def rightRisk (θ : Presentation H) (r : ℕ) : ℝ :=
  ∫ z, (fullMean θ z-rightMean θ r z)^2 ∂(visibleLaw θ : Measure _)

/-- A nonnegative tail in extended reals, with no finiteness premise. -/
def erasureTail (θ : Presentation H) (R : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, (ENNReal.ofReal (leftRisk θ (R+n)) + ENNReal.ofReal (rightRisk θ (R+n)))

theorem visible_conditional_pullback (θ : Presentation H)
    {E : Type*} [MeasurableSpace E] (o : (ℤ → Bool) → E) (ho : Measurable o) :
    (fun z : PathSpace H => bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) o (o z.2)) =ᵐ[(jointLaw θ : Measure (PathSpace H))]
      (jointLaw θ : Measure (PathSpace H))[fun z => erasedBit z.2 |
        MeasurableSpace.comap (o ∘ Prod.snd) inferInstance] := by
  have hx : Measurable (fun z : ℤ → Bool => z 0) := measurable_pi_apply 0
  have hk := condDistrib_map (ν := (jointLaw θ : Measure (PathSpace H))) (f := (Prod.snd : PathSpace H → ℤ → Bool))
    ho.aemeasurable hx.aemeasurable measurable_snd.aemeasurable
  have hka : ∀ᵐ z : PathSpace H ∂(jointLaw θ : Measure (PathSpace H)),
      condDistrib (fun z : ℤ → Bool => z 0) o (visibleLaw θ : Measure _) (o z.2) =
        condDistrib ((fun z : ℤ → Bool => z 0) ∘ Prod.snd) (o ∘ Prod.snd)
          (jointLaw θ : Measure (PathSpace H)) (o z.2) :=
    ae_of_ae_map (ho.comp measurable_snd).aemeasurable hk
  have hp := bitPredictor_condExp (jointLaw θ : Measure (PathSpace H))
    ((fun z : ℤ → Bool => z 0) ∘ Prod.snd) (o ∘ Prod.snd)
    (hx.comp measurable_snd) (ho.comp measurable_snd)
  filter_upwards [hka,hp] with z hz hpz
  exact (congrArg (fun ν : Measure Bool => ν.real {true}) hz).trans hpz


/-- The actual current-class error on the same original joint law. -/
def classError (θ : Presentation H) (r : ℕ) : ℝ≥0∞ :=
  ⨅ m : (Fin r → Bool) → FutureClass (PositiveSupportPresentation.trim θ).matrix,
    (jointLaw θ : Measure (PathSpace H)) {z | originalClass θ 0 z ≠ m (leftWord r z.2)}

def cellMass {Ω Q W : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace W] (μ : Measure Ω) (q : Ω → Q) (w : Ω → W) (b : W) (a : Q) :
    ℝ≥0∞ := μ ((q ⁻¹' {a}) ∩ (w ⁻¹' {b}))

private theorem maximizers_nonempty {Q : Type*} [Fintype Q] [Nonempty Q]
    (f : Q → ℝ≥0∞) :
    (Finset.univ.filter (fun a => ∀ j, f j ≤ f a)).Nonempty := by
  obtain ⟨a,ha,hm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  exact ⟨a,Finset.mem_filter.mpr ⟨ha,fun j => hm j (Finset.mem_univ _)⟩⟩

/-- A fixed finite ordering selects the first maximizing class for every word.
The rule is total even on a zero-mass word. -/
def mapClassifier {Ω Q W : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace W] [Fintype Q] [Nonempty Q]
    (μ : Measure Ω) (q : Ω → Q) (w : Ω → W) : W → Q := fun b =>
  letI : LinearOrder Q := LinearOrder.lift' (Fintype.equivFin Q) (Fintype.equivFin Q).injective
  (Finset.univ.filter (fun a => ∀ j, cellMass μ q w b j ≤ cellMass μ q w b a)).min'
    (maximizers_nonempty (cellMass μ q w b))

theorem mapClassifier_max {Ω Q W : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace W] [Fintype Q] [Nonempty Q]
    (μ : Measure Ω) (q : Ω → Q) (w : Ω → W) (b : W) (a : Q) :
    cellMass μ q w b a ≤ cellMass μ q w b (mapClassifier μ q w b) := by
  letI : LinearOrder Q := LinearOrder.lift' (Fintype.equivFin Q) (Fintype.equivFin Q).injective
  exact (Finset.mem_filter.mp (Finset.min'_mem _ (maximizers_nonempty (cellMass μ q w b)))).2 a

theorem error_mass_formula {Ω Q W : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace W] [MeasurableSingletonClass Q] [MeasurableSingletonClass W]
    [Fintype W] [Finite Q] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → Q) (w : Ω → W) (hq : Measurable q) (hw : Measurable w) (m : W → Q) :
    μ {ω | q ω ≠ m (w ω)} = 1 - ∑ b, cellMass μ q w b (m b) := by
  have hm : Measurable m := measurable_of_finite m
  have hs : MeasurableSet {ω | q ω = m (w ω)} := measurableSet_eq_fun hq (hm.comp hw)
  have hp := sum_measure_preimage_singleton (μ := μ.restrict {ω | q ω = m (w ω)})
    Finset.univ (f := w) (fun b _ => (measurableSet_singleton b).preimage hw)
  have he' : ∑ b, cellMass μ q w b (m b) =
      ∑ b, (μ.restrict {ω | q ω = m (w ω)}) (w ⁻¹' {b}) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Measure.restrict_apply ((measurableSet_singleton b).preimage hw)]
    unfold cellMass
    congr 1
    ext ω
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq]
    constructor
    · rintro ⟨hqa,hwb⟩
      exact ⟨hwb,by rw [hwb]; exact hqa⟩
    · rintro ⟨hwb,hqa⟩
      exact ⟨by simpa only [hwb] using hqa,hwb⟩
  have hsMass : μ {ω | q ω = m (w ω)} = ∑ b, cellMass μ q w b (m b) := by
    rw [he']
    simpa only [Finset.coe_univ,Set.preimage_univ,Measure.restrict_apply_univ] using hp.symm
  have hc : {ω | q ω ≠ m (w ω)} = {ω | q ω = m (w ω)}ᶜ := rfl
  rw [hc,measure_compl hs (measure_ne_top _ _),measure_univ,hsMass]

private theorem mapClassifier_optimal {Ω Q W : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace W] [MeasurableSingletonClass Q] [MeasurableSingletonClass W]
    [Fintype Q] [Nonempty Q] [Fintype W] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → Q) (w : Ω → W) (hq : Measurable q) (hw : Measurable w) (m : W → Q) :
    μ {ω | q ω ≠ mapClassifier μ q w (w ω)} ≤ μ {ω | q ω ≠ m (w ω)} := by
  rw [error_mass_formula μ q w hq hw,error_mass_formula μ q w hq hw]
  exact tsub_le_tsub_left (Finset.sum_le_sum fun b _ => mapClassifier_max μ q w b (m b)) 1

theorem current_map_error (θ : Presentation H) (r : ℕ) :
    ∃ m : (Fin r → Bool) → FutureClass (PositiveSupportPresentation.trim θ).matrix,
      (jointLaw θ : Measure (PathSpace H)) {z | originalClass θ 0 z ≠ m (leftWord r z.2)} = classError θ r ∧
      ∀ w a, cellMass (jointLaw θ : Measure (PathSpace H)) (originalClass θ 0)
        (leftWord r ∘ Prod.snd) w a ≤
          cellMass (jointLaw θ : Measure (PathSpace H)) (originalClass θ 0) (leftWord r ∘ Prod.snd) w (m w) := by
  letI := Fintype.ofFinite (FutureClass (PositiveSupportPresentation.trim θ).matrix)
  letI : Nonempty (FutureClass (PositiveSupportPresentation.trim θ).matrix) :=
    ⟨classOf _ (Classical.choice (positiveNonempty θ))⟩
  let m := mapClassifier (jointLaw θ : Measure (PathSpace H)) (originalClass θ 0) (leftWord r ∘ Prod.snd)
  refine ⟨m,le_antisymm ?_ (iInf_le _ m),mapClassifier_max _ _ _⟩
  apply le_iInf
  intro m'
  exact mapClassifier_optimal _ _ _ (originalClass_measurable θ 0) (by unfold leftWord; fun_prop) m'

private theorem translated_class_error (θ : Presentation H) (r : ℕ) :
    (⨅ m : (Fin r → Bool) → FutureClass (PositiveSupportPresentation.trim θ).matrix,
      (jointLaw θ : Measure (PathSpace H)) {z | originalClass θ (r+1) z ≠ m (rightWord r z.2)}) =
        classError θ r := by
  apply iInf_congr
  intro m
  have hstat := (same_law_trimming θ).2.2.2.2.2.1 (r+1)
  have hm : MeasurableSet {z : PathSpace H | originalClass θ 0 z ≠ m (leftWord r z.2)} :=
    (measurableSet_eq_fun (originalClass_measurable θ 0)
      ((measurable_of_finite m).comp (by unfold leftWord; fun_prop))).compl
  have hs : Measurable (shift (H := H) (r+1)) := by unfold shift; fun_prop
  have he := congrArg (fun μ : Measure (PathSpace H) =>
    μ {z | originalClass θ 0 z ≠ m (leftWord r z.2)}) hstat
  rw [Measure.map_apply hs hm] at he
  convert he using 1
  congr 1
  ext z
  have hq : originalClass θ 0 (shift (r+1) z) = originalClass θ (r+1) z := by
    simp [originalClass,state,shift]
  have hw : leftWord r (shift (r+1) z).2 = rightWord r z.2 := by
    funext i
    dsimp [leftWord,rightWord,shift]
    apply congrArg z.2
    push_cast
    omega
  simp only [Set.mem_preimage,Set.mem_setOf_eq,hq,hw]


private theorem norm_square_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f h : Ω → ℝ) (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    ‖hf.toLp f-hh.toLp h‖^2 = ∫ ω, (f ω-h ω)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hh.toLp h),hf.coeFn_toLp,hh.coeFn_toLp]
    with ω hsub hfω hhω
  simp only [hsub,Pi.sub_apply,hfω,hhω,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Conditional contraction and projection optimality bound innovation energy
by the squared error of any measurable predictor based on the smaller field. -/
private theorem projection_square_bound {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (a : Ω → A) (b : Ω → B) (ha : Measurable a) (hb : Measurable b)
    (hle : MeasurableSpace.comap b inferInstance ≤ MeasurableSpace.comap a inferInstance)
    (h : B → ℝ) (hh : Measurable h) (hf : MemLp f 2 μ) (hhLp : MemLp (h ∘ b) 2 μ) :
    (∫ ω, (μ[f | MeasurableSpace.comap a inferInstance] ω-
      μ[f | MeasurableSpace.comap b inferInstance] ω)^2 ∂μ) ≤
        ∫ ω, (f ω-h (b ω))^2 ∂μ := by
  let p := μ[f | MeasurableSpace.comap b inferInstance]
  have hp : MemLp p 2 μ := hf.condExp (by norm_num)
  have hpa : μ[p | MeasurableSpace.comap a inferInstance] =ᵐ[μ] p :=
    condExp_of_aestronglyMeasurable' ha.comap_le
      (stronglyMeasurable_condExp.aestronglyMeasurable.mono hle)
      (hp.integrable (by norm_num))
  have he : μ[f-p | MeasurableSpace.comap a inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap a inferInstance]-p :=
    (condExp_sub (hf.integrable (by norm_num)) (hp.integrable (by norm_num)) _).trans
      (Filter.EventuallyEq.rfl.sub hpa)
  have hc : (∫ ω, (μ[f | MeasurableSpace.comap a inferInstance] ω-p ω)^2 ∂μ) ≤
      ∫ ω, (f ω-p ω)^2 ∂μ := by
    have hc := integral_norm_condExp_rpow_le (μ := μ) (m := MeasurableSpace.comap a inferInstance)
      (p := (2 : ℝ)) (by norm_num)
      (by simpa only [Real.rpow_two] using
        ((memLp_two_iff_integrable_sq_norm (hf.sub hp).aestronglyMeasurable).mp (hf.sub hp)))
    simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs] at hc
    convert hc using 1
    · apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
      rfl
  have hmin := D5.S3.ConceptDynamics.Prediction.ConditionalExpectationOptimality.conditional_expectation_minimizes_mean_square_error μ b f h hb hf hh hhLp
  have hproj : (↑(condExpL2 ℝ ℝ hb.comap_le (hf.toLp f)) : Lp ℝ 2 μ) = hp.toLp p := by
    apply Lp.ext
    exact (hf.condExpL2_ae_eq_condExp hb.comap_le).trans hp.coeFn_toLp.symm
  rw [hproj,norm_square_integral μ f p hf hp,
    norm_square_integral μ f (h ∘ b) hf hhLp] at hmin
  exact hc.trans hmin




private theorem screened_comparison
    {Ω Q U V A B : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Finite Q] [MeasurableSpace U]
    [StandardBorelSpace U] [Nonempty U] [MeasurableSpace V]
    [StandardBorelSpace V] [Nonempty V] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace.CountableOrCountablyGenerated Q V]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → Q) (u : Ω → U) (v : Ω → V) (x : Ω → Bool)
    (a : Ω → A) (b : Ω → B) (vb : B → V)
    (hq : Measurable q) (hu : Measurable u) (hv : Measurable v) (hx : Measurable x)
    (ha : Measurable a) (hb : Measurable b) (hvb : Measurable vb)
    (hevb : v = vb ∘ b)
    (hI : CondIndepFun (MeasurableSpace.comap q inferInstance) hq.comap_le
      u (fun ω => (v ω,x ω)) μ)
    (hac : MeasurableSpace.comap a inferInstance ≤
      MeasurableSpace.comap (fun ω => (q ω,(u ω,v ω))) inferInstance)
    (hba : MeasurableSpace.comap b inferInstance ≤ MeasurableSpace.comap a inferInstance) :
    ∃ g : Q × V → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      μ[fun ω => if x ω then (1 : ℝ) else 0 |
        MeasurableSpace.comap (fun ω => (q ω,(u ω,v ω))) inferInstance] =ᵐ[μ]
        (fun ω => g (q ω,v ω)) ∧
      ∀ h : B → Q, Measurable h →
        ENNReal.ofReal (∫ ω,
          (μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap a inferInstance] ω-
            μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap b inferInstance] ω)^2 ∂μ)
          ≤ μ {ω | q ω ≠ h (b ω)} := by
  obtain ⟨g,hg,hgb,hgc⟩ := screened_binary_predictor μ q u v x hq hu hv hx hI
  refine ⟨g,hg,hgb,hgc,?_⟩
  intro h hh
  let f : Ω → ℝ := fun ω => g (q ω,v ω)
  let k : B → ℝ := fun z => g (h z,vb z)
  have hf : Measurable f := hg.comp (hq.prodMk hv)
  have hk : Measurable k := hg.comp (hh.prodMk hvb)
  have hfLp : MemLp f 2 μ := memLp_of_bounded (Filter.Eventually.of_forall fun ω => hgb _) hf.aestronglyMeasurable 2
  have hkLp : MemLp (k ∘ b) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall fun ω => hgb _) (hk.comp hb).aestronglyMeasurable 2
  have hc : Measurable (fun ω => (q ω,(u ω,v ω))) := hq.prodMk (hu.prodMk hv)
  have hta : μ[f | MeasurableSpace.comap a inferInstance] =ᵐ[μ]
      μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap a inferInstance] :=
    (condExp_congr_ae hgc.symm).trans (condExp_condExp_of_le hac hc.comap_le)
  have htb : μ[f | MeasurableSpace.comap b inferInstance] =ᵐ[μ]
      μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap b inferInstance] :=
    (condExp_congr_ae hgc.symm).trans (condExp_condExp_of_le (hba.trans hac) hc.comap_le)
  have hp := projection_square_bound μ f a b ha hb hba k hk hfLp hkLp
  have hreq : (∫ ω, (μ[f | MeasurableSpace.comap a inferInstance] ω-
      μ[f | MeasurableSpace.comap b inferInstance] ω)^2 ∂μ) =
      ∫ ω, (μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap a inferInstance] ω-
        μ[fun ω => if x ω then (1 : ℝ) else 0 | MeasurableSpace.comap b inferInstance] ω)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hta,htb] with ω hωa hωb
    rw [hωa,hωb]
  rw [hreq] at hp
  have hs : MeasurableSet {ω | q ω ≠ h (b ω)} :=
    (measurableSet_eq_fun hq (hh.comp hb)).compl
  have hdom : ∀ ω, (f ω-k (b ω))^2 ≤
      ({ω | q ω ≠ h (b ω)}.indicator (fun _ => (1 : ℝ))) ω := by
    intro ω
    have hbnd := hgb (q ω,v ω)
    have hbnd' := hgb (h (b ω),vb (b ω))
    by_cases he : q ω = h (b ω)
    · have hvω : v ω = vb (b ω) := congrFun hevb ω
      simp [f,k,he,hvω]
    · rw [Set.indicator_of_mem he]
      dsimp [f,k]
      nlinarith [sq_nonneg (g (q ω,v ω)+g (h (b ω),vb (b ω))),
        mul_nonneg hbnd.1 hbnd'.1]
  have hi : Integrable (fun ω => (f ω-k (b ω))^2) μ :=
    (memLp_two_iff_integrable_sq (hfLp.sub hkLp).aestronglyMeasurable).mp (hfLp.sub hkLp)
  have hbound := integral_mono hi ((integrable_const (1 : ℝ)).indicator hs) hdom
  rw [integral_indicator_const 1 hs,smul_eq_mul,mul_one] at hbound
  exact (ENNReal.ofReal_le_ofReal (hp.trans hbound)).trans_eq
    (ENNReal.ofReal_toReal (measure_ne_top μ _))


private def fromBefore (r : ℕ) (p : ℕ → Bool) : Fin r → Bool :=
  fun i => p (r-1-i.val)

private theorem left_word_factor (r : ℕ) (z : ℤ → Bool) :
    leftWord r z = fromBefore r (before z) := by
  funext i
  dsimp [leftWord,fromBefore,before]
  apply congrArg z
  have hi := i.isLt
  push_cast
  omega

private def rightFromPast (r : ℕ) (p : ℕ → H × Bool) :
    ((ℕ → Bool) × (Fin r → Bool)) × Bool :=
  ((fun n => (p (r+n+1)).2,fun i => (p (r-1-i.val)).2),(p r).2)

private theorem right_past_factor (r : ℕ) (z : PathSpace H) :
    rightFromPast r (past (r+1) z) = (rightObservation r z.2,z.2 0) := by
  apply Prod.ext
  · apply Prod.ext
    · funext n
      dsimp [rightFromPast,past,rightObservation,before]
      apply congrArg z.2
      push_cast
      omega
    · funext i
      dsimp [rightFromPast,past,rightObservation,rightWord]
      apply congrArg z.2
      have hi := i.isLt
      push_cast
      omega
  · dsimp [rightFromPast,past]
    apply congrArg z.2
    push_cast
    omega

private def recoverRight (r : ℕ)
    (c : (ℕ → Bool) × ((ℕ → Bool) × (Fin r → Bool))) :
    (ℕ → Bool) × (ℕ → Bool) :=
  (c.2.1,fun n => if hn : n < r then c.2.2 ⟨n,hn⟩ else c.1 (n-r))

private theorem right_exterior_factor (r : ℕ) (z : PathSpace H) :
    exterior z.2 = recoverRight r (future (r+1) z,rightObservation r z.2) := by
  apply Prod.ext
  · rfl
  funext n
  dsimp [exterior,after,recoverRight,rightObservation]
  split_ifs with hn
  · rfl
  · dsimp [future]
    apply congrArg z.2
    push_cast
    omega

theorem bitPredictor_measurable {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : Ω → Bool) (o : Ω → E) :
    Measurable (bitPredictor μ x o) :=
  (Kernel.measurable_coe _ (measurableSet_singleton true)).ennreal_toReal

private theorem risk_pullback (θ : Presentation H) (o : (ℤ → Bool) → (ℕ → Bool) × (ℕ → Bool))
    (ho : Measurable o) (p : (ℤ → Bool) → ℝ) (hp : Measurable p) :
    (∫ z, (bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) o (o z)-p z)^2
      ∂(visibleLaw θ : Measure _)) =
    ∫ z : PathSpace H, (bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) o (o z.2)-p z.2)^2
      ∂(jointLaw θ : Measure _) := by
  exact integral_map measurable_snd.aemeasurable
    (((bitPredictor_measurable _ _ _).comp ho).sub hp |>.pow_const 2).aestronglyMeasurable

set_option maxHeartbeats 2000000 in
/-- Both full-opposite-half-line comparisons under the selected original law,
with total bounded class predictors, actual MAP error and an extended-real tail. -/
theorem full_half_line_erasure_comparison (θ : Presentation H) :
    (∀ r : ℕ,
      (∃ m : (Fin r → Bool) → FutureClass (PositiveSupportPresentation.trim θ).matrix,
        (jointLaw θ : Measure _) {z | originalClass θ 0 z ≠ m (leftWord r z.2)} = classError θ r) ∧
      (⨅ m : (Fin r → Bool) → FutureClass (PositiveSupportPresentation.trim θ).matrix,
        (jointLaw θ : Measure _) {z | originalClass θ (r+1) z ≠ m (rightWord r z.2)}) = classError θ r ∧
      ENNReal.ofReal (leftRisk θ r) ≤ classError θ r ∧
      ENNReal.ofReal (rightRisk θ r) ≤ classError θ r ∧
      leftRisk θ r ≤ (classError θ r).toReal ∧
      rightRisk θ r ≤ (classError θ r).toReal) ∧
    (∀ R : ℕ, erasureTail θ R ≤ 2 * ∑' n : ℕ, classError θ (R+n)) ∧
    (∀ o : (ℤ → Bool) → (ℕ → Bool) × (ℕ → Bool), Measurable o →
      (fun z : PathSpace H => bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) o (o z.2)) =ᵐ[(jointLaw θ : Measure (PathSpace H))]
        (jointLaw θ : Measure _)[fun z => erasedBit z.2 | MeasurableSpace.comap (o ∘ Prod.snd) inferInstance]) := by
  have hL : ∀ r : ℕ, ENNReal.ofReal (leftRisk θ r) ≤ classError θ r := by
    intro r
    let μ : Measure (PathSpace H) := jointLaw θ
    let q := originalClass θ 0
    let a : PathSpace H → (ℕ → Bool) × (ℕ → Bool) := exterior ∘ Prod.snd
    let b : PathSpace H → (Fin r → Bool) × (ℕ → Bool) := leftObservation r ∘ Prod.snd
    have hq := originalClass_measurable θ 0
    have ha : Measurable a := by
      exact (show Measurable exterior by unfold exterior before after; fun_prop).comp measurable_snd
    have hb : Measurable b := by
      exact (show Measurable (leftObservation r) by unfold leftObservation leftWord after; fun_prop).comp measurable_snd
    have hI : CondIndepFun (MeasurableSpace.comap q inferInstance) hq.comap_le
        (before ∘ Prod.snd) (fun z : PathSpace H => (after z.2,z.2 0)) μ := by
      have ht := ((same_law_future_screening θ).2 0).2.1.symm.comp
        (φ := fun p : ℕ → H × Bool => fun n => (p n).2)
        (ψ := fun f : ℕ → Bool => (fun n => f (n+1),f 0))
        (by fun_prop) (by fun_prop)
      convert ht using 1
      · funext z n
        dsimp [before,past,Function.comp_def]
        apply congrArg z.2
        push_cast
        omega
      · funext z
        apply Prod.ext
        · funext n
          dsimp [after,future,Function.comp_def]
          apply congrArg z.2
          push_cast
          omega
        · simp [future,Function.comp_def]
    have hac : MeasurableSpace.comap a inferInstance ≤
        MeasurableSpace.comap (fun z : PathSpace H => (q z,(before z.2,after z.2))) inferInstance :=
      MeasurableSpace.comap_le_comap_of_eq_comp Prod.snd measurable_snd rfl
    have hba : MeasurableSpace.comap b inferInstance ≤ MeasurableSpace.comap a inferInstance := by
      apply MeasurableSpace.comap_le_comap_of_eq_comp
        (fun e : (ℕ → Bool) × (ℕ → Bool) => (fromBefore r e.1,e.2)) (by unfold fromBefore; fun_prop)
      funext z
      exact Prod.ext (left_word_factor r z.2) rfl
    obtain ⟨g,hg,hgb,hgc,hcomp⟩ := screened_comparison μ q (before ∘ Prod.snd)
      (after ∘ Prod.snd) (fun z => z.2 0) a b Prod.snd hq
      (by unfold before; fun_prop) (by unfold after; fun_prop) (by fun_prop)
      ha hb measurable_snd rfl hI hac hba
    have hcondA := visible_conditional_pullback θ exterior (by unfold exterior before after; fun_prop)
    have hcondB := visible_conditional_pullback θ (leftObservation r) (by unfold leftObservation leftWord after; fun_prop)
    have he : leftRisk θ r = ∫ z : PathSpace H,
        (μ[fun z => erasedBit z.2 | MeasurableSpace.comap a inferInstance] z-
          μ[fun z => erasedBit z.2 | MeasurableSpace.comap b inferInstance] z)^2 ∂μ := by
      refine (risk_pullback θ exterior (by unfold exterior before after; fun_prop)
        (bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (leftObservation r) ∘ leftObservation r)
        ((bitPredictor_measurable _ _ _).comp (by unfold leftObservation leftWord after; fun_prop))).trans ?_
      apply integral_congr_ae
      filter_upwards [hcondA,hcondB] with z hzA hzB
      simp only [Function.comp_apply]
      rw [hzA,hzB]
    rw [he]
    apply le_iInf
    intro m
    exact hcomp (fun e => m e.1) ((measurable_of_finite m).comp measurable_fst)
  have hR : ∀ r : ℕ, ENNReal.ofReal (rightRisk θ r) ≤ classError θ r := by
    intro r
    let μ : Measure (PathSpace H) := jointLaw θ
    let q := originalClass θ (r+1)
    let a : PathSpace H → (ℕ → Bool) × (ℕ → Bool) := exterior ∘ Prod.snd
    let b : PathSpace H → (ℕ → Bool) × (Fin r → Bool) := rightObservation r ∘ Prod.snd
    have hq := originalClass_measurable θ (r+1)
    have ha : Measurable a := by
      exact (show Measurable exterior by unfold exterior before after; fun_prop).comp measurable_snd
    have hb : Measurable b := by
      exact (show Measurable (rightObservation r) by unfold rightObservation rightWord before; fun_prop).comp measurable_snd
    have hI : CondIndepFun (MeasurableSpace.comap q inferInstance) hq.comap_le
        (future (r+1)) (fun z : PathSpace H => (b z,z.2 0)) μ := by
      have ht := ((same_law_future_screening θ).2 (r+1)).2.1.comp
        (φ := id) (ψ := rightFromPast (H := H) r) measurable_id (by unfold rightFromPast; fun_prop)
      have he : rightFromPast r ∘ past (r+1) = (fun z : PathSpace H => (b z,z.2 0)) :=
        funext (right_past_factor r)
      rwa [he,Function.id_comp] at ht
    have hac : MeasurableSpace.comap a inferInstance ≤
        MeasurableSpace.comap (fun z : PathSpace H => (q z,(future (r+1) z,b z))) inferInstance := by
      apply MeasurableSpace.comap_le_comap_of_eq_comp
        (fun c => recoverRight r c.2) (by
          have hm : Measurable (recoverRight r) := by
            unfold recoverRight
            apply Measurable.prodMk (by fun_prop)
            apply measurable_pi_lambda
            intro n
            split_ifs <;> fun_prop
          exact hm.comp measurable_snd)
      funext z
      exact right_exterior_factor r z
    have hba : MeasurableSpace.comap b inferInstance ≤ MeasurableSpace.comap a inferInstance := by
      apply MeasurableSpace.comap_le_comap_of_eq_comp
        (fun e : (ℕ → Bool) × (ℕ → Bool) => (e.1,fun i : Fin r => e.2 i.val)) (by fun_prop)
      rfl
    obtain ⟨g,hg,hgb,hgc,hcomp⟩ := screened_comparison μ q (future (r+1))
      b (fun z => z.2 0) a b id hq
      (by unfold future; fun_prop) hb (by fun_prop) ha hb measurable_id rfl hI hac hba
    have hcondA := visible_conditional_pullback θ exterior (by unfold exterior before after; fun_prop)
    have hcondB := visible_conditional_pullback θ (rightObservation r) (by unfold rightObservation rightWord before; fun_prop)
    have he : rightRisk θ r = ∫ z : PathSpace H,
        (μ[fun z => erasedBit z.2 | MeasurableSpace.comap a inferInstance] z-
          μ[fun z => erasedBit z.2 | MeasurableSpace.comap b inferInstance] z)^2 ∂μ := by
      refine (risk_pullback θ exterior (by unfold exterior before after; fun_prop)
        (bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (rightObservation r) ∘ rightObservation r)
        ((bitPredictor_measurable _ _ _).comp (by unfold rightObservation rightWord before; fun_prop))).trans ?_
      apply integral_congr_ae
      filter_upwards [hcondA,hcondB] with z hzA hzB
      simp only [Function.comp_apply]
      rw [hzA,hzB]
    rw [he,← translated_class_error θ r]
    apply le_iInf
    intro m
    exact hcomp (fun e => m e.2) ((measurable_of_finite m).comp measurable_snd)
  have hfinite : ∀ r : ℕ, classError θ r ≠ ⊤ := by
    intro r
    obtain ⟨m,hm,_⟩ := current_map_error θ r
    rw [← hm]
    exact measure_ne_top _ _
  refine ⟨fun r => ⟨?_,translated_class_error θ r,hL r,hR r,
    (ENNReal.ofReal_le_iff_le_toReal (hfinite r)).mp (hL r),
    (ENNReal.ofReal_le_iff_le_toReal (hfinite r)).mp (hR r)⟩,?_,?_⟩
  · obtain ⟨m,hm,_⟩ := current_map_error θ r
    exact ⟨m,hm⟩
  · intro R
    calc
      erasureTail θ R ≤ ∑' n : ℕ, (classError θ (R+n)+classError θ (R+n)) :=
        ENNReal.tsum_le_tsum fun n => add_le_add (hL _) (hR _)
      _ = 2 * ∑' n : ℕ, classError θ (R+n) := by
        rw [ENNReal.tsum_add]
        exact (two_mul _).symm
  · exact fun o ho => visible_conditional_pullback θ o ho

#print axioms full_half_line_erasure_comparison

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison
