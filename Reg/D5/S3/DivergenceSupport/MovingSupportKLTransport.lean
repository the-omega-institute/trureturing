import LeanInformationAuditInterface.Contract.Registration
import D5.S3.DivergenceSupport.MovingSupportKLTransport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.DivergenceSupport.MovingSupportKLTransport
open _root_.D5.S3.DivergenceSupport.MovingSupportKLTransport
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Entropy.Forgetting.CapacityMonotone
open _root_.D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
universe u v w o

structure Inputs where
  J : Type u
  I : Type v
  H : Type w
  finiteJ : Fintype J
  finiteI : Fintype I
  d : J → ℝ
  q : J → ℝ
  W : J → H → ℝ
  r : J → I

def signature : Signature where
  Params := Inputs.{u, v, w}
  State p := p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v, w} :=
  realize signature (fun _ p h => @posteriorDefect p.J p.I p.H p.finiteJ p.finiteI
    p.d p.q p.W p.r h) (fun e => nomatch e)

def loss (R : Realization signature.{u, v, w}) {J : Type u} {I : Type v} {H : Type w}
    [Fintype J] [Fintype I] (d q : J → ℝ) (W : J → H → ℝ) (r : J → I) (h : H) : ℝ :=
  R.readout () ⟨J, I, H, inferInstance, inferInstance, d, q, W, r⟩ h

def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def transportLaw (R : Realization signature.{u, v, w}) : Prop :=
  ∀
    {J : Type u} {I : Type v} {Ω : Type o} {H : ℕ → Type w} [Fintype J] [Fintype I]
    [MeasurableSpace Ω] [∀ n, Fintype (H n)]
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSingletonClass (H n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : (n : ℕ) → Ω → H n) (hr : ∀ n, Measurable (record n))
    (d q : J → ℝ) (W : (n : ℕ) → J → H n → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1)
    (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    (hW : ∀ n, (∀ j h, 0 ≤ W n j h) ∧ ∀ j, ∑ h, W n j h = 1)
    (hmass : ∀ n h, μ.real (record n ⁻¹' {h}) = channelOutput (W n) d h)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (g : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun n => loss R d q (W n) r (record n ω)) atTop (𝓝 (g ω))),
    let f := fun n ω => loss R d q (W n) r (record n ω)
    (∀ v : ℝ, 0 ≤ v → ∀ n,
      μ.real {ω | v < if 0 < channelOutput (W n) d (record n ω) then
        Real.log (M / (channelOutput (W n) d (record n ω) /
          channelOutput (W n) q (record n ω))) else 0} ≤ M * Real.exp (-v)) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ n,
      (∫ ω, ({ω | R ≤ f n ω}.indicator (f n)) ω ∂μ) ≤
        M * (R + 1) * Real.exp (-R)) ∧
    UniformIntegrable f 1 μ ∧ Integrable g μ ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ))

theorem transportLaw_actual : transportLaw.{u, v, w, o} actual.{u, v, w} := by
  exact @posterior_defect_l1_of_ae_tendsto.{u, v, o, w}

def limitLaw (R : Realization signature.{u, v, w}) : Prop :=
  ∀
    {J : Type u} {I : Type v} {Ω : Type o} {H : ℕ → Type w} [Fintype J] [Fintype I]
    [MeasurableSpace Ω] [∀ n, Fintype (H n)]
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSingletonClass (H n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : (n : ℕ) → Ω → H n) (hr : ∀ n, Measurable (record n))
    (d q : J → ℝ) (W : (n : ℕ) → J → H n → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1)
    (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    (hW : ∀ n, (∀ j h, 0 ≤ W n j h) ∧ ∀ j, ∑ h, W n j h = 1)
    (hmass : ∀ n h, μ.real (record n ⁻¹' {h}) = channelOutput (W n) d h)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (a b : Ω → J → ℝ) (t : Ω → ℝ)
    (hpath : ∀ᵐ ω ∂μ,
      0 < t ω ∧
      Tendsto (fun n => channelOutput (W n) d (record n ω) /
        channelOutput (W n) q (record n ω)) atTop (𝓝 (t ω)) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (record n ω) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (record n ω) j) atTop (𝓝 (b ω j)))),
    let f := fun n ω => loss R d q (W n) r (record n ω)
    let g := fun ω => klDivergence (a ω) (b ω) -
      klDivergence (pushforward r (a ω)) (pushforward r (b ω))
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
    UniformIntegrable f 1 μ ∧ Integrable g μ ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ))

theorem limitLaw_actual : limitLaw.{u, v, w, o} actual.{u, v, w} := by
  exact @moving_support_posterior_limit.{u, v, o, w}

def iidLaw (R : Realization signature.{u, v, w}) : Prop :=
  ∀
    {J : Type u} {I : Type v} {Z : Type w} [Fintype J] [Fintype I] [Fintype Z]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (d q : J → ℝ) (K : J → PMF Z) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1)
    (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (a b : (J × (ℕ → Z)) → J → ℝ) (t : (J × (ℕ → Z)) → ℝ),
    let μ : Measure (J × (ℕ → Z)) := ∑ j, ENNReal.ofReal (d j) •
      (productLaw (fun _ : ℕ => K j)).map (fun x => (j, x))
    let W := fun n j (h : Fin n → Z) => ∏ k, pmfRealMass (Output := fun _ : ℕ => Z) (i := 0) (K j) (h k)
    let record := fun n (ω : J × (ℕ → Z)) (k : Fin n) => ω.2 k
    let f := fun n ω => loss R d q (W n) r (record n ω)
    let g := fun ω => klDivergence (a ω) (b ω) -
      klDivergence (pushforward r (a ω)) (pushforward r (b ω))
    (∀ᵐ ω ∂μ, 0 < t ω ∧
      Tendsto (fun n => channelOutput (W n) d (record n ω) /
        channelOutput (W n) q (record n ω)) atTop (𝓝 (t ω)) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (record n ω) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (record n ω) j) atTop (𝓝 (b ω j)))) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
    UniformIntegrable f 1 μ ∧ Integrable g μ ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ))

theorem iidLaw_actual : iidLaw actual.{u, v, w} := by
  exact @iid_moving_support_posterior_limit_of_coordinates.{u, v, w}

theorem transportLaw_rejected : ¬ transportLaw.{u, v, w, o} rejected := by
  intro h
  have hh := h (J := PUnit.{u+1}) (I := PUnit.{v+1})
    (H := fun _ => PUnit.{w+1}) (Measure.dirac (PUnit.unit : PUnit.{o+1}))
    (fun _ _ => PUnit.unit) (fun _ => measurable_const)
    (fun _ => 1) (fun _ => 1) (fun _ _ _ => 1) (fun _ => PUnit.unit)
    (by simp) (by simp) (by simp) (by simp [channelOutput])
    (M := 1) (by norm_num) (by simp) (fun _ => 1)
    (Filter.Eventually.of_forall (fun _ => tendsto_const_nhds))
  have ht := hh.2.1 1 (by norm_num) 0
  norm_num [loss, rejected, realize] at ht
  have hx := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  rw [Real.exp_neg] at ht
  have he := (le_div_iff₀ (Real.exp_pos 1)).mp
    (show (1 : ℝ) ≤ 2 / Real.exp 1 by simpa only [div_eq_mul_inv] using ht)
  norm_num at he
  linarith

theorem limitLaw_rejected : ¬ limitLaw.{u, v, w, o} rejected := by
  intro h
  have hh := h (J := PUnit.{u+1}) (I := PUnit.{v+1})
    (H := fun _ => PUnit.{w+1}) (Measure.dirac (PUnit.unit : PUnit.{o+1}))
    (fun _ _ => PUnit.unit) (fun _ => measurable_const)
    (fun _ => 1) (fun _ => 1) (fun _ _ _ => 1) (fun _ => PUnit.unit)
    (by simp) (by simp) (by simp) (by simp [channelOutput])
    (M := 1) (by norm_num) (by simp) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1)
    (by simp only [channelOutput, posterior, Fintype.sum_unique, mul_one, div_one, div_self,
        one_ne_zero, Real.log_one, one_mul, true_and]
        exact Filter.Eventually.of_forall fun _ =>
          ⟨by norm_num, tendsto_const_nhds, fun _ => tendsto_const_nhds,
            fun _ => tendsto_const_nhds⟩)
  have ht := hh.1
  simp only [loss, rejected, realize, klDivergence, pushforward, Fintype.sum_unique,
    one_div_one, Real.log_one, mul_zero, sub_self, ↓reduceIte] at ht
  have hl : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by simpa using ht
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hl
  norm_num at this

theorem iidLaw_rejected : ¬ iidLaw.{u, v, w} rejected := by
  intro h
  let K : PUnit.{u+1} → PMF PUnit.{w+1} := fun _ => PMF.pure PUnit.unit
  let μ : Measure (PUnit.{u+1} × (ℕ → PUnit.{w+1})) :=
    (productLaw (fun _ : ℕ => PMF.pure PUnit.unit)).map (fun x => (PUnit.unit, x))
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ, productLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hh := h (I := PUnit.{v+1}) (fun _ : PUnit.{u+1} => 1) (fun _ => 1) K
    (fun _ => PUnit.unit) (by simp) (by simp)
    (M := 1) (by norm_num) (by simp) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1)
    (by
      simp only [K, pmfRealMass, PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one,
        Finset.prod_const_one, channelOutput, posterior, Fintype.sum_unique,
        mul_one, div_one, div_self, one_ne_zero]
      exact Filter.Eventually.of_forall fun _ =>
        ⟨by norm_num, tendsto_const_nhds, fun _ => tendsto_const_nhds,
          fun _ => tendsto_const_nhds⟩)
  have ht := hh.1
  simp only [loss, rejected, realize, klDivergence, pushforward, Fintype.sum_unique,
    one_div_one, Real.log_one, mul_zero, sub_self, ↓reduceIte,
    ENNReal.ofReal_one, one_smul] at ht
  have hl : ∀ᵐ ω ∂μ, Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := ht
  obtain ⟨ω, hω⟩ := hl.exists
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hω
  norm_num at this

/-- The actual loss distinguishes a positive actual history from an actual null history,
with a zero actual prior coordinate and a strictly positive reference prior. -/
theorem actual_dependence : ObservationalDependence signature actual.{u, v, w} := by
  intro i
  let p : Inputs.{u, v, w} :=
    ⟨ULift.{u} Bool, PUnit.{v+1}, ULift.{w} Bool, inferInstance, inferInstance,
      (fun j => if j.down then 0 else 1), (fun _ => 1/2),
      (fun j h => if j.down then 1/2 else if h.down then 0 else 1),
      (fun _ => PUnit.unit)⟩
  refine ⟨p, ⟨false⟩, ⟨true⟩, ?_⟩
  change posteriorDefect p.d p.q p.W p.r ⟨false⟩ ≠
    posteriorDefect p.d p.q p.W p.r ⟨true⟩
  have hsum (f : ULift.{u} Bool → ℝ) : ∑ j, f j = f ⟨true⟩ + f ⟨false⟩ := by
    rw [← (Equiv.ulift : ULift.{u} Bool ≃ Bool).symm.sum_comp, Fintype.sum_bool]
    rfl
  norm_num [p, posteriorDefect, channelOutput, posterior, klDivergence, pushforward,
    hsum, Real.log_ne_zero]

def transportArena : Arena where
  signature := signature.{u, v, w}
  Law := transportLaw.{u, v, w, o}

def limitArena : Arena where
  signature := signature.{u, v, w}
  Law := limitLaw.{u, v, w, o}

def transportEvidence : Registration transportArena.{u, v, w, o} (type_of% (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.posterior_defect_l1_of_ae_tendsto.{u, v, o, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨transportLaw_actual, rejected, transportLaw_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, transportLaw_rejected⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := actual_dependence

def limitEvidence : Registration limitArena.{u, v, w, o} (type_of% (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.moving_support_posterior_limit.{u, v, o, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨limitLaw_actual, rejected, limitLaw_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, limitLaw_rejected⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := actual_dependence

def iidArena : Arena where
  signature := signature.{u, v, w}
  Law := iidLaw.{u, v, w}

def iidEvidence : Registration iidArena.{u, v, w} (type_of% (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.iid_moving_support_posterior_limit_of_coordinates.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨iidLaw_actual, rejected, iidLaw_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, iidLaw_rejected⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := actual_dependence


def transportRegistration : Contract.Registration
    (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.posterior_defect_l1_of_ae_tendsto)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.DivergenceSupport.MovingSupportKLTransport.posterior_defect_l1_of_ae_tendsto.__information_unit
  realizationName := `Reg.D5.S3.DivergenceSupport.MovingSupportKLTransport.transportEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source transportArena ⟨transportEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p h =>
    @posteriorDefect p.J p.I p.H p.finiteJ p.finiteI p.d p.q p.W p.r h)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


def limitRegistration : Contract.Registration
    (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.moving_support_posterior_limit)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.DivergenceSupport.MovingSupportKLTransport.moving_support_posterior_limit.__information_unit
  realizationName := `Reg.D5.S3.DivergenceSupport.MovingSupportKLTransport.limitEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨limitArena⟩
  objectArena := .source ⟨limitArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source limitArena ⟨limitEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p h =>
    @posteriorDefect p.J p.I p.H p.finiteJ p.finiteI p.d p.q p.W p.r h)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


def iidRegistration : Contract.Registration
    (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.iid_moving_support_posterior_limit_of_coordinates)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.DivergenceSupport.MovingSupportKLTransport.iid_moving_support_posterior_limit_of_coordinates.__information_unit
  realizationName := `Reg.D5.S3.DivergenceSupport.MovingSupportKLTransport.iidEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨iidArena⟩
  objectArena := .source ⟨iidArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source iidArena ⟨iidEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p h =>
    @posteriorDefect p.J p.I p.H p.finiteJ p.finiteI p.d p.q p.W p.r h)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def modelLaw (R : Realization signature.{u,v,w}) : Prop :=
  ∀
    {J : Type u} {I : Type v} {Z : Type w} {S : Type o} [Fintype J] [Nonempty J] [Fintype I] [Fintype Z]
    [Fintype S] [DecidableEq S] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (d q : J → ℝ) (K : J → PMF Z) (r : J → I) (s : J → S)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1)
    (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    (hs : ∀ j k, s j = s k ↔ K j = K k),
    let μ := fun p : J → ℝ => ∑ j, ENNReal.ofReal (p j) •
      (productLaw (fun _ : ℕ => K j)).map (fun x => (j, x))
    let C := fun j c => if s j = c then (1 : ℝ) else 0
    let W := fun n j (h : Fin n → Z) => ∏ k, (K j (h k)).toReal
    let f := fun n (ω : J × (ℕ → Z)) => loss R d q (W n) r (fun k => ω.2 k)
    let a := fun (ω : J × (ℕ → Z)) => posterior C d (s ω.1)
    let b := fun (ω : J × (ℕ → Z)) => posterior C q (s ω.1)
    let g := fun ω => klDivergence (a ω) (b ω) -
      klDivergence (pushforward r (a ω)) (pushforward r (b ω))
    (∃ dec : (ℕ → Z) → S, Measurable dec ∧
      (∀ᵐ ω ∂μ d, dec ω.2 = s ω.1) ∧ (∀ᵐ ω ∂μ q, dec ω.2 = s ω.1)) ∧
    (∀ᵐ ω ∂μ d, 0 < channelOutput C d (s ω.1) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (fun k => ω.2 k) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (fun k => ω.2 k) j) atTop (𝓝 (b ω j)))) ∧
    (∀ᵐ ω ∂μ d, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
    UniformIntegrable f 1 (μ d) ∧ Integrable g (μ d) ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 (μ d)) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ d) atTop (𝓝 (∫ ω, g ω ∂μ d)) ∧
    (∫ ω, g ω ∂μ d) = ∑ c, channelOutput C d c *
      (klDivergence (posterior C d c) (posterior C q c) -
        klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c))) ∧
    (∫ ω, g ω ∂μ d) = klDivergence d (fun j => q j *
      (pushforward (fun j => (r j,s j)) d (r j,s j) /
        pushforward (fun j => (r j,s j)) q (r j,s j))) ∧
    ∀ c, 0 < channelOutput C d c →
      (klDivergence (posterior C d c) (posterior C q c) -
        klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c)) = 0 ↔
        posterior C d c = fun j => posterior C q c j *
          (pushforward r (posterior C d c) (r j) / pushforward r (posterior C q c) (r j)))

theorem modelLaw_actual : modelLaw.{u,v,w,o} actual := by
  exact @iid_moving_support_posterior_limit.{u,v,w,o}
theorem modelLaw_rejected : ¬ modelLaw.{u,v,w,o} rejected := by
  intro h
  let K : PUnit.{u+1} → PMF PUnit.{w+1} := fun _ => PMF.pure PUnit.unit
  let μ : Measure (PUnit.{u+1} × (ℕ → PUnit.{w+1})) :=
    (productLaw (fun _ : ℕ => PMF.pure PUnit.unit)).map (fun x => (PUnit.unit,x))
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ, productLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hh := h (I := PUnit.{v+1}) (S := PUnit.{o+1})
    (fun _ : PUnit.{u+1} => 1) (fun _ => 1) K (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (by simp) (by simp) (by intro j k; simp [K])
  have ht := hh.2.2.1
  simp only [loss, rejected, realize, posterior, channelOutput, Fintype.sum_unique,
    ↓reduceIte, mul_one, div_one, klDivergence, pushforward,
    one_div_one, Real.log_one, mul_zero, sub_self, ENNReal.ofReal_one, one_smul] at ht
  have hl : ∀ᵐ ω ∂μ, Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := ht
  obtain ⟨ω, hω⟩ := hl.exists
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hω
  norm_num at he
def modelArena : Arena where
  signature := signature.{u,v,w}
  Law := modelLaw.{u,v,w,o}
def modelEvidence : Registration modelArena.{u,v,w,o}
    (type_of% (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.iid_moving_support_posterior_limit.{u,v,w,o})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨modelLaw_actual, rejected, modelLaw_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, modelLaw_rejected⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := actual_dependence

def modelRegistration : Contract.Registration
    (@_root_.D5.S3.DivergenceSupport.MovingSupportKLTransport.iid_moving_support_posterior_limit)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.DivergenceSupport.MovingSupportKLTransport.iid_moving_support_posterior_limit.__information_unit
  realizationName := `Reg.D5.S3.DivergenceSupport.MovingSupportKLTransport.modelEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨modelArena⟩
  objectArena := .source ⟨modelArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source modelArena ⟨modelEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p h =>
    @posteriorDefect p.J p.I p.H p.finiteJ p.finiteI p.d p.q p.W p.r h)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.DivergenceSupport.MovingSupportKLTransport
