import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
open _root_.D5.S3.Analytic.Interpolation.UniformCoefficientBudget
open LeanInformationAudit MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper

private theorem dirac_law {g : ℝ} (hg : g ∈ Icc 0 1) :
    AtomicLaw 0 1 (1/2) 1 (Measure.dirac g) g := by
  classical
  refine ⟨inferInstance, by norm_num, {g}, ?_, by simp, by simp, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      have hxg : x = g := by simpa using hx
      subst x
      have hmem := Measure.support_mem_ae (μ := Measure.dirac g)
      simpa using hmem
    · exact Measure.support_subset_of_isClosed (by simpa using (isClosed_singleton : IsClosed ({g} : Set ℝ))) (by simp)
  · intro x hx
    have hxg : x = g := by simpa using hx
    subst x
    exact ⟨hg, le_rfl⟩

abbrev curveSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Measure ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def curveActual : Realization curveSignature :=
  realize curveSignature (fun _ μ t => measureCurve μ t) (fun e => nomatch e)

def curveRejected : Realization curveSignature :=
  realize curveSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem curveDependence : ObservationalDependence curveSignature curveActual := by
  intro i
  refine ⟨Measure.dirac 1, 0, 1, ?_⟩
  change measureCurve (Measure.dirac 1) 0 ≠ measureCurve (Measure.dirac 1) 1
  have hn : (1 : ℝ) ≠ Real.exp (-1) :=
    ne_of_gt (Real.exp_lt_one_iff.mpr (by norm_num))
  simpa [measureCurve] using hn

def representationArena : Arena where
  signature := curveSignature
  Law R := ∀ {Elo Ehi η : ℝ} {d : ℕ} {μ : Measure ℝ} {g : ℝ}
    (h : AtomicLaw Elo Ehi η d μ g),
    g ∈ Icc Elo Ehi ∧ ∃ w : ℝ →₀ ℝ,
      (∀ x, 0 ≤ w x) ∧ w.sum (fun _ a => a) = 1 ∧
      (∀ x ∈ w.support, x ∈ Icc g Ehi) ∧ η ≤ w g ∧ w.support.card ≤ d ∧
      μ = ∑ x ∈ w.support, ENNReal.ofReal (w x) • Measure.dirac x ∧
      ∀ t, R.readout () μ t = atomicLaplace w t

private theorem representation_rejected : ¬ representationArena.Law curveRejected := by
  intro h
  obtain ⟨_, w, _, htotal, _, _, _, _, hcurve⟩ := h (dirac_law (g := 0) (by norm_num))
  have hh := hcurve 0
  simp [curveRejected, realize, atomicLaplace] at hh
  linarith

def representationEvidence : Registration representationArena (representationArena.Law curveActual) where
  actual := curveActual
  bridge := Iff.rfl
  variation := ⟨atomic_law_representation, curveRejected, representation_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    representationArena.Law curveActual curveRejected representation_rejected
  dependence := curveDependence

abbrev estimatorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ T : ℝ, (Icc 0 T → ℝ) → ℝ)
    (fun p => Icc 0 p.1 → ℝ) (fun _ => ℝ)

def estimatorActual : Realization estimatorSignature :=
  realize estimatorSignature (fun _ p Y => p.2 Y) (fun e => nomatch e)

def estimatorRejected : Realization estimatorSignature :=
  realize estimatorSignature (fun _ _ _ => 100) (fun e => nomatch e)

private theorem estimatorDependence : ObservationalDependence estimatorSignature estimatorActual := by
  intro i
  refine ⟨⟨1, fun Y => Y ⟨0, by norm_num⟩⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [estimatorActual, realize]

def estimatorArena : Arena where
  signature := estimatorSignature
  Law R := ∀ (Elo E η T ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : Elo < E) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 ≤ d) (hT : 0 < T) (hε : 0 < ε),
    ∃ G : (Icc 0 T → ℝ) → ℝ, ∀ (μ : Measure ℝ) (g : ℝ),
      AtomicLaw Elo E η d μ g → ∀ Y : Icc 0 T → ℝ,
      (∀ t : Icc 0 T, |Y t - measureCurve μ t| ≤ ε) →
      |R.readout () ⟨T, G⟩ Y - g| ≤ (1024 * E / η ^ 2) * rateWindow d ε (E * T)

private theorem rate_all_one (ε : ℝ) : rateAll 1 ε = ε := by
  unfold rateAll
  rw [Set.Icc_self, Set.image_singleton, csSup_singleton]
  norm_num

private theorem rate_window_one (ε : ℝ) (hε : ε ≤ 1) : rateWindow 1 ε 1 = ε := by
  unfold rateWindow
  rw [Set.Icc_self, Set.image_singleton, csSup_singleton]
  norm_num [min_eq_right hε]

private theorem estimator_rejected : ¬ estimatorArena.Law estimatorRejected := by
  intro h
  obtain ⟨G, hG⟩ := h 0 1 (1/2) 1 (1/32768) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hh := hG (Measure.dirac 0) 0 (dirac_law (by norm_num)) (fun _ => 1)
    (by intro t; norm_num [measureCurve])
  norm_num only [estimatorRejected, realize, sub_zero, mul_one] at hh
  rw [rate_window_one _ (by norm_num)] at hh
  norm_num at hh

def estimatorEvidence : Registration estimatorArena (estimatorArena.Law estimatorActual) where
  actual := estimatorActual
  bridge := Iff.rfl
  variation := ⟨exists_window_estimator, estimatorRejected, estimator_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    estimatorArena.Law estimatorActual estimatorRejected estimator_rejected
  dependence := estimatorDependence

private theorem ambiguous_lower (D : Set ℝ) (hD : D ⊆ Ici 0) :
    ENNReal.ofReal (1/2 : ℝ) ≤ minimaxRisk 0 1 (1/2) 1 D 1 := by
  classical
  apply le_iInf
  intro G
  let Y : D → ℝ := fun _ => 1
  have hY0 : ∀ t : D, |Y t - measureCurve (Measure.dirac 0) t| ≤ 1 := by
    intro t
    simp [Y, measureCurve]
  have hY1 : ∀ t : D, |Y t - measureCurve (Measure.dirac 1) t| ≤ 1 := by
    intro t
    have hexp : Real.exp (-t.val) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have ht : 0 ≤ t.val := hD t.property
      exact neg_nonpos.mpr ht)
    have hpos := Real.exp_pos (-t.val)
    simp only [Y, measureCurve, integral_dirac, mul_one]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h0 : ENNReal.ofReal |G Y| ≤
      ⨆ μ : Measure ℝ, ⨆ g : ℝ, ⨆ (_ : AtomicLaw 0 1 (1/2) 1 μ g),
        ⨆ Z : D → ℝ, ⨆ (_ : ∀ t : D, |Z t - measureCurve μ t| ≤ 1),
          ENNReal.ofReal |G Z - g| := by
    apply le_iSup_of_le (Measure.dirac 0)
    apply le_iSup_of_le (0 : ℝ)
    apply le_iSup_of_le (dirac_law (g := 0) (by norm_num))
    apply le_iSup_of_le Y
    exact le_iSup_of_le hY0 (by simp)
  have h1 : ENNReal.ofReal |G Y - 1| ≤
      ⨆ μ : Measure ℝ, ⨆ g : ℝ, ⨆ (_ : AtomicLaw 0 1 (1/2) 1 μ g),
        ⨆ Z : D → ℝ, ⨆ (_ : ∀ t : D, |Z t - measureCurve μ t| ≤ 1),
          ENNReal.ofReal |G Z - g| := by
    apply le_iSup_of_le (Measure.dirac 1)
    apply le_iSup_of_le (1 : ℝ)
    apply le_iSup_of_le (dirac_law (g := 1) (by norm_num))
    apply le_iSup_of_le Y
    exact le_iSup_of_le hY1 le_rfl
  by_cases hg : (1/2 : ℝ) ≤ |G Y|
  · exact (ENNReal.ofReal_le_ofReal hg).trans h0
  · have htri := abs_sub_le (0 : ℝ) (G Y) 1
    have hg1 : (1/2 : ℝ) ≤ |G Y - 1| := by
      simp only [zero_sub, abs_neg] at htri
      norm_num at htri
      linarith
    exact (ENNReal.ofReal_le_ofReal hg1).trans h1

abbrev allSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℕ)
    (fun _ => ℝ) (fun _ => ℝ≥0∞)

abbrev windowSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℕ)
    (fun _ => ℝ) (fun _ => ℝ≥0∞)

def allActual : Realization allSignature :=
  realize allSignature (fun _ p ε => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 (Ici 0) ε)
    (fun e => nomatch e)

def windowActual : Realization windowSignature :=
  realize windowSignature (fun _ p ε => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2.2
    (Icc 0 p.2.2.2.1) ε) (fun e => nomatch e)

def allRejected : Realization allSignature :=
  realize allSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

def windowRejected : Realization windowSignature :=
  realize windowSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem allDependence : ObservationalDependence allSignature allActual := by
  intro i
  refine ⟨⟨0, 1, 1/2, 1⟩, (1/32768), 1, ?_⟩
  change minimaxRisk 0 1 (1/2) 1 (Ici 0) (1/32768) ≠ minimaxRisk 0 1 (1/2) 1 (Ici 0) 1
  have hu := minimax_all_upper 0 1 (1/2) (1/32768) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hl := ambiguous_lower (Ici 0) (fun _ h => h)
  rw [rate_all_one] at hu
  norm_num at hu
  intro heq
  rw [heq] at hu
  have hh := hl.trans hu
  norm_num at hh

private theorem windowDependence : ObservationalDependence windowSignature windowActual := by
  intro i
  refine ⟨⟨0, 1, 1/2, 1, 1⟩, (1/32768), 1, ?_⟩
  change minimaxRisk 0 1 (1/2) 1 (Icc 0 1) (1/32768) ≠ minimaxRisk 0 1 (1/2) 1 (Icc 0 1) 1
  have hu := minimax_window_upper 0 1 (1/2) 1 (1/32768) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hl := ambiguous_lower (Icc 0 1) (fun _ h => h.1)
  norm_num only [mul_one] at hu
  rw [rate_window_one _ (by norm_num)] at hu
  norm_num at hu
  intro heq
  rw [heq] at hu
  have hh := hl.trans hu
  norm_num at hh

def allArena : Arena where
  signature := allSignature
  Law R := ∀ (Elo E η ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : Elo < E) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 ≤ d) (hε : 0 < ε),
    R.readout () ⟨Elo, E, η, d⟩ ε ≤ ENNReal.ofReal ((1024 * E / η ^ 2) * rateAll d ε)

private theorem all_rejected : ¬ allArena.Law allRejected := by
  intro h
  have hh := h 0 1 (1/2) (1/32768) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal _ at hh
  exact (not_le_of_gt ENNReal.ofReal_lt_top) hh

def allEvidence : Registration allArena (allArena.Law allActual) where
  actual := allActual
  bridge := Iff.rfl
  variation := ⟨minimax_all_upper, allRejected, all_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    allArena.Law allActual allRejected all_rejected
  dependence := allDependence

def windowArena : Arena where
  signature := windowSignature
  Law R := ∀ (Elo E η T ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : Elo < E) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 ≤ d) (hT : 0 < T) (hε : 0 < ε),
    R.readout () ⟨Elo, E, η, T, d⟩ ε ≤
      ENNReal.ofReal ((1024 * E / η ^ 2) * rateWindow d ε (E * T))

private theorem window_rejected : ¬ windowArena.Law windowRejected := by
  intro h
  have hh := h 0 1 (1/2) 1 (1/32768) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal _ at hh
  exact (not_le_of_gt ENNReal.ofReal_lt_top) hh

def windowEvidence : Registration windowArena (windowArena.Law windowActual) where
  actual := windowActual
  bridge := Iff.rfl
  variation := ⟨minimax_window_upper, windowRejected, window_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    windowArena.Law windowActual windowRejected window_rejected
  dependence := windowDependence

noncomputable def atomic_law_representationRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.atomic_law_representation)
    (type_of% (realize curveSignature (fun _ μ t => measureCurve μ t) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.atomic_law_representation_unit
  realizationName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.representationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨representationArena⟩
  objectArena := .source ⟨representationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source representationArena ⟨representationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize curveSignature (fun _ μ t => measureCurve μ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def exists_window_estimatorRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.exists_window_estimator)
    (type_of% (realize estimatorSignature (fun _ p Y => p.2 Y) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.exists_window_estimator_unit
  realizationName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.estimatorEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨estimatorArena⟩
  objectArena := .source ⟨estimatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source estimatorArena ⟨estimatorEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize estimatorSignature (fun _ p Y => p.2 Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
    definition := none
    coordinates := #[3, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def minimax_all_upperRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.minimax_all_upper)
    (type_of% (realize allSignature (fun _ p ε => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 (Ici 0) ε) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.minimax_all_upper_unit
  realizationName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.allEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨allArena⟩
  objectArena := .source ⟨allArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source allArena ⟨allEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize allSignature (fun _ p ε => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 (Ici 0) ε) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def minimax_window_upperRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.minimax_window_upper)
    (type_of% (realize windowSignature (fun _ p ε => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2.2 (Icc 0 p.2.2.2.1) ε) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.minimax_window_upper_unit
  realizationName := `Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.windowEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize windowSignature (fun _ p ε => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2.2 (Icc 0 p.2.2.2.1) ε) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
