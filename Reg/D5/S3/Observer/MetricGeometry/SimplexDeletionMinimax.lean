import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax
open _root_.D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound
open LeanInformationAudit
open scoped BigOperators ENNReal

noncomputable section
namespace Reg.D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax

abbrev centerSignature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def centerActual : Realization centerSignature :=
  realize centerSignature (fun _ m w => (1 - 1 / (m : ℝ)) * w) (fun e => nomatch e)

def centerRejected : Realization centerSignature :=
  realize centerSignature (fun _ _ _ => -1) (fun e => nomatch e)

def centerArena : Arena where
  signature := centerSignature
  Law obs := ∀ {m : ℕ} (_hm : 2 ≤ m)
    (K : Set (Fin m → ℝ)) (_hK : IsCompact K) (_hne : K.Nonempty)
    (_hprob : K ⊆ stdSimplex ℝ (Fin m)) (w : ℝ) (_hw : 0 ≤ w)
    (_hdiam : ∀ p ∈ K, ∀ q ∈ K, ∀ i, |p i - q i| ≤ w),
    ∃ q ∈ stdSimplex ℝ (Fin m),
      ∀ p ∈ K, ∀ i, |p i - q i| ≤ obs.readout () m w

theorem center_rejected : ¬ centerArena.Law centerRejected := by
  intro h
  let p : Fin 2 → ℝ := Pi.single 0 1
  obtain ⟨q, _, hq⟩ := h (by norm_num : 2 ≤ 2) {p} isCompact_singleton
    (Set.singleton_nonempty p)
    (Set.singleton_subset_iff.mpr (single_mem_stdSimplex ℝ (0 : Fin 2)))
    0 le_rfl (by
      intro x hx y hy i
      simp only [Set.mem_singleton_iff] at hx hy
      subst x; subst y; simp)
  have hb := hq p (Set.mem_singleton p) 0
  change |p 0 - q 0| ≤ (-1 : ℝ) at hb
  linarith [abs_nonneg (p 0 - q 0)]

def centerRegistration : Registration centerArena (type_of% (@simplex_common_center)) where
  actual := centerActual
  bridge := Iff.rfl
  variation := ⟨simplex_common_center, centerRejected, center_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨centerRejected, ?_, rfl, center_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 - 1 / (2 : ℝ)) * 0 ≠ (1 - 1 / (2 : ℝ)) * 1
    norm_num

abbrev riskSignature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def riskActual : Realization riskSignature :=
  realize riskSignature
    (fun _ m ε => ENNReal.ofReal ((1 - 1 / (m : ℝ)) * min (2 * ε) 1))
    (fun e => nomatch e)

def riskRejected : Realization riskSignature :=
  realize riskSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

def riskArena : Arena where
  signature := riskSignature
  Law obs := ∀ {m : ℕ} (_hm : 2 ≤ m) (ε : ℝ) (_hε : 0 ≤ ε),
    (⨅ A : (ℝ × (Fin m → ℝ)) → ↥(stdSimplex ℝ (Fin m)),
      worstCaseCost {s : ↥(stdSimplex ℝ (Fin m)) × (ℝ × (Fin m → ℝ)) | ‖s.2‖ ≤ ε}
        (fun s A => ENNReal.ofReal
          ‖(A ((1, fun i => 1 - s.1.val i) + s.2)).val - s.1.val‖) A) =
      obs.readout () m ε

theorem risk_rejected : ¬ riskArena.Law riskRejected := by
  intro h
  have hb := h (by norm_num : 2 ≤ 2) 0 le_rfl
  have he := simplex_deletion_minimax (by norm_num : 2 ≤ 2) 0 le_rfl
  change _ = (⊤ : ℝ≥0∞) at hb
  rw [he] at hb
  simp at hb

def riskRegistration : Registration riskArena (type_of% (@simplex_deletion_minimax)) where
  actual := riskActual
  bridge := Iff.rfl
  variation := ⟨simplex_deletion_minimax, riskRejected, risk_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨riskRejected, ?_, rfl, risk_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
    change ENNReal.ofReal ((1 - 1 / (2 : ℝ)) * min (2 * 0) 1) ≠
      ENNReal.ofReal ((1 - 1 / (2 : ℝ)) * min (2 * 1) 1)
    norm_num

def center_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@simplex_common_center) (Realization centerSignature) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax.center_registration "__information_unit"
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax.centerRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨centerArena⟩
  objectArena := .source ⟨centerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source centerArena ⟨centerRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize centerSignature
    (fun _ m w => (1 - 1 / (m : ℝ)) * w)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def risk_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@simplex_deletion_minimax) (Realization riskSignature) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax.risk_registration "__information_unit"
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax.riskRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨riskArena⟩
  objectArena := .source ⟨riskArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source riskArena ⟨riskRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize riskSignature
    (fun _ m ε => ENNReal.ofReal ((1 - 1 / (m : ℝ)) * min (2 * ε) 1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax
