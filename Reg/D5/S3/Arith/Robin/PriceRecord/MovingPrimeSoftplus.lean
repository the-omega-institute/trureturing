import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def normalized (s : ℝ → ℝ) (P : ℝ) : ℝ :=
  (∑' p : ℕ, if p.Prime then weight P (s P) p else 0) / (P / (s P * log P))

def actual : Realization signature :=
  realize signature (fun _ s P => normalized s P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a C₁ C₂ : ℝ}, 0 < a → 0 < C₁ → C₁ ≤ C₂ →
    ∀ s : ℝ → ℝ,
    (∀ᶠ P in atTop, C₁ * log P ^ a ≤ s P ∧ s P ≤ C₂ * log P ^ a) →
    (∀ᶠ P in atTop,
      Summable (fun p : ℕ => |if p.Prime then weight P (s P) p else 0|)) ∧
    Tendsto (fun P : ℝ => R.readout () s P) atTop (𝓝 (π ^ 2 / 6))

private theorem log_scale_witness :
    ∀ᶠ P : ℝ in atTop, 1 * log P ^ (1 : ℝ) ≤ log P ∧ log P ≤ 1 * log P ^ (1 : ℝ) := by
  simp only [rpow_one, one_mul, le_refl, and_self, eventually_true]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (a := 1) (C₁ := 1) (C₂ := 1) one_pos one_pos le_rfl
    log log_scale_witness).2
  change Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 (π ^ 2 / 6)) at hh
  have he := tendsto_nhds_unique tendsto_const_nhds hh
  exact (ne_of_gt (show 0 < π ^ 2 / 6 by positivity)) he.symm

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have h := (prime_softplus_asymptotic (a := 1) (C₁ := 1) (C₂ := 1)
    one_pos one_pos le_rfl log log_scale_witness).2
  change Tendsto (normalized log) atTop (𝓝 (π ^ 2 / 6)) at h
  have hπ : 0 < π ^ 2 / 6 := by positivity
  obtain ⟨P, hP⟩ := (h.eventually (lt_mem_nhds hπ)).exists
  refine ⟨log, 1, P, ?_⟩
  change normalized log 1 ≠ normalized log P
  have hzero : normalized log 1 = 0 := by simp [normalized, log_one]
  rw [hzero]
  exact (ne_of_gt hP).symm

def family : Registration arena (type_of% (@prime_softplus_asymptotic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_softplus_asymptotic, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_softplus_asymptotic) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus.prime_softplus_asymptotic.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s P => normalized s P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus
