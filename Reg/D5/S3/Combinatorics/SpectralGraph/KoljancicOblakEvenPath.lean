import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Polynomial

/-- Parameters retain the whole edge sequence and every branch length. -/
def signature : DependentFamily.Signature where
  Params := (ℕ → ℝ) × ℕ
  State := fun _ => ℕ → ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun role p dq => variation p.1 dq (p.2 + if role then 1 else 0))
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (q dq : ℕ → ℝ) (n : ℕ),
    (∀ k < n, q k ≠ 0) →
    R.readout false (q, n) dq = 0 → R.readout true (q, n) dq = 0 →
    ∀ k < n, dq k = 0

abbrev sourceScope := type_of% (@branch_variation_injective)

lemma source_bridge : sourceScope ↔ arena.Law actual := by
  rfl

lemma actual_positive : arena.Law actual :=
  source_bridge.mp branch_variation_injective

def rejected (role : Bool) : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun index p dq => if index = role then 0 else actual.readout index p dq)
    (fun e => nomatch e)

lemma rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  cases role with
  | false =>
      intro h
      let dq : ℕ → ℝ := fun k => if k = 0 then 1 else -1
      have hz : variation (fun _ => 1) dq 3 = 0 := by
        simp [variation, continuant, dq]
      have hc := h (fun _ => 1) dq 2 (by intro k hk; norm_num)
        (by simp [rejected, DependentFamily.realize])
        (by simpa [rejected, actual, DependentFamily.realize] using hz)
        0 (by omega)
      norm_num [dq] at hc
  | true =>
      intro h
      have hc := h (fun _ => 1) (fun _ => 1) 1 (by intro k hk; norm_num)
        (by simp [rejected, actual, DependentFamily.realize, variation])
        (by simp [rejected, DependentFamily.realize]) 0 (by omega)
      norm_num at hc

lemma dependence : DependentFamily.ObservationalDependence signature actual := by
  intro role
  cases role with
  | false =>
      refine ⟨((fun _ => 1), 2), (fun _ => 1), (fun _ => 0), ?_⟩
      norm_num [actual, DependentFamily.realize, variation, continuant]
  | true =>
      refine ⟨((fun _ => 1), 1), (fun _ => 1), (fun _ => 0), ?_⟩
      norm_num [actual, DependentFamily.realize, variation, continuant]

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro index hne
      funext p dq
      simp [rejected, DependentFamily.realize, hne]
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@branch_variation_injective) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.branch_variation_injective.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun role p dq => variation p.1 dq (p.2 + if role then 1 else 0))
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
