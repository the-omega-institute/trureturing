import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntrySpectralGap
import Reg.Support.DependentFamily

/-! # Source-bound audit of the free-mode spectral extension -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u_1
open scoped BigOperators
open Matrix

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters := Σ Sites : Type u_1, Σ _ : Fintype Sites, Σ _ : DecidableEq Sites,
  (Sites → ℝ) × (Sites → ℝ) × ℝ × ℝ

abbrev signature : Signature where
  Params := Parameters.{u_1}
  State p := Option (Finset p.1) × Option (Finset p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u_1}).State p → (signature.{u_1}).Output role p :=
  fun _ p x => @modeNegativeGenerator p.1 p.2.1 p.2.2.1
    p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 x.1 x.2

def actualAnchor : ∀ (_ : (signature.{u_1}).Anchor) p, (signature.{u_1}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u_1} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the actual matrix entries at the eigenvector occurrence are varied.
The second eigenvector occurrence in the minimality clause remains unchanged. -/
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [fi : Fintype ι] [de : DecidableEq ι] [ne : Nonempty ι]
    (a b : ι → ℝ) (η θ : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < η → 0 < θ →
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < siteRate a b i) ∧ secular a b η θ l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        (fun j k => R.readout () ⟨ι, fi, de, a, b, η, θ⟩ (j, k)) *ᵥ x = l • x) ∧
      ∀ μ : ℝ, 0 < μ →
        (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
          modeNegativeGenerator a b η θ *ᵥ y = μ • y) → l ≤ μ

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  obtain ⟨l, hl, _, _, ⟨x, hx, he⟩, _⟩ :=
    h (ι := ULift.{u_1} Unit) (fun _ => 1) (fun _ => 1) 1 1
      (by intro i; norm_num) (by intro i; norm_num) (by norm_num) (by norm_num)
  apply hx
  funext j
  have hj := congrFun he j
  simp only [rejected, realize, mulVec, dotProduct, zero_mul, Finset.sum_const_zero,
    Pi.smul_apply, smul_eq_mul] at hj
  exact (mul_eq_zero.mp hj.symm).resolve_left (ne_of_gt hl)

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro role
  refine ⟨⟨ULift.{u_1} Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 1, 1, 1⟩,
    (none, none), (none, some ∅), ?_⟩
  norm_num [actual, actualReadout, realize, modeNegativeGenerator]

def family : Registration arena.{u_1} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@secular_root_least_mode_eigenvalue.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 4, 5, 6, 7]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "fn", "arg", "body", "arg", "arg",
      "arg", "arg", "fn", "arg", "body", "arg", "arg", "fn", "arg"]
    stateBinder := 14
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@secular_root_least_mode_eigenvalue.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

def analysisSource : Analysis.Source (@secular_root_least_mode_eigenvalue.{u_1}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@secular_root_least_mode_eigenvalue.{u_1}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Mode-coordinate matrix: configuration-generator conjugacy and probability-law five-mode pushforward unacquired" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

end Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
