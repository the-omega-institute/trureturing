import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntryProductMixture
import Reg.Support.DependentFamily

/-! # The original product-mixture law as a dependent source family -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.StatisticalMechanics.SingleEntryProductMixture
open _root_.D5.S3.StatisticalMechanics.SingleEntryProductMixture
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

abbrev Parameters := Σ Sites : Type u, Sites → ℝ → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p i => p.2 i

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [_fi : Fintype ι] [_de : DecidableEq ι]
    (h : ℝ → ℝ) (g : ι → ℝ → ℝ) (t : ℝ), 0 < t →
    ContinuousOn h (Icc 0 t) →
    (∀ u ∈ Icc 0 t, 0 ≤ h u) → (∀ u ∈ Ioo 0 t, 0 < h u) →
    (∀ i, ContinuousOn (g i) (Icc 0 t)) →
    (∀ i u, u ∈ Icc 0 t → 0 ≤ g i u ∧ g i u < 1) →
    (∀ i, StrictMonoOn (g i) (Icc 0 t)) →
    ∀ S T : Finset ι, ¬ S ⊆ T → ¬ T ⊆ S →
    mixtureMass h (fun i => R.readout () ⟨ι, g⟩ i) t S *
      mixtureMass h (fun i => R.readout () ⟨ι, g⟩ i) t T <
      mixtureMass h (fun i => R.readout () ⟨ι, g⟩ i) t (S ∩ T) *
      mixtureMass h (fun i => R.readout () ⟨ι, g⟩ i) t (S ∪ T)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let i : ULift.{u} (Fin 2) := ULift.up 0
  let j : ULift.{u} (Fin 2) := ULift.up 1
  have hij : i ≠ j := by simp [i, j]
  have hji : j ≠ i := Ne.symm hij
  have hbad := h (ι := ULift.{u} (Fin 2)) (fun _ => 1) (fun _ x => x / 2) 1
    (by norm_num) continuousOn_const (by intro x hx; norm_num)
    (by intro x hx; norm_num)
    (by intro k; fun_prop)
    (by intro k x hx; constructor <;> linarith [hx.1, hx.2])
    (by intro k x hx y hy hxy; dsimp; linarith)
    {i} {j} (by simpa using hij) (by simpa using hji)
  have zero_mass (A : Finset (ULift.{u} (Fin 2))) (hA : A.Nonempty) :
      mixtureMass (fun _ => 1) (fun (_ : ULift.{u} (Fin 2)) (_ : ℝ) => 0) 1 A = 0 := by
    obtain ⟨k, hk⟩ := hA
    have hz (x : ℝ) : productKernel (fun (_ : ULift.{u} (Fin 2)) (_ : ℝ) => 0) A x = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
    simp [mixtureMass, hz]
  simp only [rejected, realize] at hbad
  rw [zero_mass {i} (by simp), zero_mass ({i} ∪ {j}) (by simp)] at hbad
  simpa using hbad

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let g : ULift.{u} (Fin 2) → ℝ → ℝ := fun i _ => if i.down = 0 then 0 else 1
  refine ⟨⟨ULift.{u} (Fin 2), g⟩, ULift.up 0, ULift.up 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, actualReadout, realize, g] at hh

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@strict_mtp2_product_mixture.{u}, rejected, rejected_law⟩
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
  owner := `D5.S3.StatisticalMechanics.SingleEntryProductMixture
  definition := none
  coordinates := #[0, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``strict_mtp2_product_mixture).type
  let path := #["body", "body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "body", "body", "body",
    "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected product-mixture occurrence is absent"
  unless binders == 17 && e == .bvar 12 do
    throwError "The selected operand is not the original site occupancy function"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_mtp2_product_mixture.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryProductMixture.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryProductMixture.family
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

def analysisSource : Analysis.Source (@strict_mtp2_product_mixture.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

/-- A continuous integral family supplies no finite presentation or native
continuation reader without a separate dynamical realization bridge. -/
def analysis : AuricFib.Contract.Application (@strict_mtp2_product_mixture.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Continuous product mixture: actual inhibited trajectory and finite native reader bridges unacquired" }

#print axioms family
#print axioms registration
#print axioms analysis

end Reg.D5.S3.StatisticalMechanics.SingleEntryProductMixture
