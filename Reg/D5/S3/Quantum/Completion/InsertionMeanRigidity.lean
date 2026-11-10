import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Completion.InsertionMeanRigidity
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Completion.InsertionMeanRigidity
open _root_.D5.S3.Quantum.Completion.RawUnanchoredReplication

namespace Reg.D5.S3.Quantum.Completion.InsertionMeanRigidity
universe u

namespace Polynomial
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (t : Finset ι) (a : ι → ℝ) (v : ι → ℕ × ℕ)
    (g : Grid), (∀ q, 0 ≤ g q) →
    (∀ m n, 2 * g (m + 1, n + 1) + g (m + 1, n) + g (m, n + 1) = 4 * g (m, n)) →
    (∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r + s + 2 * r * s = 4 →
      0 ≤ ∑ k ∈ t, a k * r ^ (v k).1 * s ^ (v k).2) →
    R.readout () () 0 (∑ k ∈ t, a k * g (v k))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) ∅ (fun _ => 0) (fun _ => (0, 0)) (fun _ => 0)
    (fun _ => le_rfl) (by intros; ring) (by intros; simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  norm_num at hh

def source_registration : Registration arena.{u} (type_of% @finite_polynomial_positive.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_polynomial_positive.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_polynomial_positive.{u}) (Realization signature) Type Unit := {
  unitName := `D5.S3.Quantum.Completion.InsertionMeanRigidity.finite_polynomial_positive.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.InsertionMeanRigidity.Polynomial.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.InsertionMeanRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Polynomial

namespace OriginalKernel
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Type u)
    (fun M => M → M → ℝ) (fun M => (M → M → ℝ) → Prop)
def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {M : Type u} [MulOneClass M] (U : M → M) (c : M → M → ℝ),
    RawCost U c → (∀ x y, c x y = c y x) →
    (∀ x y, c (P U 3 x) y = c x y) →
    (∀ x y, c x (P U 3 y) = c x y) →
    c 1 (p U 1) = 0 → c 1 (p U 2) = 0 →
    (∀ m n x y, F U c m n x y = c x y) ∧
    S U c = c ∧ T U c = c ∧ S U (T U c) = c ∧
    R.readout () M (c - S U (T U c)) 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M := ULift.{u} Unit
  let c : M → M → ℝ := fun _ _ => 0
  have hc : RawCost (id : M → M) c :=
    ⟨fun _ _ => le_rfl, fun _ => rfl, by intros; dsimp [c]; ring⟩
  exact (h id c hc (by intros; rfl) (by intros; rfl) (by intros; rfl) rfl rfl).2.2.2.2
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have hh : (fun _ _ : ULift.{u} Unit => (1 : ℝ)) = (fun _ _ => 0) :=
    Eq.mp (congrFun h (fun _ _ => 0)) rfl
  have he := congrFun (congrFun hh ⟨()⟩) ⟨()⟩
  exact one_ne_zero he

def source_registration : Registration arena.{u}
    (type_of% @full_original_insertion_mean_rigidity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_original_insertion_mean_rigidity.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_original_insertion_mean_rigidity.{u}) (Realization signature.{u})
    (type_of% (@Kernel.{u})) Unit := {
  unitName := `D5.S3.Quantum.Completion.InsertionMeanRigidity.full_original_insertion_mean_rigidity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.InsertionMeanRigidity.OriginalKernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Kernel.{u})
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.InsertionMeanRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end OriginalKernel
end Reg.D5.S3.Quantum.Completion.InsertionMeanRigidity
