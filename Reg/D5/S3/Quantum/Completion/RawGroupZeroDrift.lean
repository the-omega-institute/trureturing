import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Completion.RawGroupZeroDrift

/-! Full original telescopes and exact equality-readout bridges. Source binding remains audited separately. -/
namespace Reg.D5.S3.Quantum.Completion.RawGroupZeroDrift
open _root_.D5.S3.Quantum.Completion.RawGroupZeroDrift
open _root_.D5.S3.Quantum.Completion.RawUnanchoredReplication
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

private theorem zero_raw {G : Type u} [Group G] : RawCost (id : G → G) (fun _ _ => (0 : ℝ)) := by
  constructor <;> intros <;> norm_num

def rightArena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ},
    RawCost U c → ∀ a b z : G, R.readout () () (c (a*z) (b*z)) (c a b)

private theorem right_rejected : ¬ rightArena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) zero_raw 1 1 1

def right_source : Registration rightArena.{u} (type_of% @right_invariant.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@right_invariant.{u}, rejected, right_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity rightArena.Law actual rejected right_rejected
  dependence := dependence

def inverseArena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ},
    RawCost U c → (∀ a b, c a b = c b a) →
    ∀ x : G, R.readout () () (c x⁻¹ 1) (c x 1)

private theorem inverse_rejected : ¬ inverseArena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) zero_raw (fun _ _ => rfl) 1

def inverse_source : Registration inverseArena.{u} (type_of% @inverse_budget.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_budget.{u}, rejected, inverse_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity inverseArena.Law actual rejected inverse_rejected
  dependence := dependence

def groupArena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {α : Type v} [Finite α]
    (U : G → G) (c : G → G → ℝ), RawCost U c → (∀ a b, c a b = c b a) →
    ∀ f : α → G, ∃ (S : Type u) (gS : Group S), letI : Group S := gS
      ∃ (_ : Countable S) (V : S → S) (d : S → S → ℝ) (x : α → S),
        RawCost V d ∧ (∀ a b, d a b = d b a) ∧ d (V 1) 1 = 0 ∧
          ∀ a b, R.readout () () (d (x a) (x b)) (c (f a) (f b))

private theorem group_rejected : ¬ groupArena.{u,v}.Law rejected := by
  intro h
  obtain ⟨S, gS, hS⟩ := h (G := ULift.{u} Unit) (α := ULift.{v} Unit)
    id (fun _ _ => 0) zero_raw (fun _ _ => rfl) (fun _ => 1)
  letI : Group S := gS
  obtain ⟨_, V, d, x, _, _, _, hp⟩ := hS
  exact hp ⟨()⟩ ⟨()⟩

def group_source : Registration groupArena.{u,v} (type_of% @group19_3.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@group19_3.{u,v}, rejected, group_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity groupArena.Law actual rejected group_rejected
  dependence := dependence

-- The source bridge covers the complete telescope; the compiler/judge owns binding status.
def right_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@right_invariant.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroDrift.right_invariant.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroDrift.right_source
  realizationSource := none
  generated := false
  arena := .source ⟨rightArena⟩
  objectArena := .source ⟨rightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rightArena ⟨right_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

-- The source bridge covers the complete telescope; the compiler/judge owns binding status.
def inverse_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inverse_budget.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroDrift.inverse_budget.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroDrift.inverse_source
  realizationSource := none
  generated := false
  arena := .source ⟨inverseArena⟩
  objectArena := .source ⟨inverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseArena ⟨inverse_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

-- The source bridge covers the complete telescope; the compiler/judge owns binding status.
def group_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@group19_3.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroDrift.group19_3.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroDrift.group_source
  realizationSource := none
  generated := false
  arena := .source ⟨groupArena⟩
  objectArena := .source ⟨groupArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source groupArena ⟨group_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.RawGroupZeroDrift
