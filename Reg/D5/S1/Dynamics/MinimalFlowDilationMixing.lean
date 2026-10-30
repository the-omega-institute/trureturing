import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.MinimalFlowDilationMixing

/-! The family retains the full compact minimal flow and expanding map telescope.
Its readout is membership of the actual iterate in the observed target set.
Raw source-domain selection remains unspecified; see issue 23236. -/

noncomputable section

namespace Reg.D5.S1.Dynamics.MinimalFlowDilationMixing

open _root_.D5.S1.Dynamics.MinimalFlowDilationMixing
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure Inputs where
  X : Type u
  topX : TopologicalSpace X
  compactX : @CompactSpace X topX
  hausdorffX : @T2Space X topX
  action : AddAction ℝ X
  continuousAction : @ContinuousVAdd ℝ X action.toVAdd inferInstance topX
  minimal : @AddAction.IsMinimal ℝ X inferInstance topX action
  dilation : ℝ
  expanding : 1 < dilation
  f : X → X
  continuousF : @Continuous X X topX topX f
  covariance : ∀ t x, f (action.vadd t x) = action.vadd (dilation * t) (f x)

def State (P : Inputs.{u}) := ℕ × P.X × Set P.X

def endpointMembership (P : Inputs.{u}) (s : State P) : Prop :=
  (P.f^[s.1]) s.2.1 ∈ s.2.2

def signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P s => endpointMembership P s)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law r := ∀ P : Inputs.{u},
    letI := P.topX
    ∀ U V : Set P.X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ N : ℕ, ∀ n ≥ N, ∃ x, x ∈ U ∧ r.readout () P (n, x, V)

abbrev sourceScope := type_of% (@minimal_real_flow_dilation_mixing.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.X P.topX P.compactX P.hausdorffX P.action P.continuousAction P.minimal
      P.dilation P.expanding P.f P.continuousF P.covariance
  · intro h X topX compactX hausdorffX action continuousAction minimal a ha f hcont hf
    exact h ⟨X, topX, compactX, hausdorffX, action, continuousAction, minimal,
      a, ha, f, hcont, hf⟩

private abbrev trivialAction : AddAction ℝ (ULift.{u} Unit) where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

private def sample : Inputs.{u} where
  X := ULift.{u} Unit
  topX := inferInstance
  compactX := inferInstance
  hausdorffX := inferInstance
  action := trivialAction
  continuousAction := ⟨continuous_snd⟩
  minimal := by
    letI : AddAction ℝ (ULift.{u} Unit) := trivialAction
    exact ⟨fun x => (show Function.Surjective (fun _ : ℝ => x) from
      fun y => ⟨0, Subsingleton.elim _ _⟩).denseRange⟩
  dilation := 2
  expanding := by norm_num
  f := id
  continuousF := continuous_id
  covariance := by intros; rfl

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  letI := sample.{u}.topX
  obtain ⟨N, hN⟩ := h sample Set.univ Set.univ isOpen_univ ⟨⟨()⟩, trivial⟩
    isOpen_univ ⟨⟨()⟩, trivial⟩
  obtain ⟨x, _, hx⟩ := hN N le_rfl
  exact hx

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@minimal_real_flow_dilation_mixing.{u}),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    refine ⟨sample, (0, ⟨()⟩, Set.univ), (0, ⟨()⟩, ∅), ?_⟩
    change True ≠ False
    exact true_ne_false

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@minimal_real_flow_dilation_mixing.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S1.Dynamics.MinimalFlowDilationMixing.minimal_real_flow_dilation_mixing
    "__information_unit"
  realizationName := `Reg.D5.S1.Dynamics.MinimalFlowDilationMixing.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ P s => endpointMembership P s) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration

end Reg.D5.S1.Dynamics.MinimalFlowDilationMixing
