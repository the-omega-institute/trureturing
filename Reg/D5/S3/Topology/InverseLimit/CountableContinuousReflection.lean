import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import D5.S3.Topology.InverseLimit.CountableContinuousReflection

/-!
# Faithful source-family registration attempt

The full source telescope and the actual dependent stage/function witness
are retained. The certificate is the full exact factorization conclusion.
Source occurrence selection is unfinished under
https://github.com/the-omega-institute/trureturing/issues/21901;
no validated binding is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.CountableContinuousReflection

open CategoryTheory CategoryTheory.Limits Opposite Set Function
open _root_.D5.S3.Topology.InverseLimit.CountableClopenReflection
open _root_.D5.S3.Topology.InverseLimit.CountableContinuousReflection
open _root_.D5.S3.ConceptDynamics.InformationEscape

structure SourceInputs where
  F : CountableStageᵒᵖ ⥤ Profinite.{1}
  nonempty : ∀ j, Nonempty (F.obj j)
  C : Cone F
  hC : IsLimit C
  hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a)
  base : CountableStage
  f : C(C.pt, ℝ)

def SourceState (P : SourceInputs) :=
  Σ β : CountableStage, C(P.F.obj (op β), ℝ)

def certificate (P : SourceInputs) (w : SourceState P) : Prop :=
  P.base ≤ w.1 ∧ ∀ x, P.f x = w.2 (P.C.π.app (op w.1) x)

def signature : DependentFamily.Signature where
  Params := SourceInputs
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ P w => certificate P w)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ P, ∃ w, r.readout () P w

abbrev reflectionScope := type_of% (@exists_stage)

/-- The full original statement is equivalent to the chosen source law. -/
theorem source_bridge : reflectionScope ↔ arena.Law actual := by
  constructor
  · intro h P
    let := P.nonempty
    obtain ⟨β, hb, g, hg⟩ := h P.F P.C P.hC P.hs P.base P.f
    exact ⟨⟨β, g⟩, hb, hg⟩
  · intro h F nonempty C hC hs base f
    let P : SourceInputs := ⟨F, nonempty, C, hC, hs, base, f⟩
    obtain ⟨⟨β, g⟩, hb, hg⟩ := h P
    exact ⟨β, hb, g, hg⟩

theorem actual_positive : arena.Law actual := source_bridge.mp @exists_stage

private def zeroStage : CountableStage :=
  ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩

private instance : IsConnected CountableStageᵒᵖ := IsCofiltered.isConnected _

private def unitDiagram : CountableStageᵒᵖ ⥤ Profinite.{1} :=
  (Functor.const CountableStageᵒᵖ).obj (Profinite.of (ULift.{1} Unit))

noncomputable def unitInputs : SourceInputs where
  F := unitDiagram
  nonempty := fun _ => inferInstanceAs (Nonempty (ULift.{1} Unit))
  C := constCone CountableStageᵒᵖ (Profinite.of (ULift.{1} Unit))
  hC := isLimitConstCone CountableStageᵒᵖ (Profinite.of (ULift.{1} Unit))
  hs := fun _ x => ⟨x, rfl⟩
  base := zeroStage
  f := 0

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, hw⟩ := h unitInputs
  exact hw

noncomputable def wrongState : SourceState unitInputs := ⟨zeroStage, 1⟩

theorem wrong_invalid : ¬ certificate unitInputs wrongState := by
  intro h
  have hx := h.2 (ULift.up ())
  change (0 : ℝ) = 1 at hx
  exact zero_ne_one hx

def familyRegistration : DependentFamily.Registration arena reflectionScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
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
    obtain ⟨w, hw⟩ := actual_positive unitInputs
    refine ⟨unitInputs, w, wrongState, ?_⟩
    intro h
    have hcert : certificate unitInputs w := hw
    change certificate unitInputs w = certificate unitInputs wrongState at h
    rw [h] at hcert
    exact wrong_invalid hcert

/- The enrolled template and all family-level obligations are supplied.
Raw source occurrence reconstruction is not supplied; the audit stays open. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_stage) (DependentFamily.Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Topology.InverseLimit.CountableContinuousReflection.exists_stage.__information_unit
  realizationName :=
    `Reg.D5.S3.Topology.InverseLimit.CountableContinuousReflection.familyRegistration
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
    (fun _ P w => certificate P w) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.InverseLimit.CountableContinuousReflection
