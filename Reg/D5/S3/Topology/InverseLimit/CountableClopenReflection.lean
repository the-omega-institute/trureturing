import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import D5.S3.Topology.InverseLimit.CountableClopenReflection

/-!
# Full source family for countable common-stage reflection

All original functor, cone, nonempty, limit, surjectivity, base and clopen
inputs remain in the parameter telescope. States retain the actual common
ordinal and the actual sequence of stage subsets. The readout tests every
conclusion clause. Source-selection reconstruction is explicitly unfinished.
-/

namespace Reg.D5.S3.Topology.InverseLimit.CountableClopenReflection

open CategoryTheory CategoryTheory.Limits Opposite Set Function
open _root_.D5.S3.Topology.InverseLimit.CountableClopenReflection
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe uI

structure SourceInputs where
  I : Type uI
  countableI : Countable I
  F : CountableStageᵒᵖ ⥤ Profinite.{1}
  nonempty : ∀ j, Nonempty (F.obj j)
  C : Cone F
  hC : IsLimit C
  hs : ∀ {i j} (f : i ⟶ j), Surjective (F.map f)
  base : CountableStage
  W : I → Set C.pt
  hW : ∀ n, IsClopen (W n)

def SourceState (P : SourceInputs.{uI}) :=
  Σ β : CountableStage, P.I → Set (P.F.obj (op β))

def certificate (P : SourceInputs.{uI}) (w : SourceState P) : Prop :=
  P.base ≤ w.1 ∧
    (∀ n, IsClopen (w.2 n)) ∧
    (∀ n, P.W n = P.C.π.app (op w.1) ⁻¹' w.2 n) ∧
    (∀ n, (w.2 n).Nonempty ↔ (P.W n).Nonempty) ∧
    (∀ m n, Disjoint (w.2 m) (w.2 n) ↔ Disjoint (P.W m) (P.W n))

def signature : DependentFamily.Signature where
  Params := SourceInputs.{uI}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{uI} :=
  DependentFamily.realize signature.{uI} (fun _ P w => certificate P w)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{uI}
  Law := fun r => ∀ P, ∃ w, r.readout () P w

abbrev reflectionScope := type_of% (@exists_common_stage.{uI})

theorem source_bridge : reflectionScope.{uI} ↔ arena.{uI}.Law actual.{uI} := by
  constructor
  · intro h P
    let := P.countableI
    let := P.nonempty
    obtain ⟨β, hb, V, hV⟩ := h P.F P.C P.hC P.hs P.base P.W P.hW
    exact ⟨⟨β, V⟩, hb, hV⟩
  · intro h I countableI F nonempty C hC hs base W hW
    let P : SourceInputs.{uI} := ⟨I, countableI, F, nonempty, C, hC, hs, base, W, hW⟩
    obtain ⟨⟨β, V⟩, hb, hV⟩ := h P
    exact ⟨β, hb, V, hV⟩

theorem actual_positive : arena.{uI}.Law actual.{uI} :=
  source_bridge.mp @exists_common_stage.{uI}

private def zeroStage : CountableStage :=
  ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩

private instance : IsConnected CountableStageᵒᵖ := IsCofiltered.isConnected _

private def unitDiagram : CountableStageᵒᵖ ⥤ Profinite.{1} :=
  (Functor.const CountableStageᵒᵖ).obj (Profinite.of (ULift.{1} Unit))

noncomputable def unitInputs : SourceInputs.{uI} where
  I := ULift.{uI} Unit
  countableI := inferInstance
  F := unitDiagram
  nonempty := fun _ => inferInstanceAs (Nonempty (ULift.{1} Unit))
  C := constCone CountableStageᵒᵖ (Profinite.of (ULift.{1} Unit))
  hC := isLimitConstCone CountableStageᵒᵖ (Profinite.of (ULift.{1} Unit))
  hs := fun _ x => ⟨x, rfl⟩
  base := zeroStage
  W := fun _ => univ
  hW := fun _ => isClopen_univ

def rejected : DependentFamily.Realization signature.{uI} :=
  DependentFamily.realize signature.{uI} (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{uI}.Law rejected.{uI} := by
  intro h
  obtain ⟨w, hw⟩ := h unitInputs.{uI}
  exact hw

def emptyState : SourceState unitInputs.{uI} :=
  ⟨zeroStage, fun _ => ∅⟩

theorem empty_invalid : ¬ certificate unitInputs.{uI} emptyState.{uI} := by
  intro h
  have x : unitInputs.{uI}.C.pt := ULift.up ()
  have hx : x ∈ unitInputs.{uI}.W (ULift.up ()) := Set.mem_univ x
  rw [h.2.2.1 (ULift.up ())] at hx
  exact hx

def familyRegistration : DependentFamily.Registration arena.{uI} reflectionScope.{uI} where
  actual := actual.{uI}
  bridge := source_bridge.{uI}
  variation := ⟨actual_positive.{uI}, rejected.{uI}, rejected_law.{uI}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{uI}, ?_, rfl, rejected_law.{uI}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    obtain ⟨w, hw⟩ := actual_positive.{uI} unitInputs.{uI}
    refine ⟨unitInputs.{uI}, w, emptyState.{uI}, ?_⟩
    intro h
    have hcert : certificate unitInputs.{uI} w := hw
    change certificate unitInputs.{uI} w = certificate unitInputs.{uI} emptyState.{uI} at h
    rw [h] at hcert
    exact empty_invalid.{uI} hcert

/- The enrolled dependent template is used faithfully. Raw occurrence
selection is not supplied, so this attempt asserts no validated binding. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_common_stage.{uI}) (DependentFamily.Realization signature.{uI}) Unit Unit where
  unitName :=
    `D5.S3.Topology.InverseLimit.CountableClopenReflection.exists_common_stage.__information_unit
  realizationName := `Reg.D5.S3.Topology.InverseLimit.CountableClopenReflection.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uI}⟩
  objectArena := .source ⟨arena.{uI}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uI} ⟨familyRegistration.{uI}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{uI}
    (fun _ P w => certificate P w) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.InverseLimit.CountableClopenReflection
