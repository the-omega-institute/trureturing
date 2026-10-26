import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Topology.InverseLimit.CountableClopenReflection
import D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection

/-! Faithful whole-source dependent-family attempt. The compiled source-selection
witness is missing; this registration does not assert declared_validated.
Audit gap: https://github.com/the-omega-institute/trureturing/issues/21929. -/

namespace Reg.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection

open CategoryTheory CategoryTheory.Limits Opposite Set Function MeasureTheory
open _root_.D5.S3.Topology.InverseLimit.CountableClopenReflection
open _root_.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe w

structure SourceInputs where
  I : Type w
  countableI : Countable I
  F : CountableStageᵒᵖ ⥤ Profinite.{1}
  nonempty : ∀ j, Nonempty (F.obj j)
  stageMeas : ∀ j, MeasurableSpace (F.obj j)
  stageBorel : ∀ j, @BorelSpace (F.obj j) inferInstance (stageMeas j)
  C : Cone F
  limitMeas : MeasurableSpace C.pt
  limitBorel : @BorelSpace C.pt inferInstance limitMeas
  hC : IsLimit C
  hs : ∀ {i j} (f : i ⟶ j), Surjective (F.map f)
  base : CountableStage
  s : ℕ → @SignedMeasure C.pt limitMeas
  regular : ∀ n, @Measure.Regular C.pt limitMeas inferInstance (s n).totalVariation
  W : I → Set C.pt
  hW : ∀ i, IsClopen (W i)

attribute [instance] SourceInputs.countableI SourceInputs.nonempty SourceInputs.stageMeas
  SourceInputs.stageBorel SourceInputs.limitMeas SourceInputs.limitBorel SourceInputs.regular

def SourceState (P : SourceInputs.{w}) :=
  Σ β : CountableStage, P.I → Set (P.F.obj (op β))

def certificate (P : SourceInputs.{w}) (a : SourceState P) : Prop :=
  P.base ≤ a.1 ∧
  (∀ i, IsClopen (a.2 i)) ∧
  (∀ i, P.W i = P.C.π.app (op a.1) ⁻¹' a.2 i) ∧
  (∀ i, (a.2 i).Nonempty ↔ (P.W i).Nonempty) ∧
  (∀ i j, Disjoint (a.2 i) (a.2 j) ↔ Disjoint (P.W i) (P.W j)) ∧
  (∀ γ : CountableStage, a.1 ≤ γ → ∀ n,
    PreservesJordanMass (P.s n) (fun x : P.C.pt => P.C.π.app (op γ) x) ∧
    (SignedMeasure.totalVariation ((P.s n).map (fun x : P.C.pt => P.C.π.app (op γ) x))) =
      (P.s n).totalVariation.map (fun x : P.C.pt => P.C.π.app (op γ) x)) ∧
  (∀ n i, (SignedMeasure.totalVariation ((P.s n).map (fun x : P.C.pt => P.C.π.app (op a.1) x))) (a.2 i)ᶜ = 0 ↔
    (P.s n).totalVariation (P.W i)ᶜ = 0)

def signature : DependentFamily.Signature where
  Params := SourceInputs.{w}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{w} :=
  DependentFamily.realize signature.{w} (fun _ P a => certificate P a)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{w}
  Law := fun r => ∀ P, ∃ a, r.readout () P a

abbrev reflectionScope := type_of% (@_root_.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection.exists_common_stage.{w})

theorem source_bridge : reflectionScope.{w} ↔ arena.{w}.Law actual.{w} := by
  constructor
  · intro h P
    letI := P.countableI
    letI := P.nonempty
    letI := P.stageMeas
    letI := P.stageBorel
    letI := P.limitMeas
    letI := P.limitBorel
    letI := P.regular
    obtain ⟨β, hb, V, hV⟩ := h P.F P.C P.hC P.hs P.base P.s P.W P.hW
    exact ⟨⟨β, V⟩, hb, hV⟩
  · intro h I countableI F nonempty stageMeas stageBorel C limitMeas limitBorel hC hs base s regular W hW
    let P : SourceInputs.{w} :=
      ⟨I, countableI, F, nonempty, stageMeas, stageBorel, C, limitMeas, limitBorel,
        hC, hs, base, s, regular, W, hW⟩
    obtain ⟨⟨β, V⟩, hb, hV⟩ := h P
    exact ⟨β, hb, V, hV⟩

theorem actual_positive : arena.{w}.Law actual.{w} :=
  source_bridge.mp @_root_.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection.exists_common_stage.{w}

private def zeroStage : CountableStage :=
  ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩

noncomputable def unitInputs : SourceInputs.{w} := by
  let P := CountableClopenReflection.unitInputs.{w}
  letI : ∀ j, MeasurableSpace (P.F.obj j) := fun j => borel _
  letI : MeasurableSpace P.C.pt := borel _
  letI : ∀ j, BorelSpace (P.F.obj j) := fun j => ⟨rfl⟩
  letI : BorelSpace P.C.pt := ⟨rfl⟩
  exact {
    I := ULift.{w} Unit
    countableI := inferInstance
    F := P.F
    nonempty := P.nonempty
    stageMeas := fun j => inferInstance
    stageBorel := fun j => inferInstance
    C := P.C
    limitMeas := inferInstance
    limitBorel := inferInstance
    hC := P.hC
    hs := P.hs
    base := zeroStage
    s := fun _ => 0
    regular := fun n => by rw [SignedMeasure.totalVariation_zero]; infer_instance
    W := fun _ => univ
    hW := fun _ => isClopen_univ }

def rejected : DependentFamily.Realization signature.{w} :=
  DependentFamily.realize signature.{w} (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{w}.Law rejected.{w} := by
  intro h
  obtain ⟨a, ha⟩ := h unitInputs.{w}
  exact ha

def emptyState : SourceState unitInputs.{w} := ⟨zeroStage, fun _ => ∅⟩

theorem empty_invalid : ¬ certificate unitInputs.{w} emptyState.{w} := by
  intro h
  have x : unitInputs.{w}.C.pt := ULift.up ()
  have hx : x ∈ unitInputs.{w}.W (ULift.up ()) := Set.mem_univ x
  rw [h.2.2.1 (ULift.up ())] at hx
  exact hx

def familyRegistration : DependentFamily.Registration arena.{w} reflectionScope.{w} where
  actual := actual.{w}
  bridge := source_bridge.{w}
  variation := ⟨actual_positive.{w}, rejected.{w}, rejected_law.{w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{w}, ?_, rfl, rejected_law.{w}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    obtain ⟨a, ha⟩ := actual_positive.{w} unitInputs.{w}
    refine ⟨unitInputs.{w}, a, emptyState.{w}, ?_⟩
    intro h
    have hc : certificate unitInputs.{w} a := ha
    change certificate unitInputs.{w} a = certificate unitInputs.{w} emptyState.{w} at h
    rw [h] at hc
    exact empty_invalid.{w} hc

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection.exists_common_stage.{w}) (DependentFamily.Realization signature.{w}) Unit Unit where
  unitName := `D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection.exists_common_stage.__information_unit
  realizationName := `Reg.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{w}⟩
  objectArena := .source ⟨arena.{w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{w} ⟨familyRegistration.{w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{w}
    (fun _ P a => certificate P a) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection
