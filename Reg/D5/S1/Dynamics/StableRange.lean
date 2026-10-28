import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.StableRange

/-!
# Actual core-preimage source family

The original compact Hausdorff carrier, topology, endomorphism and continuity
are retained. The readout is equality under the actual core restriction.
All core states, including degenerate and empty fibers, remain in scope.
The source selector and escape-origin identity remain unspecified.
-/

namespace Reg.D5.S1.Dynamics.StableRange

open Set Function
open _root_.D5.S1.Dynamics.StableRange
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure Inputs where
  X : Type u
  topX : TopologicalSpace X
  compactX : @CompactSpace X topX
  hausdorffX : @T2Space X topX
  f : X → X
  hf : @Continuous X X topX topX f

def State (P : Inputs.{u}) := core P.f × core P.f

def preimageLaw (P : Inputs.{u}) (y : State P) : Prop := restriction P.f y.1 = y.2

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
  DependentFamily.realize signature (fun _ P y => preimageLaw P y) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r => ∀ P : Inputs.{u},
    letI := P.topX
    IsCompact (core P.f) ∧ Continuous (restriction P.f) ∧
      ∀ c : core P.f, ∃ a : core P.f, r.readout () P (a, c)

abbrev sourceScope := type_of% (@compact_surjective_restriction.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    let := P.topX
    let := P.compactX
    let := P.hausdorffX
    exact @h P.X P.topX P.compactX P.hausdorffX P.f P.hf
  · intro h X topX compactX hausdorffX f hf
    exact h ⟨X, topX, compactX, hausdorffX, f, hf⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@compact_surjective_restriction.{u})

def sample : Inputs.{u} where
  X := ULift.{u} Bool
  topX := inferInstance
  compactX := inferInstance
  hausdorffX := inferInstance
  f := id
  hf := continuous_id

def firstPoint : core sample.{u}.f := ⟨ULift.up false, mem_iInter.mpr fun n =>
  ⟨ULift.up false, by
    change (id : ULift.{u} Bool → ULift.{u} Bool)^[n] (ULift.up false) = ULift.up false
    exact congrFun (iterate_id n) _⟩⟩
def secondPoint : core sample.{u}.f := ⟨ULift.up true, mem_iInter.mpr fun n =>
  ⟨ULift.up true, by
    change (id : ULift.{u} Bool → ULift.{u} Bool)^[n] (ULift.up true) = ULift.up true
    exact congrFun (iterate_id n) _⟩⟩

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨a, ha⟩ := (h sample).2.2 firstPoint
  exact ha

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
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
    cases i
    refine ⟨sample, (firstPoint, firstPoint), (secondPoint, firstPoint), ?_⟩
    intro heq
    have hp : actual.readout () sample (firstPoint, firstPoint) := rfl
    rw [heq] at hp
    have hbad : (ULift.up true : ULift.{u} Bool) = ULift.up false :=
      congrArg Subtype.val hp
    cases congrArg ULift.down hbad

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@compact_surjective_restriction.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Dynamics.StableRange.compact_surjective_restriction.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.StableRange.familyRegistration
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
    (fun _ P y => preimageLaw P y) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.StableRange
