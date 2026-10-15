import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.LinearMemory.FiniteWordReachability
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic

open _root_.D5.S3.Observer.LinearMemory.FiniteWordReachability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option maxHeartbeats 800000
namespace Reg.D5.S3.Observer.LinearMemory.FiniteWordReachability

universe u v w

/-- All scalar, carrier, alphabet and instance choices remain parameters. -/
structure Parameters where
  K : Type u
  E : Type v
  I : Type w
  division : DivisionRing K
  additive : AddCommGroup E
  module : @Module K E division.toSemiring additive.toAddCommMonoid
  finite : @FiniteDimensional K E division additive module
  family : @I → @Module.End K E division.toSemiring additive.toAddCommMonoid module

attribute [instance] Parameters.division Parameters.additive Parameters.module Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State p := Submodule p.K p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule p.K p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ p U => reachableSpan p.family U) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {K : Type u} {E : Type v} {I : Type w}
    [d : DivisionRing K] [a : AddCommGroup E] [m : Module K E]
    [f : FiniteDimensional K E] (A : I → Module.End K E) (U : Submodule K E),
    boundedSpan A U (Module.finrank K (reachableSpan A U) - Module.finrank K U) =
      r.readout () ⟨K, E, I, d, a, m, f, A⟩ U

private def separatingParameters : Parameters.{u,v,w} where
  K := ULift.{u} (ZMod 2)
  E := ULift.{v} (ZMod 2)
  I := ULift.{w} Empty
  division := inferInstance
  additive := inferInstance
  module := inferInstance
  finite := inferInstance
  family i := nomatch i.down

private theorem reachable_bot {K E I : Type*} [DivisionRing K] [AddCommGroup E]
    [Module K E] (A : I → Module.End K E) : reachableSpan A ⊥ = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨word, z, hz, rfl⟩
  have : z = 0 := hz
  simp [this]

private theorem reachable_top {K E I : Type*} [DivisionRing K] [AddCommGroup E]
    [Module K E] (A : I → Module.End K E) : reachableSpan A ⊤ = ⊤ := by
  apply top_unique
  intro x _
  exact Submodule.subset_span ⟨[], x, Submodule.mem_top, by simp⟩

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let p := separatingParameters.{u,v,w}
  have he := h p.family ⊤
  have hmem : (1 : ULift.{v} (ZMod 2)) ∈ boundedSpan p.family ⊤
      (Module.finrank p.K (reachableSpan p.family ⊤) - Module.finrank p.K
        (⊤ : Submodule p.K p.E)) :=
    Submodule.subset_span ⟨[], Nat.zero_le _, (1 : ULift.{v} (ZMod 2)),
      Submodule.mem_top, rfl⟩
  change _ = (⊥ : Submodule p.K p.E) at he
  rw [he] at hmem
  exact (one_ne_zero : (1 : ULift.{v} (ZMod 2)) ≠ 0) hmem

def registration : Registration arena.{u,v,w} (type_of% (@bounded_span_eq_reachable.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_span_eq_reachable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual at ⊢
    intro i
    refine ⟨separatingParameters.{u,v,w},
      (⊥ : Submodule (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))),
      (⊤ : Submodule (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))), ?_⟩
    change reachableSpan _ ⊥ ≠ reachableSpan _ ⊤
    rw [reachable_bot, reachable_top]
    change (⊥ : Submodule (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))) ≠ ⊤
    exact bot_ne_top

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_span_eq_reachable.{u,v,w})
    (type_of% (realize signature.{u,v,w}
      (fun _ p U => reachableSpan p.family U) (fun e => nomatch e))) Unit Unit := {
  unitName :=
    `D5.S3.Observer.LinearMemory.FiniteWordReachability.bounded_span_eq_reachable.information_unit,
  realizationName := `Reg.D5.S3.Observer.LinearMemory.FiniteWordReachability.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w}⟩,
  objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w} ⟨registration.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,v,w}
    (fun _ p U => reachableSpan p.family U) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.LinearMemory.FiniteWordReachability,
    definition := none,
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 8,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Observer.LinearMemory.FiniteWordReachability
