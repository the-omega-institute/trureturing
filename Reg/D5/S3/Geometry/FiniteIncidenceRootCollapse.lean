import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteIncidenceRootCollapse

/- SOURCE-ONLY REPAIR; UNCOMPILED.
The unchanged original mem_rootK, with INDEPENDENT universes u,v, is the binding.
Only its literal RHS atom s.Nonempty is observed; s is the original Finset I
state operand. The sole coordinate is the original I : Type u. J, relation,
incidence state and dictionaries remain in the original law, never in Params.
Source usage retains DecidableEq I for finset subtraction; it does not use the
section's Fintype I, Fintype J or DecidableEq J. The exact compiled telescope
and all compiled source checks remain pending; none has been executed here. -/

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteIncidenceRootCollapse

namespace Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse
universe u v

abbrev signature : Signature where
  Params := Type u
  State I := Finset I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Symbolic predicate reflection matches CompiledSourceScope.mkDecide. -/
def actual : Realization signature.{u} :=
  realize signature
    (fun _ I s => @Decidable.decide (s.Nonempty)
      (Classical.propDecidable (s.Nonempty)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Preserve the complete original RHS existential and independent I,J types. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} {J : Type v} [dvI : DecidableEq I]
    (ρ : I → J → Prop) (q : State ρ) (s : Finset I),
    s ∈ rootK ρ q ↔
      (R.readout () I s = true) ∧
        ∃ b ∈ q.rows, s ⊆ q.active \ rowNeighborhood ρ q b

private theorem actual_eq_true (I : Type u) (s : Finset I) :
    actual.{u}.readout () I s = true ↔ s.Nonempty := by
  classical
  simp [actual, realize]

private theorem bridge :
    (type_of% (@mem_rootK.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h I J dvI ρ q s
    simpa only [actual_eq_true] using (@h I J dvI ρ q s)
  · intro h I J dvI ρ q s
    simpa only [actual_eq_true] using (@h I J dvI ρ q s)

private theorem source_law : arena.{u,v}.Law actual :=
  bridge.mp (@mem_rootK.{u,v})

/- I and J are lifted independently, with a false relation, singleton active
and rows, and a genuine nonempty singleton face of the ORIGINAL rootK. -/
private abbrev testI : Type u := ULift.{u} Unit
private abbrev testJ : Type v := ULift.{v} Unit

private abbrev testRelation : testI.{u} → testJ.{v} → Prop :=
  fun _ _ => False

private abbrev testState : State testRelation.{u,v} where
  active := {⟨()⟩}
  rows := {⟨()⟩}

private theorem test_face :
    ({(⟨()⟩ : testI.{u})} : Finset testI.{u}) ∈
      rootK testRelation.{u,v} testState := by
  apply (mem_rootK testRelation testState _).mpr
  refine ⟨Finset.singleton_nonempty _, (⟨()⟩ : testJ.{v}), ?_, ?_⟩
  · simp [testState]
  · intro x hx
    refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
    intro hnb
    exact ((mem_rowNeighborhood testRelation testState x (⟨()⟩ : testJ.{v})).mp hnb).2

private theorem test_present :
    actual.{u}.readout () testI.{u} {(⟨()⟩ : testI.{u})} = true := by
  exact (actual_eq_true _ _).mpr (Finset.singleton_nonempty _)

private theorem test_absent :
    actual.{u}.readout () testI.{u} ∅ = false := by
  simp [actual, realize]

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := @h testI.{u} testJ.{v} (inferInstance : DecidableEq testI.{u})
    testRelation.{u,v} testState {(⟨()⟩ : testI.{u})}
  have hf := (hh.mp test_face).1
  change (false : Bool) = true at hf
  cases hf

private theorem variation : Variation arena.{u,v} actual :=
  ⟨source_law, rejected, rejected_law⟩

private theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

/-- Empty and singleton are different observed states in the SAME I fiber. -/
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨testI.{u}, ∅, {(⟨()⟩ : testI.{u})}, ?_⟩
  intro he
  have hf : (false : Bool) = true :=
    test_absent.symm.trans (he.trans test_present)
  cases hf

def family : Registration arena.{u,v} (type_of% (@mem_rootK.{u,v})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_rootK.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ I s => @Decidable.decide (s.Nonempty)
      (Classical.propDecidable (s.Nonempty)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/- sourceSelection = none is a remaining obligation, never an audit receipt.
Semantic occurrence: the first RHS conjunction atom s.Nonempty of mem_rootK.
State operand: that predicate's actual original s : Finset I. Raw coordinate:
the original I : Type u alone; J : Type v remains independent in the full law.
Params is exactly Type u; no record, dictionary, proof or incidence-state echo.
Pending REAL compiled evidence: original owner, independent universe ordering,
complete used telescope and binder modes; occurrence path, lexical coordinate
ordinal and operand path; resolveOriginal and resolve; dependency closure and
inverse projection; field/output/readout shape checks, exact explicit decision
dictionary and complete original source reconstruction. No numeric selector or
compiled path is supplied. Kernel, axiom closure, source audits, independent
review, geometry/native reports and all delivery obligations remain pending. -/

end Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse
