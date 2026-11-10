/- UNCOMPILED REG SOURCE ATTEMPT. No declared_validated or binding evidence.
   One faithful complete-telescope family is attempted here. Other targets and
   concrete missing encodings are listed in audit-targets.json. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteAlexanderDualCollapse

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteAlexanderDualCollapse
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse

namespace Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.DualAugmented
universe u

/- Observe only the literal RHS subset predicate of @dual_augmented.{u}.
The coordinates are its original V and W, and its original s is the state.
The source's unused section Fintype does not enter this theorem's telescope.
No dictionary, complex or properness proof is an observation coordinate.
Raw compiled selectors, fields/shapes, reconstruction and audits are pending. -/
abbrev signature : Signature where
  Params := Σ V : Type u, Finset V
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p s => @Decidable.decide (s ⊆ p.2) (Classical.propDecidable (s ⊆ p.2)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

-- Keep every original theorem binder, and replace only the RHS s ⊆ W.
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (W : Finset V) (K : PreAbstractSimplicialComplex V)
    (hp : Proper W K) (s : Finset V),
    AugmentedFace (dual W K) s ↔
      R.readout () ⟨V, W⟩ s = true ∧ ¬ AugmentedFace K (W \ s)

-- Reflection applies to the explicitly supplied decision, without synthesis.
private theorem decide_true_iff (p : Prop) (d : Decidable p) :
    @Decidable.decide p d = true ↔ p := by
  cases d with
  | isTrue hp =>
    constructor
    · intro _
      exact hp
    · intro _
      rfl
  | isFalse hn =>
    constructor
    · intro h
      cases h
    · intro hp
      exact (hn hp).elim

private theorem actual_true_iff {V : Type u} (W s : Finset V) :
    actual.readout () ⟨V, W⟩ s = true ↔ s ⊆ W := by
  exact decide_true_iff (s ⊆ W) (Classical.propDecidable (s ⊆ W))

private theorem bridge : (type_of% (@dual_augmented.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv W K hp s
    constructor
    · intro hs
      rcases (@h V fv dv W K hp s).mp hs with ⟨hsW, hn⟩
      exact ⟨(actual_true_iff W s).mpr hsW, hn⟩
    · rintro ⟨hsW, hn⟩
      exact (@h V fv dv W K hp s).mpr ⟨(actual_true_iff W s).mp hsW, hn⟩
  · intro h V fv dv W K hp s
    constructor
    · intro hs
      rcases (@h V fv dv W K hp s).mp hs with ⟨hsW, hn⟩
      exact ⟨(actual_true_iff W s).mp hsW, hn⟩
    · rintro ⟨hsW, hn⟩
      exact (@h V fv dv W K hp s).mpr ⟨(actual_true_iff W s).mpr hsW, hn⟩

private theorem source_law : arena.{u}.Law actual := bridge.mp (@dual_augmented.{u})

-- Reuse the genuine proper source fiber; the universal Law is not specialized.
private def testGround : Finset (ULift.{u} Bool) := {ULift.up false}

private def testComplex : PreAbstractSimplicialComplex (ULift.{u} Bool) := ⊥

private theorem testGround_nonempty : testGround.{u}.Nonempty := by
  exact ⟨ULift.up false, Finset.mem_singleton_self _⟩

private theorem testProper : Proper testGround.{u} testComplex.{u} := by
  intro h
  rcases h with he | hm
  · exact testGround_nonempty.ne_empty he
  · exact hm

private theorem test_empty_face :
    AugmentedFace (dual testGround.{u} testComplex.{u})
      (∅ : Finset (ULift.{u} Bool)) := Or.inl rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Bool)
    (inferInstance : Fintype (ULift.{u} Bool))
    (inferInstance : DecidableEq (ULift.{u} Bool))
    testGround.{u} testComplex.{u} testProper (∅ : Finset (ULift.{u} Bool))
  have hfalse := (hh.mp test_empty_face).1
  change (false : Bool) = true at hfalse
  cases hfalse

private theorem actual_empty :
    actual.readout () ⟨ULift.{u} Bool, testGround.{u}⟩ ∅ = true :=
  (actual_true_iff testGround ∅).mpr (Finset.empty_subset _)

private theorem outside_not_subset :
    ¬ ({ULift.up true} : Finset (ULift.{u} Bool)) ⊆ testGround.{u} := by
  intro h
  have hm := h (Finset.mem_singleton_self (ULift.up true : ULift.{u} Bool))
  have he : (ULift.up true : ULift.{u} Bool) = ULift.up false :=
    Finset.mem_singleton.mp hm
  have hb : (true : Bool) = false := congrArg ULift.down he
  cases hb

private theorem actual_outside :
    actual.readout () ⟨ULift.{u} Bool, testGround.{u}⟩ {ULift.up true} = false := by
  cases he : actual.readout () ⟨ULift.{u} Bool, testGround.{u}⟩ {ULift.up true} with
  | false => rfl
  | true =>
    exact (outside_not_subset ((actual_true_iff testGround {ULift.up true}).mp he)).elim

private theorem actual_nonconstant :
    actual.readout () ⟨ULift.{u} Bool, testGround.{u}⟩ ∅ ≠
      actual.readout () ⟨ULift.{u} Bool, testGround.{u}⟩ {ULift.up true} := by
  rw [actual_empty, actual_outside]
  intro he
  cases he

private theorem variation : Variation arena.{u} actual :=
  ⟨source_law, rejected, rejected_law⟩

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro role
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro other hne
    exact (hne (Subsingleton.elim other role)).elim
  · intro anchor
    exact nomatch anchor

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  cases role
  exact ⟨⟨ULift.{u} Bool, testGround.{u}⟩, ∅, {ULift.up true}, actual_nonconstant⟩

def family : Registration arena.{u} (type_of% (@dual_augmented.{u})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

-- No new compiled selector evidence is supplied. Select only the semantic RHS
-- s ⊆ W and its original s operand once native raw evidence becomes available.
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dual_augmented.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.DualAugmented.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.DualAugmented.family
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
    (fun _ p s => @Decidable.decide (s ⊆ p.2) (Classical.propDecidable (s ⊆ p.2)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.DualAugmented


/-!
The new fixed-apex theorem has an exact Reg source scope below. This is a
faithful source attempt only: no dependent-family realization, enrolled
readout, variation/sensitivity witness, source-selection receipt or
`declared_validated` status is claimed. The theorem itself is the only source
of the equation; the Reg mirror does not add a desired conclusion or a second
contraction.
-/
namespace Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.PContractionFixedApex
universe u

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Geometry.FiniteAlexanderDualCollapse.Certificate.pContraction_fixed_apex.{u})

theorem exact_source : sourceScope.{u} :=
  @_root_.D5.S3.Geometry.FiniteAlexanderDualCollapse.Certificate.pContraction_fixed_apex.{u}

end Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.PContractionFixedApex
