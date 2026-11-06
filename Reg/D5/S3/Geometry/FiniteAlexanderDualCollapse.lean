/- UNCOMPILED REG SOURCE ATTEMPT. No declared_validated or binding evidence.
   One faithful complete-telescope family is attempted here. Other targets and
   concrete missing encodings are listed in audit-targets.json. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteAlexanderDualCollapse

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteAlexanderDualCollapse
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse

namespace Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.DualAugmented
universe u

/-- The complete source telescope except the varied face s. -/
structure Parameters where
  V : Type u
  decidableVertices : DecidableEq V
  W : Finset V
  K : PreAbstractSimplicialComplex V
  proper : Proper W K

attribute [instance] Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The original augmented dual-face observation, not the truth of the whole theorem. -/
def actual : Realization signature.{u} :=
  realize signature (fun _ p s => AugmentedFace (dual p.W p.K) s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ s : Finset p.V,
    R.readout () p s ↔ s ⊆ p.W ∧ ¬ AugmentedFace p.K (p.W \ s)

private theorem bridge : (type_of% (@dual_augmented.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p s
    exact h p.W p.K p.proper s
  · intro h V dv W K hp s
    exact h ⟨V, dv, W, K, hp⟩ s

/-- Whole-family variation and dependence use one supported proper fiber; other
fibers, including all ghost patterns and the impossible empty proper ground,
remain in the original theorem's scope. -/
private def testParameters : Parameters.{u} where
  V := ULift.{u} Bool
  decidableVertices := inferInstance
  W := {⟨false⟩}
  K := ⊥
  proper := by
    intro h
    rcases h with he | hm
    · exact (Finset.singleton_ne_empty _) he
    · exact hm

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hr : (∅ : Finset testParameters.{u}.V) ⊆ testParameters.W ∧
      ¬ AugmentedFace testParameters.K (testParameters.W \ ∅) :=
    ⟨Finset.empty_subset _, by simpa using testParameters.proper⟩
  exact (h testParameters ∅).mpr hr

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters, ∅, ({⟨true⟩} : Finset testParameters.V), ?_⟩
  intro h
  have he : actual.readout i testParameters ∅ := Or.inl rfl
  rw [h] at he
  change AugmentedFace (dual testParameters.W testParameters.K) {⟨true⟩} at he
  rcases he with he | hm
  · exact (Finset.singleton_ne_empty _) he
  · have hw := hm.2.1 (Finset.mem_singleton_self (⟨true⟩ : testParameters.V))
    simpa [testParameters] using hw

def family : Registration arena.{u} (type_of% (@dual_augmented.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@dual_augmented.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

/-- The source-selection path is an uncompiled syntactic proposal. Only a native
source-bound report can establish exact occurrence ties and enrollment acceptance. -/
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
    (fun _ p s => AugmentedFace (dual p.W p.K) s) (fun e => nomatch e))
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

theorem exact_source : sourceScope :=
  @_root_.D5.S3.Geometry.FiniteAlexanderDualCollapse.Certificate.pContraction_fixed_apex.{u}

end Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.PContractionFixedApex
