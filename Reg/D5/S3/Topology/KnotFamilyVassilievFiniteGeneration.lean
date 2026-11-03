import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
import Reg.Support.DependentFamily
import Reg.Support.PolynomialSubalgebra

/-! Source-bound observations for finite generation of polynomial subalgebras. -/

namespace Reg.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration

open _root_.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PolynomialSubalgebra (X_not_mem_bot)

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Result

/-- The parameter is the indexing type; the state is the complete polynomial family. -/
abbrev signature : Signature where
  Params := Type
  State ι := ι → Polynomial ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Subalgebra ℚ (Polynomial ℚ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => Algebra.adjoin ℚ (Set.range p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (ι : Type) (p : ι → Polynomial ℚ), ∃ s : Finset ι,
    Algebra.adjoin ℚ (p '' (s : Set ι)) = r.readout () ι p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs⟩ := h Empty Empty.elim
  have hz : Algebra.adjoin ℚ (Empty.elim '' (s : Set Empty)) ≤
      (⊥ : Subalgebra ℚ (Polynomial ℚ)) := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, _, _⟩
    exact nomatch i
  change Algebra.adjoin ℚ (Empty.elim '' (s : Set Empty)) = ⊤ at hs
  rw [hs] at hz
  exact X_not_mem_bot (hz Algebra.mem_top)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨Unit, (fun _ => 0), (fun _ => Polynomial.X), ?_⟩
  change Algebra.adjoin ℚ (Set.range (fun _ : Unit => (0 : Polynomial ℚ))) ≠
    Algebra.adjoin ℚ (Set.range (fun _ : Unit => (Polynomial.X : Polynomial ℚ)))
  intro h
  have hz : Algebra.adjoin ℚ (Set.range (fun _ : Unit => (0 : Polynomial ℚ))) ≤
      (⊥ : Subalgebra ℚ (Polynomial ℚ)) := by
    apply Algebra.adjoin_le
    rintro _ ⟨_, rfl⟩
    exact zero_mem _
  rw [h] at hz
  exact X_not_mem_bot (hz (Algebra.subset_adjoin ⟨(), rfl⟩))

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.result)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.Result.unit
  realizationName :=
    `Reg.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.Result.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ p => Algebra.adjoin ℚ (Set.range p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
    definition := some {
      owner := `D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
      name := `D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Result

namespace SubalgebraFG

universe u

/-- The full field data is retained at the source theorem's universe. -/
abbrev FieldParameters := Σ k : Type u, Field k

abbrev signature : Signature where
  Params := FieldParameters.{u}
  State P := letI := P.2; Subalgebra P.1 (Polynomial P.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := letI := P.2; Set (Polynomial P.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ a => (a : Set _)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {k : Type u} [inst : Field k] (a : Subalgebra k (Polynomial k)),
    ∃ s : Finset (Polynomial k),
      (Algebra.adjoin k (s : Set (Polynomial k)) : Set (Polynomial k)) =
        r.readout () ⟨k, inst⟩ a

theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  obtain ⟨s, hs⟩ := @h (ULift.{u} ℚ) inferInstance ⊥
  have hz : (0 : Polynomial (ULift.{u} ℚ)) ∈
      (Algebra.adjoin (ULift.{u} ℚ) (s : Set (Polynomial (ULift.{u} ℚ))) :
        Set (Polynomial (ULift.{u} ℚ))) := zero_mem _
  change (_ : Set (Polynomial (ULift.{u} ℚ))) = ∅ at hs
  rw [hs] at hz
  exact hz

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} ℚ, inferInstance⟩, ⊥, ⊤, ?_⟩
  intro h
  have he : (⊥ : Subalgebra (ULift.{u} ℚ) (Polynomial (ULift.{u} ℚ))) = ⊤ :=
    SetLike.coe_injective h
  apply X_not_mem_bot (k := ULift.{u} ℚ)
  rw [he]
  exact Algebra.mem_top

def source_registration : Registration arena.{u}
    (∀ {k : Type u} [Field k] (a : Subalgebra k (Polynomial k)), a.FG) where
  actual := actual
  bridge := by
    constructor
    · intro h k inst a
      obtain ⟨s, hs⟩ := h a
      exact ⟨s, congrArg SetLike.coe hs⟩
    · intro h k inst a
      obtain ⟨s, hs⟩ := @h k inst a
      exact ⟨s, SetLike.coe_injective hs⟩
  variation := ⟨by
    intro k inst a
    obtain ⟨s, hs⟩ := subalgebra_fg a
    exact ⟨s, congrArg SetLike.coe hs⟩, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.subalgebra_fg.{u})
      (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.SubalgebraFG.unit
  realizationName :=
    `Reg.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.SubalgebraFG.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ a => (a : Set _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SubalgebraFG

#print axioms Result.source_registration
#print axioms Result.registration
#print axioms SubalgebraFG.source_registration
#print axioms SubalgebraFG.registration

end
end Reg.D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
