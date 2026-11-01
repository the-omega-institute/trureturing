import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

open scoped BigOperators TensorProduct
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

namespace Support

/-- The source observation is finite support of a family in a pointed carrier. -/
abbrev signature : Signature where
  Params := Σ E : Type, Zero E
  State p := ℤ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p f => @Function.HasFiniteSupport ℤ p.1 p.2 f) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D),
    R.readout () ⟨State D, inferInstance⟩ (fun m : ℤ => summand D H m x)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨ℂ, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hf : Function.HasFiniteSupport (fun _ : ℤ => (1 : ℂ)) :=
    Eq.mp h (by simp [Function.HasFiniteSupport, Function.support])
  change (Function.support (fun _ : ℤ => (1 : ℂ))).Finite at hf
  have he : Function.support (fun _ : ℤ => (1 : ℂ)) = Set.univ := by ext; simp
  rw [he] at hf
  exact Set.infinite_univ hf

def family : Registration arena (type_of% @summand_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨summand_finite, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence

def support_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summand_finite) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Support.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace Equality
abbrev signature : Signature where
  Params := Σ E : Type, E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => p.2 = x) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨ℕ, 0⟩, 0, 1, ?_⟩
  intro h
  change (0 = 0 : Prop) = (0 = 1 : Prop) at h
  exact Nat.zero_ne_one (Eq.mp h rfl)
end Equality

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

namespace Apply
abbrev arena : Arena where
  signature := Equality.signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D),
    R.readout () ⟨State D, T D H x⟩
      (∑ᶠ m : ℤ, (matterMode D H m * ghostC D (-m)) x)
private theorem rejected_law : ¬ arena.Law Equality.rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @T_apply) where
  actual := Equality.actual
  bridge := Iff.rfl
  variation := ⟨T_apply, Equality.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Equality.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Equality.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@T_apply) (Realization Equality.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Apply.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Apply.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Equality.signature Equality.actual.readout Equality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Apply

namespace Capture
abbrev arena : Arena where
  signature := Equality.signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (x : State D) (s : Finset ℤ)
    (_ : Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ)),
    R.readout () ⟨State D, T D H x⟩ (∑ m ∈ s, summand D H m x)
private theorem rejected_law : ¬ arena.Law Equality.rejected := by
  intro h
  exact h zeroLattice 0 0 ∅ (by
    intro m hm
    exact (hm (map_zero _)).elim)
def family : Registration arena (type_of% @finite_capture) where
  actual := Equality.actual
  bridge := Iff.rfl
  variation := ⟨finite_capture, Equality.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Equality.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Equality.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_capture) (Realization Equality.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Capture.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Capture.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Equality.signature Equality.actual.readout Equality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Capture

namespace Tensor
abbrev arena : Arena where
  signature := Equality.signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) (w : _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock.Fock)
    (A : ℕ) (_ : 2 ≤ A)
    (_ : _root_.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Radius A w),
    R.readout () ⟨State D, T D H (v ⊗ₜ[ℂ] w)⟩
      (∑ m ∈ Finset.Icc (-(A : ℤ)) (upper D H v),
        _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents.sugawaraMode D H m v ⊗ₜ[ℂ]
          _root_.D5.S3.Quantum.Fermionic.BcGhostFock.c (-m) w)
private theorem rejected_law : ¬ arena.Law Equality.rejected := by
  intro h
  exact h zeroLattice 0 0 0 2 (by decide) (by
    simp [_root_.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Radius])
def family : Registration arena (type_of% @T_tmul) where
  actual := Equality.actual
  bridge := Iff.rfl
  variation := ⟨T_tmul, Equality.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Equality.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Equality.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@T_tmul) (Realization Equality.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Tensor.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.Tensor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Equality.signature Equality.actual.readout Equality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Tensor

namespace B
abbrev arena : Arena where
  signature := Equality.signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨Module.End ℂ (State D), T D H * ghostB D r + ghostB D r * T D H⟩
      (matterMode D H r)
private theorem rejected_law : ¬ arena.Law Equality.rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @ward_b) where
  actual := Equality.actual
  bridge := Iff.rfl
  variation := ⟨ward_b, Equality.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Equality.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Equality.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ward_b) (Realization Equality.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.B.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.B.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Equality.signature Equality.actual.readout Equality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end B

namespace C
abbrev arena : Arena where
  signature := Equality.signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨Module.End ℂ (State D), T D H * ghostC D r + ghostC D r * T D H⟩ 0
private theorem rejected_law : ¬ arena.Law Equality.rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @ward_c) where
  actual := Equality.actual
  bridge := Iff.rfl
  variation := ⟨ward_c, Equality.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Equality.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Equality.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ward_c) (Realization Equality.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.C.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.C.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Equality.signature Equality.actual.readout Equality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end C

namespace CaptureFamily
abbrev signature : Signature where
  Params := Type
  State E := E → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ E p => ∃ x : E, p x) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (X : Finset (State D)), R.readout () (Finset ℤ) (fun s => ∀ x ∈ X,
      Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 ∅
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨Unit, (fun _ => True), (fun _ => False), ?_⟩
  intro h
  have hh : ∃ _ : Unit, False := Eq.mp h ⟨(), trivial⟩
  exact hh.choose_spec
def family : Registration arena (type_of% @common_capture) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_capture, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_capture) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.CaptureFamily.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.CaptureFamily.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CaptureFamily

end Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
