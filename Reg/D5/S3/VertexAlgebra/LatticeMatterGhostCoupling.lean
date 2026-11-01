import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! Dependent-family registrations for the actual tensor coupling and Ward identities. -/

open scoped BigOperators TensorProduct
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

/-- A native tensor functional witnesses that the original state carrier is nontrivial. -/
theorem state_nontrivial (D : LatticeData) : Nontrivial (State D) := by
  classical
  let e : Carrier D →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (fun _ : Fin D.rank × ℕ => (0 : ℂ))).toLinearMap.comp
      (Finsupp.lapply (0 : Charge D))
  let f : State D →ₗ[ℂ] Fock :=
    (TensorProduct.lid ℂ Fock).toLinearMap.comp (TensorProduct.map e LinearMap.id)
  let z : State D := Finsupp.single (0 : Charge D) (1 : Oscillator D) ⊗ₜ[ℂ] vacuum
  have hz : f z = vacuum := by simp [f, z, e]
  have hn : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    have hh := congrArg (fun w : Fock => w ∅) hz
    norm_num [vacuum, ket] at hh
  exact ⟨⟨z, 0, hn⟩⟩

namespace Support
abbrev signature : Signature where
  Params := LatticeData
  State D := ℤ → _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.State D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ f => Function.HasFiniteSupport f) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D),
    R.readout () D (fun m : ℤ => summand D H m x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  have := state_nontrivial zeroLattice
  obtain ⟨z, hz⟩ := exists_ne (0 : State zeroLattice)
  refine ⟨zeroLattice, (fun _ => 0), (fun _ => z), ?_⟩
  intro h
  have hf : Function.HasFiniteSupport (fun _ : ℤ => z) :=
    Eq.mp h (by
      change (Function.support (fun _ : ℤ => (0 : State zeroLattice))).Finite
      apply (Set.finite_empty : (∅ : Set ℤ).Finite).subset
      intro m hm
      exact (hm rfl).elim)
  change (Function.support (fun _ : ℤ => z)).Finite at hf
  have he : Function.support (fun _ : ℤ => z) = Set.univ := by ext; simp [hz]
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
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
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
    coordinates := #[0]
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

namespace Apply
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, State D
  State p := State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p := T p.1 p.2.1 p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D),
    R.readout () ⟨D,H,x⟩ (∑ᶠ m : ℤ, (matterMode D H m * ghostC D (-m)) x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  have := state_nontrivial zeroLattice
  let p : signature.Params := ⟨zeroLattice,0,0⟩
  obtain ⟨y, hy⟩ := exists_ne (lhs p)
  refine ⟨p, lhs p, y, ?_⟩
  intro h
  exact hy (Eq.mp h rfl).symm
def family : Registration arena (type_of% @T_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨T_apply, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@T_apply) (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[0, 1, 2]
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
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, State D
  State p := State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p := T p.1 p.2.1 p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D)
    (s : Finset ℤ) (_ : Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ)),
    R.readout () ⟨D,H,x⟩ (∑ m ∈ s, summand D H m x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0 ∅ (by intro m hm; exact (hm (map_zero _)).elim)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  have := state_nontrivial zeroLattice
  let p : signature.Params := ⟨zeroLattice,0,0⟩
  obtain ⟨y, hy⟩ := exists_ne (lhs p)
  refine ⟨p, lhs p, y, ?_⟩
  intro h
  exact hy (Eq.mp h rfl).symm
def family : Registration arena
    (type_of% @_root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.finite_capture) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.finite_capture,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.finite_capture)
    (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[0, 1, 2]
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
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, Σ _ : Carrier D, Fock
  State p := State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p := T p.1 p.2.1 (p.2.2.1 ⊗ₜ[ℂ] p.2.2.2)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) (w : Fock) (A : ℕ) (_ : 2 ≤ A)
    (_ : _root_.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Radius A w),
    R.readout () ⟨D,H,v,w⟩ (∑ m ∈ Finset.Icc (-(A : ℤ)) (upper D H v),
      sugawaraMode D H m v ⊗ₜ[ℂ] _root_.D5.S3.Quantum.Fermionic.BcGhostFock.c (-m) w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0 0 2 (by decide)
    (by simp [_root_.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Radius])
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  have := state_nontrivial zeroLattice
  let p : signature.Params := ⟨zeroLattice,0,0,0⟩
  obtain ⟨y, hy⟩ := exists_ne (lhs p)
  refine ⟨p, lhs p, y, ?_⟩
  intro h
  exact hy (Eq.mp h rfl).symm
def family : Registration arena (type_of% @T_tmul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨T_tmul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@T_tmul) (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[0, 1, 2, 3]
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
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  T p.1 p.2.1 * ghostB p.1 p.2.2 + ghostB p.1 p.2.2 * T p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (matterMode D H r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  have := state_nontrivial zeroLattice
  let p : signature.Params := ⟨zeroLattice,0,0⟩
  obtain ⟨y, hy⟩ := exists_ne (lhs p)
  refine ⟨p, lhs p, y, ?_⟩
  intro h
  exact hy (Eq.mp h rfl).symm
def family : Registration arena (type_of% @ward_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ward_b, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ward_b) (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[0, 1, 2]
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
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  T p.1 p.2.1 * ghostC p.1 p.2.2 + ghostC p.1 p.2.2 * T p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  have := state_nontrivial zeroLattice
  let p : signature.Params := ⟨zeroLattice,0,0⟩
  obtain ⟨y, hy⟩ := exists_ne (lhs p)
  refine ⟨p, lhs p, y, ?_⟩
  intro h
  exact hy (Eq.mp h rfl).symm
def family : Registration arena (type_of% @ward_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ward_c, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ward_c) (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
    definition := none
    coordinates := #[0, 1, 2]
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
  Params := Unit
  State _ := Finset ℤ → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ p => ∃ s : Finset ℤ, p s) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (X : Finset (State D)), R.readout () () (fun s => ∀ x ∈ X,
      Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 ∅
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (fun _ => True), (fun _ => False), ?_⟩
  intro h
  have hh : ∃ _ : Finset ℤ, False := Eq.mp h ⟨∅, trivial⟩
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
