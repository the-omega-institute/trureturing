import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian

/-! Equality-operand audit proposals using the pinned Ward pattern.
The varying state is the exact scalar right operand of equality, not a replacement
of the original tensor carrier. Dependence below is scalar equality dependence;
it asserts neither a nonzero charge nor content/escape-witness admission.
No compiled registration or declared_validated status is claimed. -/

open scoped BigOperators TensorProduct
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeBRST
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostHermitian
open _root_.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice)

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian

namespace Hmg_zero_left
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (0 : State p.1) p.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (y : State D),
    R.readout () ⟨D,y⟩ (0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0
def family : Registration arena (type_of% @Hmg_zero_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_zero_left, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_zero_left) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_zero_left.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_zero_left.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_zero_left

namespace Hmg_zero_right
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg p.2 0
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (x : State D),
    R.readout () ⟨D,x⟩ (0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0
def family : Registration arena (type_of% @Hmg_zero_right) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_zero_right, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_zero_right) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_zero_right.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_zero_right.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_zero_right

namespace Hmg_add_left
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ x : State D, Σ z : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (p.2.1 + p.2.2.1) p.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (x : State D) (z : State D) (y : State D),
    R.readout () ⟨D,x,z,y⟩ (Hmg x y + Hmg z y)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0
def family : Registration arena (type_of% @Hmg_add_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_add_left, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_add_left) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_add_left.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_add_left.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_add_left

namespace Hmg_smul_left
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ a : ℂ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (p.2.1 • p.2.2.1) p.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (a : ℂ) (x : State D) (y : State D),
    R.readout () ⟨D,a,x,y⟩ (star a * Hmg x y)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0
def family : Registration arena (type_of% @Hmg_smul_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_smul_left, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_smul_left) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_smul_left.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_smul_left.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_smul_left

namespace Hmg_hermitian
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg p.2.1 p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (x : State D) (y : State D),
    R.readout () ⟨D,x,y⟩ (star (Hmg y x))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0
def family : Registration arena (type_of% @Hmg_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_hermitian, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_hermitian) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_hermitian.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_hermitian.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_hermitian

namespace Hmg_add_right
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ x : State D, Σ y : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg p.2.1 (p.2.2.1 + p.2.2.2)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (x : State D) (y : State D) (z : State D),
    R.readout () ⟨D,x,y,z⟩ (Hmg x y + Hmg x z)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0
def family : Registration arena (type_of% @Hmg_add_right) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_add_right, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_add_right) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_add_right.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_add_right.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_add_right

namespace Hmg_smul_right
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ a : ℂ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg p.2.2.1 (p.2.1 • p.2.2.2)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (a : ℂ) (x : State D) (y : State D),
    R.readout () ⟨D,a,x,y⟩ (a * Hmg x y)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0
def family : Registration arena (type_of% @Hmg_smul_right) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_smul_right, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_smul_right) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_smul_right.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_smul_right.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_smul_right

namespace Hmg_tmul
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ v : Carrier D, Σ w : Carrier D, Σ u : Fock, Fock), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (p.2.1 ⊗ₜ[ℂ] p.2.2.2.1) (p.2.2.1 ⊗ₜ[ℂ] p.2.2.2.2)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (v : Carrier D) (w : Carrier D) (u : Fock) (z : Fock),
    R.readout () ⟨D,v,w,u,z⟩ (Hm v w * Hg u z)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0 0
def family : Registration arena (type_of% @Hmg_tmul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_tmul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_tmul) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_tmul.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_tmul.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_tmul

namespace Hmg_ghostB
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ m : ℤ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (ghostB p.1 p.2.1 p.2.2.1) p.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (m : ℤ) (x : State D) (y : State D),
    R.readout () ⟨D,m,x,y⟩ (Hmg x (ghostB D (-m) y))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0
def family : Registration arena (type_of% @Hmg_ghostB) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_ghostB, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_ghostB) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_ghostB.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_ghostB.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_ghostB

namespace Hmg_ghostC
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ m : ℤ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (ghostC p.1 p.2.1 p.2.2.1) p.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (m : ℤ) (x : State D) (y : State D),
    R.readout () ⟨D,m,x,y⟩ (Hmg x (ghostC D (-m) y))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0 0
def family : Registration arena (type_of% @Hmg_ghostC) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_ghostC, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_ghostC) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_ghostC.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_ghostC.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_ghostC

namespace Hmg_ghostCharge
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (ghostCharge p.1 p.2.1) p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (x : State D) (y : State D),
    R.readout () ⟨D,x,y⟩ (Hmg x (ghostCharge D y))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 0
def family : Registration arena (type_of% @Hmg_ghostCharge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_ghostCharge, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_ghostCharge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_ghostCharge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_ghostCharge.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_ghostCharge

namespace Hmg_matterMode
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ H : Matrix (Fin D.rank) (Fin D.rank) ℂ, Σ m : ℤ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (matterMode p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m : ℤ) (x : State D) (y : State D),
    R.readout () ⟨D,H,m,x,y⟩ (Hmg x (matterMode D H (-m) y))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0 0 0
def family : Registration arena (type_of% @Hmg_matterMode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_matterMode, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_matterMode) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_matterMode.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_matterMode.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 4, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_matterMode

namespace Hmg_T
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ H : Matrix (Fin D.rank) (Fin D.rank) ℂ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (T p.1 p.2.1 p.2.2.1) p.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : State D) (y : State D),
    R.readout () ⟨D,H,x,y⟩ (Hmg x (T D H y))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0 0
def family : Registration arena (type_of% @Hmg_T) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_T, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_T) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_T.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_T.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 4, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_T

namespace Hmg_totalCharge
abbrev signature : Signature := {
  Params := (Σ D : LatticeData, Σ H : Matrix (Fin D.rank) (Fin D.rank) ℂ, Σ x : State D, State D), State := fun _ => ℂ,
  Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance,
  Output := fun _ _ => Prop, Anchor := Empty, finiteAnchor := inferInstance }
def lhs (p : signature.Params) : ℂ := Hmg (totalCharge p.1 p.2.1 p.2.2.1) p.2.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : State D) (y : State D),
    R.readout () ⟨D,H,x,y⟩ (Hmg x (totalCharge D H y))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h; exact h (D := zeroLattice) 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0 0
def family : Registration arena (type_of% @Hmg_totalCharge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Hmg_totalCharge, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role; let p : signature.Params := ⟨zeroLattice, 0, 0, 0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h; exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Hmg_totalCharge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_totalCharge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian.Hmg_totalCharge.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian, definition := none,
    coordinates := #[0, 1, 4, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hmg_totalCharge

end Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
