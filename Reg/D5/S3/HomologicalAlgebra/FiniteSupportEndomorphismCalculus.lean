import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
import D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence

/-! Faithful full-telescope source-family attempts. Structural source recognition
is judged separately; compiled registrations do not imply declared_validated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeQuartetContraction NullFrame
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open scoped BigOperators TensorProduct
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)
namespace Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
structure ModuleParameter where
  V : Type u
  [group : AddCommGroup V]
  [space : Module ℂ V]
attribute [instance] ModuleParameter.group ModuleParameter.space
private def zeroFamily (V : Type u) [AddCommGroup V] [Module ℂ V] : Family V :=
  ⟨fun _ => 0, fun _ => 0, by intros; rfl⟩
private def oneBasis : Module.Basis (ULift.{v} Unit) ℂ (ULift.{u} ℂ) :=
  ((Module.Basis.singleton Unit ℂ).map (ULift.moduleEquiv.symm)).reindex Equiv.ulift.symm
namespace ac_add_left
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A B C : Module.End ℂ V),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (ac (A + B) C,ac A C + ac B C)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_left.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) 0 0 0
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_left.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_left.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_left.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_left.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ac_add_left
namespace ac_add_right
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A B C : Module.End ℂ V),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (ac A (B + C),ac A B + ac A C)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_right.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) 0 0 0
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_right.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_right.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_right.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_right.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_add_right.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ac_add_right
namespace ac_smul_left
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (z : ℂ) (A B : Module.End ℂ V),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (ac (z • A) B,z • ac A B)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_left.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) 0 0 0
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_left.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_left.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_left.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_left.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ac_smul_left
namespace ac_smul_right
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (z : ℂ) (A B : Module.End ℂ V),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (ac A (z • B),z • ac A B)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_right.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) 0 0 0
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_right.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_right.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_right.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_right.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.ac_smul_right.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ac_smul_right
namespace total_eq_sum
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := p.V × p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A : Family V) (v : V) (N : ℕ) (hN : A.bound v ≤ N),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (A.total v,∑ n ∈ Finset.range N, A.term n v)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_eq_sum.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) (zeroFamily _) 0 0 (by rfl)
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_eq_sum.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_eq_sum.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_eq_sum.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_eq_sum.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_eq_sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_eq_sum
namespace total_ac
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A B C : Family V)
    (hab : ∀ i j, ac (A.term i) (B.term j) = if i = j then C.term i else 0),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (ac A.total B.total,C.total)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) (zeroFamily _) (zeroFamily _) (zeroFamily _) (by intros; simp [zeroFamily, ac])
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_ac.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_ac.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_ac
namespace total_square_zero
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A : Family V)
    (haa : ∀ i j, ac (A.term i) (A.term j) = 0),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (A.total * A.total,0)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_square_zero.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) (zeroFamily _) (by intros; simp [zeroFamily, ac])
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_square_zero.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_square_zero.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_square_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_square_zero.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_square_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_square_zero
namespace total_ac_fixed
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A : Family V) (T : Module.End ℂ V)
    (hT : ∀ i, ac T (A.term i) = 0),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (ac T A.total,0)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac_fixed.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) (zeroFamily _) 0 (by intros; simp [zeroFamily, ac])
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac_fixed.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac_fixed.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_ac_fixed.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_ac_fixed.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_ac_fixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_ac_fixed
namespace total_commutes_fixed
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (A : Family V) (T : Module.End ℂ V)
    (hT : ∀ i, T * A.term i = A.term i * T),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (T * A.total,A.total * T)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_commutes_fixed.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) (zeroFamily _) 0 (by intros; simp [zeroFamily])
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_commutes_fixed.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_commutes_fixed.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.Family.total_commutes_fixed.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_commutes_fixed.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.total_commutes_fixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_commutes_fixed
namespace signed_sum
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := p.V × p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (f : ℤ → V) (hf0 : f 0 = 0) (N : ℕ)
    (hN : ∀ r, N ≤ r → f ((r : ℤ)+1) = 0 ∧ f (-((r : ℤ)+1)) = 0),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) ((∑ᶠ n, f n),∑ r ∈ Finset.range N, (f ((r : ℤ)+1) + f (-((r : ℤ)+1))))
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.signed_sum.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) (fun _ => 0) rfl 0 (by intros; exact ⟨rfl,rfl⟩)
def family : Registration arena.{u} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.signed_sum.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.signed_sum.{u}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.signed_sum.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.signed_sum.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.signed_sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end signed_sum
namespace diagonal_basis
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := p.V × p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] {I : Type v} (b : Module.Basis I ℂ V) (f : I → ℂ) (i : I),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (diagonal b f (b i),f i • b i)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis.{u,v})) ↔ arena.{u,v}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) oneBasis (fun _ => 0) ⟨()⟩
def family : Registration arena.{u,v} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis.{u,v})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis.{u,v}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end diagonal_basis
namespace diagonal_coefficient
abbrev signature : Signature.{u+1,0,0,0,0} where
  Params := ModuleParameter.{u}
  State p := ℂ × ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,0,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] {I : Type v} (b : Module.Basis I ℂ V) (f : I → ℂ) (v : V) (i : I),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (b.repr (diagonal b f v) i,f i * b.repr v i)
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient.{u,v})) ↔ arena.{u,v}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) oneBasis (fun _ => 0) 0 ⟨()⟩
def family : Registration arena.{u,v} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient.{u,v})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient.{u,v}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    let z : ℂ := 0
    let w : ℂ := 1
    have hw : z ≠ w := by norm_num [z,w]
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end diagonal_coefficient
namespace spectral_identities
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := (Module.End ℂ p.V × Module.End ℂ p.V) × (Module.End ℂ p.V × Module.End ℂ p.V) × (Module.End ℂ p.V × Module.End ℂ p.V) × (Module.End ℂ p.V × Module.End ℂ p.V) × (Module.End ℂ p.V × Module.End ℂ p.V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1.1 = x.1.2 ∧ x.2.1.1 = x.2.1.2 ∧ x.2.2.1.1 = x.2.2.1.2 ∧ x.2.2.2.1.1 = x.2.2.2.1.2 ∧ x.2.2.2.2.1 = x.2.2.2.2.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] {I : Type v} (b : Module.Basis I ℂ V) (q : I → ℕ),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) ((number b q * inverseNumber b q,1 - projectZero b q),(inverseNumber b q * number b q,1 - projectZero b q),(projectZero b q * projectZero b q,projectZero b q),(number b q * projectZero b q,0),(inverseNumber b q * projectZero b q,0))
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.spectral_identities.{u,v})) ↔ arena.{u,v}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) oneBasis (fun _ => 0)
def family : Registration arena.{u,v} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.spectral_identities.{u,v})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.spectral_identities.{u,v}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, ((z,z),(z,z),(z,z),(z,z),(z,z)), ((z,w),(z,z),(z,z),(z,z),(z,z)), ?_⟩
    intro he
    exact hw (Eq.mp he (by exact ⟨rfl,rfl,rfl,rfl,rfl⟩)).1
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.spectral_identities.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.spectral_identities.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.spectral_identities.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end spectral_identities
namespace commutes_function
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := ModuleParameter.{u}
  State p := Module.End ℂ p.V × Module.End ℂ p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] {I : Type v} (b : Module.Basis I ℂ V) (q : I → ℕ) (A : Module.End ℂ V)
    (hA : number b q * A = A * number b q) (f : ℕ → ℂ),
    obs.readout () (@ModuleParameter.mk V inferInstance inferInstance) (diagonal b (fun i => f (q i)) * A,A * diagonal b (fun i => f (q i)))
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.commutes_function.{u,v})) ↔ arena.{u,v}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u} := by
  intro h
  exact h (V := ULift.{u} ℂ) oneBasis (fun _ => 0) 0 (by simp) (fun _ => 0)
def family : Registration arena.{u,v} (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.commutes_function.{u,v})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.commutes_function.{u,v}), rejected.{u}, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let p : ModuleParameter.{u} := (@ModuleParameter.mk (ULift.{u} ℂ) inferInstance inferInstance)
    letI : Nontrivial p.V := by dsimp [p]; infer_instance
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ p.V)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.commutes_function.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.commutes_function.unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.commutes_function.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual.{u} operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end commutes_function
namespace kernel_number_iff
structure Params where
  V : Type u
  [group : AddCommGroup V]
  [space : Module ℂ V]
  I : Type v
  b : Module.Basis I ℂ V
  q : I → ℕ
attribute [instance] Params.group Params.space
abbrev signature : Signature where
  Params := Params.{u,v}
  State p := p.V
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u,v} := realize signature.{u,v}
  (fun role p x => if role then (∀ i, p.q i ≠ 0 → p.b.repr x i = 0)
    else number p.b p.q x = 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law obs := ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] {I : Type v}
    (b : Module.Basis I ℂ V) (q : I → ℕ) (x : V),
    obs.readout false (@Params.mk V inferInstance inferInstance I b q) x ↔
    obs.readout true (@Params.mk V inferInstance inferInstance I b q) x
theorem source_bridge : (type_of% (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.kernel_number_iff.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := Iff.rfl
theorem source_actual : arena.{u,v}.Law actual.{u,v} := source_bridge.mp (@D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.kernel_number_iff.{u,v})
-- Whole-family variation, slot sensitivity, actual.{u,v} observational dependence and
-- a recognized native source-selection certificate remain unfinished here.
end kernel_number_iff
end Reg.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
