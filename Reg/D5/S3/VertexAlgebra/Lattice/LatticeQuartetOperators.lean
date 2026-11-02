import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
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
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators
namespace Witness
def hyperbolic : LatticeData where
  rank := 2
  G := !![0,1;1,0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

def frame : NullFrame hyperbolic where
  ePlus := ![1,0]
  eMinus := ![0,1]
  plus_null := by
    change (∑ i : Fin 2, ∑ j : Fin 2,
      (![1,0] : Fin 2 → ℂ) i * (((!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) *
      (![1,0] : Fin 2 → ℂ) j) = 0
    norm_num [Fin.sum_univ_two]
  minus_null := by
    change (∑ i : Fin 2, ∑ j : Fin 2,
      (![0,1] : Fin 2 → ℂ) i * (((!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) *
      (![0,1] : Fin 2 → ℂ) j) = 0
    norm_num [Fin.sum_univ_two]
  plus_minus := by
    change (∑ i : Fin 2, ∑ j : Fin 2,
      (![1,0] : Fin 2 → ℂ) i * (((!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) *
      (![0,1] : Fin 2 → ℂ) j) = 1
    norm_num [Fin.sum_univ_two]

def charge : Charge hyperbolic := ![0,1]
def basis : Module.Basis (Fin 0) ℂ frame.K := frame.transverseBasis

theorem pPlus_charge : frame.pPlus charge = 1 := by
  have hc : chargeVector charge = frame.eMinus := by
    funext i
    fin_cases i
    · change ((0 : ℤ) : ℂ) = 0; norm_num
    · change ((1 : ℤ) : ℂ) = 1; norm_num
  rw [NullFrame.pPlus, hc]
  exact frame.plus_minus


theorem pPlus_ne : frame.pPlus charge ≠ 0 := by rw [pPlus_charge]; exact one_ne_zero
end Witness
open Witness
namespace tp_tmul
abbrev signature : Signature where
  Params := LatticeData
  State p := State p × State p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (A : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock)
    (v : Carrier D) (w : Fock),
    obs.readout () D (tp A G (v ⊗ₜ w),A v ⊗ₜ G w)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_tmul)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (D := zeroLattice) 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_tmul)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_tmul), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (State p)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_tmul) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.tp_tmul.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.tp_tmul.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end tp_tmul
namespace tp_ac
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (A B : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock),
    obs.readout () D (ac (tp A G) (tp B H),tp (A * B - B * A) (G * H) + tp (B * A) (G * H + H * G))
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_ac)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (D := zeroLattice) 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_ac)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_ac), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.tp_ac) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.tp_ac.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.tp_ac.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end tp_ac
namespace unscaled_contraction
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) ,
    obs.readout () D (ac (unscaledD F) (unscaledR F),M F)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.unscaled_contraction)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.unscaled_contraction)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.unscaled_contraction), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.unscaled_contraction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.unscaled_contraction.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.unscaled_contraction.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end unscaled_contraction
namespace original_contraction
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D) (hp : F.pPlus p ≠ 0),
    obs.readout () D (d0 F p * R F p + R F p * d0 F p,M F)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.original_contraction)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame charge pPlus_ne
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.original_contraction)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.original_contraction), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.original_contraction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.original_contraction.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.original_contraction.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_contraction
namespace d0_square
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D),
    obs.readout () D (d0 F p * d0 F p,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_square)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_square)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_square), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_square) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.d0_square.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.d0_square.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end d0_square
namespace R_square
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D),
    obs.readout () D (R F p * R F p,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_square)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_square)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_square), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_square) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.R_square.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.R_square.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end R_square
namespace M_commutes_d0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D),
    obs.readout () D (M F * d0 F p,d0 F p * M F)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_d0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_d0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_d0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_d0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.M_commutes_d0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.M_commutes_d0.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end M_commutes_d0
namespace M_commutes_R
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D),
    obs.readout () D (M F * R F p,R F p * M F)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_R)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_R)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_R), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_commutes_R) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.M_commutes_R.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.M_commutes_R.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end M_commutes_R
namespace signed_support
abbrev signature : Signature where
  Params := LatticeData
  State p := (ℤ → State p) × (ℤ → State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => (Function.support x.1).Finite ∧ (Function.support x.2).Finite) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (v : State D),
    obs.readout () D ((fun n : ℤ => if n=0 then 0 else dm F n v), (fun n : ℤ => if n=0 then 0 else ((n.natAbs : ℂ)⁻¹) • rr F n v))
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.signed_support)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.signed_support)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.signed_support), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    obtain ⟨z,hz⟩ := exists_ne (0 : State zeroLattice)
    refine ⟨zeroLattice, (0,0), ((fun _ => z),0), ?_⟩
    intro he
    have h0 : actual.readout role zeroLattice (0,0) := by
      constructor <;> simp [Function.support]
    have hf : (Function.support (fun _ : ℤ => z)).Finite := (Eq.mp he h0).1
    have hu : Function.support (fun _ : ℤ => z) = Set.univ := by ext; simp [hz]
    rw [hu] at hf
    exact Set.infinite_univ hf
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.signed_support) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.signed_support.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.signed_support.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end signed_support
namespace d0_signed_formula
abbrev signature : Signature where
  Params := LatticeData
  State p := State p × State p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D) (v : State D),
    obs.readout () D (d0 F p v,F.pPlus p •
      ∑ᶠ n : ℤ, if n=0 then 0 else tp (a F.eMinus n) (c (-n)) v)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_signed_formula)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_signed_formula)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_signed_formula), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (State p)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_signed_formula) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.d0_signed_formula.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.d0_signed_formula.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end d0_signed_formula
namespace R_signed_formula
abbrev signature : Signature where
  Params := LatticeData
  State p := State p × State p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D) (v : State D),
    obs.readout () D (R F p v,(F.pPlus p)⁻¹ • ∑ᶠ n : ℤ, if n=0 then 0 else
      ((n.natAbs : ℂ)⁻¹) • tp (a F.ePlus (-n)) (b n) v)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_signed_formula)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_signed_formula)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_signed_formula), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (State p)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.R_signed_formula) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.R_signed_formula.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.R_signed_formula.family
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
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end R_signed_formula
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators
