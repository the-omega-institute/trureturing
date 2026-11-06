import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.OriginalCriticalBRST
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyGhostGrading

/-! Full-telescope audit attempts for the integer decomposition and lift.
The typed family proofs do not provide compiler-bound source reconstruction.
Absent sourceSelection is an explicitly unfinished audit, not validation. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (State)
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyField (cycles Cohomology classOf)
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.OriginalCriticalBRST
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading

namespace Finite
abbrev signature : Signature where
  Params := Σ x : Input, cycles x.D x.H
  State x := Space x.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (x : signature.Params) : signature.State x :=
  ∑ g ∈ stateDegrees x.1.D (x.2 : State x.1.D),
    classOf x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH
      (cycleProject x.1.D x.1.H g x.2)
def actual : Realization signature := realize signature
  (fun _ x y => lhs x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (z : cycles D H), R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,z⟩
      (classOf D H h26 hHG hGH z)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0
def family : Registration arena (type_of% @finite_class_decomposition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_class_decomposition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨witness,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_class_decomposition) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.Finite.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.Finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => lhs x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Finite

namespace Internal
abbrev signature : Signature where
  Params := Input
  State x := ℤ → Submodule ℂ (Space x)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ f => DirectSum.IsInternal f) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1),
    R.readout () ⟨D,H,h26,hHG,hGH⟩ (grade D H h26 hHG hGH)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH
def family : Registration arena (type_of% @grades_internal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨grades_internal, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    refine ⟨witness, grade witness.D witness.H witness.h26 witness.hHG witness.hGH,
      (fun _ => ⊥), ?_⟩
    intro he
    have hi : DirectSum.IsInternal (fun _ : ℤ => (⊥ : Submodule ℂ (Space witness))) :=
      Eq.mp he (grades_internal witness.D witness.H witness.h26 witness.hHG witness.hGH)
    have ht := hi.submodule_iSup_eq_top
    simp at ht

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@grades_internal) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.Internal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.Internal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => DirectSum.IsInternal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Internal

namespace SameClass
abbrev signature : Signature where
  Params := Σ x : Input, Σ g : ℤ,
    {z : cycles x.D x.H // classOf x.D x.H x.h26 x.hHG x.hGH z ∈
      grade x.D x.H x.h26 x.hHG x.hGH g}
  State x := Space x.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs : (x : signature.Params) → signature.State x
  | ⟨p, g, z, _⟩ => classOf p.D p.H p.h26 p.hHG p.hGH
      (cycleProject p.D p.H g z)
def actual : Realization signature := realize signature
  (fun _ x y => lhs x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (g : ℤ) (z : cycles D H)
    (hz : classOf D H h26 hHG hGH z ∈ grade D H h26 hHG hGH g),
    R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,g,z,hz⟩ (classOf D H h26 hHG hGH z)
private theorem zero_mem_grade :
    classOf witness.D witness.H witness.h26 witness.hHG witness.hGH 0 ∈
      grade witness.D witness.H witness.h26 witness.hHG witness.hGH 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0 zero_mem_grade
def family : Registration arena (type_of% @project_same_class) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨project_same_class, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨witness,0,0,zero_mem_grade⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@project_same_class) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.SameClass.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.SameClass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => lhs x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end SameClass

namespace Lift
abbrev signature : Signature where
  Params := Σ x : Input, Σ g : ℤ,
    {c : Space x // c ∈ grade x.D x.H x.h26 x.hHG x.hGH g}
  State x := cycles x.1.D x.1.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def predicate (_ : Unit) (x : signature.Params) (z : signature.State x) : Prop :=
  classOf x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH z = x.2.2.1 ∧
    LatticeMatterGhostDegree.tensorNumber x.1.D (z : State x.1.D) =
      (x.2.1 : ℂ) • (z : State x.1.D)
def actual : Realization signature := realize signature predicate (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (g : ℤ) (c : Cohomology D H h26 hHG hGH)
    (hc : c ∈ grade D H h26 hHG hGH g),
    ∃ z : cycles D H, R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,g,c,hc⟩ z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad (p : Input) : False := by
    obtain ⟨z, hz⟩ := h p.D p.H p.h26 p.hHG p.hGH (0 : ℤ) (0 : Space p)
      (Submodule.zero_mem _)
    exact hz
  exact bad witness
def family : Registration arena (type_of% @homogeneous_cycle_lift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨homogeneous_cycle_lift, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have depends (p : Input) : ∃ (x : signature.Params) (u v : signature.State x),
        actual.readout role x u ≠ actual.readout role x v := by
      let x : signature.Params := ⟨p,0,0,Submodule.zero_mem _⟩
      obtain ⟨c, hc⟩ := exists_ne (0 : Space p)
      obtain ⟨z, hz⟩ := LatticeBRSTCohomologyField.classOf_surjective
        p.D p.H p.h26 p.hHG p.hGH c
      refine ⟨x, 0, z, ?_⟩
      intro he
      have h0 : actual.readout role x 0 := by
        change classOf p.D p.H p.h26 p.hHG p.hGH 0 = 0 ∧ _
        simp
      have h1 := (Eq.mp he h0).1
      exact hc (hz.symm.trans h1)
    exact depends witness

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@homogeneous_cycle_lift) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.Lift.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading.Lift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature predicate (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Lift

end Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading
