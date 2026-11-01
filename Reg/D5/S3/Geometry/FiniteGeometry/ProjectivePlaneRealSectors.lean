import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option autoImplicit false
open Configuration
open scoped LinearAlgebra.Projectivization
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors

namespace Reg.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors
universe u v

structure Parameters where
  P : Type u
  L : Type v
  membership : Membership P L
  points : Fintype P
  lines : Fintype L
  plane : ProjectivePlane P L

attribute [instance] Parameters.membership Parameters.points Parameters.lines Parameters.plane

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p d => (centeredGram (P := p.P) (L := p.L) d).PosSemidef)
    (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev interval (p : Parameters.{u,v}) (d : ℝ) : Prop :=
  rootOrder (P := p.P) (L := p.L) / (1 + rootOrder (P := p.P) (L := p.L)) ≤ d ∧
  d ≤ (orderR (P := p.P) (L := p.L) + 1) / orderR (P := p.P) (L := p.L)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ (p : Parameters.{u,v}) (d : ℝ), R.readout () p d ↔ interval p d

private theorem bridge :
    (type_of% (@centeredGram_posSemidef_iff.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h p d
    exact h d
  · intro h P L mem fp fl plane d
    exact h ⟨P, L, mem, fp, fl, plane⟩ d

private theorem order_pos (p : Parameters.{u,v}) : 0 < orderR (P := p.P) (L := p.L) := by
  have hq : (2 : ℝ) ≤ orderR (P := p.P) (L := p.L) :=
    Int.cast_le.mpr (D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice.q_ge_two
      (P := p.P) (L := p.L))
  linarith

private theorem interval_one (p : Parameters.{u,v}) : interval p 1 := by
  have hq := order_pos p
  have hs : 0 < rootOrder (P := p.P) (L := p.L) := Real.sqrt_pos.mpr hq
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < 1 + rootOrder (P := p.P) (L := p.L))).mpr
    linarith
  · apply (le_div_iff₀ hq).mpr
    linarith

private theorem not_interval_zero (p : Parameters.{u,v}) : ¬ interval p 0 := by
  have hs : 0 < rootOrder (P := p.P) (L := p.L) := Real.sqrt_pos.mpr (order_pos p)
  intro h
  have hh := (div_le_iff₀ (by linarith : 0 < 1 + rootOrder (P := p.P) (L := p.L))).mp h.1
  linarith

private abbrev SmallPlane := ℙ (ZMod 2) (Fin 3 → ZMod 2)

private instance liftedMembership : Membership (ULift.{u} SmallPlane) (ULift.{v} SmallPlane) :=
  ⟨fun l p => p.down ∈ l.down⟩

private instance liftedPlane : ProjectivePlane (ULift.{u} SmallPlane) (ULift.{v} SmallPlane) where
  exists_point l := by
    obtain ⟨p, hp⟩ := Nondegenerate.exists_point (P := SmallPlane) l.down
    exact ⟨⟨p⟩, hp⟩
  exists_line p := by
    obtain ⟨l, hl⟩ := Nondegenerate.exists_line (L := SmallPlane) p.down
    exact ⟨⟨l⟩, hl⟩
  eq_or_eq := by
    intro p q l k hp hq hpk hqk
    exact (Nondegenerate.eq_or_eq (P := SmallPlane) (L := SmallPlane) hp hq hpk hqk).imp ULift.ext ULift.ext
  mkPoint h := ⟨HasPoints.mkPoint (fun he => h (ULift.ext he))⟩
  mkPoint_ax h := HasPoints.mkPoint_ax (P := SmallPlane) (fun he => h (ULift.ext he))
  mkLine h := ⟨HasLines.mkLine (fun he => h (ULift.ext he))⟩
  mkLine_ax h := HasLines.mkLine_ax (L := SmallPlane) (fun he => h (ULift.ext he))
  exists_config := by
    obtain ⟨a,b,c,l,m,n,ha,hb,hc,hd,he,hf,hg,hh⟩ :=
      ProjectivePlane.exists_config (P := SmallPlane) (L := SmallPlane)
    exact ⟨⟨a⟩,⟨b⟩,⟨c⟩,⟨l⟩,⟨m⟩,⟨n⟩,ha,hb,hc,hd,he,hf,hg,hh⟩

private def testParameters : Parameters.{u,v} :=
  ⟨ULift.{u} SmallPlane, ULift.{v} SmallPlane, inferInstance,
    Fintype.ofFinite _, Fintype.ofFinite _, inferInstance⟩

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact (h testParameters 1).mpr (interval_one testParameters)

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨testParameters, 1, 0, ?_⟩
  intro he
  have h1 : actual.readout i testParameters 1 :=
    (centeredGram_posSemidef_iff 1).mpr (interval_one testParameters)
  have h0 : ¬ actual.readout i testParameters 0 := by
    intro h0
    exact not_interval_zero testParameters ((centeredGram_posSemidef_iff 0).mp h0)
  exact h0 (Eq.mp he h1)

def family : Registration arena.{u,v} (type_of% (@centeredGram_posSemidef_iff.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@centeredGram_posSemidef_iff.{u,v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@centeredGram_posSemidef_iff.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors.family
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
    (fun _ p d => (centeredGram (P := p.P) (L := p.L) d).PosSemidef)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors
