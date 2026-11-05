import D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The binary-block Gauss law with its complete finite-family parameters. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

universe u

noncomputable section

structure Parameters where
  Index : Type u
  finite : Fintype Index
  decidable : DecidableEq Index
  a : Index → ZMod 8
  b : Index → ZMod 8
  c : Index → ZMod 8
  odd : ∀ i, residue (b i) = 1
  d : ℤ
  unit : IsUnit d
  multiplier : ZMod 8
  multiplier_odd : residue multiplier = 1
  congruence : letI := finite
    (∏ i, (gram (a i) (b i) (c i)).det) = multiplier ^ 2 * (d : ZMod 8)

abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := Parameters.{u}
  State p := p.Index → F₂ × F₂
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p x =>
    letI := p.finite
    complexSign (∑ i, quadratic (p.a i) (p.b i) (p.c i) (x i)))
    (fun empty => nomatch empty)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law observation := ∀ p : Parameters.{u},
    letI := p.finite
    letI := p.decidable
    (∑ x : p.Index → F₂ × F₂, observation.readout () p x) =
      (2 : ℂ) ^ Fintype.card p.Index

theorem exact_source_bridge :
    (type_of% (@binary_gauss_of_integral_unit_congruence.{u})) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro source p
    letI := p.finite
    letI := p.decidable
    exact source p.a p.b p.c p.odd p.d p.unit p.multiplier p.multiplier_odd p.congruence
  · intro law I finite decidable a b c hb d hd m hm hc
    exact law ⟨I, finite, decidable, a, b, c, hb, d, hd, m, hm, hc⟩

private def hyperbolic : Parameters.{u} where
  Index := ULift.{u} (Fin 1)
  finite := inferInstance
  decidable := inferInstance
  a := 0
  b := 1
  c := 0
  odd _ := by rfl
  d := -1
  unit := isUnit_neg_one
  multiplier := 1
  multiplier_odd := by rfl
  congruence := by simp [gram, Matrix.det_fin_two]

private theorem rejected_law : ¬ arena.{u}.Law (rejected : Realization signature.{u}) := by
  intro law
  have h := law hyperbolic
  change (∑ _ : ULift.{u} (Fin 1) → F₂ × F₂, (0 : ℂ)) =
    (2 : ℂ) ^ Fintype.card (ULift.{u} (Fin 1)) at h
  norm_num at h

private theorem sensitivity : Sensitivity arena.{u} (actual : Realization signature.{u}) := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro other h
      exact (h (Subsingleton.elim (α := Unit) _ _)).elim
    · funext empty
      exact nomatch empty
  · intro empty
    exact nomatch empty

private theorem dependence : ObservationalDependence signature.{u} (actual : Realization signature.{u}) := by
  intro role
  refine ⟨hyperbolic, (fun _ => (0, 0)), (fun _ => (1, 1)), ?_⟩
  change complexSign (∑ _ : ULift.{u} (Fin 1), quadratic 0 1 0 (0, 0)) ≠
    complexSign (∑ _ : ULift.{u} (Fin 1), quadratic 0 1 0 (1, 1))
  norm_num [quadratic, residue, complexSign]

def familyRegistration : Registration arena.{u}
    (type_of% (@binary_gauss_of_integral_unit_congruence.{u})) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.{u}.mp (@binary_gauss_of_integral_unit_congruence.{u}),
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@binary_gauss_of_integral_unit_congruence.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.BinaryGauss.binary_gauss_of_integral_unit_congruence
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms exact_source_bridge
#print axioms familyRegistration

end

end Reg.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss.SingleBlock

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

structure Parameters where
  a : ZMod 8
  b : ZMod 8
  c : ZMod 8
  odd : residue b = 1

abbrev signature : Signature.{0,0,0,0,0} where
  Params := Parameters
  State _ := F₂ × F₂
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => complexSign (quadratic p.a p.b p.c x))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ p : Parameters,
    (∑ x : F₂ × F₂, observation.readout () p x) =
      2 * (ZMod.χ₈ (gram p.a p.b p.c).det : ℂ)

theorem exact_source_bridge : (type_of% (@block_sum)) ↔ arena.Law actual := by
  constructor
  · intro source p
    exact source p.a p.b p.c p.odd
  · intro law a b c hb
    exact law ⟨a, b, c, hb⟩

private def plane : Parameters := ⟨0, 1, 0, rfl⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law plane
  change (∑ _ : F₂ × F₂, (0 : ℂ)) = 2 * (ZMod.χ₈ (gram 0 1 0).det : ℂ) at h
  have value : ZMod.χ₈ (gram 0 1 0).det = 1 := by decide
  rw [value] at h
  norm_num at h

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro other h
      exact (h (Subsingleton.elim (α := Unit) _ _)).elim
    · funext empty
      exact nomatch empty
  · intro empty
    exact nomatch empty

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨plane, (0, 0), (1, 1), ?_⟩
  change complexSign (quadratic 0 1 0 (0, 0)) ≠ complexSign (quadratic 0 1 0 (1, 1))
  norm_num [quadratic, complexSign]

def familyRegistration : Registration arena (type_of% (@block_sum)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp (@block_sum), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@block_sum)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.BinaryGauss.block_sum
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss.SingleBlock.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms exact_source_bridge
#print axioms familyRegistration

end
end Reg.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss.SingleBlock
