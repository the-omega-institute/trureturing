import D5.S3.VertexAlgebra.TwistedGround.GaussElimination
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Complete finite-index source family for the global even quadratic Gauss law. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.GaussElimination

open LeanInformationAudit Matrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
open _root_.D5.S3.VertexAlgebra.TwistedGround.BinarySchur
open _root_.D5.S3.VertexAlgebra.TwistedGround.GaussElimination
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

universe u

noncomputable section

structure Parameters where
  Index : Type u
  finite : Fintype Index
  decidable : DecidableEq Index
  Q : Matrix Index Index (ZMod 8)
  unit : letI := finite
    letI := decidable
    IsUnit (Q + Qᵀ).det

abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := Parameters.{u}
  State p := p.Index → F₂
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p x =>
    letI := p.finite
    letI := p.decidable
    complexSign ((p.Q.map residue).toBilin' x x)) (fun empty => nomatch empty)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law observation := ∀ p : Parameters.{u},
    letI := p.finite
    letI := p.decidable
    Even (Fintype.card p.Index) ∧
      (∑ x : p.Index → F₂, observation.readout () p x) =
        (2 : ℂ) ^ (Fintype.card p.Index / 2) * (ZMod.χ₈ (p.Q + p.Qᵀ).det : ℂ)

theorem exact_source_bridge :
    (type_of% (@even_quadratic_gauss.{u})) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro source p
    letI := p.finite
    letI := p.decidable
    exact source p.Q p.unit
  · intro law I finite decidable Q hu
    exact law ⟨I, finite, decidable, Q, hu⟩

private def emptyParameters : Parameters.{u} where
  Index := ULift.{u} Empty
  finite := inferInstance
  decidable := inferInstance
  Q := 0
  unit := by simp

private def plane : Parameters.{u} where
  Index := ULift.{u} (Fin 2)
  finite := inferInstance
  decidable := inferInstance
  Q := (halfGram 0 1 0).submatrix ULift.down ULift.down
  unit := by
    change IsUnit (((halfGram 0 1 0) + (halfGram 0 1 0)ᵀ).submatrix
      (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2) Equiv.ulift).det
    rw [det_submatrix_equiv_self]
    norm_num [halfGram, det_fin_two, Matrix.add_apply, Matrix.transpose_apply]

private theorem rejected_law : ¬ arena.{u}.Law (rejected : Realization signature.{u}) := by
  intro law
  have h := (law emptyParameters).2
  change (∑ _ : ULift.{u} Empty → F₂, (0 : ℂ)) =
    (2 : ℂ) ^ (Fintype.card (ULift.{u} Empty) / 2) *
      (ZMod.χ₈ ((0 : Matrix (ULift.{u} Empty) (ULift.{u} Empty) (ZMod 8)) + 0ᵀ).det : ℂ) at h
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

private theorem dependence : ObservationalDependence signature.{u}
    (actual : Realization signature.{u}) := by
  intro role
  refine ⟨plane, (fun _ => 0), (fun _ => 1), ?_⟩
  change complexSign (((halfGram 0 1 0).submatrix ULift.down ULift.down).map residue |>.toBilin'
      (fun _ : ULift.{u} (Fin 2) => 0) (fun _ => 0)) ≠
    complexSign (((halfGram 0 1 0).submatrix ULift.down ULift.down).map residue |>.toBilin'
      (fun _ : ULift.{u} (Fin 2) => 1) (fun _ => 1))
  have sum_lift (f : ULift.{u} (Fin 2) → F₂) :
      (∑ x, f x) = f ⟨0⟩ + f ⟨1⟩ := by
    rw [← (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2).symm.sum_comp f]
    exact Fin.sum_univ_two _
  simp only [Matrix.toBilin'_apply]
  simp_rw [sum_lift]
  norm_num [Matrix.map_apply, Matrix.submatrix_apply, halfGram, complexSign]

def familyRegistration : Registration arena.{u} (type_of% (@even_quadratic_gauss.{u})) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.{u}.mp (@even_quadratic_gauss.{u}), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@even_quadratic_gauss.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.GaussElimination.even_quadratic_gauss "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussElimination.familyRegistration
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
end Reg.D5.S3.VertexAlgebra.TwistedGround.GaussElimination

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.GaussElimination.Lattice

open LeanInformationAudit Matrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.GaussElimination
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

structure Parameters where
  lattice : LatticeData
  unit : IsUnit lattice.G.det

abbrev signature : Signature.{0,0,0,0,0} where
  Params := Parameters
  State p := ModTwoCharge p.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => complexSign (modTwoCocycle p.lattice x x))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ p : Parameters,
    (∑ x : ModTwoCharge p.lattice, observation.readout () p x) =
      (2 : ℂ) ^ groundRank p.lattice p.unit

theorem exact_source_bridge :
    (type_of% (@actual_quadratic_gauss_sum)) ↔ arena.Law actual := by
  constructor
  · intro source p
    exact source p.lattice p.unit
  · intro law D hu
    exact law ⟨D, hu⟩

private def planeLattice : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric i j := by fin_cases i <;> fin_cases j <;> rfl
  even_diagonal i := by fin_cases i <;> exact ⟨0, rfl⟩

private def plane : Parameters where
  lattice := planeLattice
  unit := by
    change IsUnit ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det)
    norm_num [Matrix.det_fin_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law plane
  change (∑ _ : ModTwoCharge plane.lattice, (0 : ℂ)) =
    (2 : ℂ) ^ groundRank plane.lattice plane.unit at h
  simp only [Finset.sum_const_zero] at h
  exact (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) h.symm

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
  refine ⟨plane, (fun _ => 0), (fun _ => 1), ?_⟩
  change complexSign (modTwoCocycle planeLattice (fun _ => 0) (fun _ => 0)) ≠
    complexSign (modTwoCocycle planeLattice (fun _ => 1) (fun _ => 1))
  have zero : modTwoCocycle planeLattice (fun _ => 0) (fun _ => 0) = 0 := by decide
  have one : modTwoCocycle planeLattice (fun _ => 1) (fun _ => 1) = 1 := by decide
  rw [zero, one]
  norm_num [complexSign]

def familyRegistration : Registration arena (type_of% (@actual_quadratic_gauss_sum)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp (@actual_quadratic_gauss_sum), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_quadratic_gauss_sum)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.GaussElimination.actual_quadratic_gauss_sum
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussElimination.Lattice.familyRegistration
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
end Reg.D5.S3.VertexAlgebra.TwistedGround.GaussElimination.Lattice
