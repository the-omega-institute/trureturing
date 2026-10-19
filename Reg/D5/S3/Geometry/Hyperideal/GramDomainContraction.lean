import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.GramDomainContraction
import Reg.Support.DependentFamily

open scoped Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.GramDomainContraction
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Hyperideal.GramDomainContraction
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev signature : Signature where
  Params := Unit
  State _ := Coordinates
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Delta x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ContractibleSpace {x : Coordinates //
    (∀ i, 1 < x i) ∧ 0 < R.readout () () x}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change ContractibleSpace {x : Coordinates //
    (∀ i, 1 < x i) ∧ 0 < (-1 : ℝ)} at h
  obtain ⟨x, _⟩ := (contractible_iff_id_nullhomotopic
    {x : Coordinates // (∀ i, 1 < x i) ∧ 0 < (-1 : ℝ)}).mp h
  have hx := x.property.2
  norm_num at hx

def family : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration
    arena (ContractibleSpace X) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_domain_contractible, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (fun _ => 1), (fun _ => 2), ?_⟩
    change Delta (fun _ => 1) ≠ Delta (fun _ => 2)
    have h1 : Delta (fun _ => 1) = 16 := by
      norm_num [Delta, delta, gram,
        _root_.D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram,
        Matrix.det_succ_row_zero,
        Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
        Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.sum_univ_succ,
        Fin.succAbove]
    have h2 : Delta (fun _ => 2) = 135 := by
      norm_num [Delta, delta, gram,
        _root_.D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram,
        Matrix.det_succ_row_zero,
        Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
        Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.sum_univ_succ,
        Fin.succAbove]
    rw [h1, h2]
    norm_num

noncomputable def registration_attempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.GramDomainContraction.full_domain_contractible)
    (type_of% (realize signature (fun _ _ x => Delta x) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.GramDomainContraction.full_domain_contractible.determinantDomain
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.GramDomainContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Delta x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Coordinates
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperideal.GramDomainContraction
    definition := some {
      owner := `D5.S3.Geometry.Hyperideal.GramDomainContraction
      name := `D5.S3.Geometry.Hyperideal.GramDomainContraction.X
      path := #["fn", "arg"] }
    coordinates := #[]
    readouts := #[]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

end
end Reg.D5.S3.Geometry.Hyperideal.GramDomainContraction
