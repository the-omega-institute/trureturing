import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Quantum.Fermionic.BcGhostBRST
import D5.S3.Quantum.Fermionic.BcGhostJacobi

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostJacobi
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro (L)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.Quantum.Fermionic.BcGhostBRST.C (R_zero_vacuum R_two_vacuum)
open private L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

namespace Jacobi
abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ r => R r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℤ, Qg*R.readout () () r-R.readout () () r*Qg = 0
def rejected : Realization signature := realize signature (fun _ _ _ => b (-2)) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  change Qg*b (-2)-b (-2)*Qg = 0 at he
  have hv := LinearMap.congr_fun he vacuum
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Qg_vacuum, map_zero,
    sub_zero, LinearMap.zero_apply] at hv
  have hw := LinearMap.congr_fun (ward_b (-2)) vacuum
  simp only [LinearMap.add_apply, Module.End.mul_apply, Qg_vacuum, map_zero, add_zero] at hw
  rw [hw, L_vacuum] at hv
  have hc := congrArg (fun v : Fock => v {0,3}) hv
  have hI : Finset.Icc (0 : ℤ) 1 = {0,1} := by decide
  simp only [show (-2 : ℤ) + 2 = 0 by decide] at hc
  rw [hI] at hc
  norm_num [b, c, create_vacuum, create_ket, phase, lowerCount] at hc
  simp only [ket] at hc
  have hz (z : ℂ) : (Finsupp.single ({2,1} : Finset ℕ) z) {0,3} = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  rw [hz] at hc
  norm_num at hc
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 2 := by
  intro h
  change R 0 = R 2 at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {1,5}) h
  norm_num [R_zero_vacuum, R_two_vacuum, ket] at he

def family : Registration arena (type_of% @Qg_R) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Qg_R, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, 2, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@Qg_R) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostJacobi.Jacobi.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostJacobi.Jacobi.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => R r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostJacobi
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Jacobi

end Reg.D5.S3.Quantum.Fermionic.BcGhostJacobi
