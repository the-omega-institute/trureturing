import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 1 ≤ n → 12 * (R.readout () () n : ℤ) =
      (n : ℤ)^4 + 16*(n : ℤ)^3 + 83*(n : ℤ)^2 + 176*(n : ℤ) + 156) ∧
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk (fun n => if n = 0 then 0 else (R.readout () () n : ℚ)) =
       X*(36-98*X+112*X^2-61*X^3+13*X^4)*((1-X)^5)⁻¹) ∧
    (∀ n : ℕ, 6 ≤ n → (R.readout () () n : ℤ) =
      5*(R.readout () () (n-1) : ℤ)-10*(R.readout () () (n-2) : ℤ)+
      10*(R.readout () () (n-3) : ℤ)-5*(R.readout () () (n-4) : ℤ)+
        (R.readout () () (n-5) : ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h.1 1 (by decide)
  norm_num [rejected, realize] at h1

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),1,2,?_⟩
    change count 1 ≠ count 2
    have h1 := result.1 1 (by decide)
    have h2 := result.1 2 (by decide)
    norm_num at h1 h2
    intro he
    rw [he] at h1
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => count n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330
