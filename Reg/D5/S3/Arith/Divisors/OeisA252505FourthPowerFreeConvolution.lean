import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution

open _root_.D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n → R.readout () () n = ∑ d ∈ n.divisors, b d * c (n/d)

private theorem free_one : FourthPowerFree 1 := by
  intro p hp hh
  exact hp.not_dvd_one (dvd_trans (show p ∣ p^4 from ⟨p^3, by ring⟩) hh)

private theorem free_two : FourthPowerFree 2 := by
  intro p hp hh
  have hd : p ∣ 2 := dvd_trans (show p ∣ p^4 from ⟨p^3, by ring⟩) hh
  have hp2 : p=2 := le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le
  subst p
  norm_num at hh

private theorem count_one : a 1 = 1 := by simp [a, Finset.filter_singleton, free_one]
private theorem count_two : a 2 = 2 := by
  have hd : (2 : ℕ).divisors = {1,2} := Nat.Prime.divisors (by decide)
  simp [a, hd, Finset.filter_insert, Finset.filter_singleton, free_one, free_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 (by decide)
  change (0 : ℤ) = ∑ d ∈ (1 : ℕ).divisors, b d * c (1/d) at hz
  have hh := result 1 (by decide)
  have he : a 1 = 0 := hh.trans hz.symm
  rw [count_one] at he
  norm_num at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change a 1 ≠ a 2
  rw [count_one, count_two]
  norm_num

def sourceRegistration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution.unit
  realizationName := `Reg.D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
    definition := some {
      owner := `D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
      name := `D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
