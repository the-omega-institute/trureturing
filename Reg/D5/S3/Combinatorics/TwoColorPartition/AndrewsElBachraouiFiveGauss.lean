import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss
import Reg.Support.SingleDependentReadout
import Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts

/-! Source-bound readouts for the original coefficient proof. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
open Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts
open PowerSeries Finset

namespace Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss

private noncomputable def upper (n : ℕ) : ℝ :=
  Real.pi / 4 * n + 5 / 4 * Real.sqrt (2 * (n : ℝ) + 1 / 2) +
    Real.pi / 16 + 3 / 8
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℕ) (fun _ => ℝ)
noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => ((coeff n (productTrunc 2 n) : ℤ) : ℝ))
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, r.readout () () n ≤ upper n
noncomputable def bad : Realization signature :=
  realize signature (fun _ _ n => upper n+1) (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 0
  change upper 0+1 ≤ upper 0 at hx
  linarith
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss.gauss_coefficient_upper)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss.gauss_coefficient_upper,
    bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, productTrunc, sum_range_succ, prod_range_succ,
      geom, coeff_mk, pow_two, coeff_mul,
      Nat.antidiagonal_succ, Nat.antidiagonal_zero]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss.gauss_coefficient_upper)
    (type_of% (realize signature (fun _ _ n => ((coeff n (productTrunc 2 n) : ℤ) : ℝ)) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss.gauss_coefficient_upper.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => ((coeff n (productTrunc 2 n) : ℤ) : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss
