import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
import Reg.Support.SingleDependentReadout
import Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
open Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts
open PowerSeries

namespace Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction

namespace Geometric
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℕ) (fun _ => PowerSeries ℤ)
noncomputable def actual : Realization signature :=
  realize signature (fun _ _ e => geom e*(1-X^e)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ e : ℕ, 0 < e → r.readout () () e = 1
noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 1 (by decide)
  change (0 : PowerSeries ℤ) = 1 at hx
  exact zero_ne_one hx
noncomputable def registration : Registration arena (type_of% (@geom_mul_one_sub)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨geom_mul_one_sub, bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change geom 0*(1-X^0) ≠ geom 1*(1-X^1)
    rw [geom_mul_one_sub 1 (by decide), pow_zero, sub_self, mul_zero]
    exact zero_ne_one

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.geom_mul_one_sub)
    (type_of% (realize signature (fun _ _ e => geom e*(1-X^e)) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.geom_mul_one_sub.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.Geometric.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => geom e*(1-X^e)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Geometric

namespace Truncation
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℤ)
noncomputable def actual : Realization signature :=
  realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ k m n : ℕ, 1 ≤ m → m < k →
    r.readout () ⟨k,m⟩ n = coeff n (rationalTrunc k m n-productTrunc k n)
noncomputable def bad : Realization signature :=
  realize signature (fun _ p n => (coeff n (rationalTrunc p.1 p.2 n-productTrunc p.1 n))+1) (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 2 1 0 (by decide) (by decide)
  have hne : ¬ ((coeff 0 (rationalTrunc 2 1 0-productTrunc 2 0) : ℤ)+1 ≤ coeff 0 (rationalTrunc 2 1 0-productTrunc 2 0)) := by omega
  exact hne (le_of_eq hx)
noncomputable def registration : Registration arena (type_of% (@source_coefficient_reduction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_coefficient_reduction, bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨⟨2,1⟩, 0, 2, ?_⟩
    change dCoeff 2 1 0 ≠ dCoeff 2 1 2
    rw [dCoeff_zero, dCoeff_two]
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.source_coefficient_reduction)
    (type_of% (realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.source_coefficient_reduction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.Truncation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Truncation

namespace Expansion
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℤ)
noncomputable def actual : Realization signature :=
  realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ k m n : ℕ, 1 ≤ m → m < k →
    r.readout () ⟨k,m⟩ n = coeff n (rationalSeries k m)-coeff n (productSeries k)
noncomputable def bad : Realization signature :=
  realize signature (fun _ p n => (coeff n (rationalSeries p.1 p.2)-coeff n (productSeries p.1))+1) (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 2 1 0 (by decide) (by decide)
  have hne : ¬ ((coeff 0 (rationalSeries 2 1)-coeff 0 (productSeries 2) : ℤ)+1 ≤ coeff 0 (rationalSeries 2 1)-coeff 0 (productSeries 2)) := by omega
  exact hne (le_of_eq hx)
noncomputable def registration : Registration arena (type_of% (@source_coefficient_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_coefficient_expansion, bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨⟨2,1⟩, 0, 2, ?_⟩
    change dCoeff 2 1 0 ≠ dCoeff 2 1 2
    rw [dCoeff_zero, dCoeff_two]
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.source_coefficient_expansion)
    (type_of% (realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.source_coefficient_expansion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction.Expansion.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Expansion

end Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
