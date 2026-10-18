import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.A400361PillaiMean
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.A400361PillaiMean
open LeanInformationAudit Filter Topology Finset
open scoped Asymptotics

noncomputable section
namespace Reg.D5.S3.ArithSums.A400361PillaiMean

namespace KernelPrefix
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, (∑ j ∈ range N, R.readout () () j) = 1 - 1 / ((N : ℝ) + 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1
  norm_num [rejected, realize] at hh
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kernel_one_prefix, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400361PillaiMean.kernel_one_prefix)
    (type_of% (realize signature (fun _ _ n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400361PillaiMean.KernelPrefix.information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400361PillaiMean.KernelPrefix.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400361PillaiMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end KernelPrefix

namespace KernelSeries
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := HasSum (fun j : ℕ => R.readout () () j) 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : HasSum (fun _ : ℕ => (0 : ℝ)) 1 := h
  have hz : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
  have he := hh.unique hz
  norm_num at he
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hasSum_kernel_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400361PillaiMean.hasSum_kernel_one)
    (type_of% (realize signature (fun _ _ n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400361PillaiMean.KernelSeries.information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400361PillaiMean.KernelSeries.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400361PillaiMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end KernelSeries

namespace TriangularSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ q : ℕ, (∑ r ∈ Icc 1 q, R.readout () () r) = (q : ℝ) * ((q : ℝ) + 1) / 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1
  norm_num [rejected, realize] at hh
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_Icc_cast, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨(), 1, 2, by norm_num [actual, realize]⟩
noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400361PillaiMean.sum_Icc_cast)
    (type_of% (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400361PillaiMean.TriangularSum.information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400361PillaiMean.TriangularSum.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400361PillaiMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end TriangularSum

namespace QuotientLimit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, Tendsto (fun N : ℕ => R.readout () () (N / d) / N) atTop (𝓝 (1 / (d : ℝ)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1
  simp only [rejected, realize, zero_div, Nat.cast_one, div_one] at hh
  have hz := tendsto_nhds_unique hh (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
  norm_num at hz
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quotient_ratio_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨(), 1, 2, by norm_num [actual, realize]⟩
noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400361PillaiMean.quotient_ratio_limit)
    (type_of% (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400361PillaiMean.QuotientLimit.information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400361PillaiMean.QuotientLimit.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400361PillaiMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end QuotientLimit

private theorem triangular_limit :
    Tendsto (fun N : ℕ => (N : ℝ) * ((N : ℝ) + 1) / 2 / (N : ℝ)^2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2
  apply (show Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) / 2) atTop (𝓝 (1 / 2 : ℝ)) by simpa using h).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

namespace PillaiMean
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n => _root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => _root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai n + n) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := Tendsto (fun N : ℕ =>
    (∑ n ∈ Icc 1 N, (R.readout () () n : ℝ)) / (N : ℝ)^2 -
      (3 / Real.pi^2) * Real.log N) atTop
    (𝓝 ((3 / Real.pi^2) * (-1 / 2 + 2 * Real.eulerMascheroniConstant -
      6 * deriv realZeta 2 / Real.pi^2)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd := h.sub pillai_second_term
  have he (N : ℕ) :
      ((∑ n ∈ Icc 1 N, (rejected.readout () () n : ℝ)) / (N : ℝ)^2 -
        (3 / Real.pi^2) * Real.log N) -
      ((∑ n ∈ Icc 1 N, (_root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai n : ℝ)) /
        (N : ℝ)^2 - (3 / Real.pi^2) * Real.log N) =
      (N : ℝ) * ((N : ℝ) + 1) / 2 / (N : ℝ)^2 := by
    simp only [rejected, realize, Nat.cast_add, sum_add_distrib, sum_Icc_cast, add_div]
    ring
  have hz : Tendsto (fun N : ℕ => (N : ℝ) * ((N : ℝ) + 1) / 2 / (N : ℝ)^2)
      atTop (𝓝 0) := by
    convert hd.congr he using 1 <;> simp
  have hh := tendsto_nhds_unique triangular_limit hz
  norm_num at hh
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pillai_second_term, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨(), 1, 2, by
      change _root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai 1 ≠
        _root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai 2
      decide⟩
noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400361PillaiMean.pillai_second_term)
    (type_of% (realize signature (fun _ _ n => _root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400361PillaiMean.PillaiMean.information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400361PillaiMean.PillaiMean.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => _root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400361PillaiMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end PillaiMean

end Reg.D5.S3.ArithSums.A400361PillaiMean
