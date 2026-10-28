import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Weil.Mertens.WeightedPrimeLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedPrimeLimit
open LeanInformationAudit Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

namespace Kernel
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => Chebyshev.psi u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ u => u + u ^ 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := IntegrableOn (fun u : ℝ => (R.readout () () u - u) / u ^ 2) (Ioi 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 1) := by
    refine h.congr_fun ?_ measurableSet_Ioi
    intro u hu
    change (u + u ^ 2 - u) / u ^ 2 = 1
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu] : 0 < u)
    field_simp
    <;> ring
  simpa only [integrableOn_const_iff, enorm_one, one_ne_zero, volume_Ioi,
    lt_self_iff_false, or_self] using hi

def kernelEvidence : Registration arena (type_of% chebyshev_error_kernel_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨chebyshev_error_kernel_integrable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change Chebyshev.psi 1 ≠ Chebyshev.psi 2
    rw [Chebyshev.psi_one]
    exact Ne.symm (by simp)

def kernelRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chebyshev_error_kernel_integrable) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedPrimeLimit.Kernel.kernelEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨kernelEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => Chebyshev.psi u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedPrimeLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms kernelEvidence
#print axioms kernelRegistration
end Kernel

namespace Mangoldt
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => _root_.Mertens.E₁Λ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Tendsto (fun t : ℝ => R.readout () () t)
    atTop (𝓝 (-Real.eulerMascheroniConstant))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop) _ h

def mangoldtEvidence : Registration arena (type_of% E₁Λ_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨E₁Λ_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change _root_.Mertens.E₁Λ 1 ≠ _root_.Mertens.E₁Λ 2
    norm_num [_root_.Mertens.E₁Λ,
      show Finset.Ioc 0 1 = {1} by decide,
      show Finset.Ioc 0 2 = {1, 2} by decide,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith

def mangoldtRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@E₁Λ_tendsto) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedPrimeLimit.E₁Λ_tendsto.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedPrimeLimit.Mangoldt.mangoldtEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨mangoldtEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => _root_.Mertens.E₁Λ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedPrimeLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms mangoldtEvidence
#print axioms mangoldtRegistration
end Mangoldt

namespace Prime
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => _root_.Mertens.E₁p t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∃ ell : ℝ, Tendsto (fun t : ℝ => R.readout () () t) atTop (𝓝 ell)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨ell, h⟩
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop) ell h

def primeEvidence : Registration arena (type_of% exists_E₁p_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_E₁p_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change _root_.Mertens.E₁p 1 ≠ _root_.Mertens.E₁p 2
    norm_num [_root_.Mertens.E₁p,
      show Finset.Ioc 0 1 = {1} by decide,
      show Finset.Ioc 0 2 = {1, 2} by decide]
    have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith

def primeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_E₁p_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedPrimeLimit.exists_E₁p_limit.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedPrimeLimit.Prime.primeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨primeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => _root_.Mertens.E₁p t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedPrimeLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms primeEvidence
#print axioms primeRegistration
end Prime
end
end Reg.D5.S3.Weil.Mertens.WeightedPrimeLimit
