import D5.S3.VertexAlgebra.Characters.AnnularCurrentKernel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Faithful infinite-family audits of the annular scalar identity and convergence law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.AnnularCurrentKernel
open _root_.D5.S3.VertexAlgebra.AnnularCurrentKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Complex
open scoped Real

private def sampleTau : UpperHalfPlane := ⟨I, by simp⟩

namespace Identity

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ q => annularKernel q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ q z => annularKernel q z + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (τ : UpperHalfPlane) (w : ℂ), 0 < w.im → w.im < τ.im →
    R.readout () () (expCoord τ) (expCoord w) =
      (periodPair τ).weierstrassP w / (2 * π * I) ^ 2 - EisensteinSeries.E2 τ / 12

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₀ := annular_kernel_eq_periodPair_weierstrassP_sub_E2 sampleTau (I / 2)
    (by norm_num) (by norm_num [sampleTau, UpperHalfPlane.im])
  have h₁ := h sampleTau (I / 2) (by norm_num) (by norm_num [sampleTau, UpperHalfPlane.im])
  change annularKernel _ _ + 1 = _ at h₁
  rw [h₀] at h₁
  have hz : (1 : ℂ) = 0 := by linear_combination h₁
  exact one_ne_zero hz

private theorem kernel_zero {z : ℂ} (hz : ‖z‖ < 1) :
    annularKernel 0 z = z / (1 - z) ^ 2 := by
  unfold annularKernel splitKernel
  simp only [zero_div, zero_mul, zero_pow (PNat.ne_zero _), zero_add,
    sub_zero, div_one]
  have hs : Summable (fun n : ℕ => (n : ℂ) * z ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hz
  have he := tsum_zero_pnat_eq_tsum_nat hs
  simp only [Nat.cast_zero, pow_zero, zero_mul, zero_add] at he
  rw [he]
  exact tsum_coe_mul_geometric_of_norm_lt_one hz

private theorem kernel_one (z : ℂ) (hz : z ≠ 0) : annularKernel 1 z = 0 := by
  unfold annularKernel splitKernel
  simp [hz]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have h₀ := congrFun h (1 / 2)
  change annularKernel 0 (1 / 2) = annularKernel 1 (1 / 2) at h₀
  rw [kernel_zero (by norm_num), kernel_one _ (by norm_num)] at h₀
  norm_num at h₀

def family : Registration arena
    (type_of% (@annular_kernel_eq_periodPair_weierstrassP_sub_E2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨annular_kernel_eq_periodPair_weierstrassP_sub_E2, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@annular_kernel_eq_periodPair_weierstrassP_sub_E2)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.AnnularCurrentKernel.Identity.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.AnnularCurrentKernel.Identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => annularKernel q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.AnnularCurrentKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Identity

namespace Convergence

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ+ → ℂ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Summable f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (τ : UpperHalfPlane) (w : ℂ), 0 < w.im → w.im < τ.im →
    R.readout () () (fun n : ℕ+ => (n : ℂ) *
      ((expCoord τ / expCoord w) ^ (n : ℕ) + expCoord w ^ (n : ℕ)) /
      (1 - expCoord τ ^ (n : ℕ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h sampleTau (I / 2) (by norm_num) (by norm_num [sampleTau, UpperHalfPlane.im])

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hs : Summable (fun _ : ℕ+ => (1 : ℂ)) :=
    Eq.mp h (show Summable (fun _ : ℕ+ => (0 : ℂ)) from summable_zero)
  simpa [summable_const_iff] using hs

def family : Registration arena (type_of% (@annular_summable)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨annular_summable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@annular_summable) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.AnnularCurrentKernel.Convergence.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.AnnularCurrentKernel.Convergence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Summable f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ+ → ℂ)
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.AnnularCurrentKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Convergence
end Reg.D5.S3.VertexAlgebra.AnnularCurrentKernel
