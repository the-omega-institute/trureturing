import D5.S3.VertexAlgebra.Characters.EllipticModularTransport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.EllipticModularTransport
open _root_.D5.S3.VertexAlgebra.EllipticModularTransport
open _root_.D5.S3.VertexAlgebra.AnnularCurrentKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Complex
open scoped Real MatrixGroups

private def sampleTau : UpperHalfPlane := ⟨I, by simp⟩

private lemma sample_off : I / 2 ∉ (periodPair sampleTau).lattice := by
  simpa [periodPair, sampleTau] using (periodPair sampleTau).ω₂_div_two_notMem_lattice

private lemma P_dependence (L : PeriodPair) : ∃ u v : ℂ, L.weierstrassP u ≠ L.weierstrassP v := by
  by_contra! h
  have hc : ContinuousAt L.weierstrassP 0 := by
    have he : L.weierstrassP = fun _ => L.weierstrassP 0 := funext (fun w => h w 0)
    rw [he]
    exact continuousAt_const
  exact L.not_continuousAt_weierstrassP 0 (Submodule.zero_mem _) hc

namespace Weierstrass
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature PeriodPair (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ L w => L.weierstrassP w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ L w => L.weierstrassP w + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ),
    w ∉ (periodPair τ).lattice →
    R.readout () (periodPair (γ • τ)) (w / UpperHalfPlane.denom γ τ) =
      UpperHalfPlane.denom γ τ ^ 2 * (periodPair τ).weierstrassP w

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₀ := weierstrassP_modular 1 sampleTau (I / 2) sample_off
  have h₁ := h 1 sampleTau (I / 2) sample_off
  change (periodPair _).weierstrassP _ + 1 = _ at h₁
  rw [h₀] at h₁
  have hz : (1 : ℂ) = 0 := by linear_combination h₁
  exact one_ne_zero hz

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨u, v, h⟩ := P_dependence (periodPair sampleTau)
  exact ⟨periodPair sampleTau, u, v, h⟩

def family : Registration arena (type_of% (@weierstrassP_modular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weierstrassP_modular, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@weierstrassP_modular) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.EllipticModularTransport.Weierstrass.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.EllipticModularTransport.Weierstrass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L w => L.weierstrassP w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.EllipticModularTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Weierstrass

namespace Continued
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature UpperHalfPlane (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ τ w => continuedKernel τ w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ τ w => continuedKernel τ w + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ),
    w ∉ (periodPair τ).lattice →
    R.readout () (γ • τ) (w / UpperHalfPlane.denom γ τ) =
      UpperHalfPlane.denom γ τ ^ 2 * continuedKernel τ w -
        (γ 1 0 : ℂ) * UpperHalfPlane.denom γ τ / (2 * π * I)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₀ := continuedKernel_modular 1 sampleTau (I / 2) sample_off
  have h₁ := h 1 sampleTau (I / 2) sample_off
  change continuedKernel _ _ + 1 = _ at h₁
  rw [h₀] at h₁
  have hz : (1 : ℂ) = 0 := by linear_combination h₁
  exact one_ne_zero hz

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨u, v, h⟩ := P_dependence (periodPair sampleTau)
  refine ⟨sampleTau, u, v, ?_⟩
  intro hk
  change continuedKernel sampleTau u = continuedKernel sampleTau v at hk
  unfold continuedKernel at hk
  have he : (periodPair sampleTau).weierstrassP u / (2 * π * I) ^ 2 =
      (periodPair sampleTau).weierstrassP v / (2 * π * I) ^ 2 := sub_left_inj.mp hk
  exact h ((div_left_inj' (pow_ne_zero 2 (by simp [Real.pi_ne_zero]))).mp he)

def family : Registration arena (type_of% (@continuedKernel_modular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuedKernel_modular, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@continuedKernel_modular) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.EllipticModularTransport.Continued.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.EllipticModularTransport.Continued.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ τ w => continuedKernel τ w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.EllipticModularTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continued

namespace Annular
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ q => annularKernel q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ q z => annularKernel q z + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ),
    0 < w.im → w.im < τ.im →
    0 < (w / UpperHalfPlane.denom γ τ).im →
    (w / UpperHalfPlane.denom γ τ).im < (γ • τ).im →
    R.readout () () (expCoord (γ • τ)) (expCoord (w / UpperHalfPlane.denom γ τ)) =
      UpperHalfPlane.denom γ τ ^ 2 * annularKernel (expCoord τ) (expCoord w) -
        (γ 1 0 : ℂ) * UpperHalfPlane.denom γ τ / (2 * π * I)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₀ := annularKernel_modular_of_strictStrips 1 sampleTau (I / 2)
    (by norm_num) (by norm_num [sampleTau, UpperHalfPlane.im])
    (by norm_num [ModularGroup.denom_apply])
    (by norm_num [ModularGroup.denom_apply, sampleTau, UpperHalfPlane.im])
  have h₁ := h 1 sampleTau (I / 2)
    (by norm_num) (by norm_num [sampleTau, UpperHalfPlane.im])
    (by norm_num [ModularGroup.denom_apply])
    (by norm_num [ModularGroup.denom_apply, sampleTau, UpperHalfPlane.im])
  change annularKernel _ _ + 1 = _ at h₁
  rw [h₀] at h₁
  have hz : (1 : ℂ) = 0 := by linear_combination h₁
  exact one_ne_zero hz

private lemma kernel_zero {z : ℂ} (hz : ‖z‖ < 1) :
    annularKernel 0 z = z / (1 - z) ^ 2 := by
  unfold annularKernel splitKernel
  simp only [zero_div, zero_mul, zero_pow (PNat.ne_zero _), zero_add, sub_zero, div_one]
  have hs : Summable (fun n : ℕ => (n : ℂ) * z ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hz
  have he := tsum_zero_pnat_eq_tsum_nat hs
  simp only [Nat.cast_zero, pow_zero, zero_mul, zero_add] at he
  rw [he]
  exact tsum_coe_mul_geometric_of_norm_lt_one hz

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have h₀ := congrFun h (1 / 2)
  change annularKernel 0 (1 / 2) = annularKernel 1 (1 / 2) at h₀
  rw [kernel_zero (by norm_num)] at h₀
  have hz : annularKernel 1 (1 / 2) = 0 := by unfold annularKernel splitKernel; simp
  rw [hz] at h₀
  norm_num at h₀

def family : Registration arena (type_of% (@annularKernel_modular_of_strictStrips)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨annularKernel_modular_of_strictStrips, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@annularKernel_modular_of_strictStrips) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.EllipticModularTransport.Annular.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.EllipticModularTransport.Annular.family
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
    owner := `D5.S3.VertexAlgebra.Characters.EllipticModularTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Annular

end Reg.D5.S3.VertexAlgebra.EllipticModularTransport
