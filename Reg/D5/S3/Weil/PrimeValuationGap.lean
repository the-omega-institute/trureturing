import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.PrimeValuationGap
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.PrimeValuationGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology

abbrev retentionSignature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℕ × ℕ) (fun _ => ℝ)
def retentionActual : Realization retentionSignature :=
  realize retentionSignature (fun _ _ x => 1 - (x.1 : ℝ)⁻¹ ^ (x.2 + 1)) (fun e => nomatch e)
def retentionRejected : Realization retentionSignature :=
  realize retentionSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev retentionArena : Arena where
  signature := retentionSignature
  Law R := ∀ {p : ℕ}, p.Prime → ∀ a : ℕ, 0 < R.readout () () (p, a)
private theorem retention_rejected : ¬ retentionArena.Law retentionRejected := by
  intro h
  have hbad := h Nat.prime_two 0
  norm_num [retentionRejected, realize] at hbad
def retentionFamily : Registration retentionArena
    (type_of% @_root_.D5.S3.Weil.PrimeValuationGap.retention_pos) where
  actual := retentionActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Weil.PrimeValuationGap.retention_pos, retentionRejected,
    retention_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    retentionArena.Law retentionActual retentionRejected retention_rejected
  dependence := by
    intro i
    refine ⟨(), (2, 0), (2, 1), ?_⟩
    norm_num [retentionActual, realize]

abbrev sigmaSignature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℕ) (fun _ => ℝ)
def sigmaActual : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ n => (ArithmeticFunction.sigma 1 n : ℝ) / n)
    (fun e => nomatch e)
def sigmaRejected : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sigmaArena : Arena where
  signature := sigmaSignature
  Law R := ∀ {p m : ℕ}, p.Prime → p.Coprime m → ∀ a : ℕ,
    R.readout () () (p ^ a * m) =
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) * R.readout () () m
private theorem sigma_rejected : ¬ sigmaArena.Law sigmaRejected := by
  intro h
  have hbad := h Nat.prime_two (Nat.coprime_one_right 2) 1
  norm_num [sigmaRejected, realize] at hbad
def sigmaFamily : Registration sigmaArena
    (type_of% @_root_.D5.S3.Weil.PrimeValuationGap.normalized_sigma_pow_mul) where
  actual := sigmaActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Weil.PrimeValuationGap.normalized_sigma_pow_mul,
    sigmaRejected, sigma_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sigmaArena.Law sigmaActual sigmaRejected sigma_rejected
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [sigmaActual, realize]

abbrev scaleSignature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ)
def scaleActual : Realization scaleSignature :=
  realize scaleSignature (fun _ _ x => Real.log (Real.log x)) (fun e => nomatch e)
def scaleRejected : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev scaleArena : Arena where
  signature := scaleSignature
  Law R := ∀ {c : ℝ}, 0 < c → Tendsto
    (fun n : ℕ => R.readout () () (c * n) / R.readout () () n) atTop (𝓝 1)
private theorem scale_rejected : ¬ scaleArena.Law scaleRejected := by
  intro h
  have hbad := h (c := 1) (by norm_num)
  have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := by
    simpa only [scaleRejected, realize, zero_div] using hbad
  have heq : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at heq
def scaleFamily : Registration scaleArena
    (type_of% @_root_.D5.S3.Weil.PrimeValuationGap.tendsto_loglog_scale) where
  actual := scaleActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Weil.PrimeValuationGap.tendsto_loglog_scale,
    scaleRejected, scale_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    scaleArena.Law scaleActual scaleRejected scale_rejected
  dependence := by
    intro i
    refine ⟨(), 1, Real.exp (Real.exp 1), ?_⟩
    norm_num [scaleActual, realize, Real.log_exp]

/- Complete dependent laws and kernel bridges are supplied for the three
visibility exports. Raw source reconstruction is an unfinished binding obligation. -/

def retentionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.PrimeValuationGap.retention_pos)
    (Realization retentionSignature) Unit Unit where
  unitName := `D5.S3.Weil.PrimeValuationGap.retention_pos.__information_unit
  realizationName := `Reg.D5.S3.Weil.PrimeValuationGap.retentionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨retentionArena⟩
  objectArena := .source ⟨retentionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source retentionArena ⟨retentionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize retentionSignature retentionActual.readout retentionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def sigmaAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.PrimeValuationGap.normalized_sigma_pow_mul)
    (Realization sigmaSignature) Unit Unit where
  unitName := `D5.S3.Weil.PrimeValuationGap.normalized_sigma_pow_mul.__information_unit
  realizationName := `Reg.D5.S3.Weil.PrimeValuationGap.sigmaFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sigmaArena⟩
  objectArena := .source ⟨sigmaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sigmaArena ⟨sigmaFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sigmaSignature sigmaActual.readout sigmaActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def scaleAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.PrimeValuationGap.tendsto_loglog_scale)
    (Realization scaleSignature) Unit Unit where
  unitName := `D5.S3.Weil.PrimeValuationGap.tendsto_loglog_scale.__information_unit
  realizationName := `Reg.D5.S3.Weil.PrimeValuationGap.scaleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scaleArena⟩
  objectArena := .source ⟨scaleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scaleArena ⟨scaleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature scaleActual.readout scaleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.PrimeValuationGap
