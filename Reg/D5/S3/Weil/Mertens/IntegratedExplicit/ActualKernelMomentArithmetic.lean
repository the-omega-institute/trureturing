import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic

namespace BLower
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ p : PNTConstants, p.C ≤ R.readout () () (B p)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h pnt
  change pnt.C ≤ -1 at h0
  linarith only [h0, pnt.one_le_C]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.B_ge_C) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.B_ge_C, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.B_ge_C) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.B_ge_C.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.BLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end BLower


namespace InclusiveF
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, R.readout () () (F t) =
    ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.F_eq_Ioc) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.F_eq_Ioc, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.F_eq_Ioc) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.F_eq_Ioc.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.InclusiveF.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end InclusiveF


namespace RelativeError
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature PNTConstants (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ p z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ p _ => p.C + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (p : PNTConstants) {t : ℝ} (ht : 0 ≤ t),
    R.readout () p |relativeError t| ≤ p.C
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h pnt (t := 0) le_rfl
  change pnt.C + 1 ≤ pnt.C at h0
  linarith only [h0]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨pnt, 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.relativeError_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.relativeError_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.relativeError_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.relativeError_le.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.RelativeError.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end RelativeError


namespace Boundary
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature PNTConstants (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ p z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ p _ => B p + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (p : PNTConstants) (t : ℝ) (ht : 0 ≤ t),
    R.readout () p |b t| ≤ B p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h pnt 0 le_rfl
  change B pnt + 1 ≤ B pnt at h0
  linarith only [h0]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨pnt, 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.b_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.b_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.b_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.b_bound.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.Boundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Boundary


namespace PositiveWeight
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ D u : ℝ, 0 < R.readout () () (g D u)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 0
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.g_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.g_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.g_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.g_pos.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.PositiveWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end PositiveWeight


namespace HalfWeight
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 2 ≤ n), R.readout () () (weight n) =
    ArithmeticFunction.vonMangoldt n / Real.sqrt n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 2 le_rfl
  change (-1 : ℝ) = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 at h0
  have hp : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  linarith only [h0, hp]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weight_eq_sqrt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weight_eq_sqrt, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weight_eq_sqrt) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weight_eq_sqrt.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.HalfWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end HalfWeight


namespace LogEntry
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 2 ≤ n) (t : ℝ),
    R.readout () () (Real.log (n : ℝ)) ≤ t ↔ n ≤ ⌊Real.exp t⌋₊
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 2 le_rfl 0
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.log_cut_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.log_cut_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.log_cut_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.log_cut_iff.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.LogEntry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end LogEntry


namespace InclusiveIndices
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℕ) (fun _ => Finset ℕ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => {0}) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D t : ℝ) (ht : t ≤ D),
    R.readout () () ((primes D).filter (fun n => Real.log n ≤ t)) = primes t
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 0 le_rfl
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, primes] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), ∅, {0}, by change (∅ : Finset ℕ) ≠ {0}; simp⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.indices) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.indices, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.indices) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.indices.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.InclusiveIndices.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end InclusiveIndices


namespace Cumulative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, R.readout () ()
    (∑ n ∈ primes t, ArithmeticFunction.vonMangoldt n) = Chebyshev.psi (Real.exp t)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, Chebyshev.psi] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.cumulative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.cumulative, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.cumulative) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.cumulative.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.Cumulative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cumulative


namespace ComplexPair
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (z w : ℂ),
    2 * R.readout () () (star z * w) ≤
      (Y / X) * ‖w‖ ^ 2 + (X / Y) * ‖z‖ ^ 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 1 1 (by norm_num) (by norm_num) 0 0
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weighted_complex_pair) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weighted_complex_pair, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weighted_complex_pair) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.weighted_complex_pair.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.ComplexPair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ComplexPair


namespace PrefixSupport
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0)
    (t : ℝ) (ht : t ∉ Icc (0 : ℝ) D), R.readout () () («prefix» x a t) = 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 0 (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by simp) 1 (by norm_num)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.prefix_support.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.prefix_support.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.prefix_support.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.prefix_support.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.PrefixSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end PrefixSupport


namespace Translation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (p : PNTConstants)
    (D : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0),
    R.readout () () (primeQuadratic D x a) ≤ beta p D * energy x a

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance pnt 1 (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by simp)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, primeQuadratic, energy, «prefix»] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℝ) ≠ 1
  norm_num

def family : Registration arena.{u} (type_of% @actual_weighted_mangoldt_translation_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_weighted_mangoldt_translation_bound.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_weighted_mangoldt_translation_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_weighted_mangoldt_translation_bound.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic.Translation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Translation


end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic
