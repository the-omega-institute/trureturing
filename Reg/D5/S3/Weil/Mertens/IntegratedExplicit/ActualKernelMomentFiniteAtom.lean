import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom
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
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom

namespace literal_step_bounds
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q),
    0 < R.readout () () (literalStep q) ∧ literalStep q ≤ 1 / 16 ∧
      (q : ℝ) * literalStep q = 1 / 16
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num)
  change 0 < (-1 : ℝ) ∧ _ at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_step_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_step_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_step_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_step_bounds.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_step_bounds.family
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
end literal_step_bounds

namespace literal_support
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (i : Fin q × Fin 3 × Bool),
    R.readout () () (literalNodes q i) ∈ Icc (0 : ℝ) (1 / 16) ∪
      Icc (Real.log 2) (Real.log 2 + 1 / 16)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) (0, 0, false)
  change (-1 : ℝ) ∈ Icc (0 : ℝ) (1 / 16) ∪ Icc (Real.log 2) (Real.log 2 + 1 / 16) at hh
  rcases hh with hh | hh
  · linarith [hh.1]
  · linarith [hh.1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_support, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_support) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_support.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_support.family
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
end literal_support

namespace literal_S_tail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D H : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hxH : ∀ i, x i ∈ Icc (0 : ℝ) H) (ha : ∑ i, a i = 0)
    (hexp : ∑ i, a i * (Real.exp (x i / 2) : ℂ) = 0)
    (t : ℝ) (ht : H ≤ |t|),
    R.readout () () (S D x a t) = 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (I := ULift.{u} Empty) 0 0 le_rfl (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by intro i; exact Empty.elim i.down) (by simp) (by simp) 0 (by simp)
  have ho := literal_S_tail (I := ULift.{u} Empty) 0 0 le_rfl (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by intro i; exact Empty.elim i.down) (by simp) (by simp) 0 (by simp)
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @literal_S_tail.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_S_tail.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_S_tail.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_S_tail.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_S_tail.family
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
end literal_S_tail

namespace literalNu_W_lower
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D ell : ℝ) (hD : 0 ≤ D) (hl : 0 ≤ ell)
    (hlD : ell ≤ D),
    Real.exp (-ell / 4) ^ 2 * ell ^ 3 / 48 ≤
      R.readout () () (W D (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 le_rfl le_rfl le_rfl
  change Real.exp (-(0 : ℝ) / 4) ^ 2 * (0 : ℝ) ^ 3 / 48 ≤ (-1 : ℝ) at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literalNu_W_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literalNu_W_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literalNu_W_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literalNu_W_lower.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literalNu_W_lower.family
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
end literalNu_W_lower

namespace literal_moments
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ q),
    R.readout () () (∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) ^ m) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) 0 (by norm_num)
  have ho := literal_moments 1 (by norm_num) 0 (by norm_num)
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_moments) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_moments, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_moments) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_moments.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_moments.family
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
end literal_moments

namespace literal_moment_residual
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q),
    R.readout () () ((∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) ^ (q + 1))) =
      (((-1 : ℝ) ^ (q + 1) * ((q + 1).factorial : ℝ) * Real.log 2 *
        literalStep q ^ q * (1 - Real.exp (-literalStep q / 4)) / 2 : ℝ) : ℂ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num)
  have ho := literal_moment_residual 1 (by norm_num)
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_moment_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_moment_residual, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_moment_residual) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_moment_residual.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_moment_residual.family
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
end literal_moment_residual

namespace literal_exp_null
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ),
    R.readout () () (∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i *
      (Real.exp (literalNodes q i / 2) : ℂ)) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  have ho := literal_exp_null 0
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_exp_null) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_exp_null, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_exp_null) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_exp_null.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_exp_null.family
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
end literal_exp_null

namespace literal_exp_residual
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q),
    R.readout () () ((∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) *
      (Real.exp (literalNodes q i / 2) : ℂ))) =
      (((literalStep q / 2) * (1 - Real.exp (Real.log 2 / 2)) *
        (1 - Real.exp (literalStep q / 2)) ^ (q - 1) *
        (Real.exp (literalStep q / 4) - 1) : ℝ) : ℂ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num)
  have ho := literal_exp_residual 1 (by norm_num)
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_exp_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_exp_residual, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_exp_residual) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_exp_residual.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_exp_residual.family
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
end literal_exp_residual

namespace literal_S_pair
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ),
    R.readout () () (S D x (fun i => (a i : ℂ)) t) =
      -literalPair x a (fun s => max s 0 + Real.exp (-|s| / 2)) t
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (I := ULift.{u} Empty) 0 le_rfl (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp) 0
  have ho := literal_S_pair (I := ULift.{u} Empty) 0 le_rfl (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp) 0
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @literal_S_pair.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_S_pair.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_S_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_S_pair.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_S_pair.family
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
end literal_S_pair

namespace literal_eta_mass
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ),
    R.readout () () (∑ i, (literalEtaCoeffs q i : ℂ)) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  have ho := literal_eta_mass 0
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_eta_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_eta_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_eta_mass) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_eta_mass.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_eta_mass.family
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
end literal_eta_mass

namespace literal_eta_exp
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ),
    R.readout () () (∑ i, (literalEtaCoeffs q i : ℂ) * (Real.exp (literalEtaNodes q i / 2) : ℂ)) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  have ho := literal_eta_exp 0
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_eta_exp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_eta_exp, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_eta_exp) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_eta_exp.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_eta_exp.family
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
end literal_eta_exp

namespace literal_eta_support
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (i : Fin q × Fin 3),
    R.readout () () (literalEtaNodes q i) ∈ Icc (0 : ℝ) (1 / 16)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) (0, 0)
  change (-1 : ℝ) ∈ Icc (0 : ℝ) _ at hh
  linarith [hh.1]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_eta_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_eta_support, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_eta_support) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_eta_support.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_eta_support.family
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
end literal_eta_support

namespace literal_N_pos
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q),
    0 < R.readout () () (literalN q)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num)
  norm_num [rejected, realize, mem_union, mem_Icc] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_N_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_N_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_N_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_N_pos.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_N_pos.family
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
end literal_N_pos

namespace literal_eta_W
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : 1 / 16 ≤ D),
    R.readout () () (W D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ))) =
      literalN q * W D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) 1 (by norm_num)
  have ho := literal_eta_W 1 (by norm_num) 1 (by norm_num)
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_eta_W) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_eta_W, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_eta_W) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_eta_W.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_eta_W.family
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
end literal_eta_W

namespace literal_support_D
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) (i : Fin q × Fin 3 × Bool),
    R.readout () () (literalNodes q i) ∈ Icc (0 : ℝ) D
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) (Real.log 2 + 1 / 16) le_rfl (0, 0, false)
  change (-1 : ℝ) ∈ Icc (0 : ℝ) _ at hh
  linarith [hh.1]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_support_D) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_support_D, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_support_D) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_support_D.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_support_D.family
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
end literal_support_D

namespace literal_two_S
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) (t : ℝ),
    R.readout () () (S D (literalNodes q) (literalCoeffs q) t) =
      2 * S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t -
        S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) (t + Real.log 2) -
        S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) (t - Real.log 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) (Real.log 2 + 1 / 16) le_rfl 0
  have ho := literal_two_S 1 (by norm_num) (Real.log 2 + 1 / 16) le_rfl 0
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_two_S) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_two_S, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_two_S) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_two_S.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_two_S.family
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
end literal_two_S

namespace literal_energy_double
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q),
    R.readout () () (energy (literalNodes q) (literalCoeffs q)) =
      2 * literalN q * (literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num)
  have ho := literal_energy_double 1 (by norm_num)
  change _ + 1 = _ at hh
  rw [ho] at hh
  simpa using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @literal_energy_double) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_energy_double, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_energy_double) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_energy_double.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom.literal_energy_double.family
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
end literal_energy_double

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom
