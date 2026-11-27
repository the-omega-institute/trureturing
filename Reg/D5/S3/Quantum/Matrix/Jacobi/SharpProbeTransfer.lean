import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the Green minor, column detection, and two-site example. -/

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.JacobiEndpointResolvent
open _root_.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer

namespace Reg.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer

private abbrev columnSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin n → ℂ) (fun n => (Fin n → ℂ) → Prop)

private def columnActual : Realization columnSignature :=
  realize columnSignature (fun _ _ g₁ g₀ => g₁ = g₀) (fun e => nomatch e)

private def columnRejected : Realization columnSignature :=
  realize columnSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem columnDependence : ObservationalDependence columnSignature columnActual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have hone : (1 : Fin 1 → ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero (congrFun hone (0 : Fin 1))

private theorem tridiagonal_zero {n : ℕ} :
    IsTridiagonal (0 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ _ => rfl

private theorem im_I_pos : 0 < Complex.I.im := by simp
private theorem im_neg_I_neg : (-Complex.I).im < 0 := by simp

namespace Detection

private abbrev arena : Arena where
  signature := columnSignature
  Law R := ∀ {n : ℕ} [NeZero n] (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ)
    (_hH₀ : H₀.IsHermitian) (_hH₁ : H₁.IsHermitian)
    (_htri : IsTridiagonal H₀) (_hband : IsTridiagonal (H₁ - H₀))
    {z₀ z₁ : ℂ} (_hz₀ : 0 < z₀.im) (_hz₁ : z₁.im < 0),
    (firstColumn (spectralShift H₁ z₀) = firstColumn (spectralShift H₀ z₀) ∧
      firstColumn (spectralShift H₁ z₁) = firstColumn (spectralShift H₀ z₁)) ↔
      ∀ j, EndpointConnected H₀ j → R.readout () n ((H₁ - H₀).col j) 0

private theorem rejected_law : ¬ arena.Law columnRejected := by
  intro h
  have htest := h (n := 1) 0 0 Matrix.isHermitian_zero Matrix.isHermitian_zero
    tridiagonal_zero (by rw [sub_zero]; exact tridiagonal_zero) im_I_pos im_neg_I_neg
  exact htest.mp ⟨rfl, rfl⟩ 0 (fun p hp => (Fin.not_lt_zero p hp).elim)

def family : Registration arena (type_of% @two_probe_eq_iff) where
  actual := columnActual
  bridge := Iff.rfl
  variation := ⟨@two_probe_eq_iff, columnRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law columnActual columnRejected rejected_law
  dependence := columnDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@two_probe_eq_iff) (Realization columnSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.two_probe_eq_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.Detection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize columnSignature (fun _ _ g₁ g₀ => g₁ = g₀) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Detection

namespace Propagation

private abbrev arena : Arena where
  signature := columnSignature
  Law R := ∀ {n : ℕ} [NeZero n] (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ)
    (_hH₀ : H₀.IsHermitian) (_hH₁ : H₁.IsHermitian)
    (_htri : IsTridiagonal H₀) (_hband : IsTridiagonal (H₁ - H₀))
    {z₀ z₁ z : ℂ} (_hz₀ : 0 < z₀.im) (_hz₁ : z₁.im < 0) (_hz : z.im ≠ 0)
    (_e₀ : firstColumn (spectralShift H₁ z₀) = firstColumn (spectralShift H₀ z₀))
    (_e₁ : firstColumn (spectralShift H₁ z₁) = firstColumn (spectralShift H₀ z₁)),
    R.readout () n (firstColumn (spectralShift H₁ z)) (firstColumn (spectralShift H₀ z))

private theorem rejected_law : ¬ arena.Law columnRejected := by
  intro h
  exact h (n := 1) 0 0 Matrix.isHermitian_zero Matrix.isHermitian_zero
    tridiagonal_zero (by rw [sub_zero]; exact tridiagonal_zero)
    im_I_pos im_neg_I_neg (z := Complex.I) im_I_pos.ne' rfl rfl

def family : Registration arena (type_of% @firstColumn_eq_of_two_probes) where
  actual := columnActual
  bridge := Iff.rfl
  variation := ⟨@firstColumn_eq_of_two_probes, columnRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law columnActual columnRejected rejected_law
  dependence := columnDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@firstColumn_eq_of_two_probes) (Realization columnSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.firstColumn_eq_of_two_probes.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.Propagation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize columnSignature (fun _ _ g₁ g₀ => g₁ = g₀) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Propagation

namespace AdjacentMinor

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℂ) (fun _ => ℂ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (H : Matrix (Fin n) (Fin n) ℂ) (z₀ z₁ : ℂ)
    (_htri : IsTridiagonal H)
    (_hinv₀ : ∀ j, IsUnit (tail (spectralShift H z₀) j).det)
    (_hinv₁ : ∀ j, IsUnit (tail (spectralShift H z₁) j).det)
    (p i : Fin n) (_hpi : p.val + 1 = i.val),
    R.readout () ()
      (firstColumn (spectralShift H z₀) p * firstColumn (spectralShift H z₁) i -
        firstColumn (spectralShift H z₁) p * firstColumn (spectralShift H z₀) i)
      ((firstColumn (spectralShift H z₀) p * firstColumn (spectralShift H z₁) p) *
        bond H p * (tailDiagonal (spectralShift H z₁) i - tailDiagonal (spectralShift H z₀) i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hunit (j : Fin 2) :
      IsUnit (tail (spectralShift (0 : Matrix (Fin 2) (Fin 2) ℂ) 1) j).det := by
    rw [spectralShift, one_smul, sub_zero, tail, Matrix.submatrix_one _ Subtype.val_injective,
      Matrix.det_one]
    exact isUnit_one
  exact h (n := 2) 0 1 1 tridiagonal_zero hunit hunit 0 1 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero ((congrFun h 0).mp rfl)

def family : Registration arena (type_of% @adjacent_green_minor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjacent_green_minor, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adjacent_green_minor) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.adjacent_green_minor.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.AdjacentMinor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AdjacentMinor

namespace Adversary

private abbrev GreenColumn := Fin 2 → ℂ

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => GreenColumn) (fun _ => GreenColumn → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ g₁ g₀ => g₁ = g₀) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {b ε : ℝ} (_hb : b ≠ 0) (_hε : 0 < ε) {z : ℂ} (_hz : z.im ≠ 0),
    let H₀ := twoSiteReference b
    let V := twoSitePerturbation b ε z
    let H₁ := H₀ + V
    H₀.IsHermitian ∧ H₁.IsHermitian ∧ IsTridiagonal H₀ ∧ IsTridiagonal V ∧
      (∀ j, EndpointConnected H₀ j) ∧
      R.readout () () (firstColumn (spectralShift H₁ z))
        (firstColumn (spectralShift H₀ z)) ∧ V 0 0 ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (b := 1) (ε := 1) one_ne_zero zero_lt_one
    (z := Complex.I) (by simp)).2.2.2.2.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hone : (1 : GreenColumn) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero (congrFun hone (0 : Fin 2))

def family : Registration arena (type_of% @one_probe_two_site_adversary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_probe_two_site_adversary, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@one_probe_two_site_adversary) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.one_probe_two_site_adversary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer.Adversary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ g₁ g₀ => g₁ = g₀) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Adversary

end Reg.D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
