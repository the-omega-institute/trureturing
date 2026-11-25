import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzTwoFlagContraction
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Complex.Basic

/-! Source-bound readouts of the scalar and matrix upper bounds. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzTwoFlagContraction
open scoped BigOperators ComplexOrder

namespace Reg.D5.S3.Quantum.Recovery.PetzTwoFlagContraction

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

abbrev scalarArena : Arena where
  signature := signature
  Law F := ∀ (m C f g w v : ℝ) (y z : ℂ)
    (_hm : 0 ≤ m) (_hC : 0 < C) (_hf : 0 < f) (_hg : 0 < g)
    (_hw : 0 ≤ 8 * m + f * (f + g) / C - w)
    (_hv : 0 ≤ 8 * m + g * (f + g) / C - v)
    (_hmargin : 0 < (8 * m + f * (f + g) / C - w) + (8 * m + g * (f + g) / C - v))
    (_hy : Complex.normSq y ≤ 1) (_hz : Complex.normSq z ≤ 1),
    let objective := w * (1 - Complex.normSq y) + v * (1 - Complex.normSq z) +
      4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C
    let optimum := 16 * m + (f + g) ^ 2 / C
    F.readout () () objective optimum ∧
      optimum - objective =
        (8 * m + f * (f + g) / C - w) * (1 - Complex.normSq y) +
        (8 * m + g * (f + g) / C - v) * (1 - Complex.normSq z) +
        4 * m * Complex.normSq (y + z) +
        f * (f + g) / C * y.im ^ 2 + g * (f + g) / C * z.im ^ 2 +
        f * g / C * (y.re + z.re) ^ 2 ∧
      (objective = optimum ↔ (y = 1 ∧ z = -1) ∨ (y = -1 ∧ z = 1))

private theorem scalarRejected : ¬ scalarArena.Law rejected := by
  intro h
  exact (h 0 1 1 1 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp)).1

def scalarFamily : Registration scalarArena (type_of% @twoFlag_maximum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@twoFlag_maximum, rejected, scalarRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    scalarArena.Law actual rejected scalarRejected
  dependence := dependence

def scalarAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twoFlag_maximum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzTwoFlagContraction.twoFlag_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzTwoFlagContraction.scalarFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scalarArena⟩
  objectArena := .source ⟨scalarArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scalarArena ⟨scalarFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzTwoFlagContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev matrixArena : Arena where
  signature := signature
  Law F := ∀ (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a : Fin 2 × Fin 2 → ℝ) (m C f g : ℝ)
    (_hY : Y.IsHermitian) (_hY₂ : (1 - Y * Y).PosSemidef)
    (_ha : ∀ i, 0 ≤ a i) (_hm : 0 ≤ m) (_hC : 0 < C) (_hf : 0 < f) (_hg : 0 < g)
    (_hw : 0 ≤ 8 * m + f * (f + g) / C - (a (0, 0) + a (1, 0)))
    (_hv : 0 ≤ 8 * m + g * (f + g) / C - (a (0, 1) + a (1, 1)))
    (_hmargin : 0 < (8 * m + f * (f + g) / C - (a (0, 0) + a (1, 0))) +
      (8 * m + g * (f + g) / C - (a (0, 1) + a (1, 1)))),
    let partner (i : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (1 - i.1, i.2)
    let y := Y (0, 0) (1, 0)
    let z := Y (0, 1) (1, 1)
    let objective :=
      (∑ i, a i * ∑ j ∈ Finset.univ.erase (partner i), Complex.normSq (Y i j)) +
      4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C
    let optimum := 16 * m + (f + g) ^ 2 / C
    F.readout () () objective optimum ∧
      (objective = optimum ↔ (y = 1 ∧ z = -1) ∨ (y = -1 ∧ z = 1))

private theorem matrixRejected : ¬ matrixArena.Law rejected := by
  intro h
  exact (h 0 (fun _ => 0) 0 1 1 1 (by simp) (by simpa using Matrix.PosSemidef.one)
    (fun _ => le_rfl) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1

def matrixFamily : Registration matrixArena (type_of% @matrix_twoFlag_maximum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matrix_twoFlag_maximum, rejected, matrixRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    matrixArena.Law actual rejected matrixRejected
  dependence := dependence

def matrixAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@matrix_twoFlag_maximum) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzTwoFlagContraction.matrix_twoFlag_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzTwoFlagContraction.matrixFamily
  realizationSource := none
  generated := false
  arena := .source ⟨matrixArena⟩
  objectArena := .source ⟨matrixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source matrixArena ⟨matrixFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzTwoFlagContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzTwoFlagContraction
