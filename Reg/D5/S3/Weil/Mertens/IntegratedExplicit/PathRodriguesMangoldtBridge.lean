import D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source registrations for the Rodrigues coefficient LCM and its Mangoldt bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge

open Finset LeanInformationAudit
open scoped Nat
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

abbrev contentSignature := signature ℕ (fun _ => ℕ) (fun _ => ℕ)
abbrev indexedRealSignature := signature ℕ (fun _ => ℕ) (fun _ => ℝ)
abbrev diagonalSignature := signature Unit (fun _ => ℕ) (fun _ => ℝ)
abbrev powerSignature := signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private theorem content_at_one : contentLCM 2 1 = 1 := by
  rw [show 1 = 0 + 1 from rfl, contentLCM_eq_factorial_div_tail (by decide)]
  decide

private theorem content_at_three : contentLCM 2 3 = 2 := by
  rw [show 3 = 2 + 1 from rfl, contentLCM_eq_factorial_div_tail (by decide)]
  decide

private theorem diagonal_content_at_three : contentLCM 3 3 = 2 := by
  rw [show 3 = 2 + 1 from rfl, contentLCM_eq_factorial_div_tail (by decide)]
  decide

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

def contentReadout : Realization contentSignature :=
  realize contentSignature (fun _ r s => contentLCM r (s + 1)) (fun e => nomatch e)

def tailReadout : Realization indexedRealSignature :=
  realize indexedRealSignature (fun _ r x => Real.log (tailLCM (r * x - 1) (r - 1) : ℝ))
    (fun e => nomatch e)

def psiReadout : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ x => Chebyshev.psi (x : ℝ)) (fun e => nomatch e)

def centeredReadout : Realization indexedRealSignature :=
  realize indexedRealSignature (fun _ r x => T r x) (fun e => nomatch e)

def diagonalReadout : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ x => T x x) (fun e => nomatch e)

def factorialReadout : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ x => Real.log ((x - 1)! : ℝ)) (fun e => nomatch e)

def gammaReadout : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ x => Real.log (contentLCM x x : ℝ)) (fun e => nomatch e)

def powerReadout : Realization powerSignature :=
  realize powerSignature (fun _ _ x a => x ^ a) (fun e => nomatch e)

private theorem content_dependence : ObservationalDependence contentSignature contentReadout := by
  intro _
  refine ⟨2, 0, 2, ?_⟩
  change contentLCM 2 1 ≠ contentLCM 2 3
  rw [content_at_one, content_at_three]
  decide

private theorem tail_dependence : ObservationalDependence indexedRealSignature tailReadout := by
  intro _
  refine ⟨2, 1, 3, ?_⟩
  change Real.log (tailLCM 1 1 : ℝ) ≠ Real.log (tailLCM 5 1 : ℝ)
  rw [show tailLCM 1 1 = 1 by decide, show tailLCM 5 1 = 2 by decide]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Real.log_one]
  exact ne_of_lt log_two_pos

private theorem psi_dependence : ObservationalDependence diagonalSignature psiReadout := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change Chebyshev.psi ((1 : ℕ) : ℝ) ≠ Chebyshev.psi ((2 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi_eq_log_lcmUpto,
    show Nat.lcmUpto 1 = 1 by decide, show Nat.lcmUpto 2 = 2 by decide]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Real.log_one]
  exact ne_of_lt log_two_pos

private theorem centered_dependence :
    ObservationalDependence indexedRealSignature centeredReadout := by
  intro _
  refine ⟨0, 0, 1, ?_⟩
  change T 0 0 ≠ T 0 1
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  norm_num [T]
  linarith

private theorem diagonal_dependence :
    ObservationalDependence diagonalSignature diagonalReadout := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change T 0 0 ≠ T 1 1
  have h₁ : contentLCM 1 1 = 1 := by decide
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  norm_num [T, h₁]
  linarith

private theorem factorial_dependence :
    ObservationalDependence diagonalSignature factorialReadout := by
  intro _
  refine ⟨(), 1, 3, ?_⟩
  change Real.log ((0 : ℕ)! : ℝ) ≠ Real.log ((2 : ℕ)! : ℝ)
  rw [show (0 : ℕ)! = 1 by decide, show (2 : ℕ)! = 2 by decide]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Real.log_one]
  exact ne_of_lt log_two_pos

private theorem gamma_dependence : ObservationalDependence diagonalSignature gammaReadout := by
  intro _
  refine ⟨(), 2, 3, ?_⟩
  change Real.log (contentLCM 2 2 : ℝ) ≠ Real.log (contentLCM 3 3 : ℝ)
  have h₂ : contentLCM 2 2 = 1 := by
    rw [show 2 = 1 + 1 from rfl, contentLCM_eq_factorial_div_tail (by decide)]
    decide
  rw [h₂, diagonal_content_at_three]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Real.log_one]
  exact ne_of_lt log_two_pos

private theorem power_dependence : ObservationalDependence powerSignature powerReadout := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have h₁ := congrFun h (1 : ℝ)
  change (0 : ℝ) ^ (1 : ℝ) = (1 : ℝ) ^ (1 : ℝ) at h₁
  norm_num at h₁

private theorem block_left_le_right {k : ℕ} (hk : 2 ≤ k) : k ^ 12 ≤ k ^ 16 :=
  pow_le_pow_right₀ (by omega : 1 ≤ k) (by decide)

namespace FactorialLCM

abbrev arena : Arena where
  signature := contentSignature
  Law R := ∀ {r : ℕ}, 2 ≤ r → ∀ s : ℕ,
    R.readout () r s = (s !)^r / tailLCM (r * (s + 1) - 1) (r - 1)

def rejected : Realization contentSignature :=
  realize contentSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₀ := h (r := 2) (by decide) 0
  rw [← contentLCM_eq_factorial_div_tail (r := 2) (by decide) 0, content_at_one] at h₀
  exact Nat.zero_ne_one h₀

def family : Registration arena (type_of% @contentLCM_eq_factorial_div_tail) where
  actual := contentReadout
  bridge := Iff.rfl
  variation := ⟨@contentLCM_eq_factorial_div_tail, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law contentReadout rejected rejected_law
  dependence := content_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@contentLCM_eq_factorial_div_tail) (Realization contentSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.FactorialLCM.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.FactorialLCM.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize contentSignature contentReadout.readout contentReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FactorialLCM

namespace TailCeiling

abbrev arena : Arena where
  signature := indexedRealSignature
  Law R := ∀ {r x : ℕ}, 2 ≤ r → 0 < x →
    R.readout () r x =
      ∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q *
        ((⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ : ℝ) - (r : ℝ))

def rejected : Realization indexedRealSignature :=
  realize indexedRealSignature (fun _ r x => tailReadout.readout () r x + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := h (r := 2) (x := 1) (by decide) (by decide)
  change Real.log (tailLCM 1 1 : ℝ) + 1 = _ at h₁
  have actual := log_tailLCM_eq_sum_vonMangoldt_ceil (r := 2) (x := 1) (by decide) (by decide)
  linarith

def family : Registration arena (type_of% @log_tailLCM_eq_sum_vonMangoldt_ceil) where
  actual := tailReadout
  bridge := Iff.rfl
  variation := ⟨@log_tailLCM_eq_sum_vonMangoldt_ceil, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law tailReadout rejected rejected_law
  dependence := tail_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_tailLCM_eq_sum_vonMangoldt_ceil) (Realization indexedRealSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.TailCeiling.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.TailCeiling.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize indexedRealSignature tailReadout.readout tailReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailCeiling

namespace TailNormalization

abbrev arena : Arena where
  signature := indexedRealSignature
  Law R := ∀ {r x : ℕ}, 2 ≤ r → 0 < x →
    R.readout () r x / (r : ℝ) =
      (x : ℝ) * (∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
        Chebyshev.psi (x : ℝ) + ceilingError r x / (r : ℝ)

private theorem rejected_law : ¬ arena.Law TailCeiling.rejected := by
  intro h
  have h₁ := h (r := 2) (x := 1) (by decide) (by decide)
  change (Real.log (tailLCM 1 1 : ℝ) + 1) / 2 = _ at h₁
  have actual := log_tailLCM_div_eq_mangoldt (r := 2) (x := 1) (by decide) (by decide)
  linarith

def family : Registration arena (type_of% @log_tailLCM_div_eq_mangoldt) where
  actual := tailReadout
  bridge := Iff.rfl
  variation := ⟨@log_tailLCM_div_eq_mangoldt, TailCeiling.rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law tailReadout TailCeiling.rejected rejected_law
  dependence := tail_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_tailLCM_div_eq_mangoldt) (Realization indexedRealSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.TailNormalization.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.TailNormalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize indexedRealSignature tailReadout.readout tailReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailNormalization

namespace CeilingBounds

abbrev arena : Arena where
  signature := diagonalSignature
  Law R := ∀ r x : ℕ, 0 ≤ ceilingError r x ∧ ceilingError r x ≤ R.readout () () x

def rejected : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₀ : ceilingError 0 0 ≤ -1 := (h 0 0).2
  linarith [(ceilingError_bounds 0 0).1]

def family : Registration arena (type_of% @ceilingError_bounds) where
  actual := psiReadout
  bridge := Iff.rfl
  variation := ⟨@ceilingError_bounds, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law psiReadout rejected rejected_law
  dependence := psi_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ceilingError_bounds) (Realization diagonalSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.CeilingBounds.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.CeilingBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature psiReadout.readout psiReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CeilingBounds

namespace SignedCorrection

abbrev arena : Arena where
  signature := indexedRealSignature
  Law R := ∀ {r x : ℕ}, 2 ≤ r → 0 < x →
    R.readout () r x = U (x : ℝ) + ceilingError r x / (r : ℝ)

def rejected : Realization indexedRealSignature :=
  realize indexedRealSignature (fun _ r x => T r x + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := h (r := 2) (x := 1) (by decide) (by decide)
  change T 2 1 + 1 = _ at h₁
  linarith [T_eq_U_add_ceilingError (r := 2) (x := 1) (by decide) (by decide)]

def family : Registration arena (type_of% @T_eq_U_add_ceilingError) where
  actual := centeredReadout
  bridge := Iff.rfl
  variation := ⟨@T_eq_U_add_ceilingError, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law centeredReadout rejected rejected_law
  dependence := centered_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@T_eq_U_add_ceilingError) (Realization indexedRealSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.SignedCorrection.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.SignedCorrection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize indexedRealSignature centeredReadout.readout centeredReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedCorrection

namespace SignedBounds

abbrev arena : Arena where
  signature := indexedRealSignature
  Law R := ∀ {r x : ℕ}, 2 ≤ r → 0 < x →
    0 ≤ R.readout () r x - U (x : ℝ) ∧
      R.readout () r x - U (x : ℝ) ≤ Chebyshev.psi (x : ℝ) / (r : ℝ)

def rejected : Realization indexedRealSignature :=
  realize indexedRealSignature (fun _ _ x => U (x : ℝ) - 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := (h (r := 2) (x := 1) (by decide) (by decide)).1
  change 0 ≤ U ((1 : ℕ) : ℝ) - 1 - U ((1 : ℕ) : ℝ) at h₁
  linarith

def family : Registration arena (type_of% @T_sub_U_bounds) where
  actual := centeredReadout
  bridge := Iff.rfl
  variation := ⟨@T_sub_U_bounds, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law centeredReadout rejected rejected_law
  dependence := centered_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@T_sub_U_bounds) (Realization indexedRealSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.SignedBounds.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.SignedBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize indexedRealSignature centeredReadout.readout centeredReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedBounds

namespace DiagonalBounds

abbrev arena : Arena where
  signature := diagonalSignature
  Law R := ∀ {x : ℕ}, 2 ≤ x →
    0 ≤ R.readout () () x - U (x : ℝ) ∧
      R.readout () () x - U (x : ℝ) ≤ Real.log 4 + 4

def rejected : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ x => U (x : ℝ) - 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₂ : (0 : ℝ) ≤ U 2 - 1 - U 2 := (h (x := 2) (by decide)).1
  linarith

def family : Registration arena (type_of% @diagonal_sub_U_bounds) where
  actual := diagonalReadout
  bridge := Iff.rfl
  variation := ⟨@diagonal_sub_U_bounds, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law diagonalReadout rejected rejected_law
  dependence := diagonal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonal_sub_U_bounds) (Realization diagonalSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.DiagonalBounds.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.DiagonalBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature diagonalReadout.readout diagonalReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DiagonalBounds

namespace CenteredBlocks

abbrev arena : Arena where
  signature := diagonalSignature
  Law R := RiemannHypothesis ↔ ∀ A : ℕ, ∃ k ≥ max A 2,
    ∀ x : ℕ, k ^ 12 ≤ x → x ≤ k ^ 16 → R.readout () () x ≤ 2 * Real.sqrt (x : ℝ)

def rejected : Realization diagonalSignature := by
  classical
  exact realize diagonalSignature
    (fun _ _ x => if RiemannHypothesis then 2 * Real.sqrt (x : ℝ) + 1 else 0)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  change (RiemannHypothesis ↔ ∀ A : ℕ, ∃ k ≥ max A 2, ∀ x : ℕ,
    k ^ 12 ≤ x → x ≤ k ^ 16 →
    (if RiemannHypothesis then 2 * Real.sqrt (x : ℝ) + 1 else 0) ≤
      2 * Real.sqrt (x : ℝ)) at h
  by_cases hrh : RiemannHypothesis
  · obtain ⟨k, hk, hblock⟩ := h.mp hrh 2
    have hx := hblock (k ^ 12) le_rfl (block_left_le_right ((le_max_right 2 2).trans hk))
    rw [ite_eq_left hrh] at hx
    linarith
  · exact hrh (h.mpr fun A =>
      ⟨max A 2, le_rfl, fun x _ _ => by rw [ite_eq_right hrh]; positivity⟩)

def family : Registration arena (type_of% @rh_iff_cofinal_contentLCM_blocks) where
  actual := diagonalReadout
  bridge := Iff.rfl
  variation := ⟨@rh_iff_cofinal_contentLCM_blocks, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law diagonalReadout rejected rejected_law
  dependence := diagonal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_cofinal_contentLCM_blocks) (Realization diagonalSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.CenteredBlocks.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.CenteredBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature diagonalReadout.readout diagonalReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CenteredBlocks

namespace FactorialBounds

abbrev arena : Arena where
  signature := diagonalSignature
  Law R := ∀ {x : ℕ}, 1 ≤ x →
    Real.eulerMascheroniConstant * (x : ℝ) + 1 - Real.log (x : ℝ) ≤
      R.readout () () x - (x : ℝ) * Real.log (x : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (x : ℝ) ∧
    R.readout () () x - (x : ℝ) * Real.log (x : ℝ) +
      (1 + Real.eulerMascheroniConstant) * (x : ℝ) ≤
      Real.eulerMascheroniConstant * (x : ℝ) + 1

def rejected : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := (h (x := 1) le_rfl).2
  change (1 : ℝ) - ((1 : ℕ) : ℝ) * Real.log ((1 : ℕ) : ℝ) +
      (1 + Real.eulerMascheroniConstant) * ((1 : ℕ) : ℝ) ≤
    Real.eulerMascheroniConstant * ((1 : ℕ) : ℝ) + 1 at h₁
  rw [Nat.cast_one, Real.log_one] at h₁
  linarith

def family : Registration arena (type_of% @log_factorial_gamma_bounds) where
  actual := factorialReadout
  bridge := Iff.rfl
  variation := ⟨@log_factorial_gamma_bounds, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law factorialReadout rejected rejected_law
  dependence := factorial_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_factorial_gamma_bounds) (Realization diagonalSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.FactorialBounds.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.FactorialBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature factorialReadout.readout factorialReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FactorialBounds

namespace GammaThreshold

abbrev arena : Arena where
  signature := diagonalSignature
  Law R := ∀ {x : ℕ}, 2 ≤ x →
    Real.eulerMascheroniConstant * (x : ℝ) - R.readout () () x / (x : ℝ) +
      1 - Real.log (x : ℝ) - (Real.log 4 + 4) ≤ U (x : ℝ) ∧
    U (x : ℝ) ≤ Real.eulerMascheroniConstant * (x : ℝ) -
      R.readout () () x / (x : ℝ) + 1

def rejected : Realization diagonalSignature :=
  realize diagonalSignature
    (fun _ _ x => (Real.eulerMascheroniConstant * (x : ℝ) + 2 - U (x : ℝ)) * (x : ℝ))
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₂ : U 2 ≤ Real.eulerMascheroniConstant * 2 -
      (Real.eulerMascheroniConstant * 2 + 2 - U 2) * 2 / 2 + 1 :=
    (h (x := 2) (by decide)).2
  linarith

def family : Registration arena (type_of% @diagonal_gamma_threshold) where
  actual := gammaReadout
  bridge := Iff.rfl
  variation := ⟨@diagonal_gamma_threshold, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law gammaReadout rejected rejected_law
  dependence := gamma_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonal_gamma_threshold) (Realization diagonalSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.GammaThreshold.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.GammaThreshold.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature gammaReadout.readout gammaReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GammaThreshold

namespace WindowTransfer

-- The same real power operation supplies the window endpoint and both power bounds.
abbrev arena : Arena where
  signature := powerSignature
  Law R := (∀ δ : ℝ, 0 < δ → ∀ B : ℝ, ∃ Y : ℝ, max B 1 ≤ Y ∧
      ∀ t ∈ Set.Icc Y (R.readout () () Y ((3 : ℝ) / 2)),
        U t ≤ R.readout () () t ((1 : ℝ) / 2 + δ)) →
    ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ x : ℕ, k ^ 12 ≤ x → x ≤ k ^ 16 →
        Real.eulerMascheroniConstant * (x : ℝ) ^ 2 -
          R.readout () () (x : ℝ) ((3 : ℝ) / 2 + ε) ≤ Real.log (contentLCM x x : ℝ)

def rejected : Realization powerSignature := by
  classical
  exact realize powerSignature
    (fun _ _ x a => if a = (3 : ℝ) / 2 then 0 else
      Real.eulerMascheroniConstant * x ^ 2 -
        Real.log (contentLCM ⌊x⌋₊ ⌊x⌋₊ : ℝ) - 1)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have windows : ∀ δ : ℝ, 0 < δ → ∀ B : ℝ, ∃ Y : ℝ, max B 1 ≤ Y ∧
      ∀ t ∈ Set.Icc Y (rejected.readout () () Y ((3 : ℝ) / 2)),
        U t ≤ rejected.readout () () t ((1 : ℝ) / 2 + δ) := by
    intro δ _ B
    refine ⟨max B 1, le_rfl, ?_⟩
    intro t ht
    have ht₀ : t ≤ 0 := by simpa [rejected, realize] using ht.2
    linarith [ht.1, le_max_right B (1 : ℝ)]
  obtain ⟨k, hk, hblock⟩ := h windows 1 zero_lt_one 2
  have hx := hblock (k ^ 12) le_rfl (block_left_le_right ((le_max_right 2 2).trans hk))
  change Real.eulerMascheroniConstant * ((k ^ 12 : ℕ) : ℝ) ^ 2 -
    rejected.readout () () ((k ^ 12 : ℕ) : ℝ) ((3 : ℝ) / 2 + 1) ≤ _ at hx
  have hexponent : (3 : ℝ) / 2 + 1 ≠ (3 : ℝ) / 2 := by norm_num
  simp only [rejected, realize, ite_eq_right hexponent, Nat.floor_natCast] at hx
  linarith

def family : Registration arena (type_of% @contentLCM_gamma_blocks_of_pointwise_windows) where
  actual := powerReadout
  bridge := Iff.rfl
  variation := ⟨@contentLCM_gamma_blocks_of_pointwise_windows, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law powerReadout rejected rejected_law
  dependence := power_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@contentLCM_gamma_blocks_of_pointwise_windows) (Realization powerSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.WindowTransfer.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.WindowTransfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize powerSignature powerReadout.readout powerReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["domain", "body", "body", "body", "arg", "body", "arg", "body", "domain", "fn",
        "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WindowTransfer

namespace GammaBlocks

abbrev arena : Arena where
  signature := diagonalSignature
  Law R := RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ k ≥ max A 2,
    ∀ x : ℕ, k ^ 12 ≤ x → x ≤ k ^ 16 →
      Real.eulerMascheroniConstant * (x : ℝ) ^ 2 - (x : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
        R.readout () () x

def rejected : Realization diagonalSignature := by
  classical
  exact realize diagonalSignature (fun _ _ x =>
    if RiemannHypothesis then
      Real.eulerMascheroniConstant * (x : ℝ) ^ 2 - (x : ℝ) ^ ((3 : ℝ) / 2 + 1) - 1
    else Real.eulerMascheroniConstant * (x : ℝ) ^ 2)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  by_cases hrh : RiemannHypothesis
  · obtain ⟨k, hk, hblock⟩ := h.mp hrh 1 zero_lt_one 2
    have hx := hblock (k ^ 12) le_rfl (block_left_le_right ((le_max_right 2 2).trans hk))
    simp only [rejected, realize, ite_eq_left hrh] at hx
    linarith
  · apply hrh
    apply h.mpr
    intro ε _ A
    refine ⟨max A 2, le_rfl, fun x _ _ => ?_⟩
    simp only [rejected, realize, ite_eq_right hrh, sub_le_self_iff]
    positivity

def family : Registration arena (type_of% @rh_iff_cofinal_contentLCM_gamma_blocks) where
  actual := gammaReadout
  bridge := Iff.rfl
  variation := ⟨@rh_iff_cofinal_contentLCM_gamma_blocks, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law gammaReadout rejected rejected_law
  dependence := gamma_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_cofinal_contentLCM_gamma_blocks) (Realization diagonalSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.GammaBlocks.unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge.GammaBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature gammaReadout.readout gammaReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GammaBlocks

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
