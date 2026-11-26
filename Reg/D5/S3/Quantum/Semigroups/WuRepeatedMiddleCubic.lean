import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Source-bound readouts for the repeated-middle deficit identity and comparison. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private gamma h c e bias gibbsLow gibbsHigh cutA cutB entropyPair from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

namespace Reg.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence (relation : ℝ → ℝ → Prop)
    (hzero : relation 0 0) (hone : ¬ relation 1 0) :
    ObservationalDependence signature
      (realize signature (fun _ _ x y => relation x y) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro hreadout
  exact hone (Eq.mp (congrFun hreadout 0) hzero)

private abbrev occupationEquiv : Occupation ≃ Fin 4 := finProdFinEquiv

private abbrev testFrame : Frame :=
  (1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix occupationEquiv (Equiv.refl _)

private theorem testFrame_unitary : testFrameᴴ * testFrame = 1 ∧ testFrame * testFrameᴴ = 1 := by
  constructor
  · simp only [testFrame, conjTranspose_submatrix, conjTranspose_one,
      submatrix_mul_equiv, mul_one, submatrix_one_equiv]
  · simp only [testFrame, conjTranspose_submatrix, conjTranspose_one,
      submatrix_mul_equiv, mul_one, submatrix_one_equiv]

namespace Decomposition

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ (r : ℝ) (U : Frame), Uᴴ * U = 1 → U * Uᴴ = 1 →
    ∀ {m n : ℝ}, 0 ≤ m → 0 ≤ n →
    W.readout () () (centeredDeficit r U m n)
      (oneModeDeficit r m n (-cutCoordinate (-imbalance U 0)) +
        oneModeDeficit r n 1 (-cutCoordinate (imbalance U 3)) +
        oneModeDeficit r (blockRoot m n) (blockRoot n 1) (-1) +
        gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n +
        frameRemainder r U m n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  exact hlaw 1 testFrame testFrame_unitary.1 testFrame_unitary.2
    (m := 0) (n := 0) le_rfl le_rfl

def family : Registration arena (type_of% @repeated_middle_decomposition) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@repeated_middle_decomposition, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejected rejected_law
  dependence := dependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_middle_decomposition) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.repeated_middle_decomposition.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.Decomposition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Decomposition

namespace LowerBound

private theorem log_cubic_bound {t : ℝ} (ht : 1 ≤ t) :
    Real.log ((1 + t^3) / 2) ≤ 3 / 8 * (t - 1) * (t + 3) := by
  let d := t - 1
  let a := 3 / 2 * d + 3 / 8 * d^2
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hd : 0 ≤ d := sub_nonneg.mpr ht
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : (1 + t^3) / 2 ≤ 1 + a + a^2 / 2 := by
    have hid : 1 + a + a^2 / 2 - (1 + t^3) / 2 = d^3 / 16 + 9 * d^4 / 128 := by
      dsimp [a, d]
      ring
    exact sub_nonneg.mp (by rw [hid]; positivity)
  rw [Real.log_le_iff_le_exp (by positivity)]
  have haq : a = 3 / 8 * (t - 1) * (t + 3) := by
    dsimp [a, d]
    ring
  exact haq ▸ he.trans (Real.quadratic_le_exp_of_nonneg ha)

private theorem tracial_entropy {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    0 ≤ (9 / 8 : ℝ) * (w - v)^2 * (w + v) + entropyPair v w := by
  let F (x : ℝ) := (9 / 8 : ℝ) * (w - x)^2 * (w + x) + entropyPair x w
  have hcont : Continuous F := by
    unfold F entropyPair
    have hs : Continuous fun x : ℝ => (x^3 + w^3) / 2 := by fun_prop
    have hmass : (fun x : ℝ => (x^3 + w^3) * Real.log ((x^3 + w^3) / 2)) =
        fun x => 2 * (((x^3 + w^3) / 2) * Real.log ((x^3 + w^3) / 2)) := by
      funext x
      ring
    simp_rw [congrFun hmass]
    have h₁ := Real.continuous_mul_log.comp hs
    have hcube : Continuous fun x : ℝ => x^3 := by fun_prop
    have h₂ := Real.continuous_mul_log.comp hcube
    have hp : Continuous fun x : ℝ => (9 / 8 : ℝ) * (w - x)^2 * (w + x) := by fun_prop
    exact hp.add (((h₁.const_mul 2).sub h₂).sub continuous_const)
  have hderiv (x : ℝ) (hx : 0 < x) (hxw : x < w) :
      HasDerivAt F
        ((9/8 : ℝ) * (x-w) * (3*x+w) +
          3*x^2 * (Real.log ((x^3+w^3)/2) - Real.log (x^3))) x := by
    have hw : 0 < w := hx.trans hxw
    have hp : HasDerivAt (fun y : ℝ => y^3) (3*x^2) x := by
      simpa using hasDerivAt_pow 3 x
    have hsum := (hp.add_const (w^3)).div_const 2
    have hs : (x^3 + w^3) / 2 ≠ 0 := by positivity
    have h₁ := (Real.hasDerivAt_mul_log hs).comp x hsum
    have hx3 : x^3 ≠ 0 := pow_ne_zero 3 hx.ne'
    have h₂ := (Real.hasDerivAt_mul_log (x := x^3) hx3).comp
      (h := fun y : ℝ => y^3) x hp
    have hpoly := (((hasDerivAt_id x).const_sub w).pow 2).mul ((hasDerivAt_id x).const_add w)
    convert ((hpoly.const_mul (9/8 : ℝ)).add (h₁.const_mul 2) |>.sub h₂ |>.sub_const
      (w^3 * Real.log (w^3))) using 1 <;> simp [F, entropyPair, Function.comp_def]
    · funext y
      ring
    · ring
  have hanti : AntitoneOn F (Set.Icc 0 w) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 w) hcont.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x hx.1 hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hx.1
      have hxw : x < w := hx.2
      have hw : 0 < w := hx0.trans hxw
      have hlog := log_cubic_bound (t := w / x) ((le_div_iff₀ hx0).2 (by simpa using hxw.le))
      have hratio : (1 + (w / x)^3) / 2 = ((x^3+w^3)/2) / x^3 := by
        field_simp [hx0.ne']
        <;> ring
      rw [hratio, Real.log_div (by positivity) (pow_ne_zero 3 hx0.ne')] at hlog
      have hscaled := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 3*x^2 by positivity)
      have hpoly : 3*x^2 * (3/8 * (w/x-1) * (w/x+3)) =
          (9/8 : ℝ) * (w-x) * (3*x+w) := by
        field_simp [hx0.ne']
        <;> ring
      rw [hpoly] at hscaled
      rw [(hderiv x hx0 hxw).deriv]
      linarith only [hscaled]
  have hFw : F w = 0 := by
    unfold F entropyPair
    rw [show (w^3 + w^3) / 2 = w^3 by ring]
    ring
  have hle := hanti (show v ∈ Set.Icc 0 w from ⟨hv, hvw⟩)
    (show w ∈ Set.Icc 0 w from ⟨hv.trans hvw, le_rfl⟩) hvw
  rw [hFw] at hle
  exact hle

-- A feasible input for the premise of the comparison, used in the variation proof.
private theorem tracial_oneModeBound : OneModeBound 1 := by
  intro v w z hv hvw _ _
  have hw := hv.trans hvw
  have he := tracial_entropy hv hvw
  have hz : 0 ≤ (9/8 : ℝ) * (w-v)^2 * (w+v) * z^2 := by positivity
  norm_num [oneModeDeficit, h, alpha, gibbsLow, gibbsHigh, cutA, cutB, c, e, gamma, bias]
  nlinarith only [he, hz]

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r → OneModeBound r →
    ∀ (U : Frame), Uᴴ * U = 1 → U * Uᴴ = 1 →
    ∀ {m n : ℝ}, 0 ≤ m → m ≤ n → n ≤ 1 →
    0 ≤ gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n ∧
    0 ≤ frameRemainder r U m n ∧
    W.readout () ()
      (gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n + frameRemainder r U m n)
      (sourceDeficit r U m n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  exact (hlaw (r := 1) le_rfl tracial_oneModeBound testFrame
    testFrame_unitary.1 testFrame_unitary.2 (m := 0) (n := 0) le_rfl le_rfl zero_le_one).2.2

def family : Registration arena (type_of% @repeated_middle_lower_bound) where
  actual := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@repeated_middle_lower_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejected rejected_law
  dependence := dependence (· ≤ ·) le_rfl (by norm_num)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_middle_lower_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.repeated_middle_lower_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.LowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LowerBound

end Reg.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
