import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Recovery.BKMPowerPullback

/-! The cube pullback equality detects deletion of the normalization factor. -/

noncomputable section

open LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Recovery.BKMRelativeDensity (omega)
open _root_.D5.S3.Quantum.Recovery.BKMPowerPullback (omega_cube)

namespace Reg.D5.S3.Quantum.Recovery.BKMPowerPullback

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u)
    (fun ι => Matrix ι ι ℂ) (fun ι => Matrix ι ι ℂ → Prop)

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

private def unscaled : Realization signature.{u} :=
  realize signature (fun _ _ X Y => X = (3 : ℝ) • Y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℂ} (_hB : B.PosDef) (X : Matrix ι ι ℂ),
    R.readout () ι (omega (B ^ (3 : ℕ)) X)
      ((1 / 3 : ℝ) •
        (B ^ (2 : ℕ) * omega B X + B * omega B X * B + omega B X * B ^ (2 : ℕ)))

private theorem unscaled_law : ¬ arena.{u}.Law unscaled.{u} := by
  intro h
  let ι := ULift.{u} Unit
  let p : ι := ULift.up ()
  let M := Matrix ι ι ℂ
  have hp (t : ℝ) : mpow (1 : M) t = 1 := by
    rw [mpow, ← CFC.rpow_eq_cfc_real (zero_le_one : (0 : M) ≤ 1)]
    exact CFC.one_rpow
  have hOne : omega (1 : M) 1 = 1 := by
    simp [omega, hp, intervalIntegral.integral_const]
  have hbad := h (B := (1 : M)) Matrix.PosDef.one (1 : M)
  change omega ((1 : M) ^ (3 : ℕ)) 1 = (3 : ℝ) •
    ((1 / 3 : ℝ) •
      ((1 : M) ^ (2 : ℕ) * omega (1 : M) 1 +
        (1 : M) * omega (1 : M) 1 * 1 + omega (1 : M) 1 * (1 : M) ^ (2 : ℕ))) at hbad
  rw [← omega_cube (B := (1 : M)) Matrix.PosDef.one (1 : M)] at hbad
  have he : (1 : M) = (3 : ℝ) • (1 : M) := by
    simpa only [one_pow, hOne] using hbad
  have hdiag : (1 : M) p p = (1 : ℂ) := Matrix.one_apply_eq p
  have hentry : (1 : M) p p = (3 : ℝ) • ((1 : M) p p) :=
    congrArg (fun A : M => A p p) he
  rw [hdiag] at hentry
  have hre : (1 : ℝ) = 3 := by
    simpa only [Complex.real_smul, mul_one, Complex.one_re, Complex.ofReal_re] using
      congrArg Complex.re hentry
  norm_num at hre

def registration : Registration arena.{u} (type_of% @omega_cube.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omega_cube.{u}, unscaled, unscaled_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual unscaled unscaled_law
  dependence := by
    intro role
    let ι := ULift.{u} Unit
    let p : ι := ULift.up ()
    let A : Matrix ι ι ℂ := fun _ _ => 1
    refine ⟨ι, 0, A, ?_⟩
    intro h
    have he : A = 0 := Eq.mp (congrFun h 0) rfl
    exact one_ne_zero (show (1 : ℂ) = 0 from congrArg (fun Y : Matrix ι ι ℂ => Y p p) he)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omega_cube.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMPowerPullback.omega_cube.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMPowerPullback.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMPowerPullback
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.BKMPowerPullback
