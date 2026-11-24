import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction

/-! The actual charge-zero restriction as an observation of a lawful mixed field. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.ActualLeechHyperbolic (leechData leech_spec)
open _root_.D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

private abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Bool
  (fun s => LawfulMixedField leechData leechUnit s)
  (fun s => ℤ → chargeZeroOdd leechData →ₗ[ℂ] Twisted leechData leechUnit s →ₗ[ℂ]
    Twisted leechData leechUnit (!s))

private def actual : Realization signature :=
  realize signature (fun _ s => restrictChargeZero leechData leechUnit s) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Bool, Function.Injective (R.readout () s)

private def zeroField (s : Bool) : LawfulMixedField leechData leechUnit s where
  coeff := 0
  truncation := fun _ _ => ⟨0, fun _ _ => rfl⟩
  derivative := by simp
  borcherds := by
    intro a b v p q r
    simp [mixedBorcherds, Function.HasFiniteSupport]

private theorem native_ne_zero : nativeMixedField leechData leechUnit false ≠ zeroField false := by
  intro h
  let i : Fin leechData.rank := ⟨0, by rw [leech_spec.1]; decide⟩
  have hmode := congrArg
    (fun F : LawfulMixedField leechData leechUnit false =>
      F.coeff (-1) (oddCurrent leechData i) leechGroundVector) h
  have hnonzero := (leech_normalization i).2.2.1
  exact hnonzero hmode

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact native_ne_zero (h false (a₁ := nativeMixedField leechData leechUnit false)
    (a₂ := zeroField false) rfl)

def restrictionFamily : Registration arena (type_of% @leech_restrictChargeZero_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨leech_restrictChargeZero_injective, rejected, rejectedLaw⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro i
    cases i
    refine ⟨false, nativeMixedField leechData leechUnit false, zeroField false, ?_⟩
    exact fun h => native_ne_zero (leech_restrictChargeZero_injective false h)

def restrictionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@leech_restrictChargeZero_injective) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner.leech_restrictChargeZero_injective.__information_unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction.restrictionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨restrictionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s => restrictChargeZero leechData leechUnit s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
