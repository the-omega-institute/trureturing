import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.OriginalSignedPrimeBound
import Reg.Support.DependentFamily

/-! Uncompiled owner-mirrored registration candidate for the unchanged
full-complex original_prime80 statement. No declared_validated claim is made.
The observed operand is the original squared L2 norm, on the full WindowL2
carrier. A cosine mode is used only as a witness that this norm is nonconstant;
it places no restriction on the mathematical theorem's quantified input. -/

namespace Reg.D5.S3.Weil.ZetaBridge.OriginalSignedPrimeBound

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory Set
open scoped ComplexConjugate
open _root_.PhysicalCompressedCosineMatrix
open _root_.D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining (primeSymmetric)

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := PhysicalCosineTailProjection.WindowL2 (Real.log (p.1 : ℝ) / 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => ‖u‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (c : ℕ) (_hc : c = 5040 ∨ c = 5041) (M : ℕ)
    (_hM : primeCutoff (Real.log (c : ℝ) / 2) ≤ M)
    (u : PhysicalCosineTailProjection.WindowL2 (Real.log (c : ℝ) / 2)),
    ‖∫ x in window (Real.log (c : ℝ) / 2),
        conj (zeroExtension (Real.log (c : ℝ) / 2) u x) *
          (-primeSymmetric (Real.log (c : ℝ) / 2) M
            (zeroExtension (Real.log (c : ℝ) / 2) u) x)‖ ≤
      80 * R.readout () ⟨c, M⟩ u

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 5041 (Or.inr rfl)
    (primeCutoff (Real.log (5041 : ℝ) / 2)) le_rfl
    (0 : PhysicalCosineTailProjection.WindowL2 (Real.log (5041 : ℝ) / 2))
  have hp : (0 : ℝ) ≤ 80 * (-1) := (norm_nonneg _).trans hz
  norm_num at hp

private lemma actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let a : ℝ := Real.log (5041 : ℝ) / 2
  have ha : 0 < a := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨⟨5041, primeCutoff a⟩, 0, PhysicalCosineTailProjection.modeL2 a 0, ?_⟩
  change ‖(0 : PhysicalCosineTailProjection.WindowL2 a)‖ ^ 2 ≠
    ‖PhysicalCosineTailProjection.modeL2 a 0‖ ^ 2
  have hn := (PhysicalCosineTailProjection.modes_orthonormal a ha).norm_eq_one 0
  rw [norm_zero, hn]
  norm_num

def family : Registration arena
    (type_of% (@_root_.OriginalSignedPrimeFourier.original_prime80)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.OriginalSignedPrimeFourier.original_prime80, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit (inferInstance : Subsingleton Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.OriginalSignedPrimeFourier.original_prime80)
    (type_of% (realize signature
      (fun _ _ u => ‖u‖ ^ 2) (fun e => nomatch e))) Type Unit where
  unitName := `OriginalSignedPrimeFourier.original_prime80.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.OriginalSignedPrimeBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ u => ‖u‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (PhysicalCosineTailProjection.WindowL2 (Real.log (5041 : ℝ) / 2))
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.OriginalSignedPrimeBound
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Weil.ZetaBridge.OriginalSignedPrimeFourier
