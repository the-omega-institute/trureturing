import LeanInformationAuditInterface.Contract.Registration
import D5.S3.PrimeGaps.ModFourChebyshev
import Reg.Support.SingleDependentReadout

/-! Source observations for the classical prime-count lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.PrimeGaps.ModFourChebyshev

namespace Reg.D5.S3.PrimeGaps.ModFourChebyshev

namespace PrimeCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (primeCount x : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, exp 50 ≤ x → exp (-50) * x / log x ≤ R.readout () () x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : exp (-50) * exp 50 / log (exp 50) ≤ (0 : ℝ) :=
    h (x := exp 50) le_rfl
  rw [log_exp, ← exp_add] at h'
  norm_num at h'

def family : Registration arena
    (type_of% @_root_.D5.S3.PrimeGaps.ModFourChebyshev.prime_count_lower) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.PrimeGaps.ModFourChebyshev.prime_count_lower,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 5, ?_⟩
    change (primeCount 0 : ℝ) ≠ (primeCount 5 : ℝ)
    have hzero : primeCount 0 = 0 := by simp [primeCount]
    have hfive : primeCount 5 = 1 := by
      unfold primeCount
      rw [Nat.floor_ofNat]
      have hfilter : ((Finset.Ioc 0 5).filter
          (fun p : ℕ => p.Prime ∧ p % 4 = 1)) = {5} := by decide
      rw [hfilter, Finset.card_singleton]
    rw [hzero, hfive]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.PrimeGaps.ModFourChebyshev.prime_count_lower)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.PrimeGaps.ModFourChebyshev.prime_count_lower.audit
  realizationName := `Reg.D5.S3.PrimeGaps.ModFourChebyshev.PrimeCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.PrimeGaps.ModFourChebyshev
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeCount

end Reg.D5.S3.PrimeGaps.ModFourChebyshev
