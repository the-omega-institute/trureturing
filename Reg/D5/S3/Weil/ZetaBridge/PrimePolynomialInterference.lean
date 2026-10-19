import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.PrimePolynomialInterference
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference

open scoped BigOperators
open Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev absoluteSignature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def absoluteActual : Realization absoluteSignature :=
  realize absoluteSignature (fun _ _ x => |x|) (fun e => nomatch e)

def absoluteRejected : Realization absoluteSignature :=
  realize absoluteSignature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def prime_polynomial_interference_bound_arena : Arena where
  signature := absoluteSignature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c)
    (d : ℕ) {N : ℕ} (hN : 0 < N) (F B : ℂ[X])
    (hF : F.natDegree < d) (hB : B.natDegree < d),
    r.readout () () (∑ m ∈ Finset.Icc (N + 1) (2 * N),
      _root_.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primeSymbol c (m : ℤ) *
        (F.eval ((m : ℂ) / (N : ℂ)) *
          star (B.eval ((m : ℂ) / (N : ℂ)))).re) ≤
      _root_.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.primeFirstMoment c *
        (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        ((∑ r ∈ Finset.range d, ‖F.coeff r‖ ^ 2) +
          ∑ r ∈ Finset.range d, ‖B.coeff r‖ ^ 2)

private theorem actual_law :
    prime_polynomial_interference_bound_arena.Law absoluteActual := by
  exact @_root_.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference.prime_polynomial_interference_bound

private theorem rejected_law :
    ¬ prime_polynomial_interference_bound_arena.Law absoluteRejected := by
  intro h
  have hzero := h (c := 2) (by decide) 1 (N := 1) (by decide)
    (0 : ℂ[X]) (0 : ℂ[X]) (by simp) (by simp)
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [absoluteRejected, realize] using hzero
  norm_num at hbad

private theorem absolute_dependence :
    ObservationalDependence absoluteSignature absoluteActual := by
  intro _
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  norm_num [absoluteActual, realize]

def prime_polynomial_interference_bound_family :
    Registration prime_polynomial_interference_bound_arena
      (type_of% (@_root_.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference.prime_polynomial_interference_bound)) where
  actual := absoluteActual
  bridge := Iff.rfl
  variation := ⟨actual_law, absoluteRejected, rejected_law⟩
  sensitivity := by
    refine ⟨?_, ?_⟩
    · intro role
      refine ⟨absoluteRejected, ?_, rfl, rejected_law⟩
      intro other hother
      exact (hother (Subsingleton.elim (α := Unit) other role)).elim
    · exact fun impossible => nomatch impossible
  dependence := absolute_dependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference.prime_polynomial_interference_bound)
    (type_of% absoluteActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference.prime_polynomial_interference_bound.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference.prime_polynomial_interference_bound_family
  realizationSource := none
  generated := false
  arena := .source ⟨prime_polynomial_interference_bound_arena⟩
  objectArena := .source ⟨prime_polynomial_interference_bound_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prime_polynomial_interference_bound_arena
    ⟨prime_polynomial_interference_bound_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize absoluteSignature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimePolynomialInterference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaBridge.PrimePolynomialInterference
