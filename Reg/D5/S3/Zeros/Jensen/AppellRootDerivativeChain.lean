import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.AppellRootDerivativeChain
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.AppellRootDerivativeChain
open LeanInformationAudit Polynomial
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Zeros.Jensen.AppellRootDerivativeChain

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Replace exactly the coefficient-norm operand and retain the complete original telescope. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} {P : ℂ[X]} {β σ : ℂ} {a : ℝ} {g : ℕ → ℂ}
    (_hq : 1 ≤ q) (_hdeg : P.natDegree = q) (_hroot : P.eval β = 0)
    (_hσ : σ ≠ 0) (_ha : 0 < a)
    (_hode : C (σ ^ 2) * P.derivative.derivative - X * P.derivative + C (q : ℂ) * P =
      ∑ m ∈ Finset.Ico 2 q, C (g m) * (derivative^[m + 1] P))
    (_hrow : ‖β‖ / (‖σ‖ ^ 2 * a) + (q : ℝ) / (‖σ‖ ^ 2 * a ^ 2) +
      (∑ m ∈ Finset.Ico 2 q, R.readout () () (g m) * a ^ (m - 1) / ‖σ‖ ^ 2) < 1),
    P.derivative.eval β ≠ 0 ∧ ∀ m : ℕ, 1 ≤ m → m ≤ q →
      ‖(derivative^[m] P).eval β / P.derivative.eval β‖ ≤ a ^ (m - 1)

theorem positive_law : arena.Law actual := @actual_root_derivative_chain

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let P : ℂ[X] := X ^ 3 - C 3 * X + C 2
  have hdeg : P.natDegree = 3 := by
    dsimp [P]; compute_degree <;> norm_num
  have hroot : P.eval 1 = 0 := by norm_num [P]
  have hode : C ((1 : ℂ) ^ 2) * P.derivative.derivative - X * P.derivative + C (3 : ℂ) * P =
      ∑ m ∈ Finset.Ico 2 3, C (1 : ℂ) * (derivative^[m + 1] P) := by
    norm_num [P, show Finset.Ico 2 3 = {2} by decide, Function.iterate_succ_apply',
      derivative_pow, derivative_mul, C_ofNat]
    ring
  have hbudget : ‖(1 : ℂ)‖ / (‖(1 : ℂ)‖ ^ 2 * (16 : ℝ)) +
      (3 : ℝ) / (‖(1 : ℂ)‖ ^ 2 * (16 : ℝ) ^ 2) +
      (∑ m ∈ Finset.Ico 2 3,
        rejected.readout () () (1 : ℂ) * (16 : ℝ) ^ (m - 1) / ‖(1 : ℂ)‖ ^ 2) < 1 := by
    norm_num [rejected, realize]
  have hbad := (h (P := P) (β := 1) (σ := 1) (a := 16) (g := fun _ => 1)
    (by norm_num) hdeg hroot one_ne_zero (by norm_num) hode hbudget).1
  exact hbad (by norm_num [P, derivative_pow, derivative_mul])

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e; exact nomatch e

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positive_law, rejected, rejected_law⟩
    sensitivity_proof dependence_proof

noncomputable def registration_1 : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@actual_root_derivative_chain)
    (type_of% (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.Jensen.AppellRootDerivativeChain.__information_unit,
  realizationName := `Reg.D5.S3.Zeros.Jensen.AppellRootDerivativeChain.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.AppellRootDerivativeChain,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "domain",
        "fn", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Zeros.Jensen.AppellRootDerivativeChain
