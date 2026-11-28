import LeanInformationAuditInterface.Contract.Registration
import Batteries.Tactic.OpenPrivate
import D5.S1.Eigenstructure.WiersigFragmentedResponse
import Reg.Support.SingleDependentReadout

/-! # Source registration of the passive fragmented loss-rank bound -/

set_option autoImplicit false

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Module LeanInformationAudit
open _root_.D5.S1.Eigenstructure.WiersigFragmentedResponse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private Positions from D5.S1.Eigenstructure.WiersigFragmentedResponse

noncomputable section

namespace Reg.D5.S1.Eigenstructure.WiersigFragmentedResponse

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Bool)

private def rankLE (b : ℕ) : (rank : ℕ) → Decidable (b ≤ rank) := by
  induction b with
  | zero => exact fun rank => .isTrue (Nat.zero_le rank)
  | succ b smaller =>
    intro rank
    cases rank with
    | zero => exact .isFalse (Nat.not_succ_le_zero b)
    | succ rank =>
      exact match smaller rank with
      | .isTrue h => .isTrue (Nat.succ_le_succ h)
      | .isFalse h => .isFalse (fun h' => h (Nat.le_of_succ_le_succ h'))

def actual : Realization signature :=
  realize signature (fun _ b rank => @decide (b ≤ rank) (rankLE b rank)) (fun e => nomatch e)

def strictRank : Realization signature :=
  realize signature (fun _ b rank => decide (b < rank)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {b p : ℕ} (m : Fin b → ℕ+)
    (_hb : 2 ≤ b) (_hp : 2 ≤ p) (_hm : ∀ j, (m j : ℕ) ≤ p)
    (_hmax : ∃ j, (m j : ℕ) = p) (E : ℂ) (_hβ : 0 < -2 * E.im),
    let admissible := fun H : Matrix (Positions m) (Positions m) ℂ =>
      (Complex.I • (H - Hᴴ)).PosSemidef ∧
      ∃ B : Basis (Σ j, Fin (m j)) ℂ (Positions m → ℂ),
        ∀ (k : ℕ) (j : Fin b) (a : Fin (m j)),
          ((H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ k) *ᵥ B ⟨j, a⟩ =
            if h : a.val + k < m j then B ⟨j, ⟨a.val + k, h⟩⟩ else 0
    (∀ H, admissible H →
      let N := H - E • (1 : Matrix (Positions m) (Positions m) ℂ)
      N ^ (p - 1) ≠ 0 ∧
      ‖N ^ (p - 1)‖ ≤ (-2 * E.im) ^ (p - 1) ∧
      R.readout () b (Complex.I • (H - Hᴴ)).rank = true ∧
      (∀ z : ℂ, ¬ IsUnit (z • (1 : Matrix (Positions m) (Positions m) ℂ) - H) ↔ z = E) ∧
      ∀ z : ℂ, z ≠ E → (z • (1 : Matrix (Positions m) (Positions m) ℂ) - H)⁻¹ =
        ∑ k ∈ Finset.range p, ((z - E)⁻¹) ^ (k + 1) • N ^ k) ∧
    (∃ H, admissible H ∧
      ‖(H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ (p - 1)‖ = (-2 * E.im) ^ (p - 1) ∧
      (Complex.I • (H - Hᴴ)).rank = b)

private theorem source_bridge :
    (type_of% (@sharp_passive_fragmented_response)) ↔ arena.Law actual := by
  constructor <;> intro law b p m hb hp hm hmax E hβ <;>
    simpa only [actual, realize, decide_eq_true_eq] using law m hb hp hm hmax E hβ

private theorem strict_rank_fails : ¬ arena.Law strictRank := by
  intro law
  let m : Fin 2 → ℕ+ := fun j => if j = 0 then 2 else 1
  have hm : ∀ j, (m j : ℕ) ≤ 2 := by
    intro j
    fin_cases j <;> decide
  have hmax : ∃ j, (m j : ℕ) = 2 := ⟨0, by decide⟩
  have hβ : 0 < -2 * (-Complex.I).im := by norm_num [Complex.neg_im, Complex.I_im]
  have original := sharp_passive_fragmented_response m (b := 2) (p := 2)
    (by decide) (by decide) hm hmax (-Complex.I) hβ
  obtain ⟨H, hH, _, hrank⟩ := original.2
  have altered := @law 2 2 m (by decide) (by decide) hm hmax (-Complex.I) hβ
  have hlt : 2 < (Complex.I • (H - Hᴴ)).rank := of_decide_eq_true (altered.1 H hH).2.2.1
  rw [hrank] at hlt
  exact (Nat.lt_irrefl 2) hlt

def evidence : Registration arena (type_of% (@sharp_passive_fragmented_response)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@sharp_passive_fragmented_response), strictRank, strict_rank_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ strict_rank_fails
  dependence := by
    intro _role
    refine ⟨2, 1, 2, ?_⟩
    change @decide (2 ≤ 1) (rankLE 2 1) ≠ @decide (2 ≤ 2) (rankLE 2 2)
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sharp_passive_fragmented_response) (Realization signature) Unit Unit where
  unitName := Lean.Name.str ``sharp_passive_fragmented_response "__information_unit"
  realizationName := `Reg.D5.S1.Eigenstructure.WiersigFragmentedResponse.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.WiersigFragmentedResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Eigenstructure.WiersigFragmentedResponse
