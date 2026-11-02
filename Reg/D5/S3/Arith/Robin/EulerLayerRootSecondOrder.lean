import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayerRootSecondOrder
import Reg.Support.DependentFamily

/-! Faithful source telescope for the strict Euler second-order root law. -/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.EulerLayerRootSecondOrder

open _root_.D5.S3.Arith.Robin.EulerLayerRootSecondOrder
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev rootSecondOrderScope := type_of% (@strict_inventory_root_second_order)

abbrev rootSecondOrderSignature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rootSecondOrderActual : Realization rootSecondOrderSignature :=
  realize rootSecondOrderSignature
    (fun _ t U => Real.log t *
      ((Real.log U - Chebyshev.psi t) / Real.sqrt t - (Real.sqrt 2 - 1)) +
        Real.sqrt 2 * Real.log 2 / 2)
    (fun e => nomatch e)

abbrev rootSecondOrderArena : Arena where
  signature := rootSecondOrderSignature
  Law V := ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |V.readout () t U| < ε

theorem root_second_order_source_bridge : rootSecondOrderScope ↔
    rootSecondOrderArena.Law rootSecondOrderActual := Iff.rfl

theorem root_second_order_actual_law : rootSecondOrderArena.Law rootSecondOrderActual :=
  strict_inventory_root_second_order

def rootSecondOrderRejected : Realization rootSecondOrderSignature :=
  realize rootSecondOrderSignature (fun _ _ _ => Real.sqrt 2)
    (fun e => nomatch e)

private theorem root_second_order_rejected_law :
    ¬ rootSecondOrderArena.Law rootSecondOrderRejected := by
  intro h
  obtain ⟨T, hT, hbad⟩ := h (1 / 2) (by norm_num)
  let t : ℝ := max T (Real.exp 1)
  have htT : T ≤ t := le_max_left _ _
  have ht1 : 1 < t := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) (le_max_right _ _)
  have hprice : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht1))
  obtain ⟨U, hU, hcounts, _⟩ := optimal_layer_count_spec hprice
  have hh := hbad t htT U (by omega) (fun q _ => hcounts q)
  change |Real.sqrt 2| < (1 / 2 : ℝ) at hh
  have hsqrt : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  linarith

def rootSecondOrderFamily : Registration rootSecondOrderArena rootSecondOrderScope where
  actual := rootSecondOrderActual
  bridge := root_second_order_source_bridge
  variation := ⟨root_second_order_actual_law, rootSecondOrderRejected,
    root_second_order_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rootSecondOrderRejected,
    fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), root_second_order_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 2, 1, ?_⟩
    change Real.log 2 *
        ((Real.log (1 : ℕ) - Chebyshev.psi 2) / Real.sqrt 2 - (Real.sqrt 2 - 1)) +
          Real.sqrt 2 * Real.log 2 / 2 ≠
      Real.log 2 *
        ((Real.log (2 : ℕ) - Chebyshev.psi 2) / Real.sqrt 2 - (Real.sqrt 2 - 1)) +
          Real.sqrt 2 * Real.log 2 / 2
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2 : Real.log (2 : ℕ) ≠ Real.log (1 : ℕ) := by
      norm_num
    intro heq
    have : Real.log (1 : ℕ) = Real.log (2 : ℕ) := by
      field_simp at heq
      linarith
    exact hlog2 this.symm

/-- The readout selects the complete residual under the original absolute value. -/
def rootSecondOrderAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_root_second_order) (Realization rootSecondOrderSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerRootSecondOrder.strict_inventory_root_second_order.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerRootSecondOrder.rootSecondOrderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rootSecondOrderArena⟩
  objectArena := .source ⟨rootSecondOrderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootSecondOrderArena ⟨rootSecondOrderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rootSecondOrderSignature rootSecondOrderActual.readout
    rootSecondOrderActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerRootSecondOrder
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rootSecondOrderFamily

end

end Reg.D5.S3.Arith.Robin.EulerLayerRootSecondOrder
