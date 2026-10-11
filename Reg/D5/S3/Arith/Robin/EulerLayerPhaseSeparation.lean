import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayerPhaseSeparation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.EulerLayerPhaseSeparation

open _root_.D5.S3.Arith.Robin.EulerLayerPhaseSeparation
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev marginalSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def marginalActual : Realization marginalSignature :=
  realize marginalSignature (fun _ q k => goldenLayerMarginal q k) (fun e => nomatch e)

def marginalRejected : Realization marginalSignature :=
  realize marginalSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev priceArena : Arena where
  signature := marginalSignature
  Law R := ∀ {q k : ℕ}, q.Prime → 2 ≤ k → (16 : ℝ) ≤ (q : ℝ) ^ k →
    1 / ((3 * (q : ℝ) ^ k / 4) * Real.log (3 * (q : ℝ) ^ k / 4)) < R.readout () q k ∧
    (∀ tau : ℝ, 1 < tau → 1 / (tau * Real.log tau) = goldenLayerMarginal q k →
      tau < 3 * (q : ℝ) ^ k / 4)

private theorem price_rejected : ¬ priceArena.Law marginalRejected := by
  intro h
  have hh := (h (q := 2) (k := 4) (by decide) (by omega) (by norm_num)).1
  change 1 / ((3 * (2 : ℝ) ^ 4 / 4) * Real.log (3 * (2 : ℝ) ^ 4 / 4)) < 0 at hh
  have hpos : 0 < 1 / ((3 * (2 : ℝ) ^ 4 / 4) * Real.log (3 * (2 : ℝ) ^ 4 / 4)) := by
    apply one_div_pos.mpr
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  linarith

private theorem marginal_dependence : ObservationalDependence marginalSignature marginalActual := by
  intro i
  cases i
  refine ⟨2, 4, 5, ?_⟩
  exact ne_of_gt (golden_layer_strict_decrease (by decide : Nat.Prime 2) (by omega)
    (by omega : 4 < 5))

def priceRegistration : Registration priceArena
    (∀ {q k : ℕ}, q.Prime → 2 ≤ k → (16 : ℝ) ≤ (q : ℝ) ^ k →
      1 / ((3 * (q : ℝ) ^ k / 4) * Real.log (3 * (q : ℝ) ^ k / 4)) <
        goldenLayerMarginal q k ∧
      (∀ tau : ℝ, 1 < tau →
        1 / (tau * Real.log tau) = goldenLayerMarginal q k → tau < 3 * (q : ℝ) ^ k / 4)) where
  actual := marginalActual
  bridge := Iff.rfl
  variation := ⟨higher_layer_price_separation, marginalRejected, price_rejected⟩
  sensitivity := ⟨fun i => ⟨marginalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, price_rejected⟩,
    fun i => nomatch i⟩
  dependence := marginal_dependence

abbrev windowArena : Arena where
  signature := marginalSignature
  Law R := ∀ {q k : ℕ}, q.Prime → 2 ≤ k → ∀ {t : ℝ}, 243 ≤ t →
    (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) →
      1 / (t * Real.log t) < R.readout () q k) ∧
    ∀ tau : ℝ, 1 < tau → 1 / (tau * Real.log tau) = goldenLayerMarginal q k →
      tau < (q : ℝ) ^ k ∧
      (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) → tau < t) ∧
      (t ≤ tau → tau ≤ t + t ^ (4 / 5 : ℝ) → t + t ^ (4 / 5 : ℝ) < (q : ℝ) ^ k)

private theorem window_rejected : ¬ windowArena.Law marginalRejected := by
  intro h
  have hh := (h (q := 2) (k := 8) (by decide) (by omega) (t := 255) (by norm_num)).1
  have hpow : 1 ≤ (255 : ℝ) ^ (4 / 5 : ℝ) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have hx := hh (by norm_num) (by norm_num; linarith)
  change 1 / ((255 : ℝ) * Real.log 255) < 0 at hx
  have hpos : 0 < 1 / ((255 : ℝ) * Real.log 255) :=
    one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  linarith

def windowRegistration : Registration windowArena
    (∀ {q k : ℕ}, q.Prime → 2 ≤ k → ∀ {t : ℝ}, 243 ≤ t →
      (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) →
        1 / (t * Real.log t) < goldenLayerMarginal q k) ∧
      ∀ tau : ℝ, 1 < tau →
        1 / (tau * Real.log tau) = goldenLayerMarginal q k →
        tau < (q : ℝ) ^ k ∧
        (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) → tau < t) ∧
        (t ≤ tau → tau ≤ t + t ^ (4 / 5 : ℝ) → t + t ^ (4 / 5 : ℝ) < (q : ℝ) ^ k)) where
  actual := marginalActual
  bridge := Iff.rfl
  variation := ⟨higher_layer_forward_window, marginalRejected, window_rejected⟩
  sensitivity := ⟨fun i => ⟨marginalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, window_rejected⟩,
    fun i => nomatch i⟩
  dependence := marginal_dependence

abbrev inventorySignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def inventoryActual : Realization inventorySignature :=
  realize inventorySignature (fun _ U q => U.factorization q) (fun e => nomatch e)

def inventoryRejected : Realization inventorySignature :=
  realize inventorySignature (fun _ _ _ => 0) (fun e => nomatch e)

-- The inventory premise remains the literal one on U; only its conclusion readouts vary.
abbrev inventoryArena : Arena where
  signature := inventorySignature
  Law R := ∀ {U : ℕ}, 0 < U → ∀ {t : ℝ}, 243 ≤ t →
    (∀ q : ℕ, U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    (∀ q k : ℕ, q.Prime → 2 ≤ k → t < (q : ℝ) ^ k →
      (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) → k ≤ R.readout () U q ∧ q ^ k ∣ U) ∧
    (∀ q : ℕ, q.Prime → t < (q : ℝ) → (q : ℝ) ≤ t + t ^ (4 / 5 : ℝ) →
      U.factorization q = 0) ∧
    (∀ q k : ℕ, q.Prime → 2 ≤ k → ∀ tau : ℝ, 1 < tau →
      1 / (tau * Real.log tau) = goldenLayerMarginal q k →
      tau < (q : ℝ) ^ k ∧
      (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) → tau < t) ∧
      (t ≤ tau → tau ≤ t + t ^ (4 / 5 : ℝ) → t + t ^ (4 / 5 : ℝ) < (q : ℝ) ^ k))

private theorem inventory_rejected : ¬ inventoryArena.Law inventoryRejected := by
  intro h
  have hprice : 0 < 1 / ((243 : ℝ) * Real.log 243) :=
    one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hprice
  have hh := (h (U := U) (by omega) (t := 243) (by norm_num) hstrict).1 2 8
    (by decide) (by omega) (by norm_num)
  have hp : (243 : ℝ) ^ (4 / 5 : ℝ) = 81 := by
    rw [show (243 : ℝ) = 3^5 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [Real.rpow_natCast]
  have hx := hh (by rw [hp]; norm_num)
  change 8 ≤ 0 ∧ _ at hx
  omega

def inventoryRegistration : Registration inventoryArena
    (∀ {U : ℕ}, 0 < U → ∀ {t : ℝ}, 243 ≤ t →
      (∀ q : ℕ, U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      (∀ q k : ℕ, q.Prime → 2 ≤ k → t < (q : ℝ) ^ k →
        (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) → k ≤ U.factorization q ∧ q ^ k ∣ U) ∧
      (∀ q : ℕ, q.Prime → t < (q : ℝ) → (q : ℝ) ≤ t + t ^ (4 / 5 : ℝ) →
        U.factorization q = 0) ∧
      (∀ q k : ℕ, q.Prime → 2 ≤ k → ∀ tau : ℝ, 1 < tau →
        1 / (tau * Real.log tau) = goldenLayerMarginal q k →
        tau < (q : ℝ) ^ k ∧
        (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t ^ (4 / 5 : ℝ) → tau < t) ∧
        (t ≤ tau → tau ≤ t + t ^ (4 / 5 : ℝ) → t + t ^ (4 / 5 : ℝ) < (q : ℝ) ^ k))) where
  actual := inventoryActual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_forward_window, inventoryRejected, inventory_rejected⟩
  sensitivity := ⟨fun i => ⟨inventoryRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, inventory_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨2, 2, 1, ?_⟩
    change Nat.factorization 2 2 ≠ Nat.factorization 2 1
    simp [Nat.Prime.factorization_self (by decide : Nat.Prime 2)]

-- Each scoped observation varies one literal operand; all other original clauses remain fixed.
def priceAudit : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@higher_layer_price_separation) (Realization marginalSignature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerPhaseSeparation.higher_layer_price_separation.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerPhaseSeparation.priceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨priceArena⟩
  objectArena := .source ⟨priceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source priceArena ⟨priceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize marginalSignature marginalActual.readout marginalActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerPhaseSeparation
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg",
          "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def windowAudit : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@higher_layer_forward_window) (Realization marginalSignature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerPhaseSeparation.higher_layer_forward_window.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerPhaseSeparation.windowRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize marginalSignature marginalActual.readout marginalActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerPhaseSeparation
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "fn",
          "arg", "body", "body", "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def inventoryAudit : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@strict_inventory_forward_window) (Realization inventorySignature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerPhaseSeparation.strict_inventory_forward_window.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerPhaseSeparation.inventoryRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨inventoryArena⟩
  objectArena := .source ⟨inventoryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inventoryArena ⟨inventoryRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inventorySignature inventoryActual.readout inventoryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerPhaseSeparation
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg",
          "body", "body", "body", "body", "body", "body", "fn",
          "arg", "arg"],
        stateBinder := 5, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms priceRegistration
#print axioms windowRegistration
#print axioms inventoryRegistration

end

end Reg.D5.S3.Arith.Robin.EulerLayerPhaseSeparation
