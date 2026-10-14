import D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open Polynomial
open D5.S3.ConceptDynamics.Coding
open D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (VertexModule DimensionGroup groupAction leftTranslation)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
noncomputable section
local instance originalNativeIntModule (q : ℕ) : Module ℤ (DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

abbrev signature : Signature where
  Params := ℕ
  State q := VertexModule Sign q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := VertexModule Sign q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev presentationArena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    nativeIntEquiv q hq 1 = nativeStage q 0
      (D5.S1.Recurrence.FiniteCompanionCyclicModule.e0 q hq) ∧
    (∀ b : QF q, nativeIntEquiv q hq (fp q X * b) = resetTheta q (nativeIntEquiv q hq b)) ∧
    (∀ p : ℤ[X], ∀ b : QF q, nativeIntEquiv q hq (fp q p * b) =
      (aeval (resetTheta q) p) (nativeIntEquiv q hq b)) ∧
    (∀ z : ℤ, ∀ b : QF q, nativeIntEquiv q hq (z • b) = z • nativeIntEquiv q hq b) ∧
    (∀ b : QF q, nativePolynomialEquiv q hq b =
      Module.AEval'.of (resetTheta q) (nativeIntEquiv q hq b)) ∧
    (∀ n : ℕ, ∀ v : VertexModule Sign q,
      (nativeIntEquiv q hq).symm (nativeStage q n v) = ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
          ((resetInverse q hq ^ n) (r.readout () q v))))) ∧
    (∀ x : Native q, resetNativeEquiv q hq
      (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
        leftTranslation (Multiplicative.ofAdd true) (resetNativeEquiv q hq x)) ∧
    groupAction (resetMatrix q) (Multiplicative.ofAdd true) = aeval (resetTheta q) (W q)

private theorem bad_presentation : ¬ presentationArena.Law bad := by
  intro h
  let v : VertexModule Sign 1 := fun _ => 1
  have hh := (h 1 (by decide)).2.2.2.2.2.1 0 v
  have hz := (native_presentation 1 (by decide)).2.2.2.2.2.1 0 (0 : VertexModule Sign 1)
  have he : (nativeIntEquiv 1 (by decide)).symm (nativeStage 1 0 v) =
      (nativeIntEquiv 1 (by decide)).symm (nativeStage 1 0 0) := by
    simpa only [bad, realize] using hh.trans hz.symm
  have hs := (nativeIntEquiv 1 (by decide)).symm.injective he
  have hr := congrArg (resetNativeEquiv 1 (by decide)) hs
  simp only [nativeStage, resetNativeEquiv_stage, pow_zero, Module.End.one_apply] at hr
  have hc := congrArg (fun row : VertexModule Sign 1 => (row 0).coeff 1) hr
  norm_num [v, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] at hc

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  change (fun _ : Fin 1 => (0 : R)) = (fun _ : Fin 1 => (1 : R)) at h
  have hc := congrFun h (0 : Fin 1)
  have he := congrArg (fun a : R => a.coeff 1) hc
  norm_num [MonoidAlgebra.coeff_zero, MonoidAlgebra.one_def,
    MonoidAlgebra.coeff_single] at he

def presentationEvidence : Registration presentationArena
    (∀ (q : ℕ) (hq : 0 < q),
    nativeIntEquiv q hq 1 = nativeStage q 0
      (D5.S1.Recurrence.FiniteCompanionCyclicModule.e0 q hq) ∧
    (∀ b : QF q, nativeIntEquiv q hq (fp q X * b) = resetTheta q (nativeIntEquiv q hq b)) ∧
    (∀ p : ℤ[X], ∀ b : QF q, nativeIntEquiv q hq (fp q p * b) =
      (aeval (resetTheta q) p) (nativeIntEquiv q hq b)) ∧
    (∀ z : ℤ, ∀ b : QF q, nativeIntEquiv q hq (z • b) = z • nativeIntEquiv q hq b) ∧
    (∀ b : QF q, nativePolynomialEquiv q hq b =
      Module.AEval'.of (resetTheta q) (nativeIntEquiv q hq b)) ∧
    (∀ n : ℕ, ∀ v : VertexModule Sign q,
      (nativeIntEquiv q hq).symm (nativeStage q n v) = ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
          ((resetInverse q hq ^ n) v)))) ∧
    (∀ x : Native q, resetNativeEquiv q hq
      (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
        leftTranslation (Multiplicative.ofAdd true) (resetNativeEquiv q hq x)) ∧
    groupAction (resetMatrix q) (Multiplicative.ofAdd true) = aeval (resetTheta q) (W q) ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_presentation, bad, bad_presentation⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_presentation⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def native_presentation_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.native_presentation)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.presentation_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.presentationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨presentationArena⟩
  objectArena := .source ⟨presentationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source presentationArena ⟨presentationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


abbrev arithmeticSignature : Signature where
  Params := {q : ℕ // 0 < q}
  State q := Native q.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Target (q.val % 4)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arithmeticActual : Realization arithmeticSignature :=
  realize arithmeticSignature (fun _ q x => eta q.val q.property x) (fun e => nomatch e)

abbrev arithmeticBad : Realization arithmeticSignature :=
  realize arithmeticSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arithmeticArena : Arena where
  signature := arithmeticSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    (∀ b : QF q, nativeSquare q (nativeIntEquiv q hq b) = nativeIntEquiv q hq (fp q H * b)) ∧
    (∀ x : Native q, r.readout () ⟨q, hq⟩ x = 0 ↔ ∃ y : Native q, nativeSquare q y = x) ∧
    Function.Surjective (r.readout () ⟨q, hq⟩) ∧
    (∀ x : Native q, nativeArithmeticEquiv q hq ((LinearMap.range (nativeSquare q)).mkQ x) = r.readout () ⟨q, hq⟩ x) ∧
    (∀ x y : NativeSquare q, nativeArithmeticEquiv q hq (x + y) =
      nativeArithmeticEquiv q hq x + nativeArithmeticEquiv q hq y) ∧
    r.readout () ⟨q, hq⟩ (generator q hq) = 1 ∧
    (∀ p : ℤ[X], ∀ x : Native q, r.readout () ⟨q, hq⟩ ((aeval (resetTheta q) p) x) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4)) * r.readout () ⟨q, hq⟩ x) ∧
    (∀ x : Native q, r.readout () ⟨q, hq⟩ (resetTheta q x) = targetTime (q % 4) * r.readout () ⟨q, hq⟩ x) ∧
    (∀ x : Native q, r.readout () ⟨q, hq⟩ (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
      targetLabel (q % 4) * r.readout () ⟨q, hq⟩ x) ∧
    (∀ n : ℕ, ∀ v : VertexModule Sign q, r.readout () ⟨q, hq⟩ (nativeStage q n v) =
      arithmeticChart q (bProjection q (ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial
          resetLabel q ((resetInverse q hq ^ n) v)))))) ∧
    (∀ p : ℤ[X], arithmeticChart q (squarePolynomial q p) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4))) ∧
    joint q = Ideal.span {residueF (q % 4)} ⊔ (Ideal.span {H} : Ideal ℤ[X]) ∧
    (∀ u : (Target (q % 4))ˣ, ∃ n : ℕ, n < targetBound (q % 4) ∧
      targetTimeUnit (q % 4) ^ n = u ∧
      eta q hq (ResetFullStandardBeamRepresentation.rho q hq
        (StandardBeamHomeomorphisms.unitShift (ResetStandardBeamGeometry.ResetGraph q) ^ n)
        (generator q hq)) = (u : Target (q % 4)))

private theorem arithmetic_bad : ¬ arithmeticArena.Law arithmeticBad := by
  intro h
  have hh := (h 2 (by decide)).2.2.2.2.2.1
  change (0 : ZMod 5) = 1 at hh
  exact (by decide : (0 : ZMod 5) ≠ 1) hh

private theorem arithmetic_dependence : ObservationalDependence arithmeticSignature arithmeticActual := by
  intro i
  obtain ⟨x, hx⟩ := (native_square_arithmetic 2 (by decide)).2.2.1 (0 : ZMod 5)
  obtain ⟨y, hy⟩ := (native_square_arithmetic 2 (by decide)).2.2.1 (1 : ZMod 5)
  refine ⟨⟨2, by decide⟩, x, y, ?_⟩
  intro h
  change eta 2 (by decide) x = eta 2 (by decide) y at h
  rw [hx, hy] at h
  exact (by decide : (0 : ZMod 5) ≠ 1) h

def arithmeticEvidence : Registration arithmeticArena
    (∀ (q : ℕ) (hq : 0 < q),
    (∀ b : QF q, nativeSquare q (nativeIntEquiv q hq b) = nativeIntEquiv q hq (fp q H * b)) ∧
    (∀ x : Native q, eta q hq x = 0 ↔ ∃ y : Native q, nativeSquare q y = x) ∧
    Function.Surjective (eta q hq) ∧
    (∀ x : Native q, nativeArithmeticEquiv q hq ((LinearMap.range (nativeSquare q)).mkQ x) = eta q hq x) ∧
    (∀ x y : NativeSquare q, nativeArithmeticEquiv q hq (x + y) =
      nativeArithmeticEquiv q hq x + nativeArithmeticEquiv q hq y) ∧
    eta q hq (generator q hq) = 1 ∧
    (∀ p : ℤ[X], ∀ x : Native q, eta q hq ((aeval (resetTheta q) p) x) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4)) * eta q hq x) ∧
    (∀ x : Native q, eta q hq (resetTheta q x) = targetTime (q % 4) * eta q hq x) ∧
    (∀ x : Native q, eta q hq (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
      targetLabel (q % 4) * eta q hq x) ∧
    (∀ n : ℕ, ∀ v : VertexModule Sign q, eta q hq (nativeStage q n v) =
      arithmeticChart q (bProjection q (ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial
          resetLabel q ((resetInverse q hq ^ n) v)))))) ∧
    (∀ p : ℤ[X], arithmeticChart q (squarePolynomial q p) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4))) ∧
    joint q = Ideal.span {residueF (q % 4)} ⊔ (Ideal.span {H} : Ideal ℤ[X]) ∧
    (∀ u : (Target (q % 4))ˣ, ∃ n : ℕ, n < targetBound (q % 4) ∧
      targetTimeUnit (q % 4) ^ n = u ∧
      eta q hq (ResetFullStandardBeamRepresentation.rho q hq
        (StandardBeamHomeomorphisms.unitShift (ResetStandardBeamGeometry.ResetGraph q) ^ n)
        (generator q hq)) = (u : Target (q % 4))) ) where
  actual := arithmeticActual
  bridge := Iff.rfl
  variation := ⟨native_square_arithmetic, arithmeticBad, arithmetic_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨arithmeticBad, ?_, rfl, arithmetic_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := arithmetic_dependence

noncomputable def native_square_arithmetic_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.native_square_arithmetic)
      (Realization arithmeticSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.arithmetic_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.arithmeticEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arithmeticArena⟩
  objectArena := .source ⟨arithmeticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arithmeticArena ⟨arithmeticEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arithmeticSignature (fun _ q x => eta q.val q.property x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


abbrev timeUnitSignature : Signature where
  Params := ℕ
  State r := (Target r)ˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ r := Target r
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev timeUnitActual : Realization timeUnitSignature :=
  realize timeUnitSignature (fun _ _ u => u.val) (fun e => nomatch e)

abbrev timeUnitBad : Realization timeUnitSignature :=
  realize timeUnitSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev timeUnitArena : Arena where
  signature := timeUnitSignature
  Law r := ∀ n : ℕ, r.readout () n (targetTimeUnit n) = targetTime n

private theorem timeUnit_bad : ¬ timeUnitArena.Law timeUnitBad := by
  intro h
  have hh := h 2
  change (0 : ZMod 5) = 3 at hh
  exact (by decide : (0 : ZMod 5) ≠ 3) hh

private theorem timeUnit_dependence : ObservationalDependence timeUnitSignature timeUnitActual := by
  intro i
  refine ⟨2, 1, targetTimeUnit 2, ?_⟩
  change (1 : ZMod 5) ≠ 3
  decide

def timeUnitEvidence : Registration timeUnitArena
    (∀ r : ℕ, (targetTimeUnit r : Target r) = targetTime r) where
  actual := timeUnitActual
  bridge := Iff.rfl
  variation := ⟨targetTimeUnit_val, timeUnitBad, timeUnit_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨timeUnitBad, ?_, rfl, timeUnit_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := timeUnit_dependence

noncomputable def targetTimeUnit_val_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.targetTimeUnit_val)
      (Realization timeUnitSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.timeUnit_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart.timeUnitEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨timeUnitArena⟩
  objectArena := .source ⟨timeUnitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timeUnitArena ⟨timeUnitEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize timeUnitSignature (fun _ _ u => u.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
