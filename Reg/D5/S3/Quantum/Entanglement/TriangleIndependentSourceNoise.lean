import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

namespace Reg.D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra MatrixOrder ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => sourceWeight w) (fun e => nomatch e)

def rejected (i : Fin 3) : Realization signature :=
  realize signature (fun j _ w => if j = i then fun _ => 0 else sourceWeight w)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {a : Type u₁} {b : Type u₂} {b' : Type u₃} {c : Type u₄}
    {c' : Type u₅} {a' : Type u₆} {oa : Type u₇} {ob : Type u₈} {oc : Type u₉}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype b'] [DecidableEq b'] [Fintype c] [DecidableEq c]
    [Fintype c'] [DecidableEq c'] [Fintype a'] [DecidableEq a']
    [Fintype oa] [Fintype ob] [Fintype oc]
    (ab0 ab1 : DensityState (a × b)) (bc0 bc1 : DensityState (b' × c))
    (ca0 ca1 : DensityState (c' × a')) (ma : LocalPOVM (a × a') oa)
    (mb : LocalPOVM (b' × b) ob) (mc : LocalPOVM (c' × c) oc)
    (wa wb wc : ℝ), wa ∈ Set.Icc (0 : ℝ) 1 → wb ∈ Set.Icc (0 : ℝ) 1 →
      wc ∈ Set.Icc (0 : ℝ) 1 →
    (∀ x y z, 0 ≤ noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z) ∧
    (∑ x, ∑ y, ∑ z, noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z = 1) ∧
    (∀ x y z, noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z =
      ∑ i : Bool, ∑ j : Bool, ∑ k : Bool,
        (r.readout 0 () wa i * r.readout 1 () wb j * r.readout 2 () wc k) *
          triangleBorn (stateMatrix (if i then ab1 else ab0))
            (stateMatrix (if j then bc1 else bc0))
            (stateMatrix (if k then ca1 else ca0)) ma mb mc x y z)

theorem actual_law : arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉}.Law actual :=
  triangle_noise_distribution

private def unitState (h : Type*) [Fintype h] [DecidableEq h] [Inhabited h] [Subsingleton h] :
    DensityState h := by
  letI : Unique h := ⟨inferInstance, fun _ => Subsingleton.elim _ _⟩
  refine ⟨CStarMatrix.ofMatrix 1, ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv Matrix.PosSemidef.one.nonneg
  · change Matrix.trace (1 : Matrix h h ℂ) = 1
    simp [Matrix.trace, Matrix.diag, Matrix.one_apply]

private def unitPOVM (h o : Type*) [Fintype h] [DecidableEq h]
    [Fintype o] [Unique o] : LocalPOVM h o where
  effect _ := 1
  positive _ := Matrix.PosSemidef.one
  complete := by simp

theorem rejected_law (i : Fin 3) :
    ¬ arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉}.Law (rejected i) := by
  intro h
  letI A := ULift.{u₁} Unit
  letI B := ULift.{u₂} Unit
  letI B' := ULift.{u₃} Unit
  letI C := ULift.{u₄} Unit
  letI C' := ULift.{u₅} Unit
  letI A' := ULift.{u₆} Unit
  letI OA := ULift.{u₇} Unit
  letI OB := ULift.{u₈} Unit
  letI OC := ULift.{u₉} Unit
  have hh := h (unitState (A × B)) (unitState (A × B))
    (unitState (B' × C)) (unitState (B' × C))
    (unitState (C' × A')) (unitState (C' × A'))
    (unitPOVM (A × A') OA) (unitPOVM (B' × B) OB) (unitPOVM (C' × C) OC)
    0 0 0 (by norm_num) (by norm_num) (by norm_num)
  have hn := hh.2.1
  have he := hh.2.2 default default default
  fin_cases i <;> simp [rejected, realize] at he <;> simpa [he] using hn

def registration : Registration arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉} (arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j h
      funext p w signal
      simp [actual, rejected, realize, h]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro h
    have hh := congrArg (fun f => f true) h
    norm_num [actual, realize, sourceWeight] at hh

def four_slot_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.triangle_noise_distribution.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉})
    (type_of% actual) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.triangle_noise_distribution.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉}⟩
  objectArena := .source ⟨arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉} ⟨registration.{u₁,u₂,u₃,u₄,u₅,u₆,u₇,u₈,u₉}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => sourceWeight w)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg",
        "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
        stateBinder := 33
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg",
        "body", "fn", "arg", "fn", "arg", "arg", "fn"]
        stateBinder := 34
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg",
        "body", "fn", "arg", "arg", "fn"]
        stateBinder := 35
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms four_slot_registration

end

end Reg.D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
