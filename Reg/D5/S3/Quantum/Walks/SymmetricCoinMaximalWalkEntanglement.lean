import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
import Reg.Support.DependentFamily

/-! Source-bound audit of symmetric-coin maximal walk entanglement. -/

namespace Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

open _root_.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the amplitude vector at the original circle size, time and coin. -/
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ pn := Fin 2 × ZMod pn.1 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ pn c => walkState pn.1 pn.2 c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 2) (fun e => nomatch e)

/-- Retain every original parameter, normalization hypothesis and entanglement bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (c : Fin 2 → ℂ),
    _root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c →
    letI : NeZero p := ⟨by omega⟩
    r.readout () ⟨p, n⟩ c = walkState p n c ∧
      geometricEntanglement (r.readout () ⟨p, n⟩ c) ≤
        geometricEntanglement (walkState p n cStar)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) 0 cStar (by
    have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
      rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    norm_num [D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor,
      Fin.sum_univ_two, cStar, hs])
  have heq := hbad.1
  change (fun _ : Fin 2 × ZMod 1 => (2 : ℂ)) = walkState 1 0 cStar at heq
  have hcoord := congrFun heq (0, 0)
  change (2 : ℂ) = cStar 0 at hcoord
  rw [cStar] at hcoord
  change (2 : ℂ) = 1 / (Real.sqrt 2 : ℂ) at hcoord
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hm := congrArg (fun z : ℂ => z * (Real.sqrt 2 : ℂ)) hcoord
  rw [div_mul_cancel₀ _ hsqrt] at hm
  have hmr := congrArg Complex.re hm
  norm_num at hmr
  have hsq := congrArg (fun x : ℝ => x ^ 2) hmr
  have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, cStar, ?_⟩
  intro he
  have h := congrFun he (0, 0)
  have hn : cStar 0 ≠ 0 := by simp [cStar]
  apply hn
  change (0 : ℂ) = cStar 0 at h
  exact h.symm

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro h p hp n c hc
      exact ⟨rfl, h p hp n c hc⟩
    · intro h p hp n c hc
      exact (h p hp n c hc).2
  variation := ⟨by
    intro p hp n c hc
    exact ⟨rfl, result p hp n c hc⟩, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ pn c => walkState pn.1 pn.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
    definition := some {
      owner := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
      name := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
