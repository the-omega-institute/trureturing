import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.ExponentialTail
import Reg.Support.DependentFamily

noncomputable section
open NormedSpace
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.ExponentialTail

namespace Reg.D5.S3.Quantum.AURICOmega.ExponentialTail
universe u

abbrev signature : Signature where
  Params := Σ _r : ℝ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => x / (1 - p.1 / (p.2 + 1))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} [_ring : NormedRing B] [NormedAlgebra ℝ B]
    [CompleteSpace B] [NormOneClass B] (x : B) (r : ℝ) (n : ℕ),
    0 ≤ r → ‖x‖ ≤ r → r < n + 1 →
    ‖exp x - ∑ k ∈ Finset.range n, ((k.factorial : ℝ)⁻¹) • x ^ k‖ ≤
      R.readout () ⟨r, n⟩ (r ^ n / (n.factorial : ℝ))

def family : Registration arena.{u} (type_of% @exp_remainder_le.{u}) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hh := h (B := ULift.{u} ℝ) 0 0 1 (by norm_num) (by simp) (by norm_num)
    norm_num [rejected, realize] at hh
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨exp_remainder_le, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hbad⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  · intro i
    refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exp_remainder_le.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.AURICOmega.ExponentialTail.exp_remainder_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.ExponentialTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x / (1 - p.1 / (p.2 + 1)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.ExponentialTail
    definition := none
    coordinates := #[6, 7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.AURICOmega.ExponentialTail
