import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate
import Reg.Support.DependentFamily

noncomputable section
open NormedSpace
open scoped BigOperators Matrix Matrix.Norms.Operator
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate

namespace Reg.D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 5) (Fin 5) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => ‖M‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let A : Matrix (Fin 5) (Fin 5) ℝ :=
      !![0, 1, 1, 1, 0; -1, 0, 0, 0, -1; -1, 0, 0, 0, 0;
         -1, 0, 0, 0, -1; 0, 1, 0, 1, 0]
    let X := (2 / 3 : ℝ) • A
    let O := exp X
    let S := ∑ k ∈ Finset.range 13, ((k.factorial : ℝ)⁻¹) • X ^ k
    let v := Oᵀ *ᵥ Pi.single (0 : Fin 5) (1 : ℝ)
    Oᵀ * O = 1 ∧ O * Oᵀ = 1 ∧
      R.readout () () (O - S) ≤ (7 / 6 : ℝ) * 2 ^ 13 / ((13 : ℕ).factorial : ℝ) ∧
      (∀ j : Fin 5, 9 / 25 < |v j|) ∧
      (∀ j : Fin 5, (1 / 8 : ℝ) < (v j) ^ 2) ∧
      (1 / 8 : ℝ) < Finset.univ.inf' Finset.univ_nonempty (fun j : Fin 5 => (v j) ^ 2) ∧
      (∑ j : Fin 5, (v j) ^ 2) = 1

def family : Registration arena (type_of% @actual_walk_certificate) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have ht := h.2.2.1
    change (1 : ℝ) ≤ (7 / 6 : ℝ) * 2 ^ 13 / ((13 : ℕ).factorial : ℝ) at ht
    norm_num [Nat.factorial] at ht
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨actual_walk_certificate, rejected, hbad⟩
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
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_walk_certificate) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate.actual_walk_certificate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => ‖M‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","arg","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate
