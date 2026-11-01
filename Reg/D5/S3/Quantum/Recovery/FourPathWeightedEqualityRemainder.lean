import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
open scoped Matrix.Norms.Frobenius

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder

abbrev claim : Prop := ∀ (v : Index → ℂ) (U : Matrix Index Index ℂ),
  U ∈ Matrix.unitaryGroup Index ℂ →
    ∃ phase : ℂ, ‖phase‖ = 1 ∧
      ‖transport U v - phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 ≤
        2 * remainder U v

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix Index Index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix Index Index ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => U) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (v : Index → ℂ) (U : Matrix Index Index ℂ),
    U ∈ Matrix.unitaryGroup Index ℂ →
      ∃ phase : ℂ, ‖phase‖ = 1 ∧
        ‖transport (R.readout () () U) v -
            phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 ≤
          2 * remainder U v

theorem actual_law : arena.Law actual := by
  intro v U hU
  exact weighted_equality_remainder v U hU

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : Index → ℂ := fun i => if i = 0 then 1 else 0
  have hu : (1 : Matrix Index Index ℂ) ∈ Matrix.unitaryGroup Index ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simp
  obtain ⟨phase, hphase, hdist⟩ := h v 1 hu
  have hzero : remainder (1 : Matrix Index Index ℂ) v = 0 := by
    simp [remainder, radius, traceRadius, transport, v, Matrix.trace,
      Matrix.mul_diagonal, Fin.sum_univ_succ]
  rw [hzero, mul_zero] at hdist
  have hnorm :
      ‖transport (rejected.readout () () (1 : Matrix Index Index ℂ)) v -
          phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 = 1 := by
    rw [show transport (rejected.readout () () (1 : Matrix Index Index ℂ)) v = 0 by
      simp [rejected, realize, transport, v]]
    rw [zero_sub, norm_neg, norm_smul, hphase, one_mul]
    have hdiag :
        ‖Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [Matrix.frobenius_norm_diagonal]
      change ‖WithLp.toLp 2 (fun i => (‖v i‖ : ℂ))‖ ^ 2 = _
      simp [PiLp.norm_sq_eq_of_L2]
    rw [hdiag]
    simp [v, Fin.sum_univ_succ]
  rw [hnorm] at hdist
  linarith

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder.weighted_equality_remainder)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => U) (fun e _ => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
