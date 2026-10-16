import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun p => Fin (p.1*p.2) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => sumFirst 6 l) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- The equivalence and literal APPT hypothesis are kept in the original
universal telescope. No common-spectrum or purity conclusion is assumed. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : ℕ}, 4 ≤ m → 4 ≤ n →
    ∀ (e : (Fin m × Fin n) ≃ Fin (m*n)) (l : Fin (m*n) → ℝ),
      APPT (diagonal (fun p => (l (e p) : ℂ))) →
        O.readout () (m,n) l ≤ sumLast 10 l

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e : (Fin 4 × Fin 4) ≃ Fin 16 := Fintype.equivOfCardEq (by norm_num)
  have hz : APPT (diagonal (fun _ : Fin 4 × Fin 4 => (0 : ℂ))) := by
    intro U
    simpa [partialTranspose] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ).PosSemidef)
  have bad := h (m := 4) (n := 4) (by norm_num) (by norm_num) e (fun _ => 0) hz
  norm_num [rejected, realize, sumLast] at bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(4,4),(fun _ => 0),(fun _ => 1),?_⟩
  norm_num [actual, realize, sumFirst, Fin.sum_univ_succ]

def evidence : Registration arena (type_of% (@uniform_rank_four_necessary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_rank_four_necessary,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.uniform_rank_four_necessary)
      (type_of% (realize signature (fun _ _ l => sumFirst 6 l) (fun e => nomatch e)))
      (type_of% (@sumFirst)) Unit := {
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.uniform_rank_four_necessary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => sumFirst 6 l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@sumFirst)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
