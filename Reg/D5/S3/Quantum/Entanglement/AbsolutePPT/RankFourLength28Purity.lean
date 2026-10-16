import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit _root_.Matrix
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 28 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Every hypothesis of the original spectral statement is retained. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ l : Fin 28 → ℝ, Antitone l → (∀ i, 0 ≤ l i) →
    (∑ i, l i) = 1 → (K1 (boundary l)).PosSemidef →
    (K2 (boundary l)).PosSemidef → 0 ≤ L4 l → O.readout () () l ≤ 1/25

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let l : Fin 28 → ℝ := fun _ => 1/28
  have hd : (diagonal (fun _ : Fin 3 => (1 : ℝ)/14)).PosSemidef :=
    Matrix.PosSemidef.diagonal (by intro i; norm_num)
  have h₁ : (K1 (boundary l)).PosSemidef := by
    convert hd using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [K1, boundary, l, Matrix.diagonal]
    <;> dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    <;> norm_num
  have h₂ : (K2 (boundary l)).PosSemidef := by
    convert hd using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [K2, boundary, l, Matrix.diagonal]
    <;> dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    <;> norm_num
  have hb := law l (fun _ _ _ => le_rfl) (by intro i; norm_num [l])
    (by norm_num [l, Fin.sum_univ_succ]) h₁ h₂
    (by norm_num [L4, l, Fin.sum_univ_succ])
  change (1 : ℝ) ≤ 1/25 at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]

def evidence : Registration arena (type_of% (@purity_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨purity_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/- The scalar observation replaces the actual purity occurrence. Current
compiler and inspector evidence determines binding status; unresolved failures
are disclosed under issue 17734. -/
noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity.purity_bound)
      (type_of% (realize signature
        (fun _ _ (l : Fin 28 → ℝ) => ∑ i, (l i)^2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity.purity_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ (l : Fin 28 → ℝ) => ∑ i, (l i)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
