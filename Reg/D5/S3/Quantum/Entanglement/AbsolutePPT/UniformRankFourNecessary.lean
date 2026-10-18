-- UNCOMPILED source-only candidate; no registration verdict is asserted.
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.RankFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ)
    (fun p => Fin (p.1*p.2) → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ l => sumFirst 6 l) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
/-- No order, nonnegativity, mass, strictness or multiplicity hypothesis is added. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m*n)) (l : Fin (m*n) → ℝ)
    (happt : APPT (diagonal (fun p => (l (e p) : ℂ)))),
    O.readout () ⟨m,n⟩ l ≤ sumLast 10 l
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e : (Fin 4 × Fin 4) ≃ Fin (4*4) := finProdFinEquiv
  have ha : APPT (diagonal (fun p => ((0 : Fin (4*4) → ℝ) (e p) : ℂ))) := by
    intro U
    have hzero :
        partialTranspose (0 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) = 0 := by
      ext p q
      rfl
    simpa [hzero, Pi.zero_apply] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ).PosSemidef)
  have hb := h (by decide : 4 ≤ 4) (by decide : 4 ≤ 4) e 0 ha
  norm_num [rejected, realize, sumLast] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨4,4⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, sumFirst, Fin.sum_univ_succ, Pi.zero_apply]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.uniform_rank_four_necessary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.uniform_rank_four_necessary, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- Source-only candidate: compilation and compiled source-binding evidence are pending. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.uniform_rank_four_necessary) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.RankFour.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.RankFour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => sumFirst 6 l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary.RankFour
