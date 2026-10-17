import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators Matrix
noncomputable section

namespace actual_psd_zero_jump_moment
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 5 → ℝ) (fun _ => Fin 9 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ h d =>
    (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (4 : ℝ)) (fun e => nomatch e)
/-- Every binder of the literal PSD theorem is retained, including all six premises. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4)
    (hK : (!![2 * (1 - d 8), -(h 0 + d 7), -(h 1 + d 5);
                -(h 0 + d 7), 2 * (1 - d 6), -(h 2 + d 4);
                -(h 1 + d 5), -(h 2 + d 4), 2 * (1 - d 3)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef),
    O.readout () h d ≤ (7 / 2 : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hK : (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · change (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℝ)ᴴ = _
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
    · intro x
      simp [dotProduct, mulVec, Fin.sum_univ_succ, star_trivial]
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hf := h 0 0 (by intro i j hij; simp) (by intro i; simp)
    (by intro i j hij; simp) (by intro i; norm_num) (by norm_num)
    (by simpa using hK)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ, Pi.zero_apply]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_zero_jump_moment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_zero_jump_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_zero_jump_moment) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_zero_jump_moment.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_zero_jump_moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h d => (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_psd_zero_jump_moment

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
