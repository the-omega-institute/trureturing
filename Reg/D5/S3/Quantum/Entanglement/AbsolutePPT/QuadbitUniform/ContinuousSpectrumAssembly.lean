-- UNCOMPILED source-only registration candidates. No report verdict is asserted.
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators Matrix
noncomputable section

namespace actual_k1_l4_purity_bound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun N => Fin N → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ N l => ∑ i, (l i)^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ N _ => target N + 1) (fun e => nomatch e)
/-- The source law includes every dimension, arbitrary real spectrum, original L4 and literal K1. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (hN : 56 ≤ N) (l : Fin N → ℝ)
    (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (hmass : ∑ i, l i = 1)
    (hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩)
    (hK : (!![
      2*l ⟨N-1, by omega⟩, l ⟨N-2, by omega⟩-l ⟨0, by omega⟩,
        l ⟨N-4, by omega⟩-l ⟨1, by omega⟩;
      l ⟨N-2, by omega⟩-l ⟨0, by omega⟩, 2*l ⟨N-3, by omega⟩,
        l ⟨N-5, by omega⟩-l ⟨2, by omega⟩;
      l ⟨N-4, by omega⟩-l ⟨1, by omega⟩,
        l ⟨N-5, by omega⟩-l ⟨2, by omega⟩,
        2*l ⟨N-6, by omega⟩] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef),
    O.readout () N l ≤ target N
private theorem uniform_psd :
    (!![2*(1/56:ℝ),0,0; 0,2*(1/56:ℝ),0; 0,0,2*(1/56:ℝ)] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (!![2*(1/56:ℝ),0,0; 0,2*(1/56:ℝ),0; 0,0,2*(1/56:ℝ)] :
      Matrix (Fin 3) (Fin 3) ℝ)ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
  · intro x
    simp [dotProduct, mulVec, Fin.sum_univ_succ, star_trivial]
    nlinarith only [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  let l : Fin 56 → ℝ := fun _ => 1 / 56
  have hf := hall 56 (by norm_num) l
    (by intro i j hij; simp [l]) (by intro i; norm_num [l])
    (by norm_num [l]) (by norm_num [l])
    (by simpa [l] using uniform_psd)
  change target 56 + 1 ≤ target 56 at hf
  linarith only [hf]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨56, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_k1_l4_purity_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_k1_l4_purity_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_k1_l4_purity_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly.actual_k1_l4_purity_bound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly.actual_k1_l4_purity_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N l => ∑ i, (l i)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_k1_l4_purity_bound

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly
