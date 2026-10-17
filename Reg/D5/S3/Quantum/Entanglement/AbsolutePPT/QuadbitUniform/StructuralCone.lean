import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound.SharedSpectral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix
noncomputable section

namespace structural_fixed_good
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => Fin 16 → ℝ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ p x => spectralGood (Real.sqrt (target p.1)) (synth (d := p.1) (positions p.1 p.2) x)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (_hN : 67 ≤ N) (_hj : 6 ≤ j) (_hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) (_hx : ∀ q, 0 ≤ x q) (_hAx : ∀ r, 0 ≤ (A *ᵥ x) r),
    O.readout () (N,j) x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 6 (by norm_num) (by norm_num) (by norm_num) 0
    (by intro q; simp) (by intro r; simp)
  exact hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let bad : Fin 16 → ℝ := fun q => if q = 15 then -1 else 0
  refine ⟨(67,6), 0, bad, ?_⟩
  change spectralGood (Real.sqrt (target 67)) (synth (d := 67) (positions 67 6) 0) ≠
    spectralGood (Real.sqrt (target 67)) (synth (d := 67) (positions 67 6) bad)
  have hzero : spectralGood (Real.sqrt (target 67)) (synth (d := 67) (positions 67 6) 0) := by
    rw [map_zero]
    exact spectralGood_zero _ _
  have hp : ∀ q, positions 67 6 q ≤ 67 := by
    intro q; fin_cases q <;> norm_num [positions]
  have hm : (∑ k : Fin 67, synth (d := 67) (positions 67 6) bad k) = -67 := by
    rw [mass_synth (d := 67) (positions 67 6) hp]
    rw [Finset.sum_eq_single (15 : Fin 16)]
    · norm_num [bad, positions]
    · intro q _ hq
      simp [bad, hq]
    · simp
  have ht : 0 < Real.sqrt (target 67) := Real.sqrt_pos.2 (by norm_num [target])
  intro heq
  have hb := Eq.mp heq hzero
  unfold spectralGood at hb
  rw [hm] at hb
  have hn := norm_nonneg (WithLp.toLp 2 (synth (d := 67) (positions 67 6) bad))
  nlinarith
def family : Registration arena (type_of% (@structural_fixed_good)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@structural_fixed_good, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@structural_fixed_good) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.structural_fixed_good.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.structural_fixed_good.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => spectralGood (Real.sqrt (target p.1)) (synth (d := p.1) (positions p.1 p.2) x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end structural_fixed_good

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
