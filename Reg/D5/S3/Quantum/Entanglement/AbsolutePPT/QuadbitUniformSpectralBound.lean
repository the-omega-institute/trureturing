import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun N => Fin N → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (hN : 67 ≤ N)
    (l : Fin N → ℝ) (_ho : Antitone l) (_hn : ∀ i, 0 ≤ l i)
    (_hmass : ∑ i, l i = 1)
    (_hL3 : (∑ i : Fin 3, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, l ⟨N-6+i.val, by omega⟩)
    (_hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩)
    (_hC3 : l ⟨0, by omega⟩ ≤ ∑ i : Fin 3, l ⟨N-3+i.val, by omega⟩),
    let t : ℕ := (3*N+4)/8
    O.readout () N l ≤ (9*(N : ℝ)+16*(t : ℝ))/(3*(N : ℝ)+2*(t : ℝ))^2

abbrev sourceScope := type_of% (@three_row_scalar_bound)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let l : Fin 67 → ℝ := fun _ => 1/67
  have ho : Antitone l := fun _ _ _ => le_rfl
  have hn : ∀ i, 0 ≤ l i := by intro i; norm_num [l]
  have hm : ∑ i, l i = 1 := by norm_num [l]
  have hL3 : (∑ i : Fin 3, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, l ⟨67-6+i.val, by omega⟩ := by norm_num [l]
  have hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨67-10+i.val, by omega⟩ := by norm_num [l]
  have hC3 : l ⟨0, by omega⟩ ≤
      ∑ i : Fin 3, l ⟨67-3+i.val, by omega⟩ := by norm_num [l]
  have hb := h 67 (by omega) l ho hn hm hL3 hL4 hC3
  norm_num [rejected, realize] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨three_row_scalar_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def scalarRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@three_row_scalar_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.three_row_scalar_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
