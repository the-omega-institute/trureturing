import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound.SharedSpectral Matrix
open scoped BigOperators Matrix
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

namespace boundary_packed_nonneg
abbrev Params := Σ N : {n : ℕ // 16 ≤ n}, Fin 16
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.1.1 → ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ p g => boundaryPacked p.1.2 g p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (hN : 16 ≤ N) (g : Fin N → ℝ) (hg : ∀ k, 0 ≤ g k) (q : Fin 16),
    0 ≤ O.readout () ⟨⟨N,hN⟩,q⟩ g
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 16 (by norm_num) 0 (by intro k; simp) 0
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨⟨16, by norm_num⟩, 15⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, boundaryPacked]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p g => boundaryPacked p.1.2 g p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end boundary_packed_nonneg

namespace boundary_lift_packed
abbrev Params := Σ N : {n : ℕ // 16 ≤ n}, Fin N.1
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.1.1 → ℝ) (fun p => Fin p.1.1 → ℝ)
def actual : Realization signature := realize signature (fun _ p g => fixedGaps g p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (hN : 16 ≤ N) (g : Fin N → ℝ) (k : Fin N) (hk : k ∈ middle N),
    boundaryLift N (k.val+1) hN (by have := (mem_middle k).mp hk; omega)
      (by have := (mem_middle k).mp hk; omega) (boundaryPacked hN g) = O.readout () ⟨⟨N,hN⟩,k⟩ g
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 16 (by norm_num) 0 5 (by norm_num [middle])
  have he := congrFun hf 0
  norm_num [rejected, realize, boundaryLift, boundaryPacked, unitGap, middleMass] at he
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨⟨16, by norm_num⟩, 5⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hf := congrFun he 0
  norm_num [actual, realize, fixedGaps, boundaryGaps, middle, unitGap, Pi.single_apply] at hf
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_lift_packed)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_lift_packed, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_lift_packed) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_lift_packed.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_lift_packed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p g => fixedGaps g p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end boundary_lift_packed

namespace boundary_synth_lift
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => Fin 16 → ℝ) (fun p => Fin p.1 → ℝ)
def actual : Realization signature := realize signature (fun _ p x => synth (d := p.1) (positions p.1 p.2) x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ),
    fullSynth N (boundaryLift N j hN hj hj' x) = O.readout () (N,j) x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := congrFun (h 16 6 (by norm_num) (by norm_num) (by norm_num) 0) 0
  norm_num [rejected, realize, fullSynth, synth, boundaryLift, unitGap] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(16,6), (fun _ => 0), Pi.single (15 : Fin 16) 1, ?_⟩
  intro he
  have hf := congrFun he 0
  norm_num [actual, realize, synth, step, positions, Fin.sum_univ_succ, Pi.single_apply, Pi.zero_apply] at hf
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_synth_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_synth_lift, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_synth_lift) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_synth_lift.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_synth_lift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => synth (d := p.1) (positions p.1 p.2) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end boundary_synth_lift

namespace boundary_packed_image
abbrev Params := Σ N : {n : ℕ // 16 ≤ n}, Fin N.1
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.1.1 → ℝ) (fun _ => Fin 3 → ℝ)
def actual : Realization signature := realize signature (fun _ p g => boundaryGapRows p.1.1 p.1.2 g) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (hN : 16 ≤ N) (g : Fin N → ℝ) (k : Fin N) (hk : k ∈ middle N),
    A *ᵥ boundaryPacked hN g = O.readout () ⟨⟨N,hN⟩,k⟩ g
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := congrFun (h 16 (by norm_num) 0 5 (by norm_num [middle])) 0
  norm_num [rejected, realize, boundaryPacked, middleMass, A, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Pi.zero_apply] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨⟨16, by norm_num⟩, 5⟩, (fun _ => 0), Pi.single (15 : Fin 16) 1, ?_⟩
  change boundaryGapRows 16 (by norm_num) (fun _ => 0) ≠
    boundaryGapRows 16 (by norm_num) (Pi.single 15 1)
  rw [← _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image
      16 (by norm_num) (fun _ => 0) 5 (by norm_num [middle]),
    ← _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image
      16 (by norm_num) (Pi.single 15 1) 5 (by norm_num [middle])]
  intro he
  have hf := congrFun he 0
  norm_num [boundaryPacked, middleMass, middle, A, Matrix.mulVec, dotProduct,
    Finset.sum_filter, Fin.sum_univ_succ, Pi.single_apply, Pi.zero_apply] at hf
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_packed_image.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p g => boundaryGapRows p.1.1 p.1.2 g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end boundary_packed_image

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
