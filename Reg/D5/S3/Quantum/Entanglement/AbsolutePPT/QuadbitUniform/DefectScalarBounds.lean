import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace affine_defect_transport
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p z => (2 + p.2.2.2.1) * (p.2.1 + p.2.2.2.1 * p.2.2.1 + p.2.2.2.2) - (1 + p.2.2.2.1) * p.2.1 + z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p z => ((2 + p.2.2.2.1) * (p.2.1 + p.2.2.2.1 * p.2.2.1 + p.2.2.2.2) - (1 + p.2.2.2.1) * p.2.1 + z) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (theta N j w c E : ℝ)
    (ht : 0 ≤ theta) (hw : 0 ≤ w) (hj : 6 ≤ j)
    (ha0 : 0 ≤ 2*theta*(N+3+2*w)-(2+w))
    (ha1 : 2*theta*(N+3+2*w)-(2+w) ≤ 1/4)
    (hF0 : 0 ≤ theta*(N+3+2*w)^2-(N+11+3*w+w^2))
    (hE0 : E ≤ 5-4*w-w^2)
    (hE1 : E ≤ 5-4*w-w^2+(c-(3-4*w))/4),
    O.readout () ⟨theta,N,j,w,c⟩ E ≤ theta*(N+w*j+c)^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h (39 / 2450) 67 6 0 3 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0,6,0,0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.affine_defect_transport)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.affine_defect_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.affine_defect_transport) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.affine_defect_transport.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.affine_defect_transport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => (2 + p.2.2.2.1) * (p.2.1 + p.2.2.2.1 * p.2.2.1 + p.2.2.2.2) - (1 + p.2.2.2.1) * p.2.1 + z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end affine_defect_transport

namespace flat_third_head_le_one
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (a b e : ℝ)
    (hab : b ≤ a) (hbe : e ≤ b) (he0 : 0 ≤ e)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4),
    O.readout () ⟨a,b⟩ e ≤ 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_third_head_le_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_third_head_le_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_third_head_le_one) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_third_head_le_one.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_third_head_le_one.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end flat_third_head_le_one

namespace flat_endpoint_ge_third
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (3 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1),
    O.readout () () e ≤ 2 - e ^ 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_endpoint_ge_third)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_endpoint_ge_third, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_endpoint_ge_third) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_endpoint_ge_third.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_endpoint_ge_third.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end flat_endpoint_ge_third

namespace flat_pair_square_le_low
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p z => (p.1 + p.2 - z) ^ 2 + z ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (a b e : ℝ)
    (hae : e ≤ a) (hbe : e ≤ b),
    a ^ 2 + b ^ 2 ≤ O.readout () ⟨a,b⟩ e
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 0 0
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_pair_square_le_low)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_pair_square_le_low, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_pair_square_le_low) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_pair_square_le_low.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_pair_square_le_low.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => (p.1 + p.2 - z) ^ 2 + z ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end flat_pair_square_le_low

namespace flat_pair_square_le_high
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => (2 - z ^ 2) ^ 2 + z ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (a b e : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4)
    (hs : (2 - e ^ 2) + e ≤ a + b),
    a ^ 2 + b ^ 2 ≤ O.readout () ⟨a,b⟩ e
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 2 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_pair_square_le_high)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_pair_square_le_high, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_pair_square_le_high) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_pair_square_le_high.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_pair_square_le_high.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => (2 - z ^ 2) ^ 2 + z ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end flat_pair_square_le_high

namespace flat_five_middle_energy
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p z => p.2.1 * (p.2.1 - p.1) + p.2.2.1 * (p.2.2.1 - p.1) + p.2.2.2.1 * (p.2.2.2.1 - p.1) + p.2.2.2.2 * (p.2.2.2.2 - p.1) + z * (z - p.1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (100 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (w a b e x y : ℝ)
    (hw : 2 / 9 ≤ w) (hw1 : w ≤ 1 / 2) (ha : 1 + w ≤ a)
    (hab : b ≤ a) (hbe : e ≤ b) (hex : x ≤ e) (hxy : y ≤ x) (hyw : w ≤ y)
    (hmass : a + b + e + x + y ≤ 4 - w)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4),
    O.readout () ⟨w,a,b,e,x⟩ y ≤
      4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h (2 / 9) (11 / 9) (2 / 9) (2 / 9) (2 / 9) (2 / 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0,0,0,0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_five_middle_energy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_five_middle_energy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.flat_five_middle_energy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_five_middle_energy.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds.flat_five_middle_energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => p.2.1 * (p.2.1 - p.1) + p.2.2.1 * (p.2.2.1 - p.1) + p.2.2.2.1 * (p.2.2.2.1 - p.1) + p.2.2.2.2 * (p.2.2.2.2 - p.1) + z * (z - p.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end flat_five_middle_energy

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.DefectScalarBounds
