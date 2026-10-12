import D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (VertexModule transition)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State q := VertexModule Sign q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := VertexModule Sign q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature (fun _ _ v => v) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨v,hv⟩ := reset_five_clock_surjective 2 (by decide) 1
  refine ⟨2,0,v,?_⟩
  intro hh
  have hz : (0 : VertexModule Sign 2) = v := hh
  have hf := congrArg (resetFiveClock 2) hz
  rw [map_zero,hv] at hf
  exact (by decide : (0 : ZMod 5) ≠ 1) hf

abbrev imageArena : Arena where
  signature := signature
  Law r := ∀ q (hq : 0 < q) (y : VertexModule Sign q),
    (∃ v, resetSquareDefect q v = r.readout () q y) ↔ resetSquareReadout q y = 0

abbrev readoutArena : Arena where
  signature := signature
  Law r := ∀ q (hq : 0 < q), Function.Surjective (fun y => resetSquareReadout q (r.readout () q y))

abbrev kernelArena : Arena where
  signature := signature
  Law r := ∀ q (hq : 0 < q) (v : VertexModule Sign q),
    resetSquareDefect q (r.readout () q v) = 0 ↔
      if q%4 = 3 then ∃! k : ℤ × ℤ, v = resetSquareKernelVector q k else v = 0

abbrev timeArena : Arena where
  signature := signature
  Law r := ∀ q (h2 : q%4 = 2) (v : VertexModule Sign q),
    resetFiveClock q (transition (resetMatrix q) (r.readout () q v)) = 3 * resetFiveClock q v

abbrev clockOntoArena : Arena where
  signature := signature
  Law r := ∀ q (hq : 0 < q), Function.Surjective (fun v => resetFiveClock q (r.readout () q v))

abbrev clockImageArena : Arena where
  signature := signature
  Law r := ∀ q (h2 : q%4 = 2) (v : VertexModule Sign q),
    (∃ u, resetSquareDefect q u = v) ↔ resetFiveClock q (r.readout () q v) = 0

private theorem bad_image : ¬ imageArena.Law bad := by
  intro h
  obtain ⟨v,hv⟩ := reset_square_readout_surjective 2 (by decide) (1 : ZMod 5)
  have hh := (h 2 (by decide) v).mp ⟨0,map_zero _⟩
  rw [hv] at hh
  exact (by decide : (1 : ZMod 5) ≠ 0) hh

private theorem bad_readout : ¬ readoutArena.Law bad := by
  intro h
  obtain ⟨v,hv⟩ := h 2 (by decide) (1 : ZMod 5)
  change resetSquareReadout 2 0 = (1 : ZMod 5) at hv
  rw [map_zero] at hv
  exact (by decide : (0 : ZMod 5) ≠ 1) hv

private theorem bad_kernel : ¬ kernelArena.Law bad := by
  intro h
  obtain ⟨v,hv⟩ := reset_five_clock_surjective 1 (by decide) 1
  have hh := (h 1 (by decide) v).mp (map_zero _)
  change v = 0 at hh
  rw [hh,map_zero] at hv
  exact (by decide : (0 : ZMod 5) ≠ 1) hv

private theorem bad_time : ¬ timeArena.Law bad := by
  intro h
  obtain ⟨v,hv⟩ := reset_five_clock_surjective 2 (by decide) 1
  have hh := h 2 (by decide) v
  change resetFiveClock 2 (transition (resetMatrix 2) 0) = 3 * resetFiveClock 2 v at hh
  rw [map_zero,map_zero,hv,mul_one] at hh
  exact (by decide : (0 : ZMod 5) ≠ 3) hh

private theorem bad_clock_onto : ¬ clockOntoArena.Law bad := by
  intro h
  obtain ⟨v,hv⟩ := h 2 (by decide) (1 : ZMod 5)
  change resetFiveClock 2 0 = 1 at hv
  rw [map_zero] at hv
  exact (by decide : (0 : ZMod 5) ≠ 1) hv

private theorem actual_clock_image : clockImageArena.Law actual := by
  intro q h2 v
  change v ∈ LinearMap.range (resetSquareDefect q) ↔ v ∈ LinearMap.ker (resetFiveClock q)
  rw [reset_five_clock_image q h2]

private theorem bad_clock_image : ¬ clockImageArena.Law bad := by
  intro h
  obtain ⟨v,hv⟩ := reset_five_clock_surjective 2 (by decide) 1
  obtain ⟨u,hu⟩ := (h 2 (by decide) v).mpr (map_zero _)
  have hm : v ∈ LinearMap.range (resetSquareDefect 2) := ⟨u,hu⟩
  rw [reset_five_clock_image 2 (by decide)] at hm
  change resetFiveClock 2 v = 0 at hm
  rw [hv] at hm
  exact (by decide : (1 : ZMod 5) ≠ 0) hm

def reset_square_image_evidence : Registration imageArena (imageArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reset_square_image,bad,bad_image⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_image⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def reset_square_image_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_image)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_image_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_image_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena⟩
  objectArena := .source ⟨imageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena ⟨reset_square_image_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def reset_square_readout_surjective_evidence : Registration readoutArena (readoutArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reset_square_readout_surjective,bad,bad_readout⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_readout⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def reset_square_readout_surjective_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_readout_surjective)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_readout_surjective_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_readout_surjective_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨readoutArena⟩
  objectArena := .source ⟨readoutArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source readoutArena ⟨reset_square_readout_surjective_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def reset_square_kernel_evidence : Registration kernelArena (kernelArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reset_square_kernel,bad,bad_kernel⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_kernel⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def reset_square_kernel_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_kernel)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_kernel_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_square_kernel_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨reset_square_kernel_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def reset_five_clock_time_evidence : Registration timeArena (timeArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reset_five_clock_time,bad,bad_time⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_time⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def reset_five_clock_time_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_time)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_time_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_time_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨timeArena⟩
  objectArena := .source ⟨timeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timeArena ⟨reset_five_clock_time_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def reset_five_clock_surjective_evidence : Registration clockOntoArena (clockOntoArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reset_five_clock_surjective,bad,bad_clock_onto⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_clock_onto⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def reset_five_clock_surjective_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_surjective)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_surjective_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_surjective_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨clockOntoArena⟩
  objectArena := .source ⟨clockOntoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source clockOntoArena ⟨reset_five_clock_surjective_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def reset_five_clock_image_evidence : Registration clockImageArena (∀ q (h2 : q%4 = 2), LinearMap.range (resetSquareDefect q) = LinearMap.ker (resetFiveClock q)) where
  actual := actual
  bridge := by
    constructor
    · intro h q h2 v
      change v ∈ LinearMap.range (resetSquareDefect q) ↔ v ∈ LinearMap.ker (resetFiveClock q)
      rw [h q h2]
    · intro h q h2
      ext v
      exact h q h2 v
  variation := ⟨actual_clock_image,bad,bad_clock_image⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_clock_image⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def reset_five_clock_image_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_image)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_image_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.reset_five_clock_image_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨clockImageArena⟩
  objectArena := .source ⟨clockImageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source clockImageArena ⟨reset_five_clock_image_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev blockSignature : Signature where
  Params := Unit
  State _ := Row × Row
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Row
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev blockActual : Realization blockSignature := realize blockSignature (fun _ _ z => z.1) (fun e => nomatch e)
abbrev blockBad : Realization blockSignature := realize blockSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev blockArena : Arena where
  signature := blockSignature
  Law r := ∀ x y : Row,
    (fiveBlock (r.readout () () (x,y)) = 0 ↔ x = 0) ∧
      ((∃ a : Row, fiveBlock a = y) ↔ (5 : ℤ) ∣ y.coeff 1 + y.coeff (Multiplicative.ofAdd true))

private theorem block_bad : ¬ blockArena.Law blockBad := by
  intro h
  let x : Row := rowEquiv.symm (1,0)
  have hx : x = 0 := (h x 0).1.mp (map_zero _)
  have hh := congrArg rowEquiv hx
  change rowEquiv (rowEquiv.symm (1,0)) = rowEquiv 0 at hh
  rw [rowEquiv.apply_symm_apply,map_zero] at hh
  have hf := congrArg Prod.fst hh
  norm_num at hf

def five_block_classification_evidence : Registration blockArena (blockArena.Law blockActual) where
  actual := blockActual
  bridge := Iff.rfl
  variation := ⟨five_block_classification,blockBad,block_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨blockBad,?_,rfl,block_bad⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0,0),(rowEquiv.symm (1,0),0),?_⟩
    intro hh
    change (0 : Row) = rowEquiv.symm (1,0) at hh
    have hf := congrArg rowEquiv hh
    rw [map_zero,rowEquiv.apply_symm_apply] at hf
    have hz := congrArg Prod.fst hf
    norm_num at hz

noncomputable def five_block_classification_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.five_block_classification)
    (Realization blockSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.five_block_classification_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect.five_block_classification_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨blockArena⟩
  objectArena := .source ⟨blockArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source blockArena ⟨five_block_classification_evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize blockSignature (fun _ _ z => z.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
