import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
import Reg.Support.DependentFamily

/-! The actual group-order parameter readout in the complete necessity theorem. -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : ℤ, ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ k => (k : ℤ)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => 2*p.1^2-p.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t r : ℤ} {k : ℕ} (_ : 1 ≤ t) (_ : 0 ≤ r) (_ : r < t)
    (_ : R.readout () ⟨t,r⟩ k = 2*t^2-r) (a b : Target k)
    (_ : ∀ g : Target k, ∃ x y : ℤ, |x|+|y| ≤ 2*t ∧ x • a + y • b = g),
    2 ∣ r ∧ (Odd t → 4 ∣ r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcov : ∀ g : Target 1, ∃ x y : ℤ,
      |x|+|y| ≤ 2*(3 : ℤ) ∧ x • ((1,0) : Target 1) + y • ((0,1) : Target 1) = g := by
    rintro ⟨x,y⟩
    fin_cases x <;> fin_cases y
    · exact ⟨0,0,by norm_num,by norm_num <;> rfl⟩
    · exact ⟨0,1,by norm_num,by norm_num <;> rfl⟩
    · exact ⟨1,0,by norm_num,by norm_num <;> rfl⟩
    · exact ⟨1,1,by norm_num,by norm_num <;> rfl⟩
  have hh := h (k := 1) (t := 3) (r := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (by rfl) (1,0) (0,1) hcov
  have hh4 := hh.2 (by decide : Odd (3 : ℤ))
  norm_num at hh4

def sourceRegistration : Registration arena (type_of% (@top_strip_necessity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨top_strip_necessity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨3,2⟩,1,2,?_⟩
    norm_num [actual, realize]

def topStripRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@top_strip_necessity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.top_strip_necessity.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => (k : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","domain","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity

private def sampleMap : Plane →+ Target 1 where
  toFun z := ((z 0 : ZMod 2), (z 1 : ZMod 2))
  map_zero' := by simp
  map_add' z w := by simp

private theorem sampleMap_surjective : Function.Surjective sampleMap := by
  rintro ⟨a, b⟩
  refine ⟨![(a.val : ℤ), (b.val : ℤ)], ?_⟩
  apply Prod.ext <;> simp [sampleMap]

private theorem sampleMap_cover : LeeCovers sampleMap (2 * (1 : ℤ)) := by
  rintro ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exact ⟨![0, 0], by norm_num, by norm_num [sampleMap] <;> rfl⟩
  · exact ⟨![0, 1], by norm_num, by norm_num [sampleMap] <;> rfl⟩
  · exact ⟨![1, 0], by norm_num, by norm_num [sampleMap] <;> rfl⟩
  · exact ⟨![1, 1], by norm_num, by norm_num [sampleMap] <;> rfl⟩

abbrev kernelSignature : Signature where
  Params := Unit
  State _ := Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def kernelActual : Realization kernelSignature := realize kernelSignature
  (fun _ _ z => z 0) (fun e => nomatch e)

def kernelRejected : Realization kernelSignature := realize kernelSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ {k : ℕ} (f : Plane →+ Target k)
    (_ : Function.Surjective f) {z : Plane} (_ : f z = 0),
    2 ∣ R.readout () () z ∧ 2 ∣ z 1

private theorem kernelRejected_law : ¬ kernelArena.Law kernelRejected := by
  intro h
  have hh := h sampleMap sampleMap_surjective (z := 0) (map_zero sampleMap)
  norm_num [kernelRejected, realize] at hh

def kernelSource : Registration kernelArena (type_of% (@kernel_even)) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨kernel_even, kernelRejected, kernelRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨kernelRejected, ?_, rfl, kernelRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), ![0, 0], ![1, 0], by norm_num [kernelActual, realize]⟩

abbrev orderSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def orderActual : Realization orderSignature := realize orderSignature
  (fun _ _ k => 2 * k) (fun e => nomatch e)

def orderRejected : Realization orderSignature := realize orderSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev orderArena : Arena where
  signature := orderSignature
  Law R := ∀ {k : ℕ} (_ : 0 < k) (f : Plane →+ Target k)
    (_ : Function.Surjective f),
    (oddLattice f).toAddSubgroup.index = R.readout () () k

private theorem orderRejected_law : ¬ orderArena.Law orderRejected := by
  intro h
  have hh := h (k := 1) (by decide) sampleMap sampleMap_surjective
  rw [oddLattice_index (by decide) sampleMap sampleMap_surjective] at hh
  norm_num [orderRejected, realize] at hh

def orderSource : Registration orderArena (type_of% (@oddLattice_index)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨oddLattice_index, orderRejected, orderRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨orderRejected, ?_, rfl, orderRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [orderActual, realize]⟩

abbrev squareSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def squareActual : Realization squareSignature := realize squareSignature
  (fun _ _ t => 2 * t) (fun e => nomatch e)

def squareRejected : Realization squareSignature := realize squareSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev squareArena : Arena where
  signature := squareSignature
  Law R := ∀ {k : ℕ} (f : Plane →+ Target k) {t : ℤ}
    (_ : LeeCovers f (2 * t)),
    RectangleCovers (oddLattice f) (R.readout () () t) (2 * t)

private theorem squareRejected_law : ¬ squareArena.Law squareRejected := by
  intro h
  obtain ⟨x, y, hx, hx', _⟩ := h sampleMap (t := 1) sampleMap_cover (0 : Plane)
  change x < 0 at hx'
  omega

def squareSource : Registration squareArena (type_of% (@oddLattice_cover)) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨oddLattice_cover, squareRejected, squareRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨squareRejected, ?_, rfl, squareRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [squareActual, realize]⟩

def kernelRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@kernel_even) (Realization kernelSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.kernel_even.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.kernelSource
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ _ z => z 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def orderRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@oddLattice_index) (Realization orderSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.oddLattice_index.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.orderSource
  realizationSource := none
  generated := false
  arena := .source ⟨orderArena⟩
  objectArena := .source ⟨orderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source orderArena ⟨orderSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orderSignature (fun _ _ k => 2 * k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def squareRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@oddLattice_cover) (Realization squareSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.oddLattice_cover.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.squareSource
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena⟩
  objectArena := .source ⟨squareArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena ⟨squareSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize squareSignature (fun _ _ t => 2 * t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


abbrev sumDiffInjectionSignature : Signature where
  Params := Unit
  State _ := Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Plane
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def sumDiffInjectionActual : Realization sumDiffInjectionSignature := realize sumDiffInjectionSignature
  (fun _ _ z => sumDiff z) (fun e => nomatch e)
noncomputable def sumDiffInjectionRejected : Realization sumDiffInjectionSignature := realize sumDiffInjectionSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sumDiffInjectionArena : Arena where
  signature := sumDiffInjectionSignature
  Law R := Function.Injective (fun z => R.readout () () z)
private theorem sumDiffInjectionRejected_law : ¬ sumDiffInjectionArena.Law sumDiffInjectionRejected := by
  intro h
  have hh := h (a₁ := (0 : Plane)) (a₂ := ![1,0]) rfl
  have hh0 := congrFun hh 0
  norm_num at hh0
noncomputable def sumDiffInjectionSource : Registration sumDiffInjectionArena (type_of% (@sumDiff_injective)) where
  actual := sumDiffInjectionActual
  bridge := Iff.rfl
  variation := ⟨sumDiff_injective, sumDiffInjectionRejected, sumDiffInjectionRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sumDiffInjectionRejected, ?_, rfl, sumDiffInjectionRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),0,![1,0],?_⟩
    intro h
    have he := sumDiff_injective h
    have hh := congrFun he 0
    change (0 : ℤ) = 1 at hh
    norm_num at hh
noncomputable def sumDiffInjectionRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@sumDiff_injective) (Realization sumDiffInjectionSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.sumDiff_injective.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.sumDiffInjectionSource
  realizationSource := none
  generated := false
  arena := .source ⟨sumDiffInjectionArena⟩
  objectArena := .source ⟨sumDiffInjectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumDiffInjectionArena ⟨sumDiffInjectionSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sumDiffInjectionSignature (fun _ _ z => sumDiff z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev sumDiffRangeIndexSignature : Signature where
  Params := Unit
  State _ := Submodule ℤ Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def sumDiffRangeIndexActual : Realization sumDiffRangeIndexSignature := realize sumDiffRangeIndexSignature
  (fun _ _ K => K.toAddSubgroup.index) (fun e => nomatch e)
noncomputable def sumDiffRangeIndexRejected : Realization sumDiffRangeIndexSignature := realize sumDiffRangeIndexSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sumDiffRangeIndexArena : Arena where
  signature := sumDiffRangeIndexSignature
  Law R := R.readout () () sumDiff.range = 2
private theorem sumDiffRangeIndexRejected_law : ¬ sumDiffRangeIndexArena.Law sumDiffRangeIndexRejected := by
  intro h
  norm_num [sumDiffRangeIndexRejected,realize] at h
noncomputable def sumDiffRangeIndexSource : Registration sumDiffRangeIndexArena (type_of% (@sumDiff_index)) where
  actual := sumDiffRangeIndexActual
  bridge := Iff.rfl
  variation := ⟨sumDiff_index, sumDiffRangeIndexRejected, sumDiffRangeIndexRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sumDiffRangeIndexRejected, ?_, rfl, sumDiffRangeIndexRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),⊤,sumDiff.range,?_⟩
    change (⊤ : Submodule ℤ Plane).toAddSubgroup.index ≠ sumDiff.range.toAddSubgroup.index
    rw [sumDiff_index]
    change (⊤ : AddSubgroup Plane).index ≠ 2
    simp
noncomputable def sumDiffRangeIndexRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@sumDiff_index) (Realization sumDiffRangeIndexSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.sumDiff_index.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.sumDiffRangeIndexSource
  realizationSource := none
  generated := false
  arena := .source ⟨sumDiffRangeIndexArena⟩
  objectArena := .source ⟨sumDiffRangeIndexArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumDiffRangeIndexArena ⟨sumDiffRangeIndexSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sumDiffRangeIndexSignature (fun _ _ K => K.toAddSubgroup.index) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
