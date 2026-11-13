import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.Additive.NathansonLatticeRootRefutation

/-! Source-bound full-range and minimum observations. -/

namespace Reg.D5.S3.Arith.Additive.NathansonLatticeRootRefutation

open _root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Range

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  (DependentFamily.realize signature (fun _ _ k => integerRange 2 k) (fun e => nomatch e))

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (∅ : Set ℕ)) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := R.readout () () 3 = ({5,6} : Set ℕ)

abbrev sourceScope := type_of% (@_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.range_two_three)

private theorem erased_fails : ¬ arena.Law erased := by
  change ¬ ((∅ : Set ℕ) = {5,6})
  intro heq
  exact (Set.ext_iff.mp heq 5).mpr (by simp)

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.range_two_three, erased, erased_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ erased_fails
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : ℕ), (3 : ℕ), ?_⟩
    intro heq
    change integerRange 2 0 = integerRange 2 3 at heq
    have hz : 0 ∈ integerRange 2 0 := ⟨∅, rfl, by decide⟩
    rw [heq, range_two_three] at hz
    simpa using hz

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.range_two_three)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.NathansonLatticeRootRefutation.range_two_three.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.Range.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ k => integerRange 2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.NathansonLatticeRootRefutation
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Range


namespace Interval

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  (DependentFamily.realize signature (fun _ _ k => intervalCovers 2 3 k) (fun e => nomatch e))

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => True) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := R.readout () () 3 ∧ ∀ D, R.readout () () D → 3 ≤ D

abbrev sourceScope := type_of% (@_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.interval_minimum)

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have bad : 3 ≤ (0 : ℕ) := h.2 0 True.intro
  omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.interval_minimum, erased, erased_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ erased_fails
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : ℕ), (3 : ℕ), ?_⟩
    intro heq
    change intervalCovers 2 3 0 = intervalCovers 2 3 3 at heq
    have bad : intervalCovers 2 3 0 := Eq.mpr heq interval_minimum.1
    exact Nat.lt_irrefl 0 bad.1

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.interval_minimum)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.NathansonLatticeRootRefutation.interval_minimum.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.Interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ k => intervalCovers 2 3 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.NathansonLatticeRootRefutation
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "domain"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interval


namespace Cube

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  (DependentFamily.realize signature (fun _ _ k => cubeCovers 2 3 2 k) (fun e => nomatch e))

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => True) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := R.readout () () 2 ∧ ∀ D, R.readout () () D → 2 ≤ D

abbrev sourceScope := type_of% (@_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.cube_minimum)

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have bad : 2 ≤ (0 : ℕ) := h.2 0 True.intro
  omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.cube_minimum, erased, erased_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ erased_fails
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : ℕ), (2 : ℕ), ?_⟩
    intro heq
    change cubeCovers 2 3 2 0 = cubeCovers 2 3 2 2 at heq
    have bad : cubeCovers 2 3 2 0 := Eq.mpr heq cube_minimum.1
    exact Nat.lt_irrefl 0 bad.1

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.cube_minimum)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.NathansonLatticeRootRefutation.cube_minimum.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.NathansonLatticeRootRefutation.Cube.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ k => cubeCovers 2 3 2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.NathansonLatticeRootRefutation
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "domain"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cube


end Reg.D5.S3.Arith.Additive.NathansonLatticeRootRefutation
