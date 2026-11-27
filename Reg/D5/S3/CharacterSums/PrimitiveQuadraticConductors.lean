import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.PrimitiveQuadraticConductors
import Reg.Support.SingleDependentReadout

/-! The audit tests the first prime level and the recovered native level. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open DirichletCharacter
open _root_.D5.S3.CharacterSums.PrimitiveQuadraticConductors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.PrimitiveQuadraticConductors

namespace Six

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (q d : ℕ) (_hq : q.Prime) (_hd : d.Prime)
    (_hq2 : q ≠ 2) (_hd2 : d ≠ 2) (_hqd : q ≠ d),
    let j (p n : ℕ) : ℂ := (jacobiSym (n:ℤ) p:ℂ)
    let e (n : ℕ) : ℂ := (ZMod.χ₈ (n:ZMod 8):ℤ)
    represents (V.readout () () q) (j q) ∧ represents (8*q) (fun n => e n*j q n) ∧
    represents d (j d) ∧ represents (8*d) (fun n => e n*j d n) ∧
    represents (q*d) (fun n => j q n*j d n) ∧
    represents (8*(q*d)) (fun n => e n*(j q n*j d n))

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  have hr := (h 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)).1
  change represents 1 (fun n : ℕ => (jacobiSym (n:ℤ) 3 : ℂ)) at hr
  obtain ⟨χ, _, hv⟩ := hr
  have hz := hv 0
  change χ (0 : ZMod 1) = (jacobiSym 0 3 : ℂ) at hz
  rw [Subsingleton.elim (0 : ZMod 1) 1, map_one, jacobiSym.zero_left (by decide)] at hz
  norm_num at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual,realize]

def family : Registration arena (type_of% @six_quadratic_levels) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@six_quadratic_levels, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@six_quadratic_levels) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.PrimitiveQuadraticConductors.six_quadratic_levels
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.PrimitiveQuadraticConductors.Six "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.PrimitiveQuadraticConductors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Six

namespace Native

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {R : Type u} [CommMonoidWithZero R]
    {r a M : ℕ} [NeZero r] [NeZero a] [NeZero M]
    (χ : DirichletCharacter R r) (_hχ : χ.IsPrimitive) {f : ℕ → R} (_ha : represents a f)
    (_hi : ∀ n : ℕ, n.Coprime M → χ (n:ZMod r) = f n),
    r=V.readout () () a ∧ ∀ n : ℕ, χ (n:ZMod r) = f n

private theorem reject_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let χ : DirichletCharacter (ULift.{u} ℕ) 1 := 1
  have hp : χ.IsPrimitive := (χ.eq_one_iff_conductor_eq_one).mp rfl
  let f (n : ℕ) : ULift.{u} ℕ := χ (n:ZMod 1)
  have hf : represents 1 f := ⟨χ, hp, fun _ => rfl⟩
  have he := (h (M := 1) χ hp hf (fun _ _ => rfl)).1
  change 1 = (0:ℕ) at he
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual,realize]

def family : Registration arena (type_of% @inducing_level_and_values) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inducing_level_and_values, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inducing_level_and_values) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.PrimitiveQuadraticConductors.inducing_level_and_values
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.PrimitiveQuadraticConductors.Native "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.PrimitiveQuadraticConductors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Native

end Reg.D5.S3.CharacterSums.PrimitiveQuadraticConductors
