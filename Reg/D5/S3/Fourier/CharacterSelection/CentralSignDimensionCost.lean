import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost
import Reg.Support.SingleDependentReadout

/-! Source-linked readout of the number of bits that must fit into the informative channels. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost
open LeanInformationAudit
namespace Reg.D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ k => k) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ k => k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k r m : ℕ} (d : Fin m → ℕ)
    (profile : (Fin k → Bool) → (Fin r → Bool) × (Fin m → Bool))
    (_ : Function.Injective profile) (_ : ∀ x y, (profile x).1 = (profile y).1)
    (_ : ∀ j, 2 ≤ d j),
    R.readout () () k ≤ m ∧ 4 * k + 1 ≤ 1 + r + ∑ j, d j ^ 2 ∧
      ((1 + r + ∑ j, d j ^ 2) = 4 * k + 1 ↔
        m = k ∧ r = 0 ∧ (∀ j, d j = 2) ∧ Function.Bijective (fun x => (profile x).2))

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro law
  let profile (_ : Fin 0 → Bool) : (Fin 0 → Bool) × (Fin 0 → Bool) := ⟨Fin.elim0, Fin.elim0⟩
  have h := (law (k := 0) (r := 0) (m := 0) Fin.elim0 profile
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ => rfl) (fun j => Fin.elim0 j)).1
  exact Nat.not_succ_le_zero 0 h

def family : Registration arena (type_of% @central_sign_dimension_cost) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@central_sign_dimension_cost, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), 0, 1, Nat.zero_ne_one⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost.central_sign_dimension_cost)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost.unit
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost
