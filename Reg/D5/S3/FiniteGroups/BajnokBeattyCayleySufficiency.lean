import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency

abbrev signature : Signature where
  Params := Σ t : ℕ, Σ j : ℕ, ZMod 2 × ZMod (4 * (t ^ 2 - j))
  State p := ZMod 2 × ZMod (4 * (p.1 ^ 2 - p.2.1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (b : signature.State p) : Prop :=
  p.2.2 ≠ b ∧ ∀ g, ∃ x y : ℤ,
    g = x • p.2.2 + y • b ∧ |x| + |y| ≤ 2 * (p.1 : ℤ)

def actual : Realization signature :=
  realize signature (fun _ p b => observed p b) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ t j : ℕ, 1 ≤ t → j < t → (Even t ∨ Even j) →
    ∃ a b : ZMod 2 × ZMod (4 * (t ^ 2 - j)), r.readout () ⟨t, j, a⟩ b

private theorem actual_law : arena.Law actual := result

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, b, hab⟩ := h 1 0 (by omega) (by omega) (Or.inr ⟨0, rfl⟩)
  exact hab

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨a, b, hab⟩ := result 1 0 (by omega) (by omega) (Or.inr ⟨0, rfl⟩)
    refine ⟨⟨1, 0, a⟩, b, a, ?_⟩
    intro he
    have hbad : observed ⟨1, 0, a⟩ a := Eq.mp he hab
    exact hbad.1 rfl

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency.result)
      (type_of% actual) (type_of% signature.State) Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency.result.__information_unit,
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency,
    definition := none,
    coordinates := #[0, 1, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency
