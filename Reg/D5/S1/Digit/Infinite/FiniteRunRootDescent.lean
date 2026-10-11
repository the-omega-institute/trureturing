import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.FiniteRunRootDescent
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite.FiniteRunRootDescent
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S1.Digit.Infinite.FiniteRunRootDescent

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k z => root_rate_property k z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def sourceStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ z : ℝ, root_rate_property k z

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 2 ≤ k → ∃ z : ℝ, R.readout () k z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz⟩ := h 2 (by omega)
  exact hz

def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨root_rate_chain, rejected, rejected_law⟩
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
    obtain ⟨z, hz⟩ := root_rate_chain 2 (by omega)
    refine ⟨2, z, 0, ?_⟩
    intro he
    have hzero : root_rate_property 2 0 := Eq.mp he hz
    exact (lt_irrefl (0 : ℝ)) hzero.1.1

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FiniteRunRootDescent.root_rate_chain)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ k z => root_rate_property k z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FiniteRunRootDescent.root_rate_chain.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FiniteRunRootDescent.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ k z => root_rate_property k z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FiniteRunRootDescent,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S1.Digit.Infinite.FiniteRunRootDescent
