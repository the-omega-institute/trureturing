import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
import Reg.Support.DependentFamily

/-! Source-bound cover entropy observation with the entire original limit law. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
open Dynamics SymbolicDynamics Set Function Filter
open scoped Topology

namespace Reg.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy

noncomputable section
universe u

structure Parameters where
  X : Type u
  uniformX : UniformSpace X

abbrev signature : Signature where
  Params := Parameters.{u}
  State P := (P.X → P.X) × Set P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := EReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P s => @coverEntropy P.X P.uniformX s.1 s.2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

/-- Keep the source alphabet, all three instances, nonemptiness, forward
invariance, the real bounds and the actual real limit. Only the source
coverEntropy operation is interpreted by the varying readout. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [Fintype A] [UniformSpace A] [DiscreteUniformity A]
    (S : Set (ℕ → A)) (_hne : S.Nonempty)
    (_hinv : MapsTo (FullShift.shift (1 : ℕ)) S S),
    ∃ h : ℝ,
      0 ≤ h ∧ h ≤ Real.log (Fintype.card A) ∧
      Tendsto (fun n => Real.log (prefixCount S n : ℝ) / n) atTop (𝓝 h) ∧
      R.readout () ⟨ℕ → A, inferInstance⟩ (FullShift.shift (1 : ℕ), S) = (h : EReal)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hlaw
  obtain ⟨h, _, _, _, he⟩ :=
    @hlaw (ULift.{u} Unit) inferInstance inferInstance inferInstance
      Set.univ ⟨fun _ => ⟨()⟩, Set.mem_univ _⟩ (by intro x hx; trivial)
  change (⊤ : EReal) = (h : EReal) at he
  exact EReal.top_ne_coe h he

def familyRegistration : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy.prefix_growth_entropy.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy.prefix_growth_entropy.{u},
      rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let P : Parameters.{u} := ⟨ULift.{u} Unit, inferInstance⟩
    refine ⟨P, (id, ∅), (id, Set.univ), ?_⟩
    change coverEntropy (id : ULift.{u} Unit → ULift.{u} Unit) ∅ ≠
      coverEntropy (id : ULift.{u} Unit → ULift.{u} Unit) Set.univ
    rw [coverEntropy_empty]
    intro he
    have hn := coverEntropy_nonneg (id : ULift.{u} Unit → ULift.{u} Unit)
      (show (Set.univ : Set (ULift.{u} Unit)).Nonempty from ⟨⟨()⟩, trivial⟩)
    rw [← he] at hn
    simp at hn

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy.prefix_growth_entropy.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy.coverEntropy
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ P s => @coverEntropy P.X P.uniformX s.1 s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration

end
end Reg.D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
