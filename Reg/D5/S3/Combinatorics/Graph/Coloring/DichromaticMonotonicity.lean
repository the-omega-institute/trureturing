import D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

namespace Reg.D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity

open _root_.D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity
open _root_.D5.S3.Combinatorics.Graph.Coloring.DichromaticPartitionExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ V : Type u, Σ _ : Fintype V, DecidableEq V
  State p := Digraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p D ↦ @normalizedDichromaticPolynomial p.1 p.2.1 p.2.2 D)
    (fun e ↦ nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ x ↦ -x) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [f : Fintype V] [d : DecidableEq V] (D : Digraph V),
    MonotoneOn (R.readout () ⟨V, f, d⟩ D) (Set.Ici ((Fintype.card V : ℝ) - 1))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hm : MonotoneOn (fun x : ℝ ↦ -x) (Set.Ici 0) := by
    simpa [rejected, realize] using @h (ULift.{u} (Fin 1)) inferInstance inferInstance ⊥
  have hc := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show (1 : ℝ) ∈ Set.Ici 0 by simp)
    (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num at hc

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let V := ULift.{u} (Fin 1)
  refine ⟨⟨V, inferInstance, inferInstance⟩, ⊥, ⊤, ?_⟩
  intro h
  have hv : V := ⟨0⟩
  have hbot : dichromaticPolynomial (⊥ : Digraph V) = X ^ Fintype.card V :=
    dichromaticPolynomial_eq_pow_of_acyclic _ (fun _ _ _ _ ha ↦ ha 0)
  have htop : dichromaticPolynomial (⊤ : Digraph V) = 0 :=
    dichromaticPolynomial_eq_zero_of_loop _ hv trivial
  have he := congrFun h (1 : ℝ)
  change normalizedDichromaticPolynomial (⊥ : Digraph V) 1 =
    normalizedDichromaticPolynomial (⊤ : Digraph V) 1 at he
  simp [normalizedDichromaticPolynomial, hbot, htop] at he

def family : Registration arena.{u} (type_of% @normalizedDichromaticPolynomial_monotoneOn.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalizedDichromaticPolynomial_monotoneOn.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@normalizedDichromaticPolynomial_monotoneOn.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Combinatorics.Graph.Coloring.DichromaticMonotonicity
