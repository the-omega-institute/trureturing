import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering
import Mathlib.Algebra.Group.ULift

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering
open _root_.D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open scoped BigOperators

universe u v
noncomputable section

abbrev signature : DependentFamily.Signature where
  Params := Σ G : Type v, AddCommGroup G
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{v} :=
  DependentFamily.realize signature (fun _ p w => by
    letI := p.2
    classical
    exact decide (Good w)) (fun e => nomatch e)

def rejected : DependentFamily.Realization signature.{v} :=
  DependentFamily.realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature.{v}
  Law R := ∀ {X : Type u} {G : Type v} [Fintype X] [AddCommGroup G]
    (a : X → G) (ha : Function.Injective a) (ha0 : ∀ x, a x ≠ 0)
    (k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ Fintype.card X) (hhalf : Fintype.card X < 2 * k)
    (hgirth : ∀ T : Finset X, T.Nonempty → T ≠ Finset.univ →
      (∑ x ∈ T, a x) = 0 → k ≤ T.card),
    ∃ w : List X, w.Perm (Finset.univ : Finset X).toList ∧
      R.readout () ⟨G, inferInstance⟩ (w.map a) = true

abbrev sourceScope := type_of% (@exists_good_order.{u,v})

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual := by
  simp only [sourceScope, arena, actual, DependentFamily.realize, decide_eq_true_eq]

theorem actual_positive : arena.{u,v}.Law actual :=
  source_bridge.mp exists_good_order

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let a : ULift.{u} (Fin 2) → ULift.{v} ℤ := fun i => ⟨(i.down.val : ℤ) + 1⟩
  have ha : Function.Injective a := by
    intro x y he
    apply ULift.ext
    apply Fin.ext
    have hh := congrArg ULift.down he
    change (x.down.val : ℤ) + 1 = (y.down.val : ℤ) + 1 at hh
    omega
  have ha0 : ∀ x, a x ≠ 0 := by
    intro x he
    have hh := congrArg ULift.down he
    change (x.down.val : ℤ) + 1 = 0 at hh
    omega
  have hg : ∀ T : Finset (ULift.{u} (Fin 2)), T.Nonempty → T ≠ Finset.univ →
      (∑ x ∈ T, a x) = 0 → 2 ≤ T.card := by
    intro T hn _ hz
    by_contra hc
    have hcard : T.card = 1 := by have := Finset.card_pos.mpr hn; omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ha0 x (by simpa using hz)
  obtain ⟨w, _, hw⟩ := @h (ULift.{u} (Fin 2)) (ULift.{v} ℤ)
    inferInstance inferInstance a ha ha0 2 (by decide) (by simp) (by simp) hg
  change false = true at hw
  cases hw

def familyRegistration : DependentFamily.Registration arena.{u,v} sourceScope.{u,v} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{v} ℤ, inferInstance⟩, [], [0, 0], ?_⟩
    have hnil : Good ([] : List (ULift.{v} ℤ)) := by
      intro i j hij hj
      simp only [List.length_nil] at hj
      omega
    have hbad : ¬ Good ([0, 0] : List (ULift.{v} ℤ)) := by
      intro hw
      exact hw 0 1 (by decide) (by decide) (Or.inr (by decide)) (by simp)
    simpa [actual, DependentFamily.realize, hnil, hbad]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_good_order.{u,v}) (DependentFamily.Realization signature.{v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering.exists_good_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering
