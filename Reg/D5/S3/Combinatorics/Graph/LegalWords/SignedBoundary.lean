import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open _root_.D5.S3.Combinatorics.Graph.LegalWordDegree
open _root_.D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State n := Orientation (legalWordGraph n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := (↥(legalWordGraph n).edgeSet → ℝ) →ₗ[ℝ] (Legal n → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ o => signedBoundary o) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (o : Orientation (legalWordGraph n)),
    LinearMap.range (R.readout () n o) = (totalMassZero : Submodule ℝ (Legal n → ℝ)) ∧
    Function.Injective (kernelBoundaryInclusion (observation n) o) ∧
    Function.Exact (kernelBoundaryInclusion (observation n) o)
      (restrictedBoundary (observation n) o) ∧
    Function.Surjective (restrictedBoundary (observation n) o)

private noncomputable def chosen (n : ℕ) : Orientation (legalWordGraph n) :=
  fun e => ⟨Classical.choose (Sym2.mk_surjective e.val),
    Classical.choose_spec (Sym2.mk_surjective e.val)⟩

private def vacant : Legal 1 := ⟨fun _ => false, trivial⟩
private def occupied : Legal 1 := ⟨fun _ => true, trivial⟩

private theorem mass_zero_nonzero :
    ∃ v : Legal 1 → ℝ, v ∈ (totalMassZero : Submodule ℝ (Legal 1 → ℝ)) ∧ v ≠ 0 := by
  refine ⟨vertexDelta occupied - vertexDelta vacant, ?_, ?_⟩
  · change totalMass (vertexDelta occupied - vertexDelta vacant) = 0
    simp [totalMass, vertexDelta, Finset.sum_sub_distrib]
  · intro h
    have hv := congrFun h occupied
    have hne : occupied ≠ vacant := by
      intro he
      have hh := congrArg (fun b : Legal 1 => b.val 0) he
      simp [occupied, vacant] at hh
    simp [vertexDelta, hne] at hv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr := (h 1 (chosen 1)).1
  obtain ⟨v, hv, hn⟩ := mass_zero_nonzero
  have hm : v ∈ LinearMap.range (0 : (↥(legalWordGraph 1).edgeSet → ℝ) →ₗ[ℝ]
      (Legal 1 → ℝ)) := by
    rw [show LinearMap.range (0 : (↥(legalWordGraph 1).edgeSet → ℝ) →ₗ[ℝ]
      (Legal 1 → ℝ)) = totalMassZero from hr]
    exact hv
  exact hn (by simpa using hm)

private noncomputable def reversed {n : ℕ} (o : Orientation (legalWordGraph n)) :
    Orientation (legalWordGraph n) := fun e =>
  ⟨((o e).val.2, (o e).val.1), (Sym2.eq_swap).trans (o e).property⟩

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let o := chosen 1
  refine ⟨1, o, reversed o, ?_⟩
  change signedBoundary o ≠ signedBoundary (reversed o)
  intro h
  have hz : signedBoundary o = 0 := by
    apply LinearMap.ext
    intro f
    funext v
    have hh := congrArg (fun L : (↥(legalWordGraph 1).edgeSet → ℝ) →ₗ[ℝ]
      (Legal 1 → ℝ) => L f v) h
    have hn : signedBoundary (reversed o) f v = -signedBoundary o f v := by
      change (∑ e, f e * edgeVector (reversed o) e v) = -(∑ e, f e * edgeVector o e v)
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases ht : v = (o e).val.1 <;>
        by_cases hh : v = (o e).val.2 <;>
        simp [edgeVector, reversed,
          _root_.D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence,
          ht, hh] <;> ring
    change signedBoundary o f v = signedBoundary (reversed o) f v at hh
    rw [hn] at hh
    change signedBoundary o f v = 0
    linarith
  have hr := (native_boundary_image_short_exact 1 o).1
  obtain ⟨v, hv, hn⟩ := mass_zero_nonzero
  have hm : v ∈ LinearMap.range (signedBoundary o) := by rw [hr]; exact hv
  rw [hz] at hm
  exact hn (by simpa using hm)

noncomputable def registration : Registration arena
    (∀ (n : ℕ) (o : Orientation (legalWordGraph n)),
      LinearMap.range (signedBoundary o) = (totalMassZero : Submodule ℝ (Legal n → ℝ)) ∧
      Function.Injective (kernelBoundaryInclusion (observation n) o) ∧
      Function.Exact (kernelBoundaryInclusion (observation n) o)
        (restrictedBoundary (observation n) o) ∧
      Function.Surjective (restrictedBoundary (observation n) o)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_boundary_image_short_exact, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@native_boundary_image_short_exact)
      (type_of% (realize signature (fun _ _ o => signedBoundary o) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ o => signedBoundary o) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary
