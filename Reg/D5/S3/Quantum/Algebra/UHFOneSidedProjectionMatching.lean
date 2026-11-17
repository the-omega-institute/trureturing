import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
import Reg.Support.DependentFamily

/-! Exact source audits with arbitrary dependent algebra carriers. -/

namespace Reg.D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching

open _root_.D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix.Norms.L2Operator

universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev equalitySignature : Signature where
  Params := Type u
  State X := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization equalitySignature.{u} :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization equalitySignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev ScalarCarrier := ULift.{u} Unit → ℂ

private def scalarEmbed : Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ] ScalarCarrier.{u} where
  toFun A _ := A 0 0
  map_one' := by ext x; simp
  map_mul' A B := by ext x; simp [Matrix.mul_apply]
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' z := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := rfl

private def scalarModel : FullMatrixModel ScalarCarrier.{u} where
  size _ := 1
  embed _ := scalarEmbed
  injective _ := by
    intro A B h
    have h₀ := congrFun h (ULift.up ())
    change A 0 0 = B 0 0 at h₀
    ext i j
    simpa only [Subsingleton.elim i 0, Subsingleton.elim j 0] using h₀
  increasing _ _ _ := Set.Subset.rfl
  dense := by
    have h : (⋃ n : ℕ, Set.range (scalarEmbed : Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ] ScalarCarrier.{u})) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f
      refine Set.mem_iUnion.mpr ⟨0, Matrix.of (fun _ _ => f (ULift.up ())), ?_⟩
      funext x
      exact congrArg f (Subsingleton.elim _ _)
    simpa only [h] using dense_univ

private theorem dependence : ObservationalDependence equalitySignature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Bool, ULift.up false, ULift.up true, ?_⟩
  intro h
  have hf : (ULift.up true : ULift.{u} Bool) = ULift.up false :=
    Eq.mp (congrFun h (ULift.up false)) rfl
  cases hf

private theorem sensitivity (law : Realization equalitySignature.{u} → Prop)
    (hbad : ¬ law rejected) : Sensitivity ⟨equalitySignature, law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

namespace Localization

abbrev arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {C : Type u} [CStarAlgebra C] (M : FullMatrixModel C) (p : C),
    IsStarProjection p →
    ∃ (n : ℕ) (u : unitary C) (Q : Matrix (Fin (M.size n)) (Fin (M.size n)) ℂ),
      IsStarProjection Q ∧ R.readout () C ((u : C) * p * star (u : C)) (M.embed n Q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, u, Q, hQ, hf⟩ := @h ScalarCarrier inferInstance scalarModel 0 (by simp)
  exact hf

def source_registration : Registration arena (type_of% @localize_projection.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@localize_projection.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@localize_projection.{u}) (Realization equalitySignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching.localize_projection.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching.Localization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Localization

namespace Matching

abbrev arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {C : Type u} [CStarAlgebra C] (M : FullMatrixModel C) (r v : C),
    IsStarProjection r → IsStarProjection v → r ≠ 0 → v ≠ 0 →
    ∃ (N : ℕ) (s : Finset (Fin (M.size N))) (l : Fin (M.size N) → C)
      (m : C) (w : Fin (M.size N) → C),
      s.Nonempty ∧ (∀ i ∈ s, IsStarProjection (l i) ∧ l i ≠ 0) ∧
      (↑s : Set (Fin (M.size N))).Pairwise (fun i j => l i * l j = 0) ∧
      R.readout () C (∑ i ∈ s, l i) r ∧ IsStarProjection m ∧ m ≠ 0 ∧
      m * v = m ∧ v * m = m ∧
      (∀ i ∈ s, star (w i) * w i = m ∧ w i * star (w i) = l i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, s, l, m, w, hs, hL, ho, hf, rest⟩ :=
    @h ScalarCarrier inferInstance scalarModel 1 1 (by simp) (by simp) one_ne_zero one_ne_zero
  exact hf

def source_registration : Registration arena (type_of% @one_sided_projection_matching.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_sided_projection_matching.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@one_sided_projection_matching.{u}) (Realization equalitySignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching.one_sided_projection_matching.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching.Matching.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Matching

end
end Reg.D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
