import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection

universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    ∀ {V : Type u} [Fintype V] [Nonempty V],
    (∀ (F : V → V → V → ℝ)
      (h12 : ∀ i j k, F j i k = -F i j k)
      (h23 : ∀ i j k, F i k j = -F i j k),
      (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
        R.readout () () (tetraDefect F r i j k)) =
        4 * (Fintype.card V : ℝ) *
          (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2)) ∧
    (4 ≤ Fintype.card V → ∀ C : ℝ,
      (∀ (F : V → V → V → ℝ)
        (h12 : ∀ i j k, F j i k = -F i j k)
        (h23 : ∀ i j k, F i k j = -F i j k),
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (tetraDefect F r i j k) ^ 2) ≤
          C * (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2)) →
      4 * (Fintype.card V : ℝ) ≤ C)

theorem actual_law : arena.{u}.Law actual := by
  intro V _ _
  constructor
  · intro F h12 h23
    have hs := @_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal V _ _
    simpa [actual, realize, signature] using
      hs.1 F h12 h23
  · intro hcard C H
    have hs := @_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal V _ _
    exact hs.2 hcard C H

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let F : V → V → V → ℝ := fun _ _ _ => 0
  have hbad := (h (V := V)).1 F (by intros; simp [F]) (by intros; simp [F])
  norm_num [rejected, realize, signature, F, tetraDefect, edgeCoboundary,
    averageEdge, contraction] at hbad

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, signature]

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal.{u}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "SimplexTwoCochainL2Projection") "tetra_defect_energy_eq_and_optimal") "Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection/Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection
