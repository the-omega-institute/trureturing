import D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair

universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 4 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} {A : Type v} [Fintype V] [Nonempty V] [AddCommGroup A]
    (F : V → V → V → A),
    (∑ r : V, faceErrors F r) = tetraDefects F ∧
      (∃ r : V, Fintype.card V * faceErrors F r ≤ tetraDefects F) ∧
      (∀ edge : V → V → A,
        tetraDefects F ≤
          R.readout () () (Fintype.card V) * edgeErrors F edge) ∧
      ((∀ r i j k, F i j k - F r j k + F r i k - F r i j = 0) ↔
        ∃ edge : V → V → A, ∀ i j k,
          F i j k = edge j k - edge i k + edge i j)

theorem actual_law : arena.{u, v}.Law actual := by
  intro V A _ _ _ F
  simpa [actual, realize, signature] using
    (_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness
      F)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let V := ULift.{u} Bool
  let A := ULift.{v} (ZMod 2)
  let F : V → V → V → A := fun i _ _ =>
    if i.down then ULift.up (1 : ZMod 2) else ULift.up (0 : ZMod 2)
  have hbad := (h (V := V) (A := A) F).2.2.1 (fun _ _ => 0)
  norm_num [rejected, realize, signature, tetraDefects, F, edgeErrors] at hbad
  have hterm := hbad (⟨true⟩ : V) (⟨false⟩ : V)
  have hdown := congrArg ULift.down hterm
  change (0 : ZMod 2) - 1 = 0 at hdown
  exact (by decide : (0 : ZMod 2) - 1 ≠ 0) hdown

theorem sensitivity_proof : Sensitivity arena.{u, v} actual := by
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

def registration : Registration arena.{u, v} (arena.{u, v}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness
  in arena
  readout via (realize signature (fun _ _ n => 4 * n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg",
        "fn", "arg", "body", "arg", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
