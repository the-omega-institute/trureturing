import D5.S3.Fourier.CharacterSelection.TriangleDefectStability
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability

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
  realize signature (fun _ _ n => 3 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} {A : Type v} [Fintype V] [Nonempty V] [AddCommGroup A]
    (a : V → V → A)
    (hdiag : ∀ i, a i i = 0)
    (hskew : ∀ i j, a j i = -a i j),
    (∑ r : V, edgeDefects a r) = triangleDefects a ∧
      (∃ r : V, Fintype.card V * edgeDefects a r ≤ triangleDefects a) ∧
      ∀ p : V → A,
        triangleDefects a ≤
          R.readout () () (Fintype.card V - 2) * potentialErrors a p

theorem actual_law : arena.{u, v}.Law actual := by
  intro V A _ _ _ a hdiag hskew
  simpa [actual, realize, signature] using
    (_root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound
      a hdiag hskew)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 3)
  let A := ULift.{v} (ZMod 2)
  let a : V → V → A := fun i j =>
    if i = j then ULift.up (0 : ZMod 2) else ULift.up (1 : ZMod 2)
  have hdiag : ∀ i, a i i = 0 := by
    intro i; apply ULift.ext; simp [a]
  have hskew : ∀ i j, a j i = -a i j := by
    intro i j
    by_cases hij : i = j
    · subst j; apply ULift.ext; simp only [a]
      change (0 : ZMod 2) = -(0 : ZMod 2)
      norm_num
    · have hji : j ≠ i := by exact Ne.symm hij
      apply ULift.ext; simp only [a, hij, hji]
      change (1 : ZMod 2) = -(1 : ZMod 2)
      decide
  have hbad := (h (V := V) (A := A) a hdiag hskew).2.2 (fun _ => 0)
  norm_num [rejected, realize, signature, triangleDefects, a] at hbad
  have hterm := hbad (⟨0⟩ : V) (⟨1⟩ : V) (⟨2⟩ : V)
  have h01 : (⟨0⟩ : V) ≠ ⟨1⟩ := by decide
  have h12 : (⟨1⟩ : V) ≠ ⟨2⟩ := by decide
  have h20 : (⟨2⟩ : V) ≠ ⟨0⟩ := by decide
  simp only [if_neg h01, if_neg h12, if_neg h20] at hterm
  have hdown := congrArg ULift.down hterm
  change (1 : ZMod 2) + 1 + 1 = 0 at hdown
  exact (by decide : (1 : ZMod 2) + 1 + 1 ≠ 0) hdown

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
    _root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound
  in arena
  readout via (realize signature (fun _ _ n => 3 * n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability
