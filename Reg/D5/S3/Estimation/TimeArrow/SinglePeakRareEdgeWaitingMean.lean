import D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean
import Reg.Support.DependentFamily
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeSurvival
open LeanInformationAudit
open Lean Elab Command
open Filter
open scoped Topology

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean

universe u

-- Keep the source Fintype dictionary in its original parameter position.
@[reducible] def signature : Signature where
  Params := Sigma fun X : Type u => Sigma fun _ : Fintype X =>
    Sigma fun _ : X → ℝ => Sigma fun _ : X => Sigma fun _ : ℝ => Sigma fun _ : ℝ => Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def pack {X : Type u} [Fintype X] (chi : X → ℝ) (z : X) (r q : ℝ) (M : Nat) :
    signature.Params := ⟨X, ⟨inferInstance, ⟨chi, ⟨z, ⟨r, ⟨q, M⟩⟩⟩⟩⟩⟩

def actual : Realization signature :=
  realize signature
    (fun _ p T => letI := p.2.1; survival p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 T)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

-- Only the nominated first survival occurrence varies; all other clauses stay original.
def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1)
    (z : X) (hz : chi z = 1) (r q : ℝ) (M : Nat)
    (hcard : Fintype.card X = 2 * M)
    (hplus : ((Finset.univ.filter fun x => chi x = 1).card) = M)
    (hM : 2 ≤ M) (hq : q = r / ((M : ℝ) - 1)) (hr0 : 0 < r) (hr1 : r < 1),
    (∀ T : Nat, 0 ≤ R.readout () (pack chi z r q M) T) ∧
      Antitone (survival chi z r q) ∧
      Tendsto (survival chi z r q) atTop (nhds 0) ∧
      HasSum (fun T : Nat => survival chi z r q T)
        (2 * (Fintype.card X : ℝ) - 1 - r) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        HasSum (fun T : Nat => survival chi z r q T * u ^ T)
          ((1 - (1 / (2 * (Fintype.card X : ℝ))) * u -
              (1 / (2 * (Fintype.card X : ℝ))) * r * u ^ 2) /
            (1 - u + (1 / (2 * (Fintype.card X : ℝ))) * (1 - r) * u ^ 2 +
              (1 / (2 * (Fintype.card X : ℝ))) * r * u ^ 3))

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean
  let sourceName := `D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean.survival_waiting_mean
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := theoremStatementIdentity (← getEnv) sourceName
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem actual_law : arena.{u}.Law actual.{u} := by
  intro X inst chi hchi z hz r q M hcard hplus hM hq hr0 hr1
  simpa [actual, realize, pack, signature] using
    (survival_waiting_mean chi hchi z hz r q M hcard hplus hM hq hr0 hr1)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hbad := h (X := ULift.{u} (Fin 4)) (chi := fun x : ULift.{u} (Fin 4) =>
      if x.down.val < 2 then 1 else -1) (hchi := by
        intro x; rcases x with ⟨x⟩; fin_cases x <;> simp)
      (z := ⟨0⟩) (hz := by simp) (r := 1 / 2) (q := 1 / 2) (M := 2)
      (by simp) (by
        have hset : Finset.univ.filter (fun x : ULift.{u} (Fin 4) =>
            (if x.down.val < 2 then (1 : ℝ) else -1) = 1) = {⟨0⟩, ⟨1⟩} := by
          ext x; rcases x with ⟨x⟩; fin_cases x <;> norm_num [ULift.up.injEq]
        rw [hset]; decide) (by omega) (by norm_num) (by norm_num) (by norm_num)
  have hfirst := hbad.1 0
  simp [rejected, realize, pack, signature] at hfirst
  norm_num at hfirst

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  cases i
  let X := ULift.{u} (Fin 4)
  let chi : X → ℝ := fun x => if x.down.val < 2 then 1 else -1
  have hchi : ∀ x : X, chi x = 1 ∨ chi x = -1 := by
    intro x; rcases x with ⟨x⟩; fin_cases x <;> norm_num [chi, X, ULift.up.injEq]
  have hplus : ((Finset.univ.filter fun x : X => chi x = 1).card) = 2 := by
    have hset : Finset.univ.filter (fun x : X => chi x = 1) = {⟨0⟩, ⟨1⟩} := by
      ext x; rcases x with ⟨x⟩; fin_cases x <;> norm_num [chi, X, ULift.up.injEq]
    rw [hset]
    decide
  let p : signature.{u}.Params := pack chi ⟨0⟩ (1 / 2) (1 / 2) 2
  refine ⟨p, 0, 1, ?_⟩
  have h0 := survival_recurrence chi hchi ⟨0⟩ (by simp [chi])
      (1 / 2) (1 / 2) 2 (by simp [X]) hplus (by omega) (by norm_num)
  simpa [actual, realize, p, pack, signature, chi] using (show
    survival chi ⟨0⟩ (1 / 2) (1 / 2) 0 ≠ survival chi ⟨0⟩ (1 / 2) (1 / 2) 1 by
      rw [h0.1, h0.2.1]
      norm_num [X])

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected.{u}, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem survival_waiting_mean in arena
  readout via (realize signature.{u}
    (fun _ p T => letI := p.2.1; survival p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 T)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean
    coordinates := #[0, 2, 4, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean
