import D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u

namespace Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
open _root_.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => min 1 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

open scoped BigOperators ENNReal
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric

def arena : Arena where
  signature := signature.{u}
  Law observation := ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (w v : Block A → ℝ) (hw : ∀ B, 0 ≤ w B) (hv : ∀ C, 0 ≤ v C)
    (hwrow : ∀ i, ∑ B, row w i B = 1) (hvrow : ∀ i, ∑ C, row v i C = 1)
    (H : FiniteMarkovKernel (Block A) (Block A)),
    let ε := fun i => totalVariation (channelOutput H.1 (row w i)) (row v i)
    let Δ := fun i j => pair v i j - pair w i j
    let b := fun i => (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i, (Δ i j + ε i + ε j)
    let εmax := Finset.univ.sup' Finset.univ_nonempty ε
    let η := Finset.univ.sup' Finset.univ_nonempty
      (fun ij : A × A => if ij.1 = ij.2 then (0 : ℝ) else |Δ ij.1 ij.2|)
    let bmax := Finset.univ.sup' Finset.univ_nonempty b
    ∃ R : FiniteMarkovKernel (Block A) (Block A),
      (∀ i j, 0 ≤ Δ i j + ε i + ε j) ∧
      (∀ i, totalVariation (channelOutput R.1 (row v i)) (row w i) ≤ b i) ∧
      finiteDeficiency (row w) (row v) ≤ ENNReal.ofReal (min 1 bmax) ∧
      min 1 bmax ≤ observation.readout ⟨()⟩ () (((Fintype.card A : ℝ) - 1) * η / 2 +
        ((Fintype.card A : ℝ) - 1) * εmax) ∧
      ((∀ i, ε i = 0) → ∀ B C, 0 < v C →
        R.1 C B = if B.1 ⊆ C.1 then
          (B.1.card : ℝ) * (w B * H.1 B C) / ((C.1.card : ℝ) * v C) else 0)

theorem actual_law : arena.{u}.Law actual := by
  intro A _ _ _ w v hw hv hwrow hvrow H
  exact _root_.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result
    w v hw hv hwrow hvrow H

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} Unit
  have hmem (i : A) (B : Block A) : i ∈ B.1 := by
    obtain ⟨j, hj⟩ := B.2
    simpa only [Subsingleton.elim j i] using hj
  letI : Unique (Block A) := {
    default := ⟨Finset.univ, Finset.univ_nonempty⟩
    uniq := fun B => Subtype.ext (Finset.eq_univ_of_forall (fun i => hmem i B)) }
  let w : Block A → ℝ := fun _ => 1
  have hw : ∀ B, 0 ≤ w B := fun _ => zero_le_one
  have hr : ∀ i, ∑ B, row w i B = 1 := by
    intro i
    simp [row, w, hmem]
  let H : FiniteMarkovKernel (Block A) (Block A) :=
    ⟨fun B C => if B = C then 1 else 0, by
      constructor
      · intro B C; exact ite_nonneg zero_le_one le_rfl
      · intro B
        change (∑ C : Block A, if B = C then (1 : ℝ) else 0) = 1
        simp only [Finset.univ_unique, Finset.sum_singleton, if_pos (Subsingleton.elim B default)]⟩
  obtain ⟨R, _, _, _, hb, _⟩ := h w w hw hw hr hr H
  have herase (i : A) : Finset.univ.erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp only [herase, Finset.sum_empty, mul_zero] at hb
  norm_num [rejected, realize] at hb

theorem dependence_proof : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j h
    exact (h (@Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
  · intro i
    exact nomatch i

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result in arena
  readout via (realize signature.{u} (fun _ _ x => min 1 x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "arg",
        "arg", "fn", "arg", "arg" ]
      stateOperand := some #["arg"] }] })
  escape continues (open)

end Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
