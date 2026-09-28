import D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal BigOperators
noncomputable section
universe u

namespace Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
open _root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => ENNReal.ofReal x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (1 : ℝ≥0∞)) (fun e => nomatch e)

open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (U : Finset A) (hm : 3 ≤ U.card) (a : ℝ) (ha : 0 ≤ a)
    (w : Block A → ℝ) (hw : ∀ B, 0 ≤ w B)
    (hrow : ∀ i, ∑ B, experiment w i B = 1)
    (hcap : ∀ B : Block A, B.1 ⊆ U → B.1.card = 2 → a ≤ w B),
    let v := plus w U a
    let ep := a * ((U.card : ℝ) - 2) / (U.card : ℝ)
    let em := a * ((U.card : ℝ) - 2) / 2
    (∀ B, 0 ≤ v B) ∧
    (∀ i, ∑ B, experiment v i B = 1) ∧
    (∀ i j : A, i ≠ j →
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then v B else 0) =
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then w B else 0)) ∧
    finiteDeficiency (experiment w) (experiment v) = R.readout ⟨()⟩ () ep ∧
    finiteDeficiency (experiment v) (experiment w) = ENNReal.ofReal em ∧
    ∃ KP KM : FiniteMarkovKernel (Block A) (Block A),
      (∀ i, totalVariation (experiment w i) (channelOutput KP.1 (experiment v i)) =
        if i ∈ U then ep else 0) ∧
      (∀ i, totalVariation (experiment v i) (channelOutput KM.1 (experiment w i)) =
        if i ∈ U then em else 0) ∧
      (∀ K : FiniteMarkovKernel (Block A) (Block A),
        ep ≤ uniformSimulationError (experiment w) (experiment v) K) ∧
      (∀ K : FiniteMarkovKernel (Block A) (Block A),
        em ≤ uniformSimulationError (experiment v) (experiment w) K)

theorem actual_law : arena.{u}.Law actual := by
  intro A _ _ _ U hm a ha w hw hrow hcap
  exact _root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result
    U hm a ha w hw hrow hcap

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} (Fin 3)
  let U : Finset A := Finset.univ
  let w : Block A → ℝ := fun B => if B.1 = Finset.univ then 1 else 0
  have hm : 3 ≤ U.card := by simp [U, A]
  have hw : ∀ B, 0 ≤ w B := by intro B; dsimp [w]; split_ifs <;> norm_num
  let full : Block A := ⟨Finset.univ, Finset.univ_nonempty⟩
  have hr : ∀ i, ∑ B, experiment w i B = 1 := by
    intro i
    rw [Finset.sum_eq_single full]
    · simp [experiment, w, full]
    · intro B _ hne
      have hn : B.1 ≠ Finset.univ := fun hh => hne (Subtype.ext hh)
      simp [experiment, w, hn]
    · intro hfull
      exact (hfull (Finset.mem_univ full)).elim
  have hc : ∀ B : Block A, B.1 ⊆ U → B.1.card = 2 → (0 : ℝ) ≤ w B :=
    fun B _ _ => hw B
  have hb := (h U hm 0 le_rfl w hw hr hc).2.2.2.1
  have hg := (_root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result
    U hm 0 le_rfl w hw hr hc).2.2.2.1
  have hh := hg.symm.trans hb
  norm_num [rejected, realize] at hh

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

register_information_theorem _root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result in arena
  readout via (realize signature.{u} (fun _ _ x => ENNReal.ofReal x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "arg", "fn", "arg", "arg" ]
      stateOperand := some #["arg"] }] })
  escape continues (open)

end Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
