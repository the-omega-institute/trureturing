import D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
open _root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency

abbrev signature : Signature where
  Params := Σ _a : ℝ, Σ _M : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p dTwo =>
      let L := p.2.1 - p.1
      let QOne := asymmetricExperiment p.1 p.2.2 (L - p.2.2)
      let QTwo := asymmetricExperiment p.1 dTwo (L - dTwo)
      finiteDeficiency QOne QTwo)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a M dOne dTwo : ℝ),
    0 < 2 * a → 2 * a < M → M < 1 → a ≤ dOne → dOne < dTwo → dTwo < M - a →
    let D := 1 - M
    let L := M - a
    let QOne := asymmetricExperiment a dOne (L - dOne)
    let QTwo := asymmetricExperiment a dTwo (L - dTwo)
    let gamma := D * (dTwo - dOne) / (2 * dTwo + D)
    finiteDeficiency QTwo QOne = 0 ∧
      R.readout () ⟨a, M, dOne⟩ dTwo = ENNReal.ofReal gamma ∧
      0 < gamma

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad :=
    (h (1 / 8) (3 / 4) (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).2.1
  simp only [rejected, realize, signature] at hbad
  exact (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) hbad.symm

theorem actual_law : arena.Law actual := by
  intro a M dOne dTwo ha haM hM hadOne hdOneTwo hdTwo
  simpa only [actual, realize, signature] using
    asymmetric_family_deficiency a M dOne dTwo ha haM hM hadOne hdOneTwo hdTwo

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  let p : signature.Params := ⟨1 / 8, 3 / 4, 1 / 4⟩
  refine ⟨p, 3 / 8, 1 / 2, ?_⟩
  intro heq
  have hx :=
    (asymmetric_family_deficiency (1 / 8) (3 / 4) (1 / 4) (3 / 8)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).2.1
  have hy :=
    (asymmetric_family_deficiency (1 / 8) (3 / 4) (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).2.1
  simp only [actual, realize, signature, p] at heq
  rw [hx, hy] at heq
  norm_num at heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem asymmetric_family_deficiency in arena
  readout via (realize signature
    (fun _ p dTwo =>
      let L := p.2.1 - p.1
      let QOne := asymmetricExperiment p.1 p.2.2 (L - p.2.2)
      let QTwo := asymmetricExperiment p.1 dTwo (L - dTwo)
      finiteDeficiency QOne QTwo)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
