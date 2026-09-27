import D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
open LeanInformationAudit
open Set

noncomputable section
namespace Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity

abbrev signature : Signature where
  Params := Σ _aOne : ℝ, Σ _dOne : ℝ, Σ _bOne : ℝ, Σ _piOne : ℝ,
    Σ _aTwo : ℝ, Σ _MTwo : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p d => asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p d =>
      asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (aOne dOne bOne piOne aTwo MTwo piTwo : ℝ),
    ((0 < aOne ∧ aOne ≤ dOne ∧ 0 < bOne ∧ bOne + aOne + dOne < 1 ∧
        piOne ∈ Set.Icc (0 : ℝ) 1) →
      let M := bOne + aOne + dOne
      let D := 1 - M
      let tMinus := aOne / (2 * aOne + D)
      let tPlus := (dOne + D) / (2 * dOne + D)
      (0 < tMinus ∧ tMinus < 1 / 2 ∧ 1 / 2 < tPlus ∧ tPlus < 1) ∧
      (piOne ∈ Set.Icc 0 tMinus → asymmetricBayesRisk aOne dOne bOne piOne = piOne) ∧
      (piOne ∈ Set.Icc tMinus (1 / 2) →
        asymmetricBayesRisk aOne dOne bOne piOne =
          aOne + piOne * (M - 2 * aOne)) ∧
      (piOne ∈ Set.Icc (1 / 2) tPlus →
        asymmetricBayesRisk aOne dOne bOne piOne =
          M * (1 - piOne) + (2 * piOne - 1) * dOne) ∧
      (piOne ∈ Set.Icc tPlus 1 →
        asymmetricBayesRisk aOne dOne bOne piOne = 1 - piOne)) ∧
    ((0 < 2 * aTwo ∧ 2 * aTwo < MTwo ∧ MTwo < 1 ∧
        1 / 2 < piTwo ∧ piTwo ≤ 1) →
      let D := 1 - MTwo
      let L := MTwo - aTwo
      let U := 2 * L + D
      let s := 2 * piTwo - 1
      let c := MTwo * (1 - piTwo)
      let t := D * (1 - s) / (2 * s)
      (∀ d ∈ Set.Ico aTwo L,
        R.readout () ⟨aOne, dOne, bOne, piOne, aTwo, MTwo, piTwo⟩ d =
          c + s * min d t) ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) ↔
        piTwo ≤ (L + D) / (2 * L + D)) ∧
      (L + D) / (2 * L + D) = (1 + D / U) / 2 ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) →
        s ≤ D / U) ∧
      Set.InjOn
        (asymmetricFiberRisk MTwo aTwo ((L + D) / (2 * L + D)))
        (Set.Ico aTwo L) ∧
      2 * ((L + D) / (2 * L + D)) - 1 = D / U)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbadAll := (h 0 0 0 0 (1 / 8) (1 / 2) (3 / 4)).2 (by norm_num)
  have hbad := hbadAll.1 (1 / 8) (by norm_num)
  have hgoodAll :=
    (asymmetric_family_risk_and_injective_queries 0 0 0 0 (1 / 8) (1 / 2) (3 / 4)).2
      (by norm_num)
  have hgood := hgoodAll.1 (1 / 8) (by norm_num)
  simp only [rejected, realize, signature] at hbad
  linarith

theorem actual_law : arena.Law actual := by
  intro aOne dOne bOne piOne aTwo MTwo piTwo
  simpa only [actual, realize, signature] using
    asymmetric_family_risk_and_injective_queries
      aOne dOne bOne piOne aTwo MTwo piTwo

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
  let p : signature.Params := ⟨0, 0, 0, 0, 1 / 8, 1 / 2, 3 / 4⟩
  refine ⟨p, 1 / 8, 1 / 4, ?_⟩
  intro heq
  have hgoodAll :=
    (asymmetric_family_risk_and_injective_queries 0 0 0 0 (1 / 8) (1 / 2) (3 / 4)).2
      (by norm_num)
  have hx := hgoodAll.1 (1 / 8) (by norm_num)
  have hy := hgoodAll.1 (1 / 4) (by norm_num)
  simp only [actual, realize, signature, p] at heq
  norm_num at hx hy
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem asymmetric_family_risk_and_injective_queries in arena
  readout via (realize signature
    (fun _ p d => asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 14 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
