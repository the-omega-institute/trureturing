import D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments

abbrev signature : Signature where
  Params := ℕ
  State k := Fin k → ℤˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (mu : ℝ), 2 ≤ k → -1 ≤ mu → mu ≤ 1 →
    (∀ eta : Fin k → ℤˣ,
      signPairUStatistic eta = R.readout () k eta) ∧
    (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta) =
      mu ^ 2 ∧
    (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta ^ 2) -
        (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta) ^ 2 =
      4 * mu ^ 2 * (1 - mu ^ 2) / k +
        2 * (1 - mu ^ 2) ^ 2 / ((k : ℝ) * ((k : ℝ) - 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcase := (h 2 0 (by norm_num) (by norm_num) (by norm_num)).1
    (fun _ : Fin 2 => (1 : ℤˣ))
  norm_num [rejected, realize, signature, signPairUStatistic, Fin.sum_univ_succ] at hcase
  have hc :
      (Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 1 := by
    decide
  have hz :
      (Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 0 := by
    exact_mod_cast hcase
  omega

theorem actual_law : arena.Law actual := by
  intro k mu hk hmu_lower hmu_upper
  simpa [actual, realize, signature] using
    sign_pair_u_statistic_moments k mu hk hmu_lower hmu_upper

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
  let plus : Fin 2 → ℤˣ := fun _ => 1
  let mixed : Fin 2 → ℤˣ := fun j => if j = 0 then 1 else -1
  refine ⟨2, plus, mixed, ?_⟩
  norm_num [actual, realize, signature, plus, mixed, Fin.sum_univ_succ]
  have hc :
      (Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 1 := by
    decide
  have hreal :
      ((Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card : ℝ) +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 1 := by
    exact_mod_cast hc
  norm_num [hreal]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem sign_pair_u_statistic_moments in arena
  readout via (realize signature
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
