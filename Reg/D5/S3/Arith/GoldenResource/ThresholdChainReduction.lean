import D5.S3.Arith.GoldenResource.ThresholdChainReduction
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction

open Finset
open _root_.D5.S3.Arith.GoldenResource.ThresholdChainReduction
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Weil.GronwallLowerEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ B : ℕ, Σ U : ℕ,
    Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law := fun r =>
    ∀ {B U : ℕ} (hB : 3 ≤ B) (hU : U ≠ 0)
        (hBU : B ∣ U)
        (e : Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U})
        (horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2)),
        (exponentLayers B U).card =
          (∑ p ∈ U.primeFactors, (U.factorization p - B.factorization p)) ∧
        (exponentBox B U).card =
          (∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1)) ∧
        (∀ j ≤ (exponentLayers B U).card, r.readout () ⟨B, U, e⟩ j ∈ exponentBox B U) ∧
        (∀ j ≤ (exponentLayers B U).card, ∀ i : Fin (exponentLayers B U).card,
          i.val < j → ∀ k, B.factorization (e i).val.1 < k → k ≤ (e i).val.2 →
            ∃ r : Fin (exponentLayers B U).card,
              r.val < j ∧ (e r).val = ((e i).val.1, k)) ∧
        (∃ j ≤ (exponentLayers B U).card,
          IsLeast (robinLogMargin '' (↑(exponentBox B U) : Set ℕ))
            (robinLogMargin (r.readout () ⟨B, U, e⟩ j)) ∧
          IsLeast ((fun j => robinLogMargin (r.readout () ⟨B, U, e⟩ j)) ''
            Set.Iic (exponentLayers B U).card)
            (robinLogMargin (r.readout () ⟨B, U, e⟩ j))) ∧
        sInf (robinLogMargin '' (↑(exponentBox B U) : Set ℕ)) =
          sInf ((fun j => robinLogMargin (r.readout () ⟨B, U, e⟩ j)) ''
            Set.Iic (exponentLayers B U).card)

def actual : Realization signature :=
  realize signature (fun _ p j => layerChain p.1 p.2.1 p.2.2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def enumeration (B U : ℕ) :
    Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U} :=
  (Finset.equivFin (exponentLayers B U)).symm

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e := enumeration 3 3
  have hlayers : exponentLayers 3 3 = ∅ := by
    ext pk
    simp [exponentLayers]
  have horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2) := by
    intro i j hij
    have hi : i.val < 0 := by simpa [hlayers] using i.isLt
    omega
  have hp := h (B := 3) (U := 3) (by decide) (by decide) dvd_rfl e horder
  have hzero := hp.2.2.1 0 (Nat.zero_le _)
  change 0 ∈ exponentBox 3 3 at hzero
  have hz := (Nat.mem_divisors.mp (mem_filter.mp hzero).1).1
  norm_num at hz

def registration : Registration arena (
  ∀ {B U : ℕ} (hB : 3 ≤ B) (hU : U ≠ 0)
      (hBU : B ∣ U)
      (e : Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U})
      (horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2)),
      (exponentLayers B U).card =
        (∑ p ∈ U.primeFactors, (U.factorization p - B.factorization p)) ∧
      (exponentBox B U).card =
        (∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1)) ∧
      (∀ j ≤ (exponentLayers B U).card, layerChain B U e j ∈ exponentBox B U) ∧
      (∀ j ≤ (exponentLayers B U).card, ∀ i : Fin (exponentLayers B U).card,
        i.val < j → ∀ k, B.factorization (e i).val.1 < k → k ≤ (e i).val.2 →
          ∃ r : Fin (exponentLayers B U).card,
            r.val < j ∧ (e r).val = ((e i).val.1, k)) ∧
      (∃ j ≤ (exponentLayers B U).card,
        IsLeast (robinLogMargin '' (↑(exponentBox B U) : Set ℕ))
          (robinLogMargin (layerChain B U e j)) ∧
        IsLeast ((fun j => robinLogMargin (layerChain B U e j)) ''
          Set.Iic (exponentLayers B U).card)
          (robinLogMargin (layerChain B U e j))) ∧
      sInf (robinLogMargin '' (↑(exponentBox B U) : Set ℕ)) =
        sInf ((fun j => robinLogMargin (layerChain B U e j)) ''
          Set.Iic (exponentLayers B U).card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨threshold_chain_reduction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let e := enumeration 3 6
    have hlayers : exponentLayers 3 6 = {(2, 1)} := by
      have htwo : Nat.Prime 2 := by norm_num
      have hthree : Nat.Prime 3 := by norm_num
      have hu : (6 : ℕ).primeFactors = {2, 3} := by
        rw [show 6 = 2 * 3 from rfl, Nat.primeFactors_mul (by decide) (by decide),
          htwo.primeFactors, hthree.primeFactors]
        rfl
      have hf : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
        rw [show 6 = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
          htwo.factorization, hthree.factorization]
      simp [exponentLayers, hu, hf, hthree.factorization]
    have hcard : (exponentLayers 3 6).card = 1 := by rw [hlayers]; rfl
    have hvalue (r : Fin (exponentLayers 3 6).card) : (e r).val = (2, 1) := by
      have hr := (e r).property
      simp only [hlayers, mem_singleton] at hr
      exact hr
    refine ⟨⟨3, 6, e⟩, 0, 1, ?_⟩
    change layerChain 3 6 e 0 ≠ layerChain 3 6 e 1
    have hfull : (univ.filter fun r : Fin (exponentLayers 3 6).card => r.val < 1) =
        univ := by
      apply filter_eq_self.mpr
      intro r hr
      simpa [hcard] using r.isLt
    simp only [layerChain, Nat.not_lt_zero, filter_false, prod_empty, mul_one, hfull]
    have hprod : (∏ r : Fin (exponentLayers 3 6).card, (e r).val.1) = 2 := by
      simp only [hvalue]
      simp [hcard]
    rw [hprod]
    decide

register_information_theorem threshold_chain_reduction in arena
  readout via (realize signature
    (fun _ p j => layerChain p.1 p.2.1 p.2.2 j) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenResource.ThresholdChainReduction
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "body", "body", "arg", "fn"]
      functionOperand := true }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Arith.GoldenResource.ThresholdChainReduction.threshold_chain_reduction
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true | _ => false) do
    throwError "Threshold chain registration is not declaredValidated"

#print axioms registration

end
end Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction
