import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Asymptotics
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => delta m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => r.readout () () m - 1) =O[atTop]
      (fun m : ℕ => (Real.sqrt m)⁻¹)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ho := h.2.2
  change (fun _ : ℕ => (0 : ℝ) - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹) at ho
  have hi : Tendsto (fun m : ℕ => (Real.sqrt m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hc : (0 : ℝ) - 1 = 0 := tendsto_nhds_unique tendsto_const_nhds (ho.trans_tendsto hi)
  norm_num at hc

def registration : Registration arena (
(∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => delta m - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change delta 0 ≠ delta 2
    have hprimes : (Ioc 0 2).filter Nat.Prime = {2} := by decide
    norm_num [delta, hprimes]

register_information_theorem result in arena
  readout via (realize signature (fun _ _ m => delta m) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
