import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
open _root_.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Real
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
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
  realize signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
noncomputable def observedValues (r : Realization signature) (C : ℝ) (m : ℕ) : Set ℝ :=
  {v | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ (m.factorial : ℝ)^C ∧ (b : ℝ) ≤ (m.factorial : ℝ)^C ∧
    Nat.ModEq m.factorial a b ∧ v = r.readout () () a / r.readout () () b}
noncomputable def observedExtreme (r : Realization signature) (C : ℝ) (m : ℕ) : ℝ :=
  sSup (observedValues r C m)

abbrev arena : Arena where
  signature := signature
  Law r :=
    ∀ C : ℝ, 1 < C →
    (∀ m : ℕ, (observedValues r C m).Finite ∧ (1 : ℝ) ∈ observedValues r C m ∧
          observedExtreme r C m ∈ observedValues r C m ∧ 1 ≤ observedExtreme r C m) ∧
        (∀ᶠ m : ℕ in atTop,
          0 < lowerNumber C m ∧
          (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ)^C ∧
          (m.factorial : ℝ) ≤ (m.factorial : ℝ)^C ∧
          Nat.ModEq m.factorial (lowerNumber C m) m.factorial ∧
          Nat.Coprime m.factorial (primeBlock m (lowerCutoff C m)) ∧
          r.readout () () (lowerNumber C m) / r.readout () () m.factorial =
            ∏ p ∈ blockSet m (lowerCutoff C m), (1 + (p : ℝ)⁻¹)) ∧
        Tendsto (fun m : ℕ => (observedExtreme r C m - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (r.readout () () (lowerNumber C m) / r.readout () () m.factorial - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (r.readout () () (lowerNumber C m) - r.readout () () m.factorial) /
          (exp eulerMascheroniConstant * log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          r.readout () () (lowerNumber C m) - r.readout () () m.factorial) atTop atTop

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hone := (h 2 (by norm_num)).1 0 |>.2.1
  obtain ⟨a, b, ha, hb, haH, hbH, hab, heq⟩ := hone
  norm_num [rejected, realize] at heq

def registration : Registration arena (
    ∀ C : ℝ, 1 < C →
    (∀ m : ℕ, (pairValues C m).Finite ∧ (1 : ℝ) ∈ pairValues C m ∧
          extremeRatio C m ∈ pairValues C m ∧ 1 ≤ extremeRatio C m) ∧
        (∀ᶠ m : ℕ in atTop,
          0 < lowerNumber C m ∧
          (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ)^C ∧
          (m.factorial : ℝ) ≤ (m.factorial : ℝ)^C ∧
          Nat.ModEq m.factorial (lowerNumber C m) m.factorial ∧
          Nat.Coprime m.factorial (primeBlock m (lowerCutoff C m)) ∧
          normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial =
            ∏ p ∈ blockSet m (lowerCutoff C m), (1 + (p : ℝ)⁻¹)) ∧
        Tendsto (fun m : ℕ => (extremeRatio C m - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) /
          (exp eulerMascheroniConstant * log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) atTop atTop) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun C hC => result C hC, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change normalizedWeight 1 ≠ normalizedWeight 2
    have h2 : ArithmeticFunction.sigma 1 2 = 3 := by
      simpa using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
    norm_num [normalizedWeight, ArithmeticFunction.sigma_one, h2]

register_information_theorem _root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.result in arena
  readout via (realize signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
