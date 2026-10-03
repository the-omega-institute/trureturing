import D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Real
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
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

noncomputable def observedError (r : Realization signature) (C : ℝ) (m : ℕ) : ℝ := sSup
  {v : ℝ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ exp (C * m * log m) ∧ (b : ℝ) ≤ exp (C * m * log m) ∧
    Nat.ModEq m.factorial a b ∧ v = |r.readout () () a / r.readout () () b - 1|}

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ m n : ℕ, 2 ≤ m → 0 < n → ∀ X : ℝ, (m : ℝ) ≤ X →
      1 ≤ highWeight m n ∧ highWeight m n ≤
        primeProduct X / primeProduct m * exp (log n / ((X - 1) * log X))) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ a b : ℕ, 0 < a → 0 < b →
        (a : ℝ) ≤ exp (C * m * log m) → (b : ℝ) ≤ exp (C * m * log m) →
        Nat.ModEq m.factorial a b →
        |r.readout () () a / r.readout () () b - 1| < ε) ∧
    (∀ C : ℝ, 0 < C → Tendsto (fun m : ℕ => observedError r C m) atTop (𝓝 0))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.2.1 1 (by norm_num) (1/2) (by norm_num)
  obtain ⟨m, hm, hbound⟩ := (he.and (eventually_ge_atTop (2 : ℕ))).exists
  have hs : (1 : ℝ) ≤ exp (1 * m * log m) := by
    apply one_le_exp_iff.mpr
    have hlog : 0 ≤ log (m : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    positivity
  have hf := hm 1 1 (by norm_num) (by norm_num) (by simpa using hs) (by simpa using hs) (Nat.ModEq.refl 1)
  norm_num [rejected, realize] at hf

def registration : Registration arena (
    (∀ m n : ℕ, 2 ≤ m → 0 < n → ∀ X : ℝ, (m : ℝ) ≤ X →
      1 ≤ highWeight m n ∧ highWeight m n ≤
        primeProduct X / primeProduct m * exp (log n / ((X - 1) * log X))) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ a b : ℕ, 0 < a → 0 < b →
        (a : ℝ) ≤ exp (C * m * log m) → (b : ℝ) ≤ exp (C * m * log m) →
        Nat.ModEq m.factorial a b →
        |normalizedWeight a / normalizedWeight b - 1| < ε) ∧
    (∀ C : ℝ, 0 < C → Tendsto (fun m : ℕ => uniformError C m) atTop (𝓝 0))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change normalizedWeight 1 ≠ normalizedWeight 2
    have h2 : ArithmeticFunction.sigma 1 2 = 3 := by
      simpa using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
    norm_num [normalizedWeight, ArithmeticFunction.sigma_one, h2]

register_information_theorem result in arena
  readout via (realize signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "body", "body", "fn", "arg",
      "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
      "arg", "fn", "arg", "fn", "arg", "fn"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
