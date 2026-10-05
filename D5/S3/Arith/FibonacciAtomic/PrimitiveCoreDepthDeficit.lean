/- GID: D5/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Primitive nonnegative compositions have unique exit cores and logarithmic depth bounds. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S0.Carrier.Norm
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimitiveCoreDepthDeficit

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity atomicBlock)
open D5.S0.Carrier (norm)
local notation "φ" => Real.goldenRatio

private theorem step_injective : Function.Injective (step (A := ℕ)) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [step] at h₁ h₂
  exact Prod.ext (by omega) h₁

private theorem core_exists (x : ℕ × ℕ) (hx : x ≠ (0, 0)) :
    ∃ j : ℕ, ∃ c : ℕ × ℕ, c.2 < c.1 ∧ x = step^[j] c := by
  suffices h : ∀ n : ℕ, ∀ x : ℕ × ℕ, quantity x = n → x ≠ (0, 0) →
      ∃ j : ℕ, ∃ c : ℕ × ℕ, c.2 < c.1 ∧ x = step^[j] c from
    h (quantity x) x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hn hx
    by_cases hc : x.2 < x.1
    · exact ⟨0, x, hc, rfl⟩
    · have hle : x.1 ≤ x.2 := by omega
      let y : ℕ × ℕ := (x.2 - x.1, x.1)
      have hy : y ≠ (0, 0) := by
        intro hz
        have h₁ := congrArg Prod.fst hz
        have h₂ := congrArg Prod.snd hz
        dsimp [y] at h₁ h₂
        apply hx
        exact Prod.ext h₂ (by omega)
      have hdec : quantity y < n := by
        dsimp [quantity, y] at hn ⊢
        have hnonzero : 0 < x.1 + x.2 := by
          by_contra hz
          apply hx
          exact Prod.ext (by omega) (by omega)
        omega
      obtain ⟨j, c, hcore, hrep⟩ := ih (quantity y) hdec y rfl hy
      refine ⟨j + 1, c, hcore, ?_⟩
      rw [Function.iterate_succ_apply', ← hrep]
      dsimp [step, y]
      exact Prod.ext rfl (by omega)

private theorem core_unique (j k : ℕ) (c d : ℕ × ℕ)
    (hc : c.2 < c.1) (hd : d.2 < d.1)
    (heq : step^[j] c = step^[k] d) : j = k ∧ c = d := by
  have ordered (j k : ℕ) (c d : ℕ × ℕ) (hc : c.2 < c.1)
      (hjk : j ≤ k) (heq : step^[j] c = step^[k] d) : j = k ∧ c = d := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [Function.iterate_add_apply] at heq
    have hcancel := (step_injective.iterate j) heq
    cases m with
    | zero => simpa using And.intro rfl hcancel
    | succ m =>
      rw [Function.iterate_succ_apply'] at hcancel
      have h₁ := congrArg Prod.fst hcancel
      have h₂ := congrArg Prod.snd hcancel
      simp only [step] at h₁ h₂
      omega
  rcases le_total j k with h | h
  · exact ordered j k c d hc h heq
  · have h' := ordered k j d c hd h heq.symm
    exact ⟨h'.1.symm, h'.2.symm⟩

end D5.S3.Arith.FibonacciAtomic.PrimitiveCoreDepthDeficit
