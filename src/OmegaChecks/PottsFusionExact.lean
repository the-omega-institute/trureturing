module

import OmegaMath.InformationTheory.PottsFusion.Channel
import Mathlib.Tactic.Positivity

open Omega.InformationTheory.PottsFusion

universe u v

example (q : ℕ) (hq : 2 ≤ q) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (Y : Type u) (Z : Type v) [Fintype Y] [Fintype Z]
        (P : Fin q → Y → ℝ) (Q : Fin q → Z → ℝ),
        (∀ i y, 0 ≤ P i y) → (∀ i, ∑ y, P i y = 1) →
        (∀ i z, 0 ≤ Q i z) → (∀ i, ∑ z, Q i z = 1) →
        (∃ a : Equiv.Perm (Fin q) →* Equiv.Perm Y,
          ∀ σ i y, P (σ i) ((a σ) y) = P i y) →
        (∃ a : Equiv.Perm (Fin q) →* Equiv.Perm Z,
          ∀ σ i z, Q (σ i) ((a σ) z) = Q i z) →
        ∀ ε : ℝ, 0 < ε → channelCapacity P ≤ ε →
          channelCapacity (fun i (yz : Y × Z) => P i yz.1 * Q i yz.2) ≤
            (1 + A * Real.rpow ε (1 / 5)) *
              (channelCapacity P + channelCapacity Q) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  refine ⟨8 * (q : ℝ) ^ 4 + (q : ℝ), by positivity, ?_⟩
  intro Y Z _ _ P Q hp hps hq hqs hpa hqa ε hε0 hε
  obtain ⟨a, ha⟩ := hpa
  obtain ⟨b, hb⟩ := hqa
  let pc : FMSChannel (Fin q) Y := ⟨P, hp, hps, a, ha⟩
  let qc : FMSChannel (Fin q) Z := ⟨Q, hq, hqs, b, hb⟩
  have h := star_capacity_local_subadditivity pc qc ε hε0 hε
  simpa only [FMSChannel.capacity, FMSChannel.star, Fintype.card_fin] using h
