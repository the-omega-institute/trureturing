/- GID: D5/S3/Divergence/PottsLocalSubadditivity
   generality: G
   mirror-B: D5/B/S3/Divergence/PottsLocalSubadditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform local chi-square subadditivity for finite symmetric channels. -/

module

public import OmegaMath.InformationTheory.PottsFusion.Channel
import Mathlib.Tactic.Positivity

/-! # Local chi-square subadditivity under a common uniform input -/

@[expose] public section

namespace D5.S3.Divergence.PottsLocalSubadditivity

open Omega.InformationTheory.PottsFusion

universe u v

/-- A uniform fifth-root error bound for arbitrary finite output alphabets. -/
theorem fully_symmetric_fusion_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (Y : Type u) (Z : Type v) [Fintype Y] [Fintype Z]
        (P : FMSChannel (Fin q) Y) (Q : FMSChannel (Fin q) Z)
        (ε : ℝ), 0 < ε → P.capacity ≤ ε →
          (P.star Q).capacity ≤
            (1 + A * Real.rpow ε (1 / 5)) * (P.capacity + Q.capacity) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  refine ⟨8 * (q : ℝ) ^ 4 + (q : ℝ), by positivity, ?_⟩
  intro Y Z _ _ P Q ε hε0 hε
  simpa only [Fintype.card_fin] using
    star_capacity_local_subadditivity P Q ε hε0 hε

end D5.S3.Divergence.PottsLocalSubadditivity
