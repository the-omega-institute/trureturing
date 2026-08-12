/- GID: D5/S3/Entropy/Forgetting/CapacityMonotone
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/CapacityMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A genuine finite carrier merge lowers accessible capacity and cannot increase Shannon entropy. -/

/- Library-search audit trail (2026-08-12):
   * The repository's finite entropy API supplies the maximum-entropy bound and the entropy chain
     rule, but no deterministic pushforward entropy theorem.
   * The proof below therefore constructs the graph-supported joint law of a deterministic forgetting
     map, identifies its first marginal with the pushforward, and applies the frozen chain rule plus
     conditional-entropy nonnegativity.
   * Capacity is the independent accessible-outcome count `Fintype.card X`; it is not defined from
     entropy or KL divergence.
-/

import D5.S3.Entropy.ConditionalEntropy
import D5.S3.Entropy.EntropyNonneg

namespace D5.S3.Entropy.Forgetting.CapacityMonotone

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.EntropyNonneg
open D5.S3.Entropy.MaxEntropy

/-- The accessible capacity of a finite outcome carrier is its number of accessible outcomes. -/
def accessibleCapacity (X : Type*) [Fintype X] : ℕ := Fintype.card X

/-- The mass function obtained by deterministically forgetting `X` through `f : X → Y`. -/
noncomputable def pushforward {X Y : Type*} [Fintype X]
    (f : X → Y) (p : X → ℝ) (y : Y) : ℝ :=
  by classical exact ∑ x, if f x = y then p x else 0

/-- Unit column sums preserve the uniform mass function on a finite carrier. -/
theorem channel_output_uniform {X : Type*} [Fintype X] [Nonempty X]
    (W : X → X → ℝ) (hcol : ∀ y, ∑ x, W x y = 1) :
    D5.S3.Divergence.ClassicalDPI.channelOutput W
        (fun _ => (Fintype.card X : ℝ)⁻¹) =
      fun _ => (Fintype.card X : ℝ)⁻¹ := by
  funext y
  rw [D5.S3.Divergence.ClassicalDPI.channelOutput, ← Finset.mul_sum, hcol y, mul_one]

/-- A deterministic carrier merge cannot increase the Shannon entropy of a probability law.
The output is the pushforward law on the smaller accessible carrier. -/
theorem deterministic_forgetting_entropy_capacity_monotone {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (p : X → ℝ) (f : X → Y)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hsurj : Function.Surjective f) :
    shannonEntropy (pushforward f p) ≤ shannonEntropy p ∧
      shannonEntropy (pushforward f p) ≤
        Real.log (accessibleCapacity Y : ℝ) ∧
      accessibleCapacity Y ≤ accessibleCapacity X := by
  classical
  let joint : Y × X → ℝ := fun z => if f z.2 = z.1 then p z.2 else 0
  have hjoint_nonneg : ∀ z, 0 ≤ joint z := by
    intro z
    simp only [joint]
    split_ifs
    · exact hp.1 z.2
    · exact le_rfl
  have hjoint_sum : ∑ z, joint z = 1 := by
    simp only [joint, Fintype.sum_prod_type]
    calc
      (∑ y, ∑ x, if f x = y then p x else 0) =
          ∑ x, ∑ y, if f x = y then p x else 0 := Finset.sum_comm
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x _
        simp
      _ = 1 := hp.2
  have hjoint_law : (∀ z, 0 ≤ joint z) ∧ ∑ z, joint z = 1 :=
    ⟨hjoint_nonneg, hjoint_sum⟩
  have hmarginal : marginal joint = pushforward f p := by
    funext y
    rfl
  have hjoint_entropy : shannonEntropy joint = shannonEntropy p := by
    rw [shannonEntropy, Fintype.sum_prod_type]
    calc
      (∑ y, ∑ x, Real.negMulLog (if f x = y then p x else 0)) =
          ∑ x, ∑ y, Real.negMulLog (if f x = y then p x else 0) := Finset.sum_comm
      _ = ∑ x, Real.negMulLog (p x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single (f x)]
        · simp
        · intro y _ hy
          simp [Ne.symm hy]
        · simp
      _ = shannonEntropy p := rfl
  have hentropy_merge : shannonEntropy (pushforward f p) ≤ shannonEntropy p := by
    have hchain := entropy_chain_rule joint hjoint_nonneg
    have hconditional := conditional_entropy_nonneg joint hjoint_nonneg
    rw [hmarginal, hjoint_entropy] at hchain
    linarith
  have hpushforward_law :
      (∀ y, 0 ≤ pushforward f p y) ∧ ∑ y, pushforward f p y = 1 := by
    constructor
    · intro y
      simp only [pushforward]
      exact Finset.sum_nonneg fun x _ => by
        by_cases h : f x = y <;> simp [h, hp.1 x]
    · calc
        (∑ y, pushforward f p y) = ∑ y, marginal joint y := by rw [hmarginal]
        _ = ∑ y, ∑ x, joint (y, x) := by rfl
        _ = 1 := by simpa only [Fintype.sum_prod_type] using hjoint_sum
  have hcapacity : accessibleCapacity Y ≤ accessibleCapacity X := by
    simpa [accessibleCapacity] using Fintype.card_le_of_surjective f hsurj
  exact ⟨hentropy_merge, entropy_le_log_card (pushforward f p) hpushforward_law, hcapacity⟩

/-- Merging the two Boolean outcomes into one record strictly lowers both entropy and carrier size. -/
theorem bool_unit_merge_strict_witness :
    let p : Bool → ℝ := fun _ => 1 / 2
    let f : Bool → Unit := fun _ => ()
    shannonEntropy (pushforward f p) < shannonEntropy p ∧
      Real.log (accessibleCapacity (Unit) : ℝ) <
        Real.log (accessibleCapacity Bool : ℝ) := by
  dsimp
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  norm_num [shannonEntropy, pushforward, Real.negMulLog, accessibleCapacity,
    Fintype.sum_bool, hhalf]
  exact hlog

end D5.S3.Entropy.Forgetting.CapacityMonotone
